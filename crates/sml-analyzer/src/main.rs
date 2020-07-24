use std::collections::HashMap;
use std::error::Error;
use std::time::Instant;

use log::info;
use lsp_types::{
    notification::{DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument},
    request::{Completion, HoverRequest},
    InitializeParams, ServerCapabilities, *,
};

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use serde::Serialize;

use sml_util::{interner::*, span::Span};

use database::Database;

mod cache;
mod completions;
mod dispatch;
mod types;
mod util;

struct GlobalState<'arena> {
    text_cache: HashMap<lsp_types::Url, String>,
    kw_completions: Vec<CompletionItem>,
    interner: Interner,
    sender: crossbeam_channel::Sender<lsp_server::Message>,
    // def_cache: cache::Definitions<'arena>,
    arena: &'arena database::arena::Arena<'arena>,

    db: Database<'arena>,
}

pub fn diag_convert(diag: sml_util::diagnostics::Diagnostic) -> Diagnostic {
    let sp = diag.primary.span;
    let message = diag.primary.info;
    let range = Range::new(
        Position::new(sp.start.line as u64, sp.start.col as u64),
        Position::new(sp.end.line as u64, sp.end.col as u64),
    );
    Diagnostic::new_simple(range, message)
}

fn measure<T, F: FnOnce() -> T>(f: F) -> (T, u128) {
    let start = Instant::now();
    let r = f();
    let stop = Instant::now().duration_since(start).as_micros();
    (r, stop)
}

impl<'a> GlobalState<'a> {
    fn parse(&mut self, url: &Url) {
        let data = match self.text_cache.get(url) {
            Some(data) => data,
            None => return,
        };

        let mut parser = sml_frontend::parser::Parser::new(data, &mut self.interner);
        let ((res, diags), dur) = measure(|| (parser.parse_decl(), parser.diags));
        info!("parsing took {} us", dur);

        // let mut ctx = sml_core::elaborate::Context::new(&borrow);
        let mut st_diag = Vec::new();
        match res {
            Ok(d) => {
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }
                self.db = Database::new(self.arena);
                let (_, dur) = measure(|| self.db.elaborate_decl(&d));

                info!("new elab took {} us", dur);
                // self.db.dump();

                // let ((decls, diags), dur) =
                //     measure(|| sml_core::elaborate::check_and_elaborate(&self.arena, &d));
                // info!("old elab took {} us", dur);
                // if !diags.is_empty() {
                //     for diag in diags {
                //         st_diag.push(diag_convert(diag));
                //     }
                // }

                // self.def_cache = cache::Definitions::default();

                // for decl in &decls {
                //     self.def_cache.walk_decl(decl);
                // }

                // info!("{:?}", &self.def_cache);
            }
            Err(e) => {
                st_diag.push(diag_convert(e.to_diagnostic()));
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }
            }
        };

        info!("reporting {} errors for {:?}", st_diag.len(), url);

        self.send_notification::<lsp_types::notification::PublishDiagnostics>(
            lsp_types::PublishDiagnosticsParams {
                uri: url.clone(),
                diagnostics: st_diag,
                version: None,
            },
        );
    }

    pub(crate) fn send_notification<N: lsp_types::notification::Notification>(
        &mut self,
        params: N::Params,
    ) where
        N::Params: Serialize,
    {
        let not = lsp_server::Notification::new(N::METHOD.to_string(), params);
        self.send(not.into());
    }

    fn send(&self, message: lsp_server::Message) {
        self.sender.send(message).unwrap()
    }
}

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    // Set up logging. Because `stdio_transport` gets a lock on stdout and stdin, we must have
    // our logging only write out to stderr.
    flexi_logger::Logger::with_str("info").start().unwrap();
    info!("starting sml-analyzer");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).

    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(
            TextDocumentSyncKind::Incremental,
        )),
        // hover_provider: Some(true),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![':'.to_string()]),
            work_done_progress_options: Default::default(),
        }),
        ..ServerCapabilities::default()
    };

    let server_capabilities = serde_json::to_value(&caps).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;

    let owned_arena = database::arena::OwnedArena::new();
    let borrow = owned_arena.borrow();
    let mut state = GlobalState {
        text_cache: HashMap::default(),
        kw_completions: completions::keyword_completions(),
        interner: Interner::with_capacity(4096),
        sender: connection.sender.clone(),
        arena: &borrow,
        // def_cache: cache::Definitions::default(),
        db: Database::new(&borrow),
    };

    main_loop(&connection, initialization_params, &mut state)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("shutting down server");
    Ok(())
}

fn hover_request(state: &mut GlobalState, params: TextDocumentPositionParams) -> Option<Hover> {
    // state.def_cache.position_to_type(params.position).map(|ty| {
    //     let mut alpha = types::Alpha::default();
    //     let mut out = String::with_capacity(64);

    //     alpha.write_type(ty, &state.interner, &mut out).unwrap();

    //     Hover {
    //         contents: HoverContents::Scalar(MarkedString::from_markdown(format!("type: {}", out))),
    //         range: None,
    //     }
    // })
    None
}

fn map_ve(inter: &Interner, sym: Symbol, ty: &database::Type<'_>) -> Option<CompletionItem> {
    let name = inter.get(sym)?;
    let mut alpha = types::Alpha::default();
    let mut out = String::new();
    alpha.write_type2(ty, inter, &mut out);

    let mut c = CompletionItem::new_simple(name.into(), format!("{}: {}", name, out));
    c.kind = Some(CompletionItemKind::Value);
    Some(c)
}

fn map_te(
    inter: &Interner,
    sym: Symbol,
    ty: Option<&database::Type<'_>>,
) -> Option<CompletionItem> {
    let name = inter.get(sym)?;
    let mut c = if let Some(ty) = ty {
        let mut alpha = types::Alpha::default();
        let mut out = String::new();
        alpha.write_type2(ty, inter, &mut out);
        CompletionItem::new_simple(name.into(), format!("{}: {}", name, out))
    } else {
        CompletionItem::new_simple(name.into(), format!("{}", name))
    };
    c.kind = Some(CompletionItemKind::TypeParameter);
    Some(c)
}

fn completion_req(state: &mut GlobalState, params: CompletionParams) -> Option<CompletionResponse> {
    let pos = params.text_document_position.position;
    let loc = sml_util::span::Location::new(pos.line as u16, pos.character as u16, 0);
    params.context.map(
        |ctx| match ctx.trigger_character.map(|s| s.chars().next()).flatten() {
            // Some('.') => CompletionResponse::Array(state.def_cache.completions(&state.interner)),
            Some(':') => {
                let tycons = state
                    .db
                    .in_scope_types(loc)
                    .into_iter()
                    .filter_map(|(sym, ty)| map_te(&state.interner, sym, ty))
                    .collect::<Vec<CompletionItem>>();
                CompletionResponse::Array(tycons)
            }
            _ => {
                // let mut kw = state.def_cache.completions(&state.interner);

                // kw.extend(state.kw_completions.iter().cloned());
                let tycons = state
                    .db
                    .in_scope_values(loc)
                    .into_iter()
                    .filter_map(|(sym, ty)| map_ve(&state.interner, sym, ty))
                    .chain(state.kw_completions.clone())
                    .collect::<Vec<CompletionItem>>();

                CompletionResponse::Array(tycons)
            }
        },
    )
}

fn main_loop<'arena>(
    connection: &Connection,
    params: serde_json::Value,
    state: &mut GlobalState<'arena>,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();
    info!("starting example main loop");
    for msg in &connection.receiver {
        // info!("got msg: {:?}", msg);
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }

                dispatch::request(req, &connection)
                    .handle::<HoverRequest, _, _>(|params| hover_request(state, params))?
                    .handle::<Completion, _, _>(|params| completion_req(state, params))?;
            }
            Message::Response(resp) => {
                // info!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                dispatch::notification(not)
                    .handle::<DidOpenTextDocument, _>(|params| {
                        *state
                            .text_cache
                            .entry(params.text_document.uri.clone())
                            .or_default() = params.text_document.text;
                        state.parse(&params.text_document.uri);
                    })
                    .handle::<DidChangeTextDocument, _>(|params| {
                        match state.text_cache.get_mut(&params.text_document.uri) {
                            Some(data) => util::apply_changes(data, params.content_changes),
                            None => {}
                        }
                    })
                    .handle::<DidSaveTextDocument, _>(|params| {
                        state.parse(&params.text_document.uri)
                    });
            }
        }
    }
    Ok(())
}
