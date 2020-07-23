use std::collections::HashMap;
use std::error::Error;

use log::info;
use lsp_types::{
    request::{GotoDefinition, GotoDefinitionResponse},
    InitializeParams, ServerCapabilities, *,
};

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use serde::Serialize;

use sml_frontend::{lexer::Lexer, tokens::Token};
use sml_util::{
    interner::*,
    span::{Span, Spanned},
};

mod cache;
mod completions;
mod types;
mod util;

struct GlobalState<'arena> {
    text_cache: HashMap<lsp_types::Url, String>,
    kw_completions: Vec<CompletionItem>,
    ty_completions: Vec<CompletionItem>,
    interner: Interner,
    sender: crossbeam_channel::Sender<lsp_server::Message>,
    def_cache: cache::Definitions<'arena>,
    arena: &'arena sml_core::CoreArena<'arena>,
}

pub fn diag_convert(mut diag: sml_util::diagnostics::Diagnostic) -> Diagnostic {
    let sp = diag.primary.span;
    let message = diag.primary.info;
    let range = Range::new(
        Position::new(sp.start.line as u64, sp.start.col as u64),
        Position::new(sp.end.line as u64, sp.end.col as u64),
    );
    Diagnostic::new_simple(range, message)
}

impl<'a> GlobalState<'a> {
    fn parse(&mut self, url: &Url) {
        let data = match self.text_cache.get(url) {
            Some(data) => data,
            None => return,
        };

        let mut parser = sml_frontend::parser::Parser::new(data, &mut self.interner);

        let (res, diags) = (parser.parse_decl(), parser.diags);
        // let mut ctx = sml_core::elaborate::Context::new(&borrow);
        let mut st_diag = Vec::new();
        match res {
            Ok(d) => {
                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }

                let (decls, diags) = sml_core::elaborate::check_and_elaborate(&self.arena, &d);

                if !diags.is_empty() {
                    for diag in diags {
                        st_diag.push(diag_convert(diag));
                    }
                }

                self.def_cache.clear();

                for decl in &decls {
                    self.def_cache.walk_decl(decl);
                }

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
    info!("starting generic LSP server");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).

    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(
            TextDocumentSyncKind::Incremental,
        )),
        hover_provider: Some(true),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![".".to_string(), ':'.to_string()]),
            work_done_progress_options: Default::default(),
        }),
        // signature_help_provider: Some(SignatureHelpOptions {
        //     trigger_characters: Some(vec![" ".to_string()]),
        //     retrigger_characters: None,
        //     work_done_progress_options: Default::default(),
        // }),

        // document_highlight_provider: Some(true),
        // workspace_symbol_provider: Some(true),
        // execute_command_provider: Some(ExecuteCommandOptions {
        //     commands: vec!["dummy.do_something".to_string()],
        //     work_done_progress_options: Default::default(),
        // }),
        // workspace: Some(WorkspaceCapability {
        //     workspace_folders: Some(WorkspaceFolderCapability {
        //         supported: Some(true),
        //         change_notifications: Some(
        //             WorkspaceFolderCapabilityChangeNotifications::Bool(true),
        //         ),
        //     }),
        // }),
        // code_lens_provider: Some(CodeLensOptions {
        //     resolve_provider: None,
        // }),
        ..ServerCapabilities::default()
    };

    let server_capabilities = serde_json::to_value(&caps).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;

    let owned_arena = sml_core::arenas::OwnedCoreArena::new();

    let mut state = GlobalState {
        text_cache: HashMap::default(),
        kw_completions: completions::keyword_completions(),
        ty_completions: completions::builtin_ty_completions(),
        interner: Interner::with_capacity(4096),
        sender: connection.sender.clone(),
        arena: &owned_arena.borrow(),
        def_cache: cache::Definitions::default(),
    };

    main_loop(&connection, initialization_params, &mut state)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("shutting down server");
    Ok(())
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
                // info!("got request: {:?}", req);
                let req = match cast::<GotoDefinition>(req) {
                    Ok((id, params)) => {
                        info!("got gotoDefinition request #{}: {:?}", id, params);
                        let result = Some(GotoDefinitionResponse::Array(Vec::new()));
                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(req) => req,
                };

                let req = match cast::<request::HoverRequest>(req) {
                    Ok((id, params)) => {
                        let result = state.def_cache.position_to_type(params.position).map(|ty| {
                            let mut alpha = types::Alpha::default();
                            let mut out = String::with_capacity(64);

                            alpha.write_type(ty, &state.interner, &mut out).unwrap();

                            Hover {
                                contents: HoverContents::Scalar(MarkedString::from_markdown(
                                    format!("type: {}", out),
                                )),
                                range: None,
                            }
                        });
                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(req) => req,
                };

                let req = match cast::<request::Completion>(req) {
                    Ok((id, params)) => {
                        let result = match params.context {
                            Some(ctx) => {
                                match ctx.trigger_character.map(|s| s.chars().next()).flatten() {
                                    Some('.') => Some(CompletionResponse::Array(vec![
                                        CompletionItem::new_simple(
                                            "length".to_string(),
                                            "List.length".to_string(),
                                        ),
                                        CompletionItem::new_simple(
                                            "map".to_string(),
                                            "List.map".to_string(),
                                        ),
                                    ])),
                                    Some(':') => Some(CompletionResponse::Array(
                                        state.ty_completions.clone(),
                                    )),
                                    _ => Some(CompletionResponse::Array(
                                        state.kw_completions.clone(),
                                    )),
                                }
                            }
                            _ => None,
                        };

                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.sender.send(Message::Response(resp))?;

                        continue;
                    }
                    Err(req) => req,
                };
            }
            Message::Response(resp) => {
                // info!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                // info!("got notification: {:?}", not);
                let not = match cast_not::<lsp_types::notification::DidOpenTextDocument>(not) {
                    Ok(params) => {
                        *state
                            .text_cache
                            .entry(params.text_document.uri.clone())
                            .or_default() = params.text_document.text.clone();
                        state.parse(&params.text_document.uri);
                        continue;
                    }
                    Err(not) => not,
                };
                let not = match cast_not::<lsp_types::notification::DidChangeTextDocument>(not) {
                    Ok(params) => {
                        match state.text_cache.get_mut(&params.text_document.uri) {
                            Some(data) => util::apply_changes(data, params.content_changes),
                            None => {}
                        }
                        continue;
                    }
                    Err(not) => not,
                };

                let not = match cast_not::<notification::DidSaveTextDocument>(not) {
                    Ok(params) => {
                        state.parse(&params.text_document.uri);
                        continue;
                    }
                    Err(not) => not,
                };
            }
        }
    }
    Ok(())
}

fn cast<R>(req: Request) -> Result<(RequestId, R::Params), Request>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

fn cast_not<R>(req: Notification) -> Result<R::Params, Notification>
where
    R: lsp_types::notification::Notification,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}
