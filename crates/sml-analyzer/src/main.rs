//! A minimal example LSP server that can only respond to the `gotoDefinition` request. To use
//! this example, execute it and then send an `initialize` request.
//!
//! ```no_run
//! Content-Length: 85
//!
//! {"jsonrpc": "2.0", "method": "initialize", "id": 1, "params": {"capabilities": {}}}
//! ```
//!
//! This will respond with a server response. Then send it a `initialized` notification which will
//! have no response.
//!
//! ```no_run
//! Content-Length: 59
//!
//! {"jsonrpc": "2.0", "method": "initialized", "params": {}}
//! ```
//!
//! Once these two are sent, then we enter the main loop of the server. The only request this
//! example can handle is `gotoDefinition`:
//!
//! ```no_run
//! Content-Length: 159
//!
//! {"jsonrpc": "2.0", "method": "textDocument/definition", "id": 2, "params": {"textDocument": {"uri": "file://temp"}, "position": {"line": 1, "character": 1}}}
//! ```
//!
//! To finish up without errors, send a shutdown request:
//!
//! ```no_run
//! Content-Length: 67
//!
//! {"jsonrpc": "2.0", "method": "shutdown", "id": 3, "params": null}
//! ```
//!
//! The server will exit the main loop and finally we send a `shutdown` notification to stop
//! the server.
//!
//! ```
//! Content-Length: 54
//!
//! {"jsonrpc": "2.0", "method": "exit", "params": null}
//! ```
use std::error::Error;

use log::info;
use lsp_types::{
    request::{GotoDefinition, GotoDefinitionResponse},
    InitializeParams, ServerCapabilities, *,
};

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use std::sync::{Arc, Mutex};

use sml_frontend::{lexer::Lexer, tokens::Token};
use sml_util::{interner::*, span::Spanned};

mod completions;
mod util;

struct GlobalState {
    data: Arc<Mutex<String>>,
    kw_completions: Vec<CompletionItem>,
    ty_completions: Vec<CompletionItem>,
    interner: Arc<Mutex<Interner>>,
}

impl GlobalState {
    fn lex(&self) -> Vec<Spanned<Token>> {
        let lock = self.data.lock();
        let mut inner = lock.unwrap();

        let int_lock = self.interner.lock();
        let mut int_inner = int_lock.unwrap();

        let mut lexer = Lexer::new(inner.chars(), &mut *int_inner);
        lexer.collect()
    }

    fn parse(&self) -> Vec<Spanned<Token>> {
        let lock = self.data.lock();
        let mut inner = lock.unwrap();

        let int_lock = self.interner.lock();
        let mut int_inner = int_lock.unwrap();

        let mut lexer = Lexer::new(inner.chars(), &mut *int_inner);
        lexer.collect()
    }

    fn with_source<F: FnOnce(&mut String)>(&self, f: F) {
        let lock = self.data.lock();
        let mut inner = lock.unwrap();
        f(&mut *inner)
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
        signature_help_provider: Some(SignatureHelpOptions {
            trigger_characters: Some(vec![" ".to_string()]),
            retrigger_characters: None,
            work_done_progress_options: Default::default(),
        }),

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
    let state = GlobalState {
        data: Arc::new(Mutex::new(String::default())),
        kw_completions: completions::keyword_completions(),
        ty_completions: completions::builtin_ty_completions(),
        interner: Arc::new(Mutex::new(Interner::with_capacity(4096))),
    };

    main_loop(&connection, initialization_params, &state)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("shutting down server");
    Ok(())
}

fn main_loop(
    connection: &Connection,
    params: serde_json::Value,
    state: &GlobalState,
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
                // match cast::<lsp_types::request::DidOpenTextDocumentParams>(req) {
                //     Ok((id, params)) => {

                //     },
                //     Err(req) => req,
                // };
                // ...
            }
            Message::Response(resp) => {
                // info!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                // info!("got notification: {:?}", not);
                let not = match cast_not::<lsp_types::notification::DidOpenTextDocument>(not) {
                    Ok(params) => {
                        state.with_source(|f| *f = params.text_document.text.clone());

                        let tks = state.lex();
                        let s = tks
                            .into_iter()
                            .map(|t| format!("{:?}", t.data))
                            .collect::<Vec<String>>()
                            .join(" ");

                        info!("lexed: {}", &s);

                        continue;
                    }
                    Err(not) => not,
                };
                let not = match cast_not::<lsp_types::notification::DidChangeTextDocument>(not) {
                    Ok(params) => {
                        state.with_source(|f| util::apply_changes(f, params.content_changes));

                        let tks = state.lex();
                        let s = tks
                            .into_iter()
                            .map(|t| format!("{:?}", t.data))
                            .collect::<Vec<String>>()
                            .join(" ");

                        info!("lexed: {}", &s);

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

// use serde_json::Value;
// use std::sync::{Arc, Mutex};
// use tower_lsp::jsonrpc::Result;
// use tower_lsp::lsp_types::*;
// use tower_lsp::{Client, LanguageServer, LspService, Server};

// use sml_frontend::{lexer::Lexer, tokens::Token};
// use sml_util::{interner::*, span::Spanned};

// mod completions;
// mod util;

// #[tower_lsp::async_trait]
// impl LanguageServer for Backend {
//     async fn initialize(&self, _: &Client, _: InitializeParams) -> Result<InitializeResult> {
//         Ok(InitializeResult {
//             server_info: None,
//             capabilities: ServerCapabilities {
//                 text_document_sync: Some(TextDocumentSyncCapability::Kind(
//                     TextDocumentSyncKind::Incremental,
//                 )),
//                 hover_provider: Some(true),
//                 completion_provider: Some(CompletionOptions {
//                     resolve_provider: Some(false),
//                     trigger_characters: Some(vec![".".to_string(), ':'.to_string()]),
//                     work_done_progress_options: Default::default(),
//                 }),
//                 signature_help_provider: Some(SignatureHelpOptions {
//                     trigger_characters: None,
//                     retrigger_characters: None,
//                     work_done_progress_options: Default::default(),
//                 }),
//                 document_highlight_provider: Some(true),
//                 workspace_symbol_provider: Some(true),
//                 execute_command_provider: Some(ExecuteCommandOptions {
//                     commands: vec!["dummy.do_something".to_string()],
//                     work_done_progress_options: Default::default(),
//                 }),
//                 workspace: Some(WorkspaceCapability {
//                     workspace_folders: Some(WorkspaceFolderCapability {
//                         supported: Some(true),
//                         change_notifications: Some(
//                             WorkspaceFolderCapabilityChangeNotifications::Bool(true),
//                         ),
//                     }),
//                 }),
//                 code_lens_provider: Some(CodeLensOptions {
//                     resolve_provider: None,
//                 }),
//                 ..ServerCapabilities::default()
//             },
//         })
//     }

//     async fn initialized(&self, client: &Client, _: InitializedParams) {
//         client.log_message(MessageType::Info, "server initialized!");
//     }

//     async fn shutdown(&self) -> Result<()> {
//         Ok(())
//     }

//     async fn did_change_workspace_folders(
//         &self,
//         client: &Client,
//         _: DidChangeWorkspaceFoldersParams,
//     ) {
//         client.log_message(MessageType::Info, "workspace folders changed!");
//     }

//     async fn did_change_configuration(&self, client: &Client, _: DidChangeConfigurationParams) {
//         client.log_message(MessageType::Info, "configuration changed!");
//     }

//     async fn did_change_watched_files(&self, client: &Client, _: DidChangeWatchedFilesParams) {
//         client.log_message(MessageType::Info, "watched files have changed!");
//     }

//     async fn execute_command(
//         &self,
//         client: &Client,
//         _: ExecuteCommandParams,
//     ) -> Result<Option<Value>> {
//         client.log_message(MessageType::Info, "command executed!");

//         match client.apply_edit(WorkspaceEdit::default()).await {
//             Ok(res) if res.applied => client.log_message(MessageType::Info, "edit applied"),
//             Ok(_) => client.log_message(MessageType::Info, "edit not applied"),
//             Err(err) => client.log_message(MessageType::Error, err),
//         }

//         Ok(None)
//     }

//     async fn did_open(&self, client: &Client, params: DidOpenTextDocumentParams) {
//         self.with_source(|f| *f = params.text_document.text.clone());

//         client.log_message(MessageType::Info, "file opened!");

//         let tks = self.lex();
//         let s = tks
//             .into_iter()
//             .map(|t| format!("{:?}", t.data))
//             .collect::<Vec<String>>()
//             .join(" ");
//         client.log_message(MessageType::Info, &s);
//     }

//     async fn did_change(&self, client: &Client, params: DidChangeTextDocumentParams) {
//         self.with_source(|f| util::apply_changes(f, params.content_changes));
//         client.log_message(MessageType::Info, "file changed!");

//         let tks = self.lex();
//         let s = tks
//             .into_iter()
//             .map(|t| format!("{:?}", t.data))
//             .collect::<Vec<String>>()
//             .join(" ");
//         client.log_message(MessageType::Info, &s);
//     }

//     async fn did_save(&self, client: &Client, _: DidSaveTextDocumentParams) {
//         client.log_message(MessageType::Info, "file saved!");
//     }

//     async fn did_close(&self, client: &Client, _: DidCloseTextDocumentParams) {
//         client.log_message(MessageType::Info, "file closed!");
//     }

//     async fn completion(&self, c: CompletionParams) -> Result<Option<CompletionResponse>> {
//         match c.context {
//             Some(ctx) => match ctx.trigger_character.map(|s| s.chars().next()).flatten() {
//                 Some('.') => Ok(Some(CompletionResponse::Array(vec![
//                     CompletionItem::new_simple("length".to_string(), "List.length".to_string()),
//                     CompletionItem::new_simple("map".to_string(), "List.map".to_string()),
//                 ]))),
//                 Some(':') => Ok(Some(CompletionResponse::Array(self.ty_completions.clone()))),
//                 _ => Ok(Some(CompletionResponse::Array(self.kw_completions.clone()))),
//             },
//             _ => Ok(None),
//         }
//     }

//     async fn code_lens(&self, params: CodeLensParams) -> Result<Option<Vec<CodeLens>>> {
//         // dbg!(params.text_document.uri);

//         // let mut v = Vec::new();
//         // v.push(CodeLens {
//         //     command: Some(Command::new("Command".into(), "name?".into(), None)),
//         //     range: Range::new(Position::new(0, 0), Position::new(0, 10)),
//         //     data: Some(Value::String("Lense!!".into())),
//         // });

//         Ok(None)
//     }

//     async fn code_lens_resolve(&self, params: CodeLens) -> Result<CodeLens> {
//         let p = CodeLens {
//             range: params.range,
//             command: params.command,
//             data: Some(Value::String("Lens!".into())),
//         };
//         Ok(p)
//     }

//     async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
//         Ok(Some(Hover {
//             contents: HoverContents::Scalar(MarkedString::from_markdown("test".into())),
//             range: Some(Range::new(
//                 params.text_document_position_params.position,
//                 params.text_document_position_params.position,
//             )),
//         }))
//     }
// }

// #[tokio::main]
// async fn main() {
//     let stdin = tokio::io::stdin();
//     let stdout = tokio::io::stdout();

//     let backend = Backend {
//         data: Arc::new(Mutex::new(String::default())),
//         kw_completions: completions::keyword_completions(),
//         ty_completions: completions::builtin_ty_completions(),
//         interner: Arc::new(Mutex::new(Interner::with_capacity(4096))),
//     };

//     let (service, messages) = LspService::new(backend);
//     Server::new(stdin, stdout)
//         .interleave(messages)
//         .serve(service)
//         .await;
// }
