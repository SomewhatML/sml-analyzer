use serde_json::Value;
use std::sync::{Arc, Mutex};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

mod completions;

#[derive(Debug, Default)]
struct Backend {
    data: Arc<Mutex<String>>,
    kw_completions: Vec<CompletionItem>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: &Client, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
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
                    trigger_characters: None,
                    retrigger_characters: None,
                    work_done_progress_options: Default::default(),
                }),
                document_highlight_provider: Some(true),
                workspace_symbol_provider: Some(true),
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec!["dummy.do_something".to_string()],
                    work_done_progress_options: Default::default(),
                }),
                workspace: Some(WorkspaceCapability {
                    workspace_folders: Some(WorkspaceFolderCapability {
                        supported: Some(true),
                        change_notifications: Some(
                            WorkspaceFolderCapabilityChangeNotifications::Bool(true),
                        ),
                    }),
                }),
                code_lens_provider: Some(CodeLensOptions {
                    resolve_provider: None,
                }),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn initialized(&self, client: &Client, _: InitializedParams) {
        client.log_message(MessageType::Info, "server initialized!");
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_change_workspace_folders(
        &self,
        client: &Client,
        _: DidChangeWorkspaceFoldersParams,
    ) {
        client.log_message(MessageType::Info, "workspace folders changed!");
    }

    async fn did_change_configuration(&self, client: &Client, _: DidChangeConfigurationParams) {
        client.log_message(MessageType::Info, "configuration changed!");
    }

    async fn did_change_watched_files(&self, client: &Client, _: DidChangeWatchedFilesParams) {
        client.log_message(MessageType::Info, "watched files have changed!");
    }

    async fn execute_command(
        &self,
        client: &Client,
        _: ExecuteCommandParams,
    ) -> Result<Option<Value>> {
        client.log_message(MessageType::Info, "command executed!");

        match client.apply_edit(WorkspaceEdit::default()).await {
            Ok(res) if res.applied => client.log_message(MessageType::Info, "edit applied"),
            Ok(_) => client.log_message(MessageType::Info, "edit not applied"),
            Err(err) => client.log_message(MessageType::Error, err),
        }

        Ok(None)
    }

    async fn did_open(&self, client: &Client, params: DidOpenTextDocumentParams) {
        // params.text_document.text
        let lock = self.data.lock();
        let mut inner = lock.unwrap();
        std::mem::replace(&mut *inner, params.text_document.text.clone());

        client.log_message(MessageType::Info, "file opened!");
        client.log_message(MessageType::Info, &*inner);
    }

    async fn did_change(&self, client: &Client, params: DidChangeTextDocumentParams) {
        client.log_message(MessageType::Info, "file changed!");
    }

    async fn did_save(&self, client: &Client, _: DidSaveTextDocumentParams) {
        client.log_message(MessageType::Info, "file saved!");
    }

    async fn did_close(&self, client: &Client, _: DidCloseTextDocumentParams) {
        client.log_message(MessageType::Info, "file closed!");
    }

    async fn completion(&self, c: CompletionParams) -> Result<Option<CompletionResponse>> {
        match c.context {
            Some(ctx) => match ctx.trigger_character.map(|s| s.chars().next()).flatten() {
                Some('.') => Ok(Some(CompletionResponse::Array(vec![
                    CompletionItem::new_simple("Hello".to_string(), "Some detail".to_string()),
                    CompletionItem::new_simple("Bye".to_string(), "More detail".to_string()),
                ]))),
                Some(':') => Ok(Some(CompletionResponse::Array(vec![
                    CompletionItem::new_simple("int".to_string(), "Integer type".to_string()),
                    CompletionItem::new_simple("bool".to_string(), "Boolean type".to_string()),
                    CompletionItem::new_simple("char".to_string(), "Character type".to_string()),
                    CompletionItem::new_simple("string".to_string(), "String type".to_string()),
                    CompletionItem::new_simple("list".to_string(), "List type".to_string()),
                ]))),
                _ => Ok(Some(CompletionResponse::Array(self.kw_completions.clone()))),
            },
            _ => Ok(None),
        }
    }

    async fn code_lens(&self, params: CodeLensParams) -> Result<Option<Vec<CodeLens>>> {
        // dbg!(params.text_document.uri);

        // let mut v = Vec::new();
        // v.push(CodeLens {
        //     command: Some(Command::new("Command".into(), "name?".into(), None)),
        //     range: Range::new(Position::new(0, 0), Position::new(0, 10)),
        //     data: Some(Value::String("Lense!!".into())),
        // });

        Ok(None)
    }

    async fn code_lens_resolve(&self, params: CodeLens) -> Result<CodeLens> {
        let p = CodeLens {
            range: params.range,
            command: params.command,
            data: Some(Value::String("Lens!".into())),
        };
        Ok(p)
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        Ok(Some(Hover {
            contents: HoverContents::Scalar(MarkedString::from_markdown("test".into())),
            range: Some(Range::new(
                params.text_document_position_params.position,
                params.text_document_position_params.position,
            )),
        }))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let backend = Backend {
        data: Arc::new(Mutex::new(String::default())),
        kw_completions: completions::keyword_completions(),
    };

    let (service, messages) = LspService::new(backend);
    Server::new(stdin, stdout)
        .interleave(messages)
        .serve(service)
        .await;
}
