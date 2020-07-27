use std::collections::HashMap;
use std::error::Error;
use std::time::Instant;

use log::info;
use lsp_types::{
    notification::{DidChangeTextDocument, DidOpenTextDocument, DidSaveTextDocument},
    request::{Completion, GotoDefinition, HoverRequest},
    InitializeParams, ServerCapabilities, *,
};

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use serde::Serialize;

use sml_util::{interner::*, span::Span};

use database::Database;

mod completions;
mod dispatch;
mod state;
mod types;
mod util;

use state::GlobalState;

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
        hover_provider: Some(true),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![':'.to_string()]),
            work_done_progress_options: Default::default(),
        }),
        definition_provider: Some(true),
        ..ServerCapabilities::default()
    };

    let server_capabilities = serde_json::to_value(&caps).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;

    let owned_arena = database::arena::OwnedArena::new();
    let borrow = owned_arena.borrow();

    let mut state = GlobalState::new(&borrow, connection.sender.clone());

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

                dispatch::request(req, &connection)
                    .handle::<HoverRequest, _, _>(|params| state.hover_request(params))?
                    .handle::<Completion, _, _>(|params| state.completion_req(params))?
                    .handle::<GotoDefinition, _, _>(|params| state.goto_def_request(params))?;
            }
            Message::Response(_) => {
                // info!("got response: {:?}", resp);
            }
            Message::Notification(not) => {
                dispatch::notification(not)
                    .handle::<DidOpenTextDocument, _>(|params| state.open(params))
                    .handle::<DidChangeTextDocument, _>(|params| state.update(params))
                    .handle::<DidSaveTextDocument, _>(|params| {
                        state.parse(&params.text_document.uri)
                    });
            }
        }
    }
    Ok(())
}
