/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import { workspace, ExtensionContext, TextDocument, Range, } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind,
	Executable,
	VersionedTextDocumentIdentifier,
	CodeLens,
	CancellationToken,
	ProvideCodeLensesSignature,
	NotificationType,
	MessageType,
} from 'vscode-languageclient';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	// The server is implemented in node
	let cwd = ".";
	let command = path.join(context.extensionPath, "target", "debug", "sml-analyzer.exe");
	const run: Executable = {
		command,
		options: { cwd },
	};

	// The debug options for the server
	// --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
	let debugOptions = { execArgv: ['--nolazy', '--inspect=6009'] };

	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	let serverOptions: ServerOptions = {
		run,
		debug: run
	};

	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
		// Register the server for plain text documents
		documentSelector: [{ scheme: 'file', language: 'sml' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
		},
		// middleware: {			
		// 	async provideCodeLenses(document: TextDocument, token: CancellationToken, next: ProvideCodeLensesSignature) {
		// 		var items = [];
		// 		// CodeLens {
		// 		// 	range: Range {

		// 		// 	}
		// 		// }
		// 		// client.sendNotification(MessageType.Info())
		// 		return client.protocol2CodeConverter.asCodeLenses(items)				
		// 	}
		// }
	};


	// Create the language client and start the client.
	client = new LanguageClient(
		'languageServerExample',
		'Language Server Example',
		serverOptions,
		clientOptions
	);

	// Start the client. This will also launch the server
	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
