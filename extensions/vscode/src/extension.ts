import * as fs from 'node:fs';
import * as path from 'node:path';
import * as vscode from 'vscode';
import { LanguageClient, LanguageClientOptions, ServerOptions } from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    const folder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    const configured = vscode.workspace.getConfiguration('ref').get<string>('server.path', '').trim();
    const binary = process.platform === 'win32' ? 'ref-lsp.exe' : 'ref-lsp';
    const bundled = context.asAbsolutePath(path.join('server', binary));
    const local = folder && path.join(folder, 'target', 'debug', binary);
    const command = configured || (fs.existsSync(bundled) ? bundled : local && fs.existsSync(local) ? local : binary);
    const serverOptions: ServerOptions = { command, options: folder ? { cwd: folder } : undefined };
    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'ref' }],
        synchronize: { fileEvents: vscode.workspace.createFileSystemWatcher('**/*.{ref,toml}') }
    };
    client = new LanguageClient('ref', 'Ref Type', serverOptions, clientOptions);
    context.subscriptions.push(client);
    await client.start();
}

export async function deactivate(): Promise<void> {
    await client?.dispose();
    client = undefined;
}
