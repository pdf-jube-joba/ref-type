import { copyFileSync, chmodSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import packageJson from '../package.json' with { type: 'json' };

const extension = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const repository = path.resolve(extension, '../..');
const target = {
    linux: { x64: 'linux-x64', arm64: 'linux-arm64' },
    darwin: { x64: 'darwin-x64', arm64: 'darwin-arm64' },
    win32: { x64: 'win32-x64', arm64: 'win32-arm64' }
}[process.platform]?.[process.arch];

if (!target) {
    throw new Error(`Unsupported platform: ${process.platform}-${process.arch}`);
}

function run(command, args, cwd) {
    const result = spawnSync(command, args, {
        cwd,
        stdio: 'inherit',
        shell: process.platform === 'win32'
    });
    if (result.error) throw result.error;
    if (result.status !== 0) process.exit(result.status ?? 1);
}

run('cargo', ['build', '--release', '-p', 'ref-lsp'], repository);
run('npm', ['run', 'compile'], extension);

const executable = process.platform === 'win32' ? 'ref-lsp.exe' : 'ref-lsp';
const serverDirectory = path.join(extension, 'server');
mkdirSync(serverDirectory, { recursive: true });
const bundled = path.join(serverDirectory, executable);
copyFileSync(path.join(repository, 'target', 'release', executable), bundled);
if (process.platform !== 'win32') chmodSync(bundled, 0o755);

const outputDirectory = path.join(repository, 'extensions', 'dist');
mkdirSync(outputDirectory, { recursive: true });
const output = path.join(outputDirectory, `${packageJson.name}-${packageJson.version}-${target}.vsix`);
run('npm', ['exec', '--', 'vsce', 'package', '--no-dependencies', '--allow-missing-repository', '--target', target, '--out', output], extension);
console.log(output);
