# Releasing the Linux CLI

The [Release workflow](../.github/workflows/release.yml) publishes the Linux x86_64 CLI to GitHub Releases when a version tag is pushed.
It uses Rust 1.100.0, the committed `Cargo.lock`, and an Ubuntu 22.04 runner.
The executable targets `x86_64-unknown-linux-gnu` and requires glibc 2.35 or newer.
Debug information is stripped from the release executable.

## Validate without publishing

After the workflow is available on the default branch, open **Actions → Release → Run workflow** and select a branch.
The workflow runs the Rust workspace tests, Python test runner tests, and source acceptance tests, then uploads the archive and `SHA256SUMS` as the `linux-release` workflow artifact.
Branch runs do not create a GitHub Release.

## Publish a release

1. Set the version in `src/cli/Cargo.toml`. Update the workspace lockfile with `cargo check -p cli` and commit both files when the version changes.
2. Commit and push the changes, including the release workflow.
3. Create and push an annotated tag matching the CLI version exactly:

   ```sh
   git tag -a v0.1.0 -m "Release v0.1.0"
   git push origin v0.1.0
   ```

The workflow rejects tags that do not match `src/cli/Cargo.toml`.
For example, `v0.1.0-rc.1` requires version `0.1.0-rc.1` and is published as a prerelease.
All tests must pass before the archive is uploaded and the release is published with automatically generated release notes.
Only the publishing job receives `contents: write`; the workflow uses GitHub's built-in token and requires no additional secrets.

The release contains:

- `ref-type-v0.1.0-x86_64-unknown-linux-gnu.tar.gz`, containing a directory with `cli`, `LICENSE`, and `USAGE.md`.
- `SHA256SUMS`, containing the archive's SHA-256 checksum.

## Use a release

Download the archive and `SHA256SUMS` from the same release into one directory, then run:

```sh
sha256sum --check SHA256SUMS
tar -xzf ref-type-v0.1.0-x86_64-unknown-linux-gnu.tar.gz
./ref-type-v0.1.0-x86_64-unknown-linux-gnu/cli --version
./ref-type-v0.1.0-x86_64-unknown-linux-gnu/cli /path/to/package
```

Replace `v0.1.0` with the downloaded version.
The executable is named `cli`, matching local Cargo builds.
See [CLI usage](../src/USAGE.md) for the available options.

## Retry a failed release

Fix failures before creating a new version tag, or rerun the failed workflow if the failure was transient.
If publication fails after creating a draft, rerunning the publishing job replaces the draft's archive and checksum before publishing.
The workflow refuses to modify an already published release.
Manually running the workflow on a matching version tag also publishes a release; select a branch when validating without publication.
