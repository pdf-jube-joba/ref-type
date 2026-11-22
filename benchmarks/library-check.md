# Normal library verification

The baseline checkout and fetched `origin/main` both pointed to `269f97c3cac78ecd6c94fab02f71f9c50aee50e7`.
`cargo +1.100.0 build --locked --release -p cli` produced SHA-256 `49569d26de5581c34705abde75587256b7c26353bae4a953154fc5cff067d430`.
Running that executable on `libs/std --module std.Data.Nat --cache-dir libs/refcache --cache-stats --no-progress` verified 101 modules through 101 disk result hits, with zero new checks, corrupt objects or save failures.
The checker revision was `65cf880e493c8a420023d5ab5d710ec38bf6f1738e91f617f71e696f5e6c4a61`.
