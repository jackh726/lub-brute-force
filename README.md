Fuzzer for testing changes to Rust's coercion algorithm through brute force combinations of deref and unsizing coercion graphs.

## Purpose

Tests potential changes to rustc's LUB (Least Upper Bound) coercion algorithm by generating all possible digraphs for deref and unsizing coercions, then verifying that different orderings of match arms produce consistent results.

## Usage

Run the fuzzer:
```bash
cargo run --release
```

## Debugging

Enable tracing info (uncomment tracing lines in code first):
```bash
RUST_LOG=info cargo run --release
```

For detailed debug output (generates substantial logs):
```bash
RUSTC_LOG=debug cargo run --release
```

## Testing Algorithm Changes

Different potential changes can passed to `find_lub`/`do_find_inner`. They are found in the `AlgoChanges` enum.
