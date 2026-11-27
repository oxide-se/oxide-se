#!/bin/sh
# Build the reference and check its examples without flashing a board.
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

if [ "$#" -ne 0 ]; then
    printf '%s\n' 'Usage: sh scripts/check_rustlet_docs.sh' >&2
    exit 2
fi

# Keep the reference separate from documentation for unrelated workspace crates.
export CARGO_TARGET_DIR="$repo_root/target/rustlet-reference"
export RUSTDOCFLAGS="${RUSTDOCFLAGS:-} -D warnings"

# Host doctests exercise only APIs that do not require an active Rustlet SVC.
cargo test -p rustlet_runtime --lib
cargo test -p rustlet_runtime --doc

# Check the documented declaration forms for Pico 1. Build std from rust-src
# using the same features as build-fae; no installed target libraries are needed.
cargo check --manifest-path rustlets/tests/Cargo.toml \
    -p rustlet_declare_macro_forms -p rustlet_getting_started_test -p rustlet_crypto_test \
    --release --target thumbv6m-none-eabi \
    -Zbuild-std=core,alloc,compiler_builtins \
    -Zbuild-std-features=compiler-builtins-mem

# Generate the complete feature-gated interface only after checks have passed.
cargo doc -p rustlet_runtime --no-default-features --no-deps
cargo doc -p rustlet_runtime --features runtime --no-deps

printf 'Reference: %s\n' "$CARGO_TARGET_DIR/doc/rustlet_runtime/index.html"
