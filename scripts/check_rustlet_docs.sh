#!/bin/sh
# Build the reference and check its examples without flashing a board.
set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

doc_version=${1:-development}
case "$doc_version" in
    ''|.|..|*[!A-Za-z0-9._-]*)
        printf '%s\n' 'Version must contain only letters, digits, dot, underscore or hyphen.' >&2
        exit 2
        ;;
esac
if [ "$#" -gt 1 ]; then
    printf '%s\n' 'Usage: sh scripts/check_rustlet_docs.sh [version]' >&2
    exit 2
fi

# Isolate the published tree from documentation for unrelated workspace crates.
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

# A fresh staging directory prevents stale files from an earlier version from
# leaking into the artifact. Keep old artifacts; nothing here publishes them.
staging=$(mktemp -d "$CARGO_TARGET_DIR/site.XXXXXX")
mkdir -p "$staging/api/$doc_version"
cp -R "$CARGO_TARGET_DIR/doc/." "$staging/api/$doc_version/"
touch "$staging/.nojekyll"
printf '<!doctype html><html lang="en"><meta charset="utf-8"><title>oXiDe SE Rustlet API</title><h1>oXiDe SE Rustlet API</h1><p><a href="api/%s/rustlet_runtime/index.html">Reference: %s</a></p></html>\n' \
    "$doc_version" "$doc_version" > "$staging/index.html"
git rev-parse HEAD > "$staging/api/$doc_version/source-commit.txt"
git diff --quiet && git diff --cached --quiet && snapshot_state=clean || snapshot_state=modified
printf '%s\n' "$snapshot_state" > "$staging/api/$doc_version/source-state.txt"
printf 'Reference: %s\nPages artifact: %s\n' \
    "$CARGO_TARGET_DIR/doc/rustlet_runtime/index.html" "$staging"
