# Contributing to Oxide SE

## Language Policy

Repository content should be written in English by default, including
README files, contributor-facing documentation, code comments, commit
messages when possible, and newly added project materials.

The single standing exception is `.journal.de.labo.txt`, which is kept
in French on purpose.

## Laboratory Journal

The file `.journal.de.labo.txt` is the running laboratory journal for
the project. It is used to preserve design reflections, implementation
notes, milestones and research traces over time.

The format is mandatory:

- first line: `# Journal de suivi du projet Oxide SE`
- each entry header: `## DD-MM-YYYY at HH:MM - action/reflection title`

Entries should be appended chronologically and written in French.

## Scope of the Journal

Use the journal to record:

- architectural reflections
- implementation progress
- technical decisions
- open questions
- notable project events

This convention is recurring and applies for the lifetime of the
project.

## Low-Level Debugging Discipline

When debugging Rustlet entry, return, exception, or ABI-transition
issues, use the documented proof-first workflow in
`docs/isolated-app-debugging.md`.

In particular:

- start from the minimal automated Rustlet APDU scenario before manual
  APDU exchanges;
- prove one transition at a time instead of changing several low-level
  layers at once;
- move to QEMU + GDB early for assembly, privilege, PSP/MSP, SVC, and
  vector-table issues;
- keep Thumb branch/vector addresses distinct from the even memory
  addresses used for breakpoints and disassembly.

## Rust Tooling

Use the repository toolchain defaults when working on Rust code.

The repository root provides:

- `rust-toolchain.toml` for the expected nightly toolchain and required
  components;
- `rustfmt.toml` for formatting;
- `clippy.toml` for baseline lint configuration.

Prefer running:

- `cargo fmt --all -- --check`
- `cargo clippy --workspace --all-targets --offline -- -D warnings`

Target-specific clippy runs for the kernel may also be used when
appropriate.

For Rustlet API changes, run `sh scripts/check_rustlet_docs.sh`. It validates
public Rustdoc, host examples (including rejected borrow patterns), and Pico 1
compilation of declaration/APDU examples. Document errors, buffer ownership,
copies, allocations and unsupported behavior at the API item. Keep examples
executable where they do not need a kernel; validate service calls through the
embedded scenarios described in the Rustlet developer guide. The script also
prepares a versioned static reference artifact without publishing it.

## Workspace Conventions

Rustlets live under `rustlets/`.

The current layout is:

- `rustlets/rustlet_runtime`: shared runtime crate and ABI definitions for Rustlets
- `rustlets/complete_security_domain`: full embedded administrative Rustlet
- `rustlets/tests/`: functional Rustlet test applications
