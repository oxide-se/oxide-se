# APDU client

- Treat the [CLI reference](README.md) as the contract for flags, transport
  syntax, output formats and exit codes. Keep stdout suitable for scripts
  and send progress messages to stderr.
- Preserve the command lifecycle: `atr` reads the startup ATR without sending
  an APDU, and normal command exchanges send immediately.
- Keep TCP, Unix-domain sockets and physical serial links working. Check
  session reuse and isolation when changing link selection, timeouts or session
  handling. Keep credentials and live session state out of output and fixtures.
- For changes to deployment commands, check both loading the package and
  installing and selecting its instance.

Run the host-side checks from the repository root:

```sh
cargo test -p apdu_tool
```

For transport or deployment changes, also replay the affected commands against
the [DevKit QEMU setup](../../docs/getting-started.md#software-emulation-of-pico1).
