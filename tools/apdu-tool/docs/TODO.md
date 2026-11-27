# APDU tool roadmap

See the [APDU tool guide](../README.md) for the current CLI and protocols.

## Registry operations and keys

- [ ] Segment data automatically when the command or Secure Channel reduces APDU
  payload capacity. Blocked until the Oxide SE profile defines transactional `STORE
  DATA` reassembly; the tool currently rejects such data before connection.
- [ ] Document and test recovery, abandonment, and absence of partial publication
  once the segmented mutation protocol is introduced. Current short mutations remain
  atomic.
- [ ] Calculate and check the KCV when required by the key format.
- [ ] Add wrapping of new keys under `DEK` when needed.

## Documentation and validation

- [ ] Turn target examples in the README into documentation or CLI tests as each
  command becomes available.
- [ ] Run package unit tests, QEMU GP/SCP campaigns, and tests over a physical
  serial connection.
- [ ] Check that test and error output contains no secrets.

## ISO 7816 filesystem commands

- [ ] Add a shared short ISO 7816 APDU encoder/decoder.
- [ ] Add occurrence options and `FCI`, `FCP`, `FMD`, or no-data response options.
- [ ] Validate and normalize AIDs written with spaces, colons, or continuous
  hexadecimal digits.
- [ ] Expose `get-response` for diagnostics without duplicating the T=0 client's
  automatic chaining.
- [ ] Add `get-challenge`, `manage-channel`, `read-binary`, `update-binary`, `read-
  record`, and `verify` only if Oxide SE actually supports and tests their
  semantics.

Representative tests cover TCP, Unix-domain sockets, simulated transport and
physical serial links. Check diagnostic output and test reports for secrets.
