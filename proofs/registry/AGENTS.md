# Registry proof

- Start with the [public contract](theories/interface/OwnedDataContract.v)
  and the [proof overview](README.md). Keep supplier obligations and guarantees
  visible when changing a theorem statement or its hypotheses.
- Update the [implementation map](ImplementationMap.md) when a mapped Rust
  path or a referenced lemma changes. Verify that line links still point to the
  intended statements. Describe correspondence separately from the proved
  guarantees of the Rocq model.
- Validate changes to proofs or interfaces with the pinned
  [Rocq and FreerDPS setup](FreerDPS-Setup.md#install-the-dependencies).

From the repository root, with the documented opam switch installed:

```sh
opam exec --switch=registry-proof \
  -- make -C proofs/registry -f Makefile.freer -j4 check check-interface
```

`check` validates the proof development. `check-interface` checks that the
public signature also compiles and passes checks with the standard library alone.
