# Rocq 9 and FreerDPS setup

The proof uses **Rocq 9.0.0** and the `FreerDPS.Core`, `Impure`, and `Hoare`
modules from [`2xs/FreerDPS`](https://github.com/2xs/FreerDPS), pinned to
`3c22f0bd15ce0c15482a7dd0febd37fac89d9174`. FreerDPS sources carry MPL-2.0 headers.

The dependency set includes OCaml 5.3.0, Monae 0.9.2, Infotheo 0.9.7,
MathComp 2.5.0, MathComp Analysis 1.16.0, and Hierarchy Builder 1.10.3.
Monae is LGPL-2.1-or-later; consult package metadata for dependency licenses.

## Install the dependencies

From the repository root, choose a dedicated switch name and create it if it
does not already exist. These commands assume opam has been initialized.

```sh
REGISTRY_SWITCH=registry-proof
opam switch create "$REGISTRY_SWITCH" ocaml-base-compiler.5.3.0
opam repository add rocq-released https://rocq-prover.org/opam/released \
  --switch="$REGISTRY_SWITCH"
opam install --switch="$REGISTRY_SWITCH" coq.9.0.0 coq-hierarchy-builder.1.10.3 \
  coq-mathcomp-ssreflect.2.5.0 coq-mathcomp-classical.1.16.0 \
  coq-monae.0.9.2 coq-infotheo.0.9.7
```

Place the pinned FreerDPS checkout in the repository-relative dependency directory
used by the build. Clone only if that directory is not already populated.

```sh
mkdir -p .local/registry-proof-deps
git clone https://github.com/2xs/FreerDPS.git .local/registry-proof-deps/FreerDPS
git -C .local/registry-proof-deps/FreerDPS checkout --detach \
  3c22f0bd15ce0c15482a7dd0febd37fac89d9174
opam exec --switch="$REGISTRY_SWITCH" \
  -- make -C .local/registry-proof-deps/FreerDPS -j4
```

The dependency checkout is excluded from Git. The registry build imports its
compiled theories through a logical path; it does not substitute a local
reimplementation of FreerDPS. Use the same switch for the dependency and the
registry proof.

## Verify the proof

```sh
opam exec --switch="$REGISTRY_SWITCH" \
  -- make -C proofs/registry -f Makefile.freer -j4 check check-interface
```

This checks the foundations, composition, public signature, component theorem,
and scenario witnesses. It includes `Print Assumptions` and `coqchk`.
`check-interface` checks the public signature in isolation with the standard
library. Build products are written under `.local/registry-build/freer/`.
