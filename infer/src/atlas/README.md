# Atlas

## Licensing

The source files in this directory (`infer/src/atlas/`) are licensed under
the **Apache License, Version 2.0**. See [LICENSE](LICENSE) for the full
license text and [NOTICE](NOTICE) for attribution.

The rest of the host repository is Meta's [Infer](https://github.com/facebook/infer),
which remains under its original **MIT License**. See the `LICENSE` file at the
repository root for the host project's license.

Modifications to Infer source files outside this directory (made to register
Atlas as a checker) remain under Infer's MIT license; only files in
`infer/src/atlas/` carry the Apache 2.0 license.

## Building

Atlas builds as part of the host Infer tree. The Astral solver must be
available before building — see [Astral dependency](#astral-dependency) below.

Then, from the repository root:

```sh
facebook-clang-plugins/clang/setup.sh
./build-infer.sh
```

Setting up [opam](https://opam.ocaml.org/) beforehand is not strictly
required (`build-infer.sh` can bootstrap it via its `--only-setup-opam` switch),
but is strongly recommended to avoid downstream headaches.

Build failures typically come from missing system tools (`make`, `ninja`, a
specific `glibc` version, etc.) rather than anything Atlas-specific. If you
hit one, consult the [upstream Infer documentation](https://github.com/facebook/infer)
for the canonical dependency list and setup steps.

## Astral dependency

Atlas links against the [Astral](https://github.com/TDacik/Astral)
separation-logic solver. To make Astral available:

1. Clone the Astral repository.
2. Check out the `low-level-seplog` branch.
3. Follow the build and install instructions in that repository.
