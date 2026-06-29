# SphereObstructionHilbertShiftQuotient

This repository contains a Lean 4 formalization of an obstruction to Hilbert embeddability for a quotient of the Hilbert sphere by the bilateral shift.

Let $H = \ell_2(\mathbb{Z})$ and let $S$ be the bilateral shift. The main result proves that the quotient $\mathbb{S}(\ell_2(\mathbb{Z}))/ \langle S \rangle$, equipped with the chordal quotient metric, has infinite Hilbert distortion. The formalization also proves the corresponding statement for the angular quotient metric and records the finite-profile consequence: the quotient contains finite subsets with arbitrarily large Hilbert distortion.

The proof follows the blueprint in `blueprint/`: finite pieces of hard flat tori are embedded, after rescaling and controlled error, into higher-rank sphere quotients and then coded into the one-dimensional shift quotient.

## Repository layout

- `SphereObstructionHilbertShiftQuotient/` contains the Lean source files.
- `SphereObstructionHilbertShiftQuotient/Main.lean` assembles the main theorem
  and the finite distortion profile corollary.
- `blueprint/` contains the informal blueprint for the formalization.
- `home_page/` contains the GitHub Pages wrapper used for generated
  documentation.
- `lakefile.toml` and `lean-toolchain` pin the Lean/Lake project configuration.

## Setup

Install Lean through `elan`, then fetch this repository and build it with Lake.
The Lean version is pinned by `lean-toolchain`; no separate manual version selection is needed.

```bash
git clone https://github.com/adas1236/SphereObstructionHilbertShiftQuotient
cd SphereObstructionHilbertShiftQuotient
lake exe cache get
lake build
```

`lake exe cache get` downloads precompiled mathlib artifacts when available.
If the cache is unavailable, `lake build` will build the needed dependencies locally.

## Useful commands

```bash
lake build
lake env lean SphereObstructionHilbertShiftQuotient/Main.lean
```

The project depends on mathlib, `doc-gen4`, and `checkdecls`, as recorded in `lakefile.toml` and `lake-manifest.json`.
