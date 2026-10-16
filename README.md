# The smallest critical set in a Latin square: Lean 4 formalization

[![Lean proof check](https://github.com/RichardBean/latin-quarter-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/RichardBean/latin-quarter-lean/actions/workflows/lean.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23410171.svg)](https://doi.org/10.5281/zenodo.23410171)

For every positive integer $n$, this project proves

$$\operatorname{scs}(n)=\operatorname{scs}(Z_n)=\left\lfloor n^2/4\right\rfloor.$$

Here `scs(n)` is the smallest size of a critical set among all Latin squares
of order $n$, and `scs(Z_n)` is the smallest size in the cyclic Latin square.
A critical set specifies entries that determine the square uniquely, and no
proper subset does so. The proof covers every positive order.

It also proves the parity theorem behind this bound: a partial Latin square of
order $n$ with fewer than $\lfloor n^2/4\rfloor$ filled cells has an even
number of completions. These are Theorems A and B of the paper.

**Author and maintainer:** Richard Bean. The formalization was substantially
AI-generated; see [Provenance](#provenance).

**Paper:** Richard Bean, [*A counting proof for the smallest critical set in a
Latin square*](https://arxiv.org/abs/2610.18199), arXiv:2610.18199 (2026).

## Start here

- [LatinQuarter/Textbook.lean](LatinQuarter/Textbook.lean) states Theorems A and
  B with the definitions of Section 1 of the paper, written from scratch. To
  check that the package proves what the paper claims, read the definitions and
  theorem statements in this file.
- [LatinQuarterStandalone.lean](LatinQuarterStandalone.lean) contains all project
  definitions and proofs in one file, importing only `Mathlib`.
- [LatinQuarter/Main.lean](LatinQuarter/Main.lean) contains the statements of
  Theorem B in the package's own terms, and
  [LatinQuarter/Parity.lean](LatinQuarter/Parity.lean) proves Theorem A.
- [LatinQuarter/Basic.lean](LatinQuarter/Basic.lean) defines Latin squares and
  unique completion. The definition of criticality is in `Main.lean`.
- [Audit.lean](Audit.lean) displays the definitions and checks the axioms used
  by the principal results.

The project is self-contained relative to Lean and mathlib. Checking it does
not require the paper, an external solver, or a separate computational certificate.
Both theorems of the paper are formalized.

## Check the proof

Install Lean's toolchain manager [elan](https://github.com/leanprover/elan), then
run these commands from the directory containing `lakefile.toml`:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true LatinQuarterStandalone.lean
```

The first command downloads the dependencies and the precompiled mathlib cache.
An initial check needs an Internet connection and several gigabytes of disk
space. The repository pins these versions:

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.24.0` |
| mathlib | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (v4.24.0) |
| This package | `0.2.0` |

`lean-toolchain` selects the compiler; `lake-manifest.json` pins transitive
dependencies. Keep both files when sharing the proof. `verification-build.txt`,
`verification.txt` and
[verification-publication.txt](verification-publication.txt) record the checks
of version 0.1.0; [verification-v0.2.0.txt](verification-v0.2.0.txt) records
the checks of version 0.2.0. The workflow badge above reports the status of
GitHub's own runs.

## Use the result

Within this project, the following is a complete example:

```lean
import LatinQuarter

example (n : ℕ) (hn : 0 < n) :
    LatinQuarter.scs n = n * n / 4 :=
  LatinQuarter.scs_eq_quarter n hn
```

Natural-number division in Lean implements the floor. Another compatible Lake
project can add this repository as a Git dependency, preferably pinned to the
particular commit being cited, and then use `import LatinQuarter`.

| Theorem | Statement |
| --- | --- |
| `LatinQuarter.Textbook.completions_even` | Theorem A: fewer than `n * n / 4` filled cells give an even number of completions. |
| `LatinQuarter.Textbook.definingSet_card` | Every defining set of every Latin square has at least `n * n / 4` filled cells. |
| `LatinQuarter.Textbook.scs_eq_quarter` | Theorem B: `scs(n) = scs(B_n) = n * n / 4`, for `0 < n`. |
| `LatinQuarter.completions_card_even` | Theorem A in the package's terms, for clues taken from a Latin square. |
| `LatinQuarter.defining_set_lower_bound` | Every defining set in every Latin square has at least `n * n / 4` entries. |
| `LatinQuarter.cornerSet_isCritical` | The two corner triangles form a critical set in the cyclic square, for `0 < n`. |
| `LatinQuarter.cornerSet_card` | That corner set has exactly `n * n / 4` entries, for `0 < n`. |
| `LatinQuarter.scs_eq_quarter` | The minimum over all Latin squares is `n * n / 4`, for `0 < n`. |
| `LatinQuarter.cyclic_scs_eq_quarter` | The minimum in the cyclic square is `n * n / 4`, for `0 < n`. |

The first three use the definitions of the paper, stated in `Textbook.lean`:
filled cells are (row, column, symbol) triples, a Latin square has each symbol
exactly once in every row and column, a critical set is a defining set from
which emptying any one filled cell leaves more than one completion, and
`scs(n)` is the minimum of `scs(L)` over all Latin squares `L` of order `n`.
Theorem A is stated for every finite set of triples, which covers every partial
Latin square.

Import either `LatinQuarter` or `LatinQuarterStandalone` in a given downstream
file: they define the same declarations and must not be imported together.

## Verification and automatic builds

[The GitHub workflow](.github/workflows/lean.yml) runs on pushes, pull requests,
and manual requests from the Actions tab. It:

1. Regenerates the standalone file and fails if it differs from the committed version.
2. Installs the pinned Lean toolchain and obtains the mathlib cache.
3. Builds the modular proof, standalone proof, and audit, treating warnings as failures.
4. Replays every declaration of the modular and standalone proofs through Lean's
   kernel with [lean4checker](https://github.com/leanprover/lean4checker).
5. Runs the axiom audit and standalone source check explicitly.
6. Exports the main theorems and everything they depend on with
   [lean4export](https://github.com/leanprover/lean4export), and checks the
   export with [nanoda](https://github.com/ammkrn/nanoda_lib), a separate type
   checker for Lean written in Rust, allowing only the three standard axioms.

The workflow uses [Lean's standard GitHub action](https://github.com/leanprover/lean-action).
It does not restore cached build products for this project, so its own modules
are rebuilt on each run. Only the dependency cache is downloaded.

The checked principal results use only Lean's standard foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`. The `#guard_msgs` checks fail if
their reported axiom lists change. The proofs contain no admitted goals or
additional mathematical axioms. Human review of the definitions and statements
remains useful for checking their correspondence with the mathematical claim.

After editing the modular sources, regenerate the single-file version with:

```sh
python3 make_standalone.py
```

Then repeat the checks above. Python is needed for this regeneration check, but
not for Lean to check an existing proof file. See [README.txt](README.txt) for
the detailed source map and the relationship with the counting manuscript.

## Citation

Please cite the software version or commit used, and the accompanying paper
when discussing the mathematical result. [CITATION.cff](CITATION.cff) provides
machine-readable software metadata for GitHub's **Cite this repository** menu.
[CITATION.bib](CITATION.bib) supplies BibTeX entries for the software and paper.

> Richard Bean (2026). *The smallest critical set in a Latin square: Lean 4
> formalization*, version 0.2.0. Zenodo. https://doi.org/10.5281/zenodo.23410172

> Richard Bean (2026). *A counting proof for the smallest critical set in a
> Latin square*. arXiv:2610.18199. https://arxiv.org/abs/2610.18199

The paper's arXiv identifier refers to the manuscript. Zenodo archives each
release of this repository: https://doi.org/10.5281/zenodo.23410171 always
resolves to the latest version, and https://doi.org/10.5281/zenodo.23410172 is
version 0.2.0.

## Provenance

The mathematical argument and manuscript were developed with substantial use
of Codex and Claude under Richard Bean's direction. Codex substantially
generated the Lean formalization of version 0.1.0, its supporting scripts, and
this repository's documentation in collaboration with Richard Bean. The initial
formalization used the shorter counting manuscript as its starting point.
Claude wrote the version 0.2.0 additions at Richard Bean's request:
`Parity.lean` (Theorem A), `Textbook.lean` (both theorems with the paper's
definitions), the kernel-replay and nanoda checks in the workflow, and the
matching documentation changes.

The package records successful Lean checks of the formal deductions. These
checks do not constitute independent human peer review. AI tools are disclosed
here as tools and are not listed as authors in the citation metadata.

## Licence

Copyright 2026 Richard Bean. This project's source code and accompanying
documentation are licensed under the [Apache License, Version 2.0](LICENSE).
Lean, mathlib, and other dependencies retain their own licences. The linked
arXiv manuscript has its own licence, specified on its arXiv record.
