THE SMALLEST CRITICAL SET IN A LATIN SQUARE: LEAN 4 FORMALIZATION
Prepared with Codex at Richard Bean's request, 16 October 2026.
Version 0.2.0 additions written by Claude at Richard Bean's request,
16 October 2026.

PUBLICATION PACKAGE

README.md is the GitHub landing page and includes the paper link, citation
information, licence and automatic build instructions. CITATION.cff and
CITATION.bib describe version 0.2.0. The project is licensed under Apache-2.0;
see LICENSE and NOTICE.

START HERE

LatinQuarterStandalone.lean contains the entire proof in one file. It imports
only Mathlib, and contains every additional definition and proof needed for
the results. Send this file together with this project archive, so recipients
have the exact toolchain and dependency pins as well as the source.

LatinQuarter/Textbook.lean states Theorems A and B of the paper with the
definitions of its Section 1, written from scratch. To check that the package
proves what the paper claims, read the definitions and theorem statements in
that file. LatinQuarter/Main.lean gives the statements of Theorem B in the
package's own terms. Audit.lean prints the definitions and theorem types and
checks the axiom lists.

WHAT IS PROVED

Theorem A (parity). For every n, a set of fewer than floor(n*n/4) filled cells
has an even number of completions to a Latin square of order n.

Theorem B. For every positive integer n:

  1. Every defining set of every Latin square of order n has at least
     floor(n*n/4) clues.
  2. The two corner triangles in the cyclic square form a critical set of
     exactly that size.
  3. Consequently scs(n) = scs(Z_n) = floor(n*n/4).

The public theorem names are:

  LatinQuarter.completions_card_even        Theorem A, package terms
  LatinQuarter.defining_set_lower_bound
  LatinQuarter.cornerSet_isCritical
  LatinQuarter.cornerSet_card
  LatinQuarter.scs_eq_quarter
  LatinQuarter.cyclic_scs_eq_quarter
  LatinQuarter.quarter_bound
  LatinQuarter.Textbook.completions_even    Theorem A, paper's definitions
  LatinQuarter.Textbook.definingSet_card    lower bound, paper's definitions
  LatinQuarter.Textbook.scs_eq_quarter      Theorem B, paper's definitions

The statements quantify over all orders, not a finite list of checked cases.
Natural-number division in Lean is floor division.

The definitions are explicit. A square is a function Fin n -> Fin n -> Fin n;
each row and column is required to be bijective. A defining set specifies the
entries of a Latin square on a finite set of cells and requires any agreeing
Latin square to equal it. A critical set has no proper defining subset.
The function scs is the infimum of the actual sizes of critical sets over all
Latin squares. The proof supplies a critical set attaining the bound.

Textbook.lean repeats both theorems with the paper's wording instead. Filled
cells are (row, column, symbol) triples, and Theorem A holds for every finite
set of triples, so it covers every partial Latin square. A Latin square has
each symbol exactly once in every row and in every column. A critical set is
a defining set from which emptying any one filled cell leaves more than one
completion, and scs(n) is the minimum of scs(L) over all Latin squares L of
order n. None of these definitions reuse the package's own, so the file is an
independent check that the formal statements say what the paper says.

SCOPE OF SELF-CONTAINMENT

The source is mathematically self-contained relative to Lean and mathlib.
It does not need a TeX file, a PDF, a saved conversation, an external solver,
a computational certificate, or an unproved lemma from the manuscript.
Mathlib provides standard finite-set, polynomial, ideal, and matrix theory.
Version 0.2.0 adds the parity statement (Theorem A of the paper) in
Parity.lean, using the same coefficient argument. The original lower-bound
proof in LowerBound.lean, which specializes that argument to unique
completion, is unchanged.

WHICH MANUSCRIPT, AND WHY

The starting version is quarter_bound_counting.tex. It contains the complete
counting proof without the expanded examples and historical material of qu2.tex
(the arXiv version), and avoids the determinantal-primality machinery of
subgroup_parity_proof.tex.

The formalization follows that counting proof, with two useful changes:

  * All marked pivots are removed at once using block matrix elimination.
    The residual entries generate an ideal; powers of that ideal record the
    number of residual factors. More factors than positions forces zero.
  * The two cyclic corner triangles are injected into an (n/2)-by-(n-n/2)
    rectangle. This gives the upper size bound directly; the already proved
    lower bound makes its size exact.

The key combinatorial coefficient identity and the cyclic forcing argument
are proved in the source, rather than assumed.

REPRODUCIBLE CHECK

Pinned versions:

  Lean:    leanprover/lean4:v4.24.0
  Mathlib: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

With Lean's toolchain manager elan installed, open a terminal in this directory
and run:

  lake exe cache get
  lake build
  lake env lean Audit.lean
  lake env lean LatinQuarterStandalone.lean

The first command fetches the pinned dependencies and their precompiled cache;
it needs an Internet connection and several gigabytes of disk space. The
lean-toolchain file selects the required compiler automatically. No local paths
or modifications to mathlib are required.

The standalone command checks the whole proof from its source in one invocation.
The modular command reuses compiled local modules. Import either LatinQuarter
or LatinQuarterStandalone in a downstream file, not both: their declarations
are identical.

The standalone file is generated from the modular sources. After editing the
modules, regenerate it with:

  python3 make_standalone.py

Then rerun the checks above.

AXIOM AUDIT

The checked top-level results depend only on:

  propext          propositional extensionality
  Classical.choice classical choice
  Quot.sound       soundness of Lean's quotient construction

These are standard Lean foundations. There are no additional mathematical
axioms, admitted goals, sorry placeholders, or native_decide computations.
The #guard_msgs commands fail if the reported axiom lists change. Tactics such
as omega and nlinarith produce proof terms that Lean checks.

The GitHub workflow also replays every declaration through Lean's kernel with
lean4checker, and checks the main theorems and everything they depend on with
nanoda, a separate type checker for Lean written in Rust. See README.md.

As with any formalization, a reader should also inspect the definitions and
statements to confirm that they express the intended mathematical claim.
Audit.lean and Textbook.lean make those definitions and statements easy to
inspect.

SOURCE MAP

  Basic       Latin squares, clues, agreement, unique completion
  SquareZero  repeated-factor and finite-position vanishing
  Minors      minor-ideal membership under matrix multiplication
  Vanishing   block elimination and the abstract vanishing lemma
  Tags        bookkeeping quotient and square-free coefficients
  Shifted     marked dummy entries and arbitrary selected minors
  Rows        row permutations and unsigned matching sums
  Budget      the global clue count and the quarter-square arithmetic
  Counting    the coefficient argument for unique completion
  LowerBound  the unrestricted lower bound
  Cyclic      the cyclic square and forced completion of the corner set
  CornerSize  the rectangular injection
  Main        criticality and the exact scs statements
  Parity      Theorem A: completions correspond to Latin row choices, whose
              number the coefficient counts modulo two
  Textbook    Theorems A and B restated with the paper's definitions

PROVENANCE

The formalization was substantially AI-generated by Codex in collaboration
with Richard Bean. It formalizes the supplied counting manuscript, whose
background development involved Richard Bean, Codex, and Claude. Claude wrote
the version 0.2.0 additions (Parity.lean, Textbook.lean and the kernel-replay
and nanoda checks in the GitHub workflow) at Richard Bean's request. Successful
Lean checking validates the formal deductions; it is not a claim of independent
human peer review or of a historical priority investigation.
