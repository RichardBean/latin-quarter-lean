THE SMALLEST CRITICAL SET IN A LATIN SQUARE: LEAN 4 FORMALIZATION
Prepared with Codex at Richard Bean's request, 16 October 2026.

PUBLICATION PACKAGE

README.md is the GitHub landing page and includes the paper link, citation
information, licence and automatic build instructions. CITATION.cff and
CITATION.bib describe version 0.1.0. The project is licensed under Apache-2.0;
see LICENSE and NOTICE. UPLOAD.txt explains how to preserve the hidden .github
directory when uploading the unpacked distribution to GitHub.

START HERE

LatinQuarterStandalone.lean contains the entire proof in one file. It imports
only Mathlib, and contains every additional definition and proof needed for
the result. Send this file together with this project archive, so recipients
have the exact toolchain and dependency pins as well as the source.

LatinQuarter/Main.lean gives the same final statements in the modular version.
Audit.lean prints the definitions and theorem types and checks the axiom lists.

WHAT IS PROVED

For every positive integer n:

  1. Every defining set of every Latin square of order n has at least
     floor(n*n/4) clues.
  2. The two corner triangles in the cyclic square form a critical set of
     exactly that size.
  3. Consequently scs(n) = scs(Z_n) = floor(n*n/4).

The public theorem names are:

  LatinQuarter.defining_set_lower_bound
  LatinQuarter.cornerSet_isCritical
  LatinQuarter.cornerSet_card
  LatinQuarter.scs_eq_quarter
  LatinQuarter.cyclic_scs_eq_quarter
  LatinQuarter.quarter_bound

The statements quantify over all orders, not a finite list of checked cases.
Natural-number division in Lean is floor division.

The definitions are explicit. A square is a function Fin n -> Fin n -> Fin n;
each row and column is required to be bijective. A defining set specifies the
entries of a Latin square on a finite set of cells and requires any agreeing
Latin square to equal it. A critical set has no proper defining subset.
The function scs is the infimum of the actual sizes of critical sets over all
Latin squares. The proof supplies a critical set attaining the bound.

SCOPE OF SELF-CONTAINMENT

The source is mathematically self-contained relative to Lean and mathlib.
It does not need a TeX file, a PDF, a saved conversation, an external solver,
a computational certificate, or an unproved lemma from the manuscript.
Mathlib provides standard finite-set, polynomial, ideal, and matrix theory.
The proof formalizes the exact critical-set theorem; the stronger separate
statement about the parity of all completion counts is not a public theorem
in this package. The lower bound instead specializes the same coefficient
argument to unique completion.

WHICH MANUSCRIPT, AND WHY

The starting version is quarter_bound_counting.tex. It contains the complete
counting proof without the expanded examples and historical material of qu2.tex,
and avoids the determinantal-primality machinery of subgroup_parity_proof.tex.

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

As with any formalization, a reader should also inspect the definitions and
statements to confirm that they express the intended mathematical claim.
Audit.lean makes those definitions and statements easy to inspect.

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

PROVENANCE

The formalization was substantially AI-generated by Codex in collaboration
with Richard Bean. It formalizes the supplied counting manuscript, whose
background development involved Richard Bean, Codex, and Claude. Successful
Lean checking validates the formal deductions; it is not a claim of independent
human peer review or of a historical priority investigation.
