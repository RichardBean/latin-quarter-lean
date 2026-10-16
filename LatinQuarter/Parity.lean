import LatinQuarter.LowerBound

/-!
# Parity of the number of completions

Written by Claude (Anthropic) at Richard Bean's request, October 2026, for
version 0.2.0. This is Theorem A of the paper: below the quarter bound, every
set of clues taken from a Latin square has an even number of completions.

The coefficient computation in `Counting.lean` holds for every set of clues,
not only for defining sets: the square-free coefficient counts, modulo two,
the row choices that produce Latin squares. Those row choices correspond
exactly to the completions. The vanishing argument used in `LowerBound.lean`
makes the coefficient zero below the quarter bound.
-/

namespace LatinQuarter
open scoped BigOperators Matrix Classical
open MvPolynomial

/-- The square-free coefficient counts the Latin row choices modulo two. -/
theorem coefficient_eq_card_latin_choices {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (a : Cell n → ZMod 2) :
    coeff (allTagsExponent (Cell n))
      (clueProduct P L (fun c s => X (c,s) + C (a (c,s))) *
       rowMinorProduct P L (fun c s => X (c,s) + C (a (c,s)))) =
      ((Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card : ZMod 2) := by
  rw [expand_row_matchings, coeff_sum]
  have hc (σ : RowChoices P) :
      coeff (allTagsExponent (Cell n))
        (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
          C (a (columnSymbol (chosenSquare P L σ) p)))) =
        if IsLatin (chosenSquare P L σ) then 1 else 0 := by
    rw [coeff_prod_add_constants _ _ _ (by simp)]
    exact full_coefficient _ (chosenSquare_rows P L hL σ)
  change (∑ σ : RowChoices P, coeff (allTagsExponent (Cell n))
    (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
      C (a (columnSymbol (chosenSquare P L σ) p))))) = _
  simp_rw [hc]
  rw [Finset.sum_boole]

/-- Every completion arises from one permutation of the free cells in each row. -/
theorem exists_rowChoices_of_completion {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (M : Square n) (hM : IsLatin M)
    (ha : Agrees P L M) : ∃ σ : RowChoices P, chosenSquare P L σ = M := by
  -- In row `r`, the free cell `c` of `M` holds the symbol that `L` has in
  -- column `(L r)⁻¹ (M r c)`, and that column is also free.
  have hfree : ∀ (r : Fin n) (c : FreeColumn P r),
      (r, (Equiv.ofBijective (L r) (hL.1 r)).symm (M r c)) ∉ P := by
    intro r c hmem
    have hLd : L r ((Equiv.ofBijective (L r) (hL.1 r)).symm (M r c)) = M r c :=
      Equiv.ofBijective_apply_symm_apply (L r) (hL.1 r) (M r c)
    have hMd := ha _ hmem
    have hdc : (Equiv.ofBijective (L r) (hL.1 r)).symm (M r c) = c.val :=
      (hM.1 r).injective (hMd.trans hLd)
    rw [hdc] at hmem
    exact c.property hmem
  let f : (r : Fin n) → FreeColumn P r → FreeColumn P r := fun r c =>
    ⟨(Equiv.ofBijective (L r) (hL.1 r)).symm (M r c), hfree r c⟩
  have hf : ∀ r, Function.Injective (f r) := by
    intro r c c' h
    have h1 := congrArg Subtype.val h
    have h2 := (Equiv.ofBijective (L r) (hL.1 r)).symm.injective h1
    exact Subtype.ext ((hM.1 r).injective h2)
  let σ : RowChoices P := fun r => Equiv.ofBijective (f r) (hf r).bijective_of_finite
  refine ⟨σ, ?_⟩
  funext r c
  by_cases hc : (r, c) ∈ P
  · rw [chosenSquare_clue P L σ r c hc]
    exact (ha (r, c) hc).symm
  · calc chosenSquare P L σ r c = L r (σ r ⟨c, hc⟩) := chosenSquare_free P L σ r ⟨c, hc⟩
      _ = M r c := Equiv.ofBijective_apply_symm_apply (L r) (hL.1 r) (M r c)

/-- The completions are in bijection with the Latin row choices. -/
theorem card_completions_eq {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (hL : IsLatin L) :
    (completions P L).card =
      (Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card := by
  symm
  apply Finset.card_bij (fun σ _ => chosenSquare P L σ)
  · intro σ hσ
    exact mem_completions.mpr ⟨(Finset.mem_filter.mp hσ).2, chosenSquare_agrees P L σ⟩
  · intro σ _ τ _ h
    exact chosenSquare_injective P L hL h
  · intro M hM
    obtain ⟨hMl, hMa⟩ := mem_completions.mp hM
    obtain ⟨σ, hσ⟩ := exists_rowChoices_of_completion P L hL M hMl hMa
    refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, ?_⟩, hσ⟩
    rw [hσ]
    exact hMl

/-- Theorem A, in the cell form used throughout this package: if fewer than
`n * n / 4` cells of a Latin square `L` are given, the number of Latin squares
that agree with `L` on those cells is even. -/
theorem completions_card_even {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (hL : IsLatin L) (hP : P.card < n * n / 4) :
    Even (completions P L).card := by
  let e : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  let Y : Matrix (Fin n) (Fin n) (MvPolynomial (Cell n) (ZMod 2)) :=
    fun c s => X (c,s) + C (markedConstant e c s)
  let q := Ideal.Quotient.mk (repeatedTagIdeal (Cell n))
  have hrow : q (rowMinorProduct P L Y) = rowMinorProduct P L (shiftedTags e) := by
    unfold rowMinorProduct
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r _
    rw [q.map_det]
    congr 1
  have hz : rowMinorProduct P L (shiftedTags e) = 0 :=
    shifted_tags_product_vanishes e (fun r => FreeColumn P r)
      (fun _ c => c.val) (fun r c => L r c) (clue_budget P hP)
  have hzq : q (clueProduct P L Y * rowMinorProduct P L Y) = 0 := by
    rw [map_mul, hrow, hz, mul_zero]
  have hc0 := squarefree_coeff_zero_of_quotient_zero hzq
    (d := allTagsExponent (Cell n)) (by simp)
  have hc1 := coefficient_eq_card_latin_choices P L hL
    (fun p => markedConstant e p.1 p.2)
  change coeff (allTagsExponent (Cell n))
    (clueProduct P L Y * rowMinorProduct P L Y) = _ at hc1
  rw [hc0, ← card_completions_eq P L hL] at hc1
  exact ZMod.natCast_eq_zero_iff_even.mp hc1.symm

end LatinQuarter
