import LatinQuarter.Rows
import LatinQuarter.Tags
import LatinQuarter.SquareZero

namespace LatinQuarter
open scoped BigOperators Matrix Classical
open MvPolynomial

noncomputable def clueProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, ∏ c : {c : Fin n // (r,c) ∈ P}, Y c (L r c)

noncomputable def rowMinorProduct {n : ℕ} {R : Type*} [CommRing R]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∏ r, (Y.submatrix (fun c : FreeColumn P r => c.val)
    (fun c : FreeColumn P r => L r c)).det

/-- Expanding the row matching sums enumerates all independent ways to
finish the rows. The clue factors restore the full set of cells. -/
theorem expand_row_matchings {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) :
    clueProduct P L Y * rowMinorProduct P L Y =
      ∑ σ : RowChoices P, ∏ p : Cell n, Y p.2 (chosenSquare P L σ p.1 p.2) := by
  classical
  unfold rowMinorProduct
  simp_rw [det_eq_matching_sum]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fintype.prod_prod_type]
  unfold clueProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun c : Fin n => (r,c) ∈ P)
    (fun c => Y c (chosenSquare P L σ r c))
  convert hp using 1
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro c _
      rw [chosenSquare_clue P L σ r c c.property]
    · apply Finset.prod_congr rfl
      intro c _
      simp only [Matrix.submatrix_apply, chosenSquare_free]

abbrev columnSymbol {n : ℕ} (M : Square n) (p : Cell n) : Cell n :=
  (p.2, M p.1 p.2)

theorem columnSymbol_bijective {n : ℕ} {M : Square n} (hM : IsLatin M) :
    Function.Bijective (columnSymbol M) := by
  apply Function.Injective.bijective_of_finite
  intro p q hpq
  have hc : p.2 = q.2 := congrArg Prod.fst hpq
  have hs : M p.1 p.2 = M q.1 q.2 := congrArg Prod.snd hpq
  apply Prod.ext
  · apply (hM.2 p.2).injective
    simpa only [columnSymbol, ← hc] using hs
  · exact hc

theorem isLatin_of_columnSymbol_injective {n : ℕ} {M : Square n}
    (hr : ∀ r, Function.Bijective (M r)) (hi : Function.Injective (columnSymbol M)) :
    IsLatin M := by
  refine ⟨hr, fun c => Function.Injective.bijective_of_finite ?_⟩
  intro r s h
  have he : columnSymbol M (r,c) = columnSymbol M (s,c) := Prod.ext rfl h
  exact congrArg Prod.fst (hi he)

/-- The full square-free coefficient is one for a Latin square and zero
for a row permutation that repeats a symbol in a column. -/
theorem full_coefficient {n : ℕ} (M : Square n)
    (hr : ∀ r, Function.Bijective (M r)) :
    coeff (allTagsExponent (Cell n))
      (∏ p : Cell n, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)) =
      if IsLatin M then 1 else 0 := by
  classical
  by_cases hM : IsLatin M
  · rw [if_pos hM]
    have hp := (Equiv.ofBijective (columnSymbol M) (columnSymbol_bijective hM)).prod_comp
      (fun p => (X p : MvPolynomial (Cell n) (ZMod 2)))
    change (∏ p, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)) = ∏ p, X p at hp
    rw [hp]
    exact coeff_allTags_product
  · rw [if_neg hM]
    have hn : ¬ Function.Injective (columnSymbol M) :=
      fun hi => hM (isLatin_of_columnSymbol_injective hr hi)
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨p, q, hpq⟩ := hn
    have he : columnSymbol M p = columnSymbol M q := by tauto
    have hne : p ≠ q := by tauto
    apply squarefree_coeff_zero_of_quotient_zero _ (by simp)
    simp only [map_prod]
    change (∏ p : Cell n, tag (columnSymbol M p)) = 0
    exact product_eq_zero_of_repeated_square_zero _ hne (congrArg tag he) (tag_sq _)

/-- Adding constants preserves the completion coefficient, and unique
completion makes that coefficient exactly one. -/
theorem defining_coefficient_one {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) (a : Cell n → ZMod 2) :
    coeff (allTagsExponent (Cell n))
      (clueProduct P L (fun c s => X (c,s) + C (a (c,s))) *
       rowMinorProduct P L (fun c s => X (c,s) + C (a (c,s)))) = 1 := by
  classical
  rw [expand_row_matchings, coeff_sum]
  have hc (σ : RowChoices P) :
      coeff (allTagsExponent (Cell n))
        (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
          C (a (columnSymbol (chosenSquare P L σ) p)))) =
        if IsLatin (chosenSquare P L σ) then 1 else 0 := by
    rw [coeff_prod_add_constants _ _ _ (by simp)]
    exact full_coefficient _ (chosenSquare_rows P L h.1 σ)
  change (∑ σ : RowChoices P, coeff (allTagsExponent (Cell n))
    (∏ p : Cell n, (X (columnSymbol (chosenSquare P L σ) p) +
      C (a (columnSymbol (chosenSquare P L σ) p))))) = 1
  simp_rw [hc]
  rw [Finset.sum_eq_single (1 : RowChoices P)]
  · simp [h.1]
  · intro σ _ hσ
    rw [if_neg]
    exact fun hl => hσ (unique_chosenSquare P L h σ hl)
  · simp

end LatinQuarter
