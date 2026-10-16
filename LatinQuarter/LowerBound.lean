import LatinQuarter.Counting
import LatinQuarter.Shifted
import LatinQuarter.Budget

namespace LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial

/-- Every defining set in every labelled Latin square has at least the
quarter-square number of clues. No restriction on the completed square
or on the distribution of its clues is assumed. -/
theorem defining_set_lower_bound {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (h : IsDefining P L) : n * n / 4 ≤ P.card := by
  classical
  by_contra! hP
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
  have hc1 := defining_coefficient_one P L h (fun p => markedConstant e p.1 p.2)
  change coeff (allTagsExponent (Cell n))
    (clueProduct P L Y * rowMinorProduct P L Y) = 1 at hc1
  exact zero_ne_one (hc0.symm.trans hc1)

end LatinQuarter
