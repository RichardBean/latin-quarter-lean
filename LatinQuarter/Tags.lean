import Mathlib

namespace LatinQuarter
open scoped BigOperators
open MvPolynomial

/-- The discarded monomials: those divisible by the square of a tag. -/
def repeatedTagIdeal (κ : Type*) : Ideal (MvPolynomial κ (ZMod 2)) :=
  Ideal.span ((fun d => monomial d (1 : ZMod 2)) ''
    Set.range (fun j : κ => Finsupp.single j 2))

/-- Discarding repeated tags cannot affect any square-free coefficient. -/
theorem squarefree_coeff_zero_of_mem {κ : Type*}
    {p : MvPolynomial κ (ZMod 2)} (hp : p ∈ repeatedTagIdeal κ)
    {d : κ →₀ ℕ} (hd : ∀ j, d j ≤ 1) : coeff d p = 0 := by
  classical
  by_contra hn
  have hmem := mem_support_iff.mpr hn
  obtain ⟨e, ⟨j, rfl⟩, he⟩ := mem_ideal_span_monomial_image.mp hp d hmem
  have hj := he j
  simp only [Finsupp.single_eq_same] at hj
  have := hd j
  omega

theorem repeatedTagIdeal_ne_top (κ : Type*) : repeatedTagIdeal κ ≠ ⊤ := by
  intro h
  have hp : (1 : MvPolynomial κ (ZMod 2)) ∈ repeatedTagIdeal κ := by rw [h]; trivial
  have hz := squarefree_coeff_zero_of_mem hp (d := 0) (by simp)
  simp at hz

/-- Polynomials modulo two, with the square of every tag set to zero. -/
abbrev TagRing (κ : Type*) := MvPolynomial κ (ZMod 2) ⧸ repeatedTagIdeal κ

instance (κ : Type*) : Nontrivial (TagRing κ) :=
  Ideal.Quotient.nontrivial (repeatedTagIdeal_ne_top κ)

instance (κ : Type*) : CharP (TagRing κ) 2 :=
  charP_of_injective_algebraMap' (ZMod 2) (TagRing κ) 2

noncomputable def tag {κ : Type*} (j : κ) : TagRing κ :=
  Ideal.Quotient.mk _ (X j)

@[simp] theorem tag_sq {κ : Type*} (j : κ) : tag j * tag j = 0 := by
  rw [tag, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨Finsupp.single j 2, ⟨j, rfl⟩, ?_⟩
  simp [X, monomial_mul, ← Finsupp.single_add]

/-- A zero polynomial in the bookkeeping ring has zero square-free
coefficients in the original polynomial ring. -/
theorem squarefree_coeff_zero_of_quotient_zero {κ : Type*}
    {p : MvPolynomial κ (ZMod 2)}
    (hp : Ideal.Quotient.mk (repeatedTagIdeal κ) p = 0)
    {d : κ →₀ ℕ} (hd : ∀ j, d j ≤ 1) : coeff d p = 0 :=
  squarefree_coeff_zero_of_mem (Ideal.Quotient.eq_zero_iff_mem.mp hp) hd

/-- Adding constants to `m` individual tags does not change a coefficient
of total degree `m`. This also allows zero constants. -/
theorem coeff_prod_add_constants {ι κ : Type*} [Fintype ι]
    (f : ι → κ) (a : ι → ZMod 2) (d : κ →₀ ℕ)
    (hd : ∑ j ∈ d.support, d j = Fintype.card ι) :
    coeff d (∏ i, (X (f i) + C (a i))) = coeff d (∏ i, X (f i) : MvPolynomial κ (ZMod 2)) := by
  classical
  rw [Fintype.prod_add, coeff_sum]
  rw [Finset.sum_eq_single (Finset.univ : Finset ι)]
  · simp
  · intro s _ hs
    apply coeff_eq_zero_of_totalDegree_lt
    have hc : s.card < Fintype.card ι := by
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
    have hdeg : (∏ i ∈ s, (X (f i) : MvPolynomial κ (ZMod 2))).totalDegree ≤ s.card := by
      simpa using totalDegree_finset_prod s (fun i => (X (f i) : MvPolynomial κ (ZMod 2)))
    have hconst : (∏ i ∈ sᶜ, C (a i) : MvPolynomial κ (ZMod 2)).totalDegree = 0 := by
      rw [← map_prod]
      exact totalDegree_C _
    have hm := totalDegree_mul (∏ i ∈ s, (X (f i) : MvPolynomial κ (ZMod 2)))
      (∏ i ∈ sᶜ, C (a i))
    rw [hconst, add_zero] at hm
    rw [hd]
    exact lt_of_le_of_lt (hm.trans hdeg) hc
  · simp

/-- The exponent vector for the product of all tags, once each. -/
noncomputable def allTagsExponent (κ : Type*) [Fintype κ] : κ →₀ ℕ :=
  ∑ j : κ, Finsupp.single j 1

@[simp] theorem allTagsExponent_apply {κ : Type*} [Fintype κ] (j : κ) :
    allTagsExponent κ j = 1 := by
  classical
  simp [allTagsExponent, Finsupp.single_apply]

@[simp] theorem allTagsExponent_support {κ : Type*} [Fintype κ] :
    (allTagsExponent κ).support = Finset.univ := by
  classical
  ext j
  simp

@[simp] theorem allTagsExponent_degree {κ : Type*} [Fintype κ] :
    ∑ j ∈ (allTagsExponent κ).support, allTagsExponent κ j = Fintype.card κ := by
  classical
  simp

theorem coeff_allTags_product {κ : Type*} [Fintype κ] :
    coeff (allTagsExponent κ) (∏ j : κ, X j : MvPolynomial κ (ZMod 2)) = 1 := by
  classical
  have hp := prod_X_pow_eq_monomial (R := ZMod 2) (s := allTagsExponent κ)
  simp only [allTagsExponent_support, allTagsExponent_apply, pow_one] at hp
  rw [hp]
  simp

end LatinQuarter

