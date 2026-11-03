/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialMeaningFoundations
public import Mathlib.Algebra.Polynomial.Roots

/-! Trigonometric-polynomial uniqueness for the nonatomic singular branch of Theorem 7.
Laurent clearing is applied to the circle restriction, not to the formal bivariate polynomial.
-/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem circleCharacter_mul_conj (t : Boundary) :
    fourier (T := 1) 1 t * conj (fourier (T := 1) 1 t) = 1 := by
  rw [← fourier_neg, ← fourier_add]
  norm_num

theorem circleCharacter_ne_zero (t : Boundary) : fourier (T := 1) 1 t ≠ 0 := by
  intro h
  have hm := circleCharacter_mul_conj t
  simp only [h, zero_mul, zero_ne_one] at hm

theorem circleCharacter_injective : Function.Injective (fun t : Boundary => fourier (T := 1) 1 t) := by
  intro t s h
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Subtype.ext
  simpa only [fourier_one] using h

/-- A clearing exponent dominating every conjugate exponent in the finite support. -/
def laurentClearingOrder (q : BiPolynomial) : ℕ := q.support.sup (fun jk => jk.2)

/-- The ordinary polynomial obtained by multiplying the circle restriction by z^N. -/
def laurentClearedPolynomial (q : BiPolynomial) : Polynomial ℂ :=
  ∑ jk ∈ q.support, Polynomial.monomial (laurentClearingOrder q + jk.1 - jk.2) (q jk)

theorem laurentClearingOrder_ge (q : BiPolynomial) (jk : ℕ × ℕ) (h : jk ∈ q.support) :
    jk.2 ≤ laurentClearingOrder q := by
  exact Finset.le_sup h

theorem laurentMonomial_clear (z : ℂ) {N j k : ℕ} (hk : k ≤ N)
    (hz : z * conj z = 1) :
    z ^ N * (z ^ j * conj z ^ k) = z ^ (N + j - k) := by
  have he : N + j - k + k = N + j := by omega
  calc
    z ^ N * (z ^ j * conj z ^ k) = (z ^ N * z ^ j) * conj z ^ k := by ring
    _ = z ^ (N + j) * conj z ^ k := by rw [pow_add]
    _ = z ^ (N + j - k + k) * conj z ^ k := by rw [he]
    _ = z ^ (N + j - k) * (z ^ k * conj z ^ k) := by rw [pow_add]; ring
    _ = z ^ (N + j - k) := by rw [← mul_pow, hz, one_pow, mul_one]

/-- Clearing conjugate powers agrees with the original boundary polynomial, even when
that restriction vanishes identically for a nonzero formal bivariate polynomial. -/
theorem laurentClearedPolynomial_eval (q : BiPolynomial) (t : Boundary) :
    (laurentClearedPolynomial q).eval (fourier (T := 1) 1 t) =
      fourier (T := 1) 1 t ^ laurentClearingOrder q *
        polynomialValue q (fourier (T := 1) 1 t) := by
  classical
  simp only [laurentClearedPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, polynomialValue, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro jk hjk
  have hp := laurentMonomial_clear (fourier (T := 1) 1 t)
    (N := laurentClearingOrder q) (j := jk.1) (k := jk.2)
    (laurentClearingOrder_ge q jk hjk) (circleCharacter_mul_conj t)
  rw [← hp]
  ring

theorem laurentClearedPolynomial_ne_zero (q : BiPolynomial) (t : Boundary)
    (h : polynomialValue q (fourier (T := 1) 1 t) ≠ 0) :
    laurentClearedPolynomial q ≠ 0 := by
  intro hp
  have he := laurentClearedPolynomial_eval q t
  rw [hp, Polynomial.eval_zero] at he
  exact (mul_ne_zero (pow_ne_zero _ (circleCharacter_ne_zero t)) h) he.symm

/-- A non-identically-zero circle restriction has only finitely many circle zeros.
The hypothesis deliberately concerns the restriction, not the formal bivariate polynomial. -/
theorem trigonometric_zeroSet_finite (q : BiPolynomial)
    (h : ∃ t : Boundary, polynomialValue q (fourier (T := 1) 1 t) ≠ 0) :
    {t : Boundary | polynomialValue q (fourier (T := 1) 1 t) = 0}.Finite := by
  obtain ⟨t,ht⟩ := h
  have hp := laurentClearedPolynomial_ne_zero q t ht
  have hz : {z : ℂ | (laurentClearedPolynomial q).eval z = 0}.Finite := by
    simpa only [Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hp
  have hpre : ((fun s : Boundary => fourier (T := 1) 1 s) ⁻¹'
      {z : ℂ | (laurentClearedPolynomial q).eval z = 0}).Finite :=
    hz.preimage circleCharacter_injective.injOn
  apply hpre.subset
  intro s hs
  change (laurentClearedPolynomial q).eval (fourier (T := 1) 1 s) = 0
  rw [laurentClearedPolynomial_eval, hs, mul_zero]

/-- Nonatomic measure cannot be concentrated on the finite zeros of a nontrivial
circle polynomial. No measurability assumption on a general symbol is hidden here. -/
theorem nonatomic_measure_zero_of_trigonometric_ae (μ : Measure Boundary)
    (hμ : NonatomicMeasure μ) (q : BiPolynomial)
    (hae : ∀ᵐ t ∂μ, polynomialValue q (fourier (T := 1) 1 t) = 0)
    (h : ∃ t : Boundary, polynomialValue q (fourier (T := 1) 1 t) ≠ 0) : μ = 0 := by
  have hz : μ {t : Boundary | polynomialValue q (fourier (T := 1) 1 t) = 0} = 0 :=
    (measure_null_iff_singleton (trigonometric_zeroSet_finite q h).countable).mpr
      (fun t _ => hμ t)
  have hn : μ {t : Boundary | polynomialValue q (fourier (T := 1) 1 t) ≠ 0} = 0 :=
    ae_iff.mp hae
  have hu : μ Set.univ = 0 := by
    have he : ({t : Boundary | polynomialValue q (fourier (T := 1) 1 t) = 0} ∪
        {t : Boundary | polynomialValue q (fourier (T := 1) 1 t) ≠ 0}) = Set.univ := by
      ext t
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Classical.em _
    simpa only [he] using measure_union_null hz hn
  apply Measure.ext
  intro s _hs
  change μ s = 0
  exact measure_mono_null (Set.subset_univ s) hu

/-- A nonconstant singular inner function cannot have zero representing singular measure. -/
theorem singularRepresentation_measure_ne_zero (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) : μ ≠ 0 := by
  intro hm
  obtain ⟨_,α,hα,hvalue⟩ := hμ
  have hv := hvalue 0 (by norm_num [disk])
  have hv' : innerValue u 0 = α := by
    simpa only [singularInnerValue, hm, integral_zero_measure, mul_zero, neg_zero,
      Complex.exp_zero, mul_one] using hv
  have hi := norm_innerValue_lt_one u hu hn origin
  change ‖innerValue u 0‖ < 1 at hi
  rw [hv', hα] at hi
  exact (lt_irrefl (1 : ℝ)) hi

/-- The frozen T7 nonatomic trigonometric-uniqueness obligation, with no additional hypotheses. -/
theorem trigonometricUniqueness : TrigonometricUniqueness := by
  intro u hu hn μ hμ hnonatomic q
  constructor
  · intro hae
    by_contra h
    push Not at h
    exact singularRepresentation_measure_ne_zero u hu hn μ hμ
      (nonatomic_measure_zero_of_trigonometric_ae μ hnonatomic q hae h)
  · intro h
    exact Filter.Eventually.of_forall h

end TTO.Paper.Proved
