/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialInnerOuterFoundations
public import TTO.HardyL1SymbolFoundations
public import TTO.HardyPolynomialApproximationFoundations
public import TTO.HankelSymbolDualityFoundations

/-! Actual Hankel core tests and the polynomial H¹ pairing bound.
The norm estimate is proved from actual polynomial factors, not assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The shifted conjugate of a Hardy vector is strictly negative, including constants. -/
def negativeHardyTest (r : Hardy) : ↥hardy.orthogonal :=
  ⟨star (multiply coordinate r.val),by
    apply (mem_hardy_orthogonal_iff _).mpr
    intro n
    rw [fourierCoeff_star_L2]
    change conj (fourierCoeff (multiply (mode 1) r.val) (-(n : ℤ)))=0
    rw [fourierCoeff_mode_multiply,(mem_hardy_iff r.val).mp r.property _ (by omega),map_zero]⟩

theorem norm_negativeHardyTest (r : Hardy) : ‖negativeHardyTest r‖=‖r‖ := by
  change ‖star (multiply coordinate r.val)‖=‖r‖
  rw [boundary_norm_star]
  exact (innerMultiplyIsometry coordinate coordinate_isInner).norm_map r.val

theorem bounded_negativeHardyTest (r : Hardy) (hr : IsBounded r.val) :
    IsBounded (negativeHardyTest r).val :=
  (bounded_multiply coordinate r.val hr).star.ae_eq (Lp.coeFn_star _).symm

/-- Both coordinate factors cancel in the actual bounded-core form. -/
theorem hankel_product_coreForm (g : BoundaryL2) (q : BoundaryLInf) (r : BoundaryL2) :
    coreForm (star (multiply coordinate g)) (toL2 q) (star (multiply coordinate r)) =
      inner ℂ g (multiply q r) := by
  rw [coreForm,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (multiply coordinate g),Lp.coeFn_star (multiply coordinate r),
    multiply_ae coordinate g,multiply_ae coordinate r,multiply_ae q r,toL2_ae q,
    coordinate_unimodular] with t hsg hsr hzg hzr hqr hq hc
  change (star (multiply coordinate g)) t=star ((multiply coordinate g) t) at hsg
  change (star (multiply coordinate r)) t=star ((multiply coordinate r) t) at hsr
  rw [hsg,hsr,hzg,hzr,hqr,hq]
  simp only [RCLike.inner_apply,Complex.star_def,map_mul,Complex.conj_conj]
  have hcc : conj (coordinate t)*coordinate t=1 := by simp [Complex.conj_mul',hc]
  calc
    _ = (conj (coordinate t)*coordinate t)*(conj (g t)*q t*r t) := by ring
    _ = _ := by rw [hcc,one_mul]; ring

theorem hankel_hardy_factor_pair_bound (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (q r : BoundaryLInf) (hq : toL2 q∈hardy) (hr : toL2 r∈hardy) :
    ‖inner ℂ g (multiply q (toL2 r))‖≤‖H‖*(‖toL2 q‖*‖toL2 r‖) := by
  have hRep := hH ⟨toL2 q,hq⟩ (negativeHardyTest ⟨toL2 r,hr⟩)
    (bounded_toL2 q) (bounded_negativeHardyTest _ (bounded_toL2 r))
  change inner ℂ (negativeHardyTest ⟨toL2 r,hr⟩) (H ⟨toL2 q,hq⟩) =
    coreForm (star (multiply coordinate g)) (toL2 q) (star (multiply coordinate (toL2 r))) at hRep
  rw [hankel_product_coreForm] at hRep
  rw [← hRep]
  calc
    _ ≤ ‖negativeHardyTest ⟨toL2 r,hr⟩‖*‖H ⟨toL2 q,hq⟩‖ := norm_inner_le_norm _ _
    _ = ‖toL2 r‖*‖H ⟨toL2 q,hq⟩‖ := by rw [norm_negativeHardyTest]; rfl
    _ ≤ ‖toL2 r‖*(‖H‖*‖toL2 q‖) := mul_le_mul_of_nonneg_left
      (H.le_opNorm ⟨toL2 q,hq⟩) (norm_nonneg _)
    _ = _ := by ring

/-- The actual polynomial H¹ estimate needed by the bounded-symbol lift. -/
theorem hankel_polynomial_pair_bound (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) (p : Polynomial ℂ) :
    ‖inner ℂ g (polynomialBoundary p).val‖≤
      ‖H‖*(∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure) := by
  obtain ⟨q,r,hq,hr,hProd,hNorm⟩ := polynomialH1Factorization p
  have h := hankel_hardy_factor_pair_bound g H hH q r hq hr
  rw [← toL2_multiplyInf,hProd,toL2_analyticPolynomialBoundary,hNorm] at h
  exact h

/-- Actual finite-basis estimates, with no factorization or norm bound left as a proof input. -/
theorem hankel_finite_hardy_l1_bound (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) (N : ℕ) (c : ℕ → ℂ) :
    ‖inner ℂ g (∑ n∈Finset.range N,c n • hardyBasis n).val‖ ≤
      ‖H‖*‖nativeL2toL1 (∑ n∈Finset.range N,c n • hardyBasis n).val‖ := by
  obtain ⟨p,hp⟩ := exists_polynomialBoundary_finite_hardy_sum N c
  rw [← hp,nativeL1_norm_polynomialBoundary]
  exact hankel_polynomial_pair_bound g H hH p

/-- The norm-controlled bounded-symbol theorem is proved, rather than assumed. -/
theorem nehari_bounded_symbol (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    ∃ a : BoundaryLInf,‖a‖≤‖H‖ ∧ SameHankel (star (multiply coordinate g)) (toL2 a) :=
  exists_sameHankel_bounded_symbol_of_finite_hardy_l1_bound g ‖H‖ (norm_nonneg H)
    (hankel_finite_hardy_l1_bound g H hH)

/-- The shifted conjugate symbol transformation is an actual L² involution. -/
theorem hankel_symbol_flip_involutive (σ : BoundaryL2) :
    star (multiply coordinate (star (multiply coordinate σ)))=σ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (multiply coordinate (star (multiply coordinate σ))),
    multiply_ae coordinate (star (multiply coordinate σ)),Lp.coeFn_star (multiply coordinate σ),
    multiply_ae coordinate σ,coordinate_unimodular] with t hso hmo hsi hmi hc
  change (star (multiply coordinate (star (multiply coordinate σ)))) t=
    star ((multiply coordinate (star (multiply coordinate σ))) t) at hso
  change (star (multiply coordinate σ)) t=star ((multiply coordinate σ) t) at hsi
  rw [hso,hmo,hsi,hmi]
  simp only [Complex.star_def,map_mul,Complex.conj_conj]
  have hcc : conj (coordinate t)*coordinate t=1 := by simp [Complex.conj_mul',hc]
  rw [← mul_assoc,hcc,one_mul]

/-- Every represented bounded Hankel operator has an actual L∞ symbol with the sharp bound. -/
theorem nehari_bounded_symbol_for_symbol (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) :
    ∃ a : BoundaryLInf,‖a‖≤‖H‖ ∧ SameHankel σ (toL2 a) := by
  have h := nehari_bounded_symbol (star (multiply coordinate σ)) H
    (by simpa only [hankel_symbol_flip_involutive] using hH)
  simpa only [hankel_symbol_flip_involutive] using h

end TTO.Paper.Proved
