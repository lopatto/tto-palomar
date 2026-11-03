/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ShortBandHankelLowerFoundations
public import TTO.DirichletLocalizationFoundations

/-! Genuine low-p lower estimates for an arbitrary short frequency band, using
exact cyclic reconstruction by two coordinate compressions. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal frequency band translated from [b,b+2L) to [0,2L). -/
def offsetShortBandPolynomial (b L : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (2*L), Polynomial.monomial k (P.coeff (b+k))

theorem offsetShortBandPolynomial_coeff (b L : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    (offsetShortBandPolynomial b L P).coeff k = if k < 2*L then P.coeff (b+k) else 0 := by
  classical
  simp only [offsetShortBandPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range]

theorem offsetShortBandPolynomial_natDegree_lt (b L : ℕ) (hL : 0 < L) (P : Polynomial ℂ) :
    (offsetShortBandPolynomial b L P).natDegree < 2*L := by
  have h := (Polynomial.natDegree_le_iff_coeff_eq_zero (p := offsetShortBandPolynomial b L P)
    (n := 2*L - 1)).mpr (fun k hk => by
      rw [offsetShortBandPolynomial_coeff, ite_eq_right (by omega : ¬ k < 2*L)])
  omega

/-- Source band support implies an actual polynomial factorization, including all zero cases. -/
theorem offsetShortBandPolynomial_factor (b L : ℕ) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) :
    P = Polynomial.X^(b)*offsetShortBandPolynomial b L P := by
  classical
  ext k
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hk : b ≤ k
  · rw [ite_eq_left hk, offsetShortBandPolynomial_coeff]
    by_cases hs : k - b < 2*L
    · rw [ite_eq_left hs, show b+(k - b) = k by omega]
    · rw [ite_eq_right hs, hhi k (by omega)]
  · rw [ite_eq_right hk, hlo k (by omega)]

theorem norm_offsetShortBandPolynomial_eval (b L : ℕ) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖(offsetShortBandPolynomial b L P).eval w‖ = ‖P.eval w‖ := by
  conv_rhs => rw [offsetShortBandPolynomial_factor b L P hlo hhi]
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow,
    hw, one_pow, one_mul]

/-- The cyclic operator is relabeled into the actual consecutive Fin coordinates. -/
def offsetShortBandCyclicFin (b L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (2*L)) →L[ℂ] EuclideanSpace ℂ (Fin (2*L)) :=
  unitaryConjugate (shortBandCyclicEquiv L).symm
    (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (b+t.val)))

theorem approximationNumber_offsetShortBandCyclicFin (b L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) (n : ℕ) :
    approximationNumber (offsetShortBandCyclicFin b L P) n =
      approximationNumber (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (b+t.val))) n := by
  let U := (shortBandCyclicEquiv L).symm
  let A := cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (b+t.val))
  have hU := norm_isometry_clm_le_one U.toLinearIsometry
  have hi := norm_isometry_clm_le_one U.symm.toLinearIsometry
  apply le_antisymm (approximationNumber_comp_contractions _ A _ hU hi n)
  have h := approximationNumber_comp_contractions
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap (unitaryConjugate U A)
    U.toContinuousLinearEquiv.toContinuousLinearMap hi hU n
  rw [unitaryConjugate_reverse] at h
  exact h

theorem schattenNorm_offsetShortBandCyclicFin (b L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) (p : ℝ) :
    schattenNorm p (offsetShortBandCyclicFin b L P) =
      schattenNorm p (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (b+t.val))) := by
  simp only [schattenNorm, approximationNumber_offsetShortBandCyclicFin]

theorem offsetShortBandCyclicFin_single_apply (b L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (i j : Fin (2*L)) :
    offsetShortBandCyclicFin b L P (EuclideanSpace.single j (1 : ℂ)) i =
      P.coeff (b + ((i.val+j.val) % (2*L))) := by
  let U := shortBandCyclicEquiv L
  let A := cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (b+t.val))
  have he := U.inner_map_map (EuclideanSpace.single i (1 : ℂ))
    (U.symm (A (U (EuclideanSpace.single j (1 : ℂ)))))
  rw [U.apply_symm_apply] at he
  dsimp only [U, A] at he
  rw [shortBandCyclicEquiv_single, shortBandCyclicEquiv_single] at he
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul, cyclicHankelOperator_single_apply] at he
  rw [← Nat.cast_add, ZMod.val_natCast] at he
  simpa only [offsetShortBandCyclicFin, unitaryConjugate, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_symm, shortBandCyclicEquiv_single] using! he.symm

/-- The literal cyclic coefficient matrix is the SUM of two actual compressions.
The wrap region and the non-wrap region use the two disjoint coefficient ranges. -/
theorem offsetShortBandCyclicFin_eq_two_compressions (b L : ℕ) (hb : 2*L ≤ b) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) :
    offsetShortBandCyclicFin b L P =
      offsetCoordinateCompression (2*L) (3*L) L (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P) +
      offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (2*L)) ℂ).toBasis.ext
  intro j
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro i
  change offsetShortBandCyclicFin b L P (EuclideanSpace.single j (1 : ℂ)) i =
    offsetCoordinateCompression (2*L) (3*L) L (by omega)
      (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P) (EuclideanSpace.single j (1 : ℂ)) i +
    offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
      (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P) (EuclideanSpace.single j (1 : ℂ)) i
  rw [offsetShortBandCyclicFin_single_apply, offsetCoordinateCompression_single_apply,
    offsetCoordinateCompression_single_apply, polynomialHankelRectangleOffset_single_apply,
    polynomialHankelRectangleOffset_single_apply]
  change P.coeff (b + ((i.val+j.val) % (2*L))) =
    P.coeff (b-2*L+(L+i.val)+(L+j.val)) + P.coeff (b-2*L+(0+i.val)+(0+j.val))
  by_cases hs : i.val+j.val < 2*L
  · rw [Nat.mod_eq_of_lt hs, hlo (b-2*L+(0+i.val)+(0+j.val)) (by omega), add_zero]
    congr 1
    omega
  · have hmod : (i.val+j.val) % (2*L) = i.val+j.val - 2*L := by
      calc
        _ = ((i.val+j.val - 2*L) + 2*L) % (2*L) := by rw [Nat.sub_add_cancel (by omega)]
        _ = (i.val+j.val - 2*L) % (2*L) := Nat.add_mod_right _ _
        _ = _ := Nat.mod_eq_of_lt (by omega)
    rw [hmod, hhi (b-2*L+(L+i.val)+(L+j.val)) (by omega), zero_add]
    congr 1
    omega

/-- Fourier spectral weights of the reconstructed cyclic matrix are actual samples of P. -/
theorem offsetShortBandCyclicFin_schattenNorm_rpow_samples (b L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (offsetShortBandCyclicFin b L P)^p =
      ∑ j : ZMod (2*L), ‖P.eval (fourier (T := 1) 1 (ZMod.toAddCircle j))‖^p := by
  have hL : 0 < L := by have h := NeZero.ne (2*L); omega
  rw [schattenNorm_offsetShortBandCyclicFin, cyclicHankelOperator_schattenNorm_rpow _ _ p hp]
  have hc : (fun t : ZMod (2*L) => P.coeff (b+t.val)) =
      (fun t : ZMod (2*L) => (offsetShortBandPolynomial b L P).coeff t.val) := by
    funext t
    rw [offsetShortBandPolynomial_coeff, ite_eq_left (ZMod.val_lt t)]
  rw [hc]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [cyclicFourierWeight_polynomial (2*L) (offsetShortBandPolynomial b L P)
    (offsetShortBandPolynomial_natDegree_lt b L hL P) j,
    norm_offsetShortBandPolynomial_eval b L P hlo hhi _ (by rw [fourier_apply, Circle.norm_coe])]

/-- Low-p subadditivity is applied only to this proved two-compression sum. -/
theorem offsetShortBand_polynomial_samples_le_rectangle (b L : ℕ) (hb : 2*L ≤ b) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j : ZMod (2*L), ‖P.eval (fourier (T := 1) 1 (ZMod.toAddCircle j))‖^p) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p := by
  rw [← offsetShortBandCyclicFin_schattenNorm_rpow_samples b L P hlo hhi p hp,
    offsetShortBandCyclicFin_eq_two_compressions b L hb P hlo hhi]
  calc
    _ ≤ schattenNorm p (offsetCoordinateCompression (2*L) (3*L) L (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P))^p +
      schattenNorm p (offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P))^p :=
      finite_schattenNorm_add_rpow_le _ _ p hp hp1
    _ ≤ schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p +
      schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p :=
      add_le_add (Real.rpow_le_rpow (schattenNorm_nonneg p _)
        (schattenNorm_offsetCoordinateCompression_le _ _ _ _ _ p hp) hp.le)
        (Real.rpow_le_rpow (schattenNorm_nonneg p _)
          (schattenNorm_offsetCoordinateCompression_le _ _ _ _ _ p hp) hp.le)
    _ = _ := by ring

/-- Genuine short-band Hankel lower estimate throughout 0 < p ≤ 1.
All frequencies outside [b,b+2L) vanish explicitly. No pinching is used. -/
theorem offsetShortBand_polynomial_integral_lower (b L : ℕ) (hb : 2*L ≤ b) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < b → P.coeff k = 0)
    (hhi : ∀ k : ℕ, b+2*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (2*(L : ℝ))*(∫ τ : Boundary, ‖P.eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p := by
  by_cases hL : L = 0
  · subst L
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (schattenNorm_nonneg p _) p)
  have hL0 : 0 < L := Nat.pos_of_ne_zero hL
  let : NeZero (2*L) := ⟨by omega⟩
  let F : Boundary → ℝ := fun τ => ‖P.eval (fourier (T := 1) 1 τ)‖^p
  have hCont : Continuous F := by
    apply (Real.continuous_rpow_const hp.le).comp
    fun_prop
  have hShift (j : ZMod (2*L)) : Integrable (fun τ : Boundary => F (τ + ZMod.toAddCircle j)) circleMeasure :=
    (hCont.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSum : Integrable (fun τ : Boundary => ∑ j : ZMod (2*L), F (τ + ZMod.toAddCircle j)) circleMeasure :=
    integrable_finsetSum Finset.univ (fun j _hj => hShift j)
  have hPoint (τ : Boundary) : (∑ j : ZMod (2*L), F (τ + ZMod.toAddCircle j)) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p := by
    have hl : ∀ k : ℕ, k < b → (polynomialCircleRotate P τ).coeff k = 0 := by
      intro k hk
      rw [polynomialCircleRotate_coeff, hlo k hk, zero_mul]
    have hh : ∀ k : ℕ, b+2*L ≤ k → (polynomialCircleRotate P τ).coeff k = 0 := by
      intro k hk
      rw [polynomialCircleRotate_coeff, hhi k hk, zero_mul]
    have h := offsetShortBand_polynomial_samples_le_rectangle b L hb (polynomialCircleRotate P τ) hl hh p hp hp1
    rw [schattenNorm_polynomialRectangleOffset_rotate_rpow (3*L) (3*L) (b-2*L) P τ p hp] at h
    simpa only [polynomialCircleRotate_eval, F] using h
  calc
    _ = ∫ τ : Boundary, ∑ j : ZMod (2*L), F (τ + ZMod.toAddCircle j) ∂circleMeasure := by
      rw [integral_finsetSum Finset.univ (fun j _hj => hShift j)]
      simp_rw [integral_add_right_eq_self (μ := circleMeasure) F]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      rfl
    _ ≤ ∫ _τ : Boundary, 2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p ∂circleMeasure :=
      integral_mono hSum (integrable_const _) hPoint
    _ = _ := by simp

end TTO.Paper.Proved
