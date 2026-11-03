/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FiniteCyclicFourierFoundations
public import TTO.RectangularHankelFoundations
public import TTO.DirichletLocalizationFoundations

/-! Actual cyclic reconstruction gives a lower bound for a genuine short frequency band.
It is a two-compression identity, not an invalid low-p pinching assertion. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal frequency band translated from [4L,6L) to [0,2L). -/
def shortBandPolynomial (L : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (2*L), Polynomial.monomial k (P.coeff (4*L+k))

theorem shortBandPolynomial_coeff (L : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    (shortBandPolynomial L P).coeff k = if k < 2*L then P.coeff (4*L+k) else 0 := by
  classical
  simp only [shortBandPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range]

theorem shortBandPolynomial_natDegree_lt (L : ℕ) (hL : 0 < L) (P : Polynomial ℂ) :
    (shortBandPolynomial L P).natDegree < 2*L := by
  have h := (Polynomial.natDegree_le_iff_coeff_eq_zero (p := shortBandPolynomial L P)
    (n := 2*L - 1)).mpr (fun k hk => by
      rw [shortBandPolynomial_coeff, ite_eq_right (by omega : ¬ k < 2*L)])
  omega

/-- Source band support implies an actual polynomial factorization, including all zero cases. -/
theorem shortBandPolynomial_factor (L : ℕ) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) :
    P = Polynomial.X^(4*L)*shortBandPolynomial L P := by
  classical
  ext k
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hk : 4*L ≤ k
  · rw [ite_eq_left hk, shortBandPolynomial_coeff]
    by_cases hs : k - 4*L < 2*L
    · rw [ite_eq_left hs, show 4*L+(k - 4*L) = k by omega]
    · rw [ite_eq_right hs, hhi k (by omega)]
  · rw [ite_eq_right hk, hlo k (by omega)]

theorem norm_shortBandPolynomial_eval (L : ℕ) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖(shortBandPolynomial L P).eval w‖ = ‖P.eval w‖ := by
  conv_rhs => rw [shortBandPolynomial_factor L P hlo hhi]
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow,
    hw, one_pow, one_mul]

/-- Native coordinate inclusion of an actual consecutive interval. -/
def offsetCoordinateEmbedding (small large offset : ℕ) (h : offset + small ≤ large) : Fin small ↪ Fin large where
  toFun i := ⟨offset + i.val, by omega⟩
  inj' i j hij := Fin.ext (by have he := congrArg Fin.val hij; dsimp only at he; omega)

def offsetCoordinateInclusion (small large offset : ℕ) (h : offset + small ≤ large) :
    EuclideanSpace ℂ (Fin small) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin large) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (offsetCoordinateEmbedding small large offset h)

theorem offsetCoordinateInclusion_single (small large offset : ℕ) (h : offset + small ≤ large)
    (i : Fin small) :
    offsetCoordinateInclusion small large offset h (EuclideanSpace.single i (1 : ℂ)) =
      EuclideanSpace.single (offsetCoordinateEmbedding small large offset h i) (1 : ℂ) :=
  LinearIsometry.piLpExtendByZero_apply_single (p := 2) (𝕜 := ℂ) (E := ℂ)
    (offsetCoordinateEmbedding small large offset h) i 1

def shortBandCyclicEquiv (L : ℕ) [NeZero (2*L)] :
    EuclideanSpace ℂ (Fin (2*L)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod (2*L)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cyclicIndexEquiv (2*L))

theorem shortBandCyclicEquiv_single (L : ℕ) [NeZero (2*L)] (i : Fin (2*L)) :
    shortBandCyclicEquiv L (EuclideanSpace.single i (1 : ℂ)) =
      EuclideanSpace.single (i.val : ZMod (2*L)) (1 : ℂ) :=
  EuclideanSpace.piLpCongrLeft_single (cyclicIndexEquiv (2*L)) i 1

/-- Actual compression onto a consecutive coordinate interval. -/
def offsetCoordinateCompression (small large offset : ℕ) (h : offset + small ≤ large)
    (A : EuclideanSpace ℂ (Fin large) →L[ℂ] EuclideanSpace ℂ (Fin large)) :
    EuclideanSpace ℂ (Fin small) →L[ℂ] EuclideanSpace ℂ (Fin small) :=
  (offsetCoordinateInclusion small large offset h).toContinuousLinearMap.adjoint ∘L A ∘L
    (offsetCoordinateInclusion small large offset h).toContinuousLinearMap

theorem offsetCoordinateCompression_single_apply (small large offset : ℕ) (h : offset + small ≤ large)
    (A : EuclideanSpace ℂ (Fin large) →L[ℂ] EuclideanSpace ℂ (Fin large))
    (i j : Fin small) :
    offsetCoordinateCompression small large offset h A (EuclideanSpace.single j (1 : ℂ)) i =
      A (EuclideanSpace.single (offsetCoordinateEmbedding small large offset h j) (1 : ℂ))
        (offsetCoordinateEmbedding small large offset h i) := by
  have he : inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (offsetCoordinateCompression small large offset h A (EuclideanSpace.single j (1 : ℂ))) =
      A (EuclideanSpace.single (offsetCoordinateEmbedding small large offset h j) (1 : ℂ))
        (offsetCoordinateEmbedding small large offset h i) := by
    simp only [offsetCoordinateCompression, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap,
      offsetCoordinateInclusion_single, EuclideanSpace.inner_single_left, map_one, one_mul]
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using he

theorem schattenNorm_offsetCoordinateCompression_le (small large offset : ℕ) (h : offset + small ≤ large)
    (A : EuclideanSpace ℂ (Fin large) →L[ℂ] EuclideanSpace ℂ (Fin large)) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (offsetCoordinateCompression small large offset h A) ≤ schattenNorm p A :=
  euclidean_schattenNorm_comp_contractions_le small small large large A _ _
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le (norm_isometry_clm_le_one _))
    (norm_isometry_clm_le_one _) p hp

/-- The cyclic operator is relabeled into the actual consecutive Fin coordinates. -/
def shortBandCyclicFin (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (2*L)) →L[ℂ] EuclideanSpace ℂ (Fin (2*L)) :=
  unitaryConjugate (shortBandCyclicEquiv L).symm
    (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (4*L+t.val)))

theorem approximationNumber_shortBandCyclicFin (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) (n : ℕ) :
    approximationNumber (shortBandCyclicFin L P) n =
      approximationNumber (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (4*L+t.val))) n := by
  let U := (shortBandCyclicEquiv L).symm
  let A := cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (4*L+t.val))
  have hU := norm_isometry_clm_le_one U.toLinearIsometry
  have hi := norm_isometry_clm_le_one U.symm.toLinearIsometry
  apply le_antisymm (approximationNumber_comp_contractions _ A _ hU hi n)
  have h := approximationNumber_comp_contractions
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap (unitaryConjugate U A)
    U.toContinuousLinearEquiv.toContinuousLinearMap hi hU n
  rw [unitaryConjugate_reverse] at h
  exact h

theorem schattenNorm_shortBandCyclicFin (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ) (p : ℝ) :
    schattenNorm p (shortBandCyclicFin L P) =
      schattenNorm p (cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (4*L+t.val))) := by
  simp only [schattenNorm, approximationNumber_shortBandCyclicFin]

theorem cyclicHankelOperator_single_apply (N : ℕ) [NeZero N] (a : ZMod N → ℂ) (i j : ZMod N) :
    cyclicHankelOperator N a (EuclideanSpace.single j (1 : ℂ)) i = a (i+j) := by
  simp only [cyclicHankelOperator_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem shortBandCyclicFin_single_apply (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (i j : Fin (2*L)) :
    shortBandCyclicFin L P (EuclideanSpace.single j (1 : ℂ)) i =
      P.coeff (4*L + ((i.val+j.val) % (2*L))) := by
  let U := shortBandCyclicEquiv L
  let A := cyclicHankelOperator (2*L) (fun t : ZMod (2*L) => P.coeff (4*L+t.val))
  have he := U.inner_map_map (EuclideanSpace.single i (1 : ℂ))
    (U.symm (A (U (EuclideanSpace.single j (1 : ℂ)))))
  rw [U.apply_symm_apply] at he
  dsimp only [U, A] at he
  rw [shortBandCyclicEquiv_single, shortBandCyclicEquiv_single] at he
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul, cyclicHankelOperator_single_apply] at he
  rw [← Nat.cast_add, ZMod.val_natCast] at he
  simpa only [shortBandCyclicFin, unitaryConjugate, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_symm, shortBandCyclicEquiv_single] using! he.symm

/-- The literal cyclic coefficient matrix is the SUM of two actual compressions.
The wrap region and the non-wrap region use the two disjoint coefficient ranges. -/
theorem shortBandCyclicFin_eq_two_compressions (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) :
    shortBandCyclicFin L P =
      offsetCoordinateCompression (2*L) (3*L) L (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P) +
      offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (2*L)) ℂ).toBasis.ext
  intro j
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro i
  change shortBandCyclicFin L P (EuclideanSpace.single j (1 : ℂ)) i =
    offsetCoordinateCompression (2*L) (3*L) L (by omega)
      (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P) (EuclideanSpace.single j (1 : ℂ)) i +
    offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
      (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P) (EuclideanSpace.single j (1 : ℂ)) i
  rw [shortBandCyclicFin_single_apply, offsetCoordinateCompression_single_apply,
    offsetCoordinateCompression_single_apply, polynomialHankelRectangleOffset_single_apply,
    polynomialHankelRectangleOffset_single_apply]
  change P.coeff (4*L + ((i.val+j.val) % (2*L))) =
    P.coeff (2*L+(L+i.val)+(L+j.val)) + P.coeff (2*L+(0+i.val)+(0+j.val))
  by_cases hs : i.val+j.val < 2*L
  · rw [Nat.mod_eq_of_lt hs, hlo (2*L+(0+i.val)+(0+j.val)) (by omega), add_zero]
    congr 1
    omega
  · have hmod : (i.val+j.val) % (2*L) = i.val+j.val - 2*L := by
      calc
        _ = ((i.val+j.val - 2*L) + 2*L) % (2*L) := by rw [Nat.sub_add_cancel (by omega)]
        _ = (i.val+j.val - 2*L) % (2*L) := Nat.add_mod_right _ _
        _ = _ := Nat.mod_eq_of_lt (by omega)
    rw [hmod, hhi (2*L+(L+i.val)+(L+j.val)) (by omega), zero_add]
    congr 1
    omega

/-- Fourier spectral weights of the reconstructed cyclic matrix are actual samples of P. -/
theorem shortBandCyclicFin_schattenNorm_rpow_samples (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (shortBandCyclicFin L P)^p =
      ∑ j : ZMod (2*L), ‖P.eval (fourier (T := 1) 1 (ZMod.toAddCircle j))‖^p := by
  have hL : 0 < L := by have h := NeZero.ne (2*L); omega
  rw [schattenNorm_shortBandCyclicFin, cyclicHankelOperator_schattenNorm_rpow _ _ p hp]
  have hc : (fun t : ZMod (2*L) => P.coeff (4*L+t.val)) =
      (fun t : ZMod (2*L) => (shortBandPolynomial L P).coeff t.val) := by
    funext t
    rw [shortBandPolynomial_coeff, ite_eq_left (ZMod.val_lt t)]
  rw [hc]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [cyclicFourierWeight_polynomial (2*L) (shortBandPolynomial L P)
    (shortBandPolynomial_natDegree_lt L hL P) j,
    norm_shortBandPolynomial_eval L P hlo hhi _ (by rw [fourier_apply, Circle.norm_coe])]

/-- Low-p subadditivity is applied only to this proved two-compression sum. -/
theorem shortBand_polynomial_samples_le_rectangle (L : ℕ) [NeZero (2*L)] (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j : ZMod (2*L), ‖P.eval (fourier (T := 1) 1 (ZMod.toAddCircle j))‖^p) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p := by
  rw [← shortBandCyclicFin_schattenNorm_rpow_samples L P hlo hhi p hp,
    shortBandCyclicFin_eq_two_compressions L P hlo hhi]
  calc
    _ ≤ schattenNorm p (offsetCoordinateCompression (2*L) (3*L) L (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P))^p +
      schattenNorm p (offsetCoordinateCompression (2*L) (3*L) 0 (by omega)
        (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P))^p :=
      finite_schattenNorm_add_rpow_le _ _ p hp hp1
    _ ≤ schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p +
      schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p :=
      add_le_add (Real.rpow_le_rpow (schattenNorm_nonneg p _)
        (schattenNorm_offsetCoordinateCompression_le _ _ _ _ _ p hp) hp.le)
        (Real.rpow_le_rpow (schattenNorm_nonneg p _)
          (schattenNorm_offsetCoordinateCompression_le _ _ _ _ _ p hp) hp.le)
    _ = _ := by ring

/-- Rotation preserves the actual offset rectangle Schatten power by the proved phase identity. -/
theorem schattenNorm_polynomialRectangleOffset_rotate_rpow (r c s : ℕ) (P : Polynomial ℂ)
    (τ : Boundary) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (polynomialHankelRectangleOffset r c s (polynomialCircleRotate P τ))^p =
      schattenNorm p (polynomialHankelRectangleOffset r c s P)^p := by
  rw [polynomialHankelRectangleOffset_eq_mask, polynomialHankelRectangleOffset_eq_mask]
  exact schattenNorm_polynomialHankelSchurOffset_rotate_rpow r c s P _ τ p hp

/-- Genuine short-band Hankel lower estimate throughout 0 < p ≤ 1.
All frequencies outside [4L,6L) vanish explicitly. No pinching is used. -/
theorem shortBand_polynomial_integral_lower (L : ℕ) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ, k < 4*L → P.coeff k = 0)
    (hhi : ∀ k : ℕ, 6*L ≤ k → P.coeff k = 0) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (2*(L : ℝ))*(∫ τ : Boundary, ‖P.eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p := by
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
      2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p := by
    have hl : ∀ k : ℕ, k < 4*L → (polynomialCircleRotate P τ).coeff k = 0 := by
      intro k hk
      rw [polynomialCircleRotate_coeff, hlo k hk, zero_mul]
    have hh : ∀ k : ℕ, 6*L ≤ k → (polynomialCircleRotate P τ).coeff k = 0 := by
      intro k hk
      rw [polynomialCircleRotate_coeff, hhi k hk, zero_mul]
    have h := shortBand_polynomial_samples_le_rectangle L (polynomialCircleRotate P τ) hl hh p hp hp1
    rw [schattenNorm_polynomialRectangleOffset_rotate_rpow (3*L) (3*L) (2*L) P τ p hp] at h
    simpa only [polynomialCircleRotate_eval, F] using h
  calc
    _ = ∫ τ : Boundary, ∑ j : ZMod (2*L), F (τ + ZMod.toAddCircle j) ∂circleMeasure := by
      rw [integral_finsetSum Finset.univ (fun j _hj => hShift j)]
      simp_rw [integral_add_right_eq_self (μ := circleMeasure) F]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      rfl
    _ ≤ ∫ _τ : Boundary, 2*schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p ∂circleMeasure :=
      integral_mono hSum (integrable_const _) hPoint
    _ = _ := by simp

end TTO.Paper.Proved
