/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FiniteCyclicFourierFoundations

/-! Actual finite polynomial Hankel corners and all-positive-p sampling bounds. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The natural coefficient-index equivalence, with explicit values. -/
def cyclicIndexEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i.val : ZMod N)
  invFun j := ⟨j.val,ZMod.val_lt j⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  right_inv j := ZMod.natCast_zmod_val j

theorem finiteCyclicCharacter_natCast (N : ℕ) [NeZero N] (j : ZMod N) (n : ℕ) :
    finiteCyclicCharacter N j (n : ZMod N)=
      (fourier (T:=1) 1 (ZMod.toAddCircle j))^n := by
  have he := AddChar.map_nsmul_eq_pow (finiteCyclicCharacter N j) n (1 : ZMod N)
  simpa only [nsmul_eq_mul,mul_one,finiteCyclicCharacter_apply] using he

/-- The cyclic spectral weights are the literal polynomial values at equally spaced nodes. -/
theorem cyclicFourierWeight_polynomial (N : ℕ) [NeZero N] (P : Polynomial ℂ)
    (hP : P.natDegree<N) (j : ZMod N) :
    cyclicFourierWeight N (fun t : ZMod N => P.coeff t.val) j=
      P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j)) := by
  rw [cyclicFourierWeight,Polynomial.eval_eq_sum_range' hP]
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (cyclicIndexEquiv N)
  intro i
  simp only [cyclicIndexEquiv,Equiv.coe_fn_mk,ZMod.val_natCast_of_lt i.isLt,finiteCyclicCharacter_natCast]

/-- Actual inclusion of the first m coordinates into the 2m cyclic coordinate set. -/
def firstCyclicEmbedding (m : ℕ) [NeZero m] : Fin m ↪ ZMod (2*m) where
  toFun i := (i.val : ZMod (2*m))
  inj' := by
    intro i j hij
    have hi : i.val<2*m := by omega
    have hj : j.val<2*m := by omega
    apply Fin.ext
    have he := congrArg (fun z : ZMod (2*m) => z.val) hij
    simpa only [ZMod.val_natCast_of_lt hi,ZMod.val_natCast_of_lt hj] using he

/-- Native finite-Hilbert coordinate inclusion, with zero outside the first m coordinates. -/
def firstCyclicInclusion (m : ℕ) [NeZero m] :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod (2*m)) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (firstCyclicEmbedding m)

/-- Actual finite polynomial Hankel corner as a compression of the cyclic matrix. -/
def polynomialHankelCompression (m : ℕ) [NeZero m] (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (firstCyclicInclusion m).toContinuousLinearMap.adjoint ∘L
    cyclicHankelOperator (2*m) (fun t : ZMod (2*m) => P.coeff t.val) ∘L
      (firstCyclicInclusion m).toContinuousLinearMap

/-- Every actual matrix coefficient is P_(i+j), with no cyclic wrap in this corner. -/
theorem polynomialHankelCompression_entry (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (i j : Fin m) :
    inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (polynomialHankelCompression m P (EuclideanSpace.single j (1 : ℂ)))=
        P.coeff (i.val+j.val) := by
  simp only [polynomialHankelCompression,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,LinearIsometry.coe_toContinuousLinearMap]
  rw [show (firstCyclicInclusion m) (EuclideanSpace.single i (1 : ℂ))=
      EuclideanSpace.single ((i.val : ℕ) : ZMod (2*m)) (1 : ℂ) by
        exact LinearIsometry.piLpExtendByZero_apply_single (p:=2) (𝕜:=ℂ) (E:=ℂ) (firstCyclicEmbedding m) i 1]
  rw [show (firstCyclicInclusion m) (EuclideanSpace.single j (1 : ℂ))=
      EuclideanSpace.single ((j.val : ℕ) : ZMod (2*m)) (1 : ℂ) by
        exact LinearIsometry.piLpExtendByZero_apply_single (p:=2) (𝕜:=ℂ) (E:=ℂ) (firstCyclicEmbedding m) j 1]
  simp only [EuclideanSpace.inner_single_left,map_one,one_mul,cyclicHankelOperator_apply,
    PiLp.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Nat.cast_add,ZMod.val_natCast_of_lt (by omega : i.val+j.val<2*m)]

theorem approximationNumber_polynomialHankelCompression_le (m : ℕ) [NeZero m]
    (P : Polynomial ℂ) (n : ℕ) :
    approximationNumber (polynomialHankelCompression m P) n≤
      approximationNumber (cyclicHankelOperator (2*m) (fun t : ZMod (2*m) => P.coeff t.val)) n := by
  have hJ := norm_isometry_clm_le_one (firstCyclicInclusion m)
  exact approximationNumber_comp_contractions _ _ _
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le hJ) hJ n

/-- A genuine all-p finite polynomial Hankel estimate, including p below one. -/
theorem polynomialHankelCompression_power_sum_le (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (hP : P.natDegree<2*m) (p : ℝ) (hp : 0<p) :
    (∑' n : ℕ,(approximationNumber (polynomialHankelCompression m P) n : ℝ)^p)≤
      ∑ j : ZMod (2*m),‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p := by
  let a : ZMod (2*m) → ℂ := fun t => P.coeff t.val
  have hw : summableValues p (cyclicFourierWeight (2*m) a) := by
    unfold summableValues
    exact (hasSum_fintype _).summable
  have hD := (indexedDiagonal_schatten_iff (cyclicFourierWeight (2*m) a)
    (cyclicFourierDiagonal (2*m) a) (cyclicFourierDiagonal_diagonal (2*m) a) p hp).mpr hw
  have hC : Summable (fun n : ℕ =>
      (approximationNumber (cyclicHankelOperator (2*m) a) n : ℝ)^p) := by
    simpa only [approximationNumber_cyclicFourierDiagonal] using hD.2.2
  have hPoint (n : ℕ) : (approximationNumber (polynomialHankelCompression m P) n : ℝ)^p≤
      (approximationNumber (cyclicHankelOperator (2*m) a) n : ℝ)^p :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _)
      (by exact_mod_cast approximationNumber_polynomialHankelCompression_le m P n) hp.le
  have hH := hC.of_nonneg_of_le (fun n => Real.rpow_nonneg (NNReal.coe_nonneg _) p) hPoint
  calc
    _ ≤ ∑' n : ℕ,(approximationNumber (cyclicHankelOperator (2*m) a) n : ℝ)^p :=
      Summable.tsum_le_tsum hPoint hH hC
    _ = ∑ j : ZMod (2*m),‖cyclicFourierWeight (2*m) a j‖^p :=
      cyclicHankelOperator_power_sum (2*m) a p hp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [show cyclicFourierWeight (2*m) a j=
        P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j)) from
          cyclicFourierWeight_polynomial (2*m) P hP j]


theorem polynomialHankelCompression_rank_le (m : ℕ) [NeZero m] (P : Polynomial ℂ) :
    (polynomialHankelCompression m P).rank≤(m : Cardinal) := by
  have he := LinearMap.rank_le_domain (polynomialHankelCompression m P).toLinearMap
  simpa only [← Module.finrank_eq_rank,finrank_euclideanSpace,Fintype.card_fin] using he

theorem polynomialHankelCompression_schatten (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (p : ℝ) (hp : 0<p) : Schatten p (polynomialHankelCompression m P) :=
  finiteRankSchatten _ ⟨m,polynomialHankelCompression_rank_le m P⟩ p hp

theorem polynomialHankelCompression_schattenNorm_rpow_le (m : ℕ) [NeZero m]
    (P : Polynomial ℂ) (hP : P.natDegree<2*m) (p : ℝ) (hp : 0<p) :
    schattenNorm p (polynomialHankelCompression m P)^p≤
      ∑ j : ZMod (2*m),‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p := by
  rw [schattenNorm_rpow hp]
  exact polynomialHankelCompression_power_sum_le m P hP p hp


theorem polynomialHankelCompression_single_apply (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (i j : Fin m) :
    polynomialHankelCompression m P (EuclideanSpace.single j (1 : ℂ)) i=
      P.coeff (i.val+j.val) := by
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using
    polynomialHankelCompression_entry m P i j

/-- Actual multiplication by a unit complex scalar, with its genuine inverse. -/
def unitComplexScalarEquiv (z : ℂ) (hz : ‖z‖=1) : ℂ ≃ₗᵢ[ℂ] ℂ := by
  have hz0 : z≠0 := by intro he; simp [he] at hz
  exact LinearIsometryEquiv.ofSurjective (LinearIsometry.toSpanSingleton ℂ ℂ hz)
    (fun y => ⟨y/z,by
      simpa only [LinearIsometry.toSpanSingleton_apply,smul_eq_mul] using div_mul_cancel₀ y hz0⟩)

@[simp] theorem unitComplexScalarEquiv_apply (z : ℂ) (hz : ‖z‖=1) (x : ℂ) :
    unitComplexScalarEquiv z hz x=x*z := by
  rfl

/-- The coordinate phases needed to rotate an actual polynomial Hankel matrix. -/
def polynomialPhaseEquiv (m : ℕ) (τ : Boundary) :
    EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin m =>
    unitComplexScalarEquiv ((fourier (T:=1) 1 τ)^i.val) (by simp [norm_pow]))

theorem polynomialPhaseEquiv_apply (m : ℕ) (τ : Boundary)
    (x : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    polynomialPhaseEquiv m τ x i=(fourier (T:=1) 1 τ)^i.val*x i := by
  simp only [polynomialPhaseEquiv,LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply,unitComplexScalarEquiv_apply]
  ring

theorem polynomialPhaseEquiv_single (m : ℕ) (τ : Boundary) (j : Fin m) :
    polynomialPhaseEquiv m τ (EuclideanSpace.single j (1 : ℂ))=
      (fourier (T:=1) 1 τ)^j.val • EuclideanSpace.single j (1 : ℂ) := by
  ext i
  rw [polynomialPhaseEquiv_apply]
  simp only [PiLp.smul_apply,smul_eq_mul,PiLp.single_apply]
  by_cases hij : i=j
  · subst i; simp
  · simp [hij]

def polynomialCircleRotate (P : Polynomial ℂ) (τ : Boundary) : Polynomial ℂ :=
  P.comp (Polynomial.C (fourier (T:=1) 1 τ)*Polynomial.X)

theorem polynomialCircleRotate_coeff (P : Polynomial ℂ) (τ : Boundary) (n : ℕ) :
    (polynomialCircleRotate P τ).coeff n=P.coeff n*(fourier (T:=1) 1 τ)^n := by
  exact Polynomial.comp_C_mul_X_coeff

theorem polynomialCircleRotate_natDegree_le (P : Polynomial ℂ) (τ : Boundary) :
    (polynomialCircleRotate P τ).natDegree≤P.natDegree := by
  have hQ : (Polynomial.C (fourier (T:=1) 1 τ)*Polynomial.X : Polynomial ℂ).natDegree≤1 := by
    simpa only [Polynomial.natDegree_X] using
      Polynomial.natDegree_C_mul_le (fourier (T:=1) 1 τ) (Polynomial.X : Polynomial ℂ)
  exact (Polynomial.natDegree_comp_le).trans (by simpa only [mul_one] using Nat.mul_le_mul_left P.natDegree hQ)

theorem polynomialHankelCompression_rotation (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (τ : Boundary) :
    polynomialHankelCompression m (polynomialCircleRotate P τ)=
      (polynomialPhaseEquiv m τ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        polynomialHankelCompression m P ∘L
          (polynomialPhaseEquiv m τ).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [polynomialPhaseEquiv_single,map_smul]
  apply PiLp.ext
  intro i
  simp only [polynomialHankelCompression_single_apply,polynomialPhaseEquiv_apply,
    PiLp.smul_apply,smul_eq_mul,polynomialCircleRotate_coeff,pow_add]
  ring

theorem approximationNumber_polynomialCircleRotate (m : ℕ) [NeZero m]
    (P : Polynomial ℂ) (τ : Boundary) (n : ℕ) :
    approximationNumber (polynomialHankelCompression m (polynomialCircleRotate P τ)) n=
      approximationNumber (polynomialHankelCompression m P) n := by
  let U := polynomialPhaseEquiv m τ
  have hU := norm_isometry_clm_le_one U.toLinearIsometry
  have hUi := norm_isometry_clm_le_one U.symm.toLinearIsometry
  have hEq := polynomialHankelCompression_rotation m P τ
  have hForward := approximationNumber_comp_contractions
    U.toContinuousLinearEquiv.toContinuousLinearMap (polynomialHankelCompression m P)
    U.toContinuousLinearEquiv.toContinuousLinearMap hU hU n
  rw [← hEq] at hForward
  refine le_antisymm hForward ?_
  have hInverse : U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      polynomialHankelCompression m (polynomialCircleRotate P τ) ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap=polynomialHankelCompression m P := by
    rw [hEq]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    change U.symm (U (polynomialHankelCompression m P (U (U.symm x))))=_
    rw [U.apply_symm_apply,U.symm_apply_apply]
  have hBack := approximationNumber_comp_contractions
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    (polynomialHankelCompression m (polynomialCircleRotate P τ))
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap hUi hUi n
  rw [hInverse] at hBack
  exact hBack

theorem schattenNorm_polynomialCircleRotate (m : ℕ) [NeZero m] (P : Polynomial ℂ)
    (τ : Boundary) (p : ℝ) :
    schattenNorm p (polynomialHankelCompression m (polynomialCircleRotate P τ))=
      schattenNorm p (polynomialHankelCompression m P) := by
  simp only [schattenNorm,approximationNumber_polynomialCircleRotate]


theorem polynomialCircleRotate_eval (P : Polynomial ℂ) (τ s : Boundary) :
    (polynomialCircleRotate P τ).eval (fourier (T:=1) 1 s)=
      P.eval (fourier (T:=1) 1 (τ+s)) := by
  simp only [polynomialCircleRotate,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,fourier_position_add]

/-- Rotation averaging gives a dimension-uniform Lp polynomial Hankel-corner estimate.
No convexity or p-subadditivity is used, so the statement retains EVERY positive p. -/
theorem polynomialHankelCompression_schattenNorm_rpow_le_integral (m : ℕ) [NeZero m]
    (P : Polynomial ℂ) (hP : P.natDegree<2*m) (p : ℝ) (hp : 0<p) :
    schattenNorm p (polynomialHankelCompression m P)^p≤
      (2*(m : ℝ))*(∫ τ,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  let F : Boundary → ℝ := fun τ => ‖P.eval (fourier (T:=1) 1 τ)‖^p
  have hCont : Continuous F := by
    apply (Real.continuous_rpow_const hp.le).comp
    fun_prop
  have hShift (j : ZMod (2*m)) :
      Integrable (fun τ : Boundary => F (τ+ZMod.toAddCircle j)) circleMeasure :=
    (hCont.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSumI : Integrable
      (fun τ : Boundary => ∑ j : ZMod (2*m),F (τ+ZMod.toAddCircle j)) circleMeasure :=
    integrable_finsetSum Finset.univ (fun j _hj => hShift j)
  have hPoint (τ : Boundary) :
      schattenNorm p (polynomialHankelCompression m P)^p≤
        ∑ j : ZMod (2*m),F (τ+ZMod.toAddCircle j) := by
    have hDeg : (polynomialCircleRotate P τ).natDegree<2*m :=
      (polynomialCircleRotate_natDegree_le P τ).trans_lt hP
    have he := polynomialHankelCompression_schattenNorm_rpow_le m
      (polynomialCircleRotate P τ) hDeg p hp
    rw [schattenNorm_polynomialCircleRotate] at he
    simpa only [polynomialCircleRotate_eval,F] using he
  calc
    _ = ∫ _τ : Boundary,schattenNorm p (polynomialHankelCompression m P)^p ∂circleMeasure := by
      simp
    _ ≤ ∫ τ : Boundary,∑ j : ZMod (2*m),F (τ+ZMod.toAddCircle j) ∂circleMeasure :=
      integral_mono (integrable_const _) hSumI hPoint
    _ = ∑ j : ZMod (2*m),∫ τ : Boundary,F (τ+ZMod.toAddCircle j) ∂circleMeasure :=
      integral_finsetSum Finset.univ (fun j _hj => hShift j)
    _ = _ := by
      simp_rw [integral_add_right_eq_self (μ:=circleMeasure) F]
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,
        Nat.cast_mul,Nat.cast_ofNat]
      rfl

end TTO.Paper.Proved
