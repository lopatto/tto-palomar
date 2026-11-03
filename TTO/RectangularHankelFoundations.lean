/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CappedSchattenFoundations
public import TTO.PolynomialHankelEstimatesFoundations

/-! Genuine finite Fourier rank-one decompositions and rectangular polynomial Hankel corners. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The zeroth approximation number for a map between possibly different spaces. -/
theorem approximationNumber_index_zero_map {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) : approximationNumber A 0=‖A‖₊ := by
  apply le_antisymm (approximationNumber_le_nnnorm A 0)
  apply le_approximationNumber_iff.mpr
  intro R hR
  have hrank : R.rank=0 := le_antisymm hR zero_le
  have hrange : R.range=⊥ := Submodule.rank_eq_zero.mp hrank
  have hz : R=0 := by
    have he : R.toLinearMap=0 := LinearMap.range_eq_bot.mp hrange
    ext x
    exact congrArg (fun T : E →ₗ[ℂ] F => T x) he
  simp only [hz,sub_zero,le_refl]

/-- Every positive Schatten gauge of a rank-at-most-one map is its operator norm. -/
theorem schattenNorm_rpow_of_rank_le_one {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : E →L[ℂ] F) (hA : A.rank≤(1 : Cardinal)) (p : ℝ) (hp : 0<p) :
    schattenNorm p A^p=‖A‖^p := by
  rw [schattenNorm_rpow hp,tsum_eq_single 0]
  · rw [approximationNumber_index_zero_map,coe_nnnorm]
  · intro n hn
    have hRank : A.rank≤(n : Cardinal) := hA.trans (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have h0 : approximationNumber A n=0 := le_antisymm
      (by simpa only [sub_self,nnnorm_zero] using approximationNumber_le_nnnorm_sub A (n:=n) (R:=A) hRank) bot_le
    rw [h0,NNReal.coe_zero,Real.zero_rpow hp.ne']

/-- Rank-one here has its native literal inner-product meaning, including zero vectors. -/
theorem rank_nativeRankOne_le {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (u : F) (v : E) :
    (InnerProductSpace.rankOne ℂ u v).rank≤(1 : Cardinal) := by
  by_cases hu : u=0
  · simp [hu]
  by_cases hv : v=0
  · simp [hv]
  exact le_of_eq (InnerProductSpace.rank_rankOne hu hv)

/-- Actual cyclic Hankel expansion in the native Fourier orthonormal basis. -/
theorem cyclicHankelOperator_eq_sum_rankOne (N : ℕ) [NeZero N] (a : ZMod N → ℂ) :
    cyclicHankelOperator N a=
      ∑ j : ZMod N,cyclicFourierWeight N a j •
        InnerProductSpace.rankOne ℂ (finiteFourierBasis N (-j)) (finiteFourierBasis N j) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (finiteFourierBasis N).toBasis.ext
  intro j
  change cyclicHankelOperator N a (finiteFourierBasis N j)=
    (∑ k : ZMod N,cyclicFourierWeight N a k •
      InnerProductSpace.rankOne ℂ (finiteFourierBasis N (-k)) (finiteFourierBasis N k))
        (finiteFourierBasis N j)
  simpa only [sum_apply,smul_apply,InnerProductSpace.rankOne_apply,
    (finiteFourierBasis N).inner_eq_ite,ite_smul,one_smul,zero_smul,smul_ite,smul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using cyclicHankelOperator_fourierBasis N a j

/-- Actual inclusion of an initial coordinate block into a cyclic coordinate set. -/
def cyclicCoordinateEmbedding (N r : ℕ) [NeZero N] (hr : r≤N) : Fin r ↪ ZMod N where
  toFun i := (i.val : ZMod N)
  inj' := by
    intro i j hij
    apply Fin.ext
    have he := congrArg (fun z : ZMod N => z.val) hij
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hr),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hr)] using he

def cyclicCoordinateInclusion (N r : ℕ) [NeZero N] (hr : r≤N) :
    EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod N) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (cyclicCoordinateEmbedding N r hr)

/-- The actual initial segment of a normalized Fourier vector. -/
def initialFourierVector (N r : ℕ) [NeZero N] (j : ZMod N) :
    EuclideanSpace ℂ (Fin r) :=
  ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • WithLp.toLp 2 (fun i : Fin r =>
    finiteCyclicCharacter N j (i.val : ZMod N))

theorem initialFourierVector_norm (N r : ℕ) [NeZero N] (j : ZMod N) :
    ‖initialFourierVector N r j‖=Real.sqrt (r : ℝ)/Real.sqrt (N : ℝ) := by
  rw [initialFourierVector,norm_smul]
  have hv : ‖(WithLp.toLp 2 (fun i : Fin r => finiteCyclicCharacter N j (i.val : ZMod N)) :
      EuclideanSpace ℂ (Fin r))‖=Real.sqrt (r : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    simp only [finiteCyclicCharacter_apply,fourier_apply,Circle.norm_coe,
      one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [hv,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem cyclicCoordinateInclusion_adjoint_fourier (N r : ℕ) [NeZero N]
    (hr : r≤N) (j : ZMod N) :
    (cyclicCoordinateInclusion N r hr).toContinuousLinearMap.adjoint (finiteFourierBasis N j)=
      initialFourierVector N r j := by
  ext i
  have he := ContinuousLinearMap.adjoint_inner_right
    (cyclicCoordinateInclusion N r hr).toContinuousLinearMap
    (EuclideanSpace.single i (1 : ℂ)) (finiteFourierBasis N j)
  simp only [LinearIsometry.coe_toContinuousLinearMap] at he
  rw [show (cyclicCoordinateInclusion N r hr) (EuclideanSpace.single i (1 : ℂ))=
      EuclideanSpace.single (i.val : ZMod N) (1 : ℂ) by
        exact LinearIsometry.piLpExtendByZero_apply_single (p:=2) (𝕜:=ℂ) (E:=ℂ)
          (cyclicCoordinateEmbedding N r hr) i 1] at he
  simpa only [EuclideanSpace.inner_single_left,finiteFourierBasis_apply,finiteFourierVector,
    initialFourierVector,PiLp.smul_apply,PiLp.toLp_apply,smul_eq_mul,map_one,one_mul] using he

/-- The native coefficient matrix; it does not depend on a chosen sampling modulus. -/
def polynomialHankelRectangle (r c : ℕ) (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i : Fin r => fun k : Fin c => P.coeff (i.val+k.val))).toContinuousLinearMap


theorem cyclicCoordinateInclusion_single (N r : ℕ) [NeZero N] (hr : r≤N) (i : Fin r) :
    cyclicCoordinateInclusion N r hr (EuclideanSpace.single i (1 : ℂ))=
      EuclideanSpace.single (i.val : ZMod N) (1 : ℂ) :=
  LinearIsometry.piLpExtendByZero_apply_single (p:=2) (𝕜:=ℂ) (E:=ℂ)
    (cyclicCoordinateEmbedding N r hr) i 1

theorem polynomialHankelRectangle_single_apply (r c : ℕ) (P : Polynomial ℂ)
    (i : Fin r) (j : Fin c) :
    polynomialHankelRectangle r c P (EuclideanSpace.single j (1 : ℂ)) i=P.coeff (i.val+j.val) := by
  change (∑ k : Fin c,P.coeff (i.val+k.val)*Pi.single (M:=fun _ : Fin c => ℂ) j (1 : ℂ) k)=_
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The actual rectangular coefficient matrix is a cyclic compression with no wrap. -/
theorem polynomialHankelRectangle_eq_compression (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) :
    polynomialHankelRectangle r c P=
      (cyclicCoordinateInclusion N r (by omega)).toContinuousLinearMap.adjoint ∘L
        cyclicHankelOperator N (fun t : ZMod N => P.coeff t.val) ∘L
          (cyclicCoordinateInclusion N c (by omega)).toContinuousLinearMap := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  change polynomialHankelRectangle r c P ((EuclideanSpace.basisFun (Fin c) ℂ) j)=_
  rw [EuclideanSpace.basisFun_apply]
  ext i
  have he : inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (((cyclicCoordinateInclusion N r (by omega)).toContinuousLinearMap.adjoint ∘L
        cyclicHankelOperator N (fun t : ZMod N => P.coeff t.val) ∘L
          (cyclicCoordinateInclusion N c (by omega)).toContinuousLinearMap)
            (EuclideanSpace.single j (1 : ℂ)))=P.coeff (i.val+j.val) := by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
      LinearIsometry.coe_toContinuousLinearMap,cyclicCoordinateInclusion_single]
    simp only [EuclideanSpace.inner_single_left,map_one,one_mul,cyclicHankelOperator_apply,
      PiLp.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [← Nat.cast_add,ZMod.val_natCast_of_lt (by omega : i.val+j.val<N)]
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul,
    polynomialHankelRectangle_single_apply,ContinuousLinearMap.coe_coe,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply] using he.symm

/-- Literal polynomial samples and the two truncated Fourier vectors give its rank-one sum. -/
theorem polynomialHankelRectangle_eq_sum_rankOne (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N) :
    polynomialHankelRectangle r c P=
      ∑ j : ZMod N,P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j)) •
        InnerProductSpace.rankOne ℂ (initialFourierVector N r (-j)) (initialFourierVector N c j) := by
  rw [polynomialHankelRectangle_eq_compression N r c hsize P]
  apply ContinuousLinearMap.ext
  intro x
  change (cyclicCoordinateInclusion N r (by omega)).toContinuousLinearMap.adjoint
    (cyclicHankelOperator N (fun t : ZMod N => P.coeff t.val)
      ((cyclicCoordinateInclusion N c (by omega)).toContinuousLinearMap x))=_
  rw [cyclicHankelOperator_eq_sum_rankOne]
  simp only [sum_apply,smul_apply,InnerProductSpace.rankOne_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← ContinuousLinearMap.adjoint_inner_left,
    cyclicCoordinateInclusion_adjoint_fourier,cyclicCoordinateInclusion_adjoint_fourier,
    cyclicFourierWeight_polynomial N P hP j]


/-- The rank-one Fourier sum yields the geometric row/column gain in the low-p range. -/
theorem polynomialHankelRectangle_schattenNorm_rpow_le_samples (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangle r c P)^p≤
      ((Real.sqrt (r : ℝ)/Real.sqrt (N : ℝ))*
        (Real.sqrt (c : ℝ)/Real.sqrt (N : ℝ)))^p*
          ∑ j : ZMod N,‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p := by
  let C : ℝ := (Real.sqrt (r : ℝ)/Real.sqrt (N : ℝ))*
    (Real.sqrt (c : ℝ)/Real.sqrt (N : ℝ))
  have hC : 0≤C := by dsimp [C]; positivity
  rw [polynomialHankelRectangle_eq_sum_rankOne N r c hsize P hP]
  calc
    _ ≤ ∑ j : ZMod N,schattenNorm p
        (P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j)) •
          InnerProductSpace.rankOne ℂ (initialFourierVector N r (-j)) (initialFourierVector N c j))^p :=
      finite_schattenNorm_sum_rpow_le Finset.univ _ p hp hp1
    _ = ∑ j : ZMod N,(‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖*C)^p := by
      apply Finset.sum_congr rfl
      intro j _hj
      let w := P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))
      have he : w • InnerProductSpace.rankOne ℂ (initialFourierVector N r (-j))
          (initialFourierVector N c j)=
          InnerProductSpace.rankOne ℂ (w • initialFourierVector N r (-j)) (initialFourierVector N c j) := by
        ext y
        simp only [smul_apply,InnerProductSpace.rankOne_apply,smul_smul]
        rw [mul_comm]
      change schattenNorm p (w • InnerProductSpace.rankOne ℂ
        (initialFourierVector N r (-j)) (initialFourierVector N c j))^p=(‖w‖*C)^p
      rw [he,schattenNorm_rpow_of_rank_le_one _ (rank_nativeRankOne_le _ _) p hp,
        InnerProductSpace.norm_rankOne,norm_smul,initialFourierVector_norm,initialFourierVector_norm]
      congr 1
      dsimp [C]
      ring
    _ = C^p*∑ j : ZMod N,‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Real.mul_rpow (norm_nonneg _) hC,mul_comm]


/-- Rotation changes the actual rectangular matrix by unitary phases on both sides. -/
theorem polynomialHankelRectangle_rotation (r c : ℕ) (P : Polynomial ℂ) (τ : Boundary) :
    polynomialHankelRectangle r c (polynomialCircleRotate P τ)=
      (polynomialPhaseEquiv r τ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        polynomialHankelRectangle r c P ∘L
          (polynomialPhaseEquiv c τ).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [polynomialPhaseEquiv_single,map_smul]
  apply PiLp.ext
  intro i
  simp only [polynomialHankelRectangle_single_apply,polynomialPhaseEquiv_apply,
    PiLp.smul_apply,smul_eq_mul,polynomialCircleRotate_coeff,pow_add]
  ring

theorem approximationNumber_polynomialHankelRectangle_rotate (r c : ℕ)
    (P : Polynomial ℂ) (τ : Boundary) (n : ℕ) :
    approximationNumber (polynomialHankelRectangle r c (polynomialCircleRotate P τ)) n=
      approximationNumber (polynomialHankelRectangle r c P) n := by
  let U := polynomialPhaseEquiv r τ
  let V := polynomialPhaseEquiv c τ
  have hU := norm_isometry_clm_le_one U.toLinearIsometry
  have hV := norm_isometry_clm_le_one V.toLinearIsometry
  have hUi := norm_isometry_clm_le_one U.symm.toLinearIsometry
  have hVi := norm_isometry_clm_le_one V.symm.toLinearIsometry
  have hEq := polynomialHankelRectangle_rotation r c P τ
  have hForward := approximationNumber_comp_contractions
    U.toContinuousLinearEquiv.toContinuousLinearMap (polynomialHankelRectangle r c P)
    V.toContinuousLinearEquiv.toContinuousLinearMap hU hV n
  rw [← hEq] at hForward
  refine le_antisymm hForward ?_
  have hInverse : U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      polynomialHankelRectangle r c (polynomialCircleRotate P τ) ∘L
        V.symm.toContinuousLinearEquiv.toContinuousLinearMap=polynomialHankelRectangle r c P := by
    rw [hEq]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    change U.symm (U (polynomialHankelRectangle r c P (V (V.symm x))))=_
    rw [V.apply_symm_apply,U.symm_apply_apply]
  have hBack := approximationNumber_comp_contractions
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    (polynomialHankelRectangle r c (polynomialCircleRotate P τ))
    V.symm.toContinuousLinearEquiv.toContinuousLinearMap hUi hVi n
  rw [hInverse] at hBack
  exact hBack

theorem schattenNorm_polynomialHankelRectangle_rotate (r c : ℕ)
    (P : Polynomial ℂ) (τ : Boundary) (p : ℝ) :
    schattenNorm p (polynomialHankelRectangle r c (polynomialCircleRotate P τ))=
      schattenNorm p (polynomialHankelRectangle r c P) := by
  simp only [schattenNorm,approximationNumber_polynomialHankelRectangle_rotate]

theorem initialFourier_norm_product (N r c : ℕ) :
    (Real.sqrt (r : ℝ)/Real.sqrt (N : ℝ))*(Real.sqrt (c : ℝ)/Real.sqrt (N : ℝ))=
      (Real.sqrt (r : ℝ)*Real.sqrt (c : ℝ))/(N : ℝ) := by
  rw [div_mul_div_comm,← pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Haar averaging preserves the geometric rectangular gain for every 0<p≤1. -/
theorem polynomialHankelRectangle_schattenNorm_rpow_le_integral (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangle r c P)^p≤
      (N : ℝ)*((Real.sqrt (r : ℝ)*Real.sqrt (c : ℝ))/(N : ℝ))^p*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  let F : Boundary → ℝ := fun τ => ‖P.eval (fourier (T:=1) 1 τ)‖^p
  let C : ℝ := (Real.sqrt (r : ℝ)*Real.sqrt (c : ℝ))/(N : ℝ)
  have hCont : Continuous F := by
    apply (Real.continuous_rpow_const hp.le).comp
    fun_prop
  have hShift (j : ZMod N) :
      Integrable (fun τ : Boundary => F (τ+ZMod.toAddCircle j)) circleMeasure :=
    (hCont.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSumI : Integrable
      (fun τ : Boundary => ∑ j : ZMod N,F (τ+ZMod.toAddCircle j)) circleMeasure :=
    integrable_finsetSum Finset.univ (fun j _hj => hShift j)
  have hPoint (τ : Boundary) :
      schattenNorm p (polynomialHankelRectangle r c P)^p≤
        C^p*∑ j : ZMod N,F (τ+ZMod.toAddCircle j) := by
    have hDeg : (polynomialCircleRotate P τ).natDegree<N :=
      (polynomialCircleRotate_natDegree_le P τ).trans_lt hP
    have he := polynomialHankelRectangle_schattenNorm_rpow_le_samples N r c hsize
      (polynomialCircleRotate P τ) hDeg p hp hp1
    rw [schattenNorm_polynomialHankelRectangle_rotate,initialFourier_norm_product] at he
    simpa only [polynomialCircleRotate_eval,F,C] using he
  calc
    _ = ∫ _τ : Boundary,schattenNorm p (polynomialHankelRectangle r c P)^p ∂circleMeasure := by simp
    _ ≤ ∫ τ : Boundary,C^p*∑ j : ZMod N,F (τ+ZMod.toAddCircle j) ∂circleMeasure :=
      integral_mono (integrable_const _) (hSumI.const_mul _) hPoint
    _ = C^p*∑ j : ZMod N,∫ τ : Boundary,F (τ+ZMod.toAddCircle j) ∂circleMeasure := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _hj => hShift j)]
    _ = _ := by
      simp_rw [integral_add_right_eq_self (μ:=circleMeasure) F]
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      dsimp [C,F]
      ring

end TTO.Paper.Proved
