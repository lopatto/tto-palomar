/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.RectangularHankelFoundations

/-! Polynomial Fourier masks on actual finite Hilbert matrices. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Exact inverse finite Fourier coefficient formula, with the normalization and sign explicit. -/
theorem polynomial_coeff_cyclic_inverse (N : ℕ) [NeZero N] (P : Polynomial ℂ)
    (hP : P.natDegree<N) (n : ℕ) (hn : n<N) :
    P.coeff n=∑ j : ZMod N,(N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))*
      (fourier (T:=1) 1 (-ZMod.toAddCircle j))^n := by
  classical
  let q : ℂ := ((Real.sqrt (N : ℝ))⁻¹ : ℂ)
  have hq : q*q=(N : ℂ)⁻¹ := by
    have hr : ((Real.sqrt (N : ℝ))⁻¹)^2=(N : ℝ)⁻¹ := by
      rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
    dsimp [q]
    simp only [pow_two] at hr
    simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast] using
      congrArg (fun x : ℝ => (x : ℂ)) hr
  have h0 (j : ZMod N) : (finiteFourierBasis N j) (0 : ZMod N)=q := by
    simp [finiteFourierBasis_apply,finiteFourierVector,finiteCyclicCharacter_apply,q]
  have hN (j : ZMod N) :
      (finiteFourierBasis N (-j)) (n : ZMod N)=q*(fourier (T:=1) 1 (-ZMod.toAddCircle j))^n := by
    rw [finiteFourierBasis_apply]
    change q*finiteCyclicCharacter N (-j) (n : ZMod N)=_
    rw [finiteCyclicCharacter_natCast]
    simp only [map_neg]
  let C := cyclicHankelOperator N (fun t : ZMod N => P.coeff t.val)
  have hCol : inner ℂ (EuclideanSpace.single (n : ZMod N) (1 : ℂ))
      (C (EuclideanSpace.single (0 : ZMod N) (1 : ℂ)))=P.coeff n := by
    simp only [EuclideanSpace.inner_single_left,map_one,one_mul,C,cyclicHankelOperator_apply,
      PiLp.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      add_zero,ZMod.val_natCast_of_lt hn]
  calc
    _ = inner ℂ (EuclideanSpace.single (n : ZMod N) (1 : ℂ))
        (C (EuclideanSpace.single (0 : ZMod N) (1 : ℂ))) := hCol.symm
    _ = ∑ j : ZMod N,inner ℂ (EuclideanSpace.single (n : ZMod N) (1 : ℂ))
        ((cyclicFourierWeight N (fun t : ZMod N => P.coeff t.val) j •
          InnerProductSpace.rankOne ℂ (finiteFourierBasis N (-j)) (finiteFourierBasis N j))
            (EuclideanSpace.single (0 : ZMod N) (1 : ℂ))) := by
      dsimp only [C]
      rw [cyclicHankelOperator_eq_sum_rankOne,sum_apply,inner_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [smul_apply,InnerProductSpace.rankOne_apply,inner_smul_right,
        EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,map_one,one_mul,h0,hN]
      rw [cyclicFourierWeight_polynomial N P hP j]
      have hc : conj q=q := by simp [q]
      rw [hc]
      calc
        _ = (q*q)*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))*
            (fourier (T:=1) 1 (-ZMod.toAddCircle j))^n := by ring
        _ = _ := by rw [hq]

/-- Scalar multiplication preserves the actual positive Schatten power gauge exactly. -/
theorem schattenNorm_smul_rpow {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (A : E →L[ℂ] F) (c : ℂ)
    (p : ℝ) (hp : 0<p) :
    schattenNorm p (c • A)^p=‖c‖^p*schattenNorm p A^p := by
  simp only [schattenNorm_rpow hp,approximationNumber_smul,NNReal.coe_mul,coe_nnnorm]
  have hMul (n : ℕ) :
      (‖c‖*(approximationNumber A n : ℝ))^p=‖c‖^p*(approximationNumber A n : ℝ)^p :=
    Real.mul_rpow (norm_nonneg c) (NNReal.coe_nonneg (approximationNumber A n))
  simp_rw [hMul]
  exact tsum_mul_left

/-- Actual coefficientwise Hankel masking, with no assumed matrix identity. -/
def polynomialHankelSchur (r c : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i : Fin r => fun j : Fin c =>
    P.coeff (i.val+j.val)*A (EuclideanSpace.single j (1 : ℂ)) i)).toContinuousLinearMap


/-- Literal unitary coordinate phases on the two sides of a rectangular map. -/
def polynomialPhaseSandwich (r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (τ : Boundary) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (polynomialPhaseEquiv r τ).toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
    (polynomialPhaseEquiv c τ).toContinuousLinearEquiv.toContinuousLinearMap

theorem polynomialPhaseSandwich_single_apply (r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (τ : Boundary) (i : Fin r) (j : Fin c) :
    polynomialPhaseSandwich r c A τ (EuclideanSpace.single j (1 : ℂ)) i=
      (fourier (T:=1) 1 τ)^(i.val+j.val)*A (EuclideanSpace.single j (1 : ℂ)) i := by
  simp only [polynomialPhaseSandwich,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,polynomialPhaseEquiv_single,map_smul,
    polynomialPhaseEquiv_apply,PiLp.smul_apply,smul_eq_mul,pow_add]
  ring

theorem approximationNumber_polynomialPhaseSandwich (r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (τ : Boundary) (n : ℕ) :
    approximationNumber (polynomialPhaseSandwich r c A τ) n=approximationNumber A n := by
  let U := polynomialPhaseEquiv r τ
  let V := polynomialPhaseEquiv c τ
  have hU := norm_isometry_clm_le_one U.toLinearIsometry
  have hV := norm_isometry_clm_le_one V.toLinearIsometry
  have hUi := norm_isometry_clm_le_one U.symm.toLinearIsometry
  have hVi := norm_isometry_clm_le_one V.symm.toLinearIsometry
  apply le_antisymm (approximationNumber_comp_contractions _ A _ hU hV n)
  have hInverse : U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      polynomialPhaseSandwich r c A τ ∘L V.symm.toContinuousLinearEquiv.toContinuousLinearMap=A := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [polynomialPhaseSandwich,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    change U.symm (U (A (V (V.symm x))))=_
    rw [V.apply_symm_apply,U.symm_apply_apply]
  have hBack := approximationNumber_comp_contractions
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap (polynomialPhaseSandwich r c A τ)
    V.symm.toContinuousLinearEquiv.toContinuousLinearMap hUi hVi n
  rw [hInverse] at hBack
  exact hBack

theorem schattenNorm_polynomialPhaseSandwich (r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (τ : Boundary) (p : ℝ) :
    schattenNorm p (polynomialPhaseSandwich r c A τ)=schattenNorm p A := by
  simp only [schattenNorm,approximationNumber_polynomialPhaseSandwich]

theorem polynomialHankelSchur_single_apply (r c : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i : Fin r) (j : Fin c) :
    polynomialHankelSchur r c P A (EuclideanSpace.single j (1 : ℂ)) i=
      P.coeff (i.val+j.val)*A (EuclideanSpace.single j (1 : ℂ)) i := by
  change (∑ k : Fin c,(P.coeff (i.val+k.val)*A (EuclideanSpace.single k (1 : ℂ)) i)*
    Pi.single (M:=fun _ : Fin c => ℂ) j (1 : ℂ) k)=_
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The actual Schur mask is an explicitly normalized sum of unitary phase sandwiches. -/
theorem polynomialHankelSchur_eq_sum_phase (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchur r c P A=
      ∑ k : ZMod N,((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle k))) •
        polynomialPhaseSandwich r c A (-ZMod.toAddCircle k) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  have he : inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (polynomialHankelSchur r c P A (EuclideanSpace.single j (1 : ℂ)))=
      inner ℂ (EuclideanSpace.single i (1 : ℂ))
        ((∑ k : ZMod N,((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle k))) •
          polynomialPhaseSandwich r c A (-ZMod.toAddCircle k))
            (EuclideanSpace.single j (1 : ℂ))) := by
    rw [EuclideanSpace.inner_single_left,map_one,one_mul,polynomialHankelSchur_single_apply,
      polynomial_coeff_cyclic_inverse N P hP (i.val+j.val) (by omega)]
    rw [Finset.sum_mul]
    simp only [sum_apply,inner_sum,smul_apply,inner_smul_right,
      EuclideanSpace.inner_single_left,map_one,one_mul,polynomialPhaseSandwich_single_apply]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using he

/-- Dimension-independent low-p Schur estimate at the actual cyclic samples. -/
theorem polynomialHankelSchur_schattenNorm_rpow_le_samples (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelSchur r c P A)^p≤
      ((N : ℝ)⁻¹)^p*(∑ j : ZMod N,‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p)*
        schattenNorm p A^p := by
  rw [polynomialHankelSchur_eq_sum_phase N r c hsize P hP A]
  calc
    _ ≤ ∑ j : ZMod N,schattenNorm p
        (((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))) •
          polynomialPhaseSandwich r c A (-ZMod.toAddCircle j))^p :=
      finite_schattenNorm_sum_rpow_le Finset.univ _ p hp hp1
    _ = ∑ j : ZMod N,((N : ℝ)⁻¹)^p*
        ‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p*schattenNorm p A^p := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [schattenNorm_smul_rpow,schattenNorm_polynomialPhaseSandwich,norm_mul,norm_inv,
        Complex.norm_natCast,Real.mul_rpow (inv_nonneg.mpr (Nat.cast_nonneg N)) (norm_nonneg _)]
      exact hp
    _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]


/-- Shifted coefficient masking also represents genuine trigonometric cutoffs: P=z^s Q. -/
def polynomialHankelSchurOffset (r c s : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i : Fin r => fun j : Fin c =>
    P.coeff (s+i.val+j.val)*A (EuclideanSpace.single j (1 : ℂ)) i)).toContinuousLinearMap

theorem polynomialHankelSchurOffset_zero (r c : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchurOffset r c 0 P A=polynomialHankelSchur r c P A := by
  simp only [polynomialHankelSchurOffset,zero_add,polynomialHankelSchur]

theorem polynomialHankelSchurOffset_single_apply (r c s : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i : Fin r) (j : Fin c) :
    polynomialHankelSchurOffset r c s P A (EuclideanSpace.single j (1 : ℂ)) i=
      P.coeff (s+i.val+j.val)*A (EuclideanSpace.single j (1 : ℂ)) i := by
  change (∑ k : Fin c,(P.coeff (s+i.val+k.val)*A (EuclideanSpace.single k (1 : ℂ)) i)*
    Pi.single (M:=fun _ : Fin c => ℂ) j (1 : ℂ) k)=_
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Shifted masks retain all polynomial samples, with the exact unimodular shift factor. -/
theorem polynomialHankelSchurOffset_eq_sum_phase (N r c s : ℕ) [NeZero N]
    (hsize : s+r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchurOffset r c s P A=
      ∑ k : ZMod N,((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle k))*
        (fourier (T:=1) 1 (-ZMod.toAddCircle k))^s) •
          polynomialPhaseSandwich r c A (-ZMod.toAddCircle k) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  have he : inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (polynomialHankelSchurOffset r c s P A (EuclideanSpace.single j (1 : ℂ)))=
      inner ℂ (EuclideanSpace.single i (1 : ℂ))
        ((∑ k : ZMod N,((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle k))*
          (fourier (T:=1) 1 (-ZMod.toAddCircle k))^s) •
            polynomialPhaseSandwich r c A (-ZMod.toAddCircle k))
              (EuclideanSpace.single j (1 : ℂ))) := by
    rw [EuclideanSpace.inner_single_left,map_one,one_mul,polynomialHankelSchurOffset_single_apply,
      polynomial_coeff_cyclic_inverse N P hP (s+i.val+j.val) (by omega)]
    rw [Finset.sum_mul]
    simp only [sum_apply,inner_sum,smul_apply,inner_smul_right,EuclideanSpace.inner_single_left,
      map_one,one_mul,polynomialPhaseSandwich_single_apply,pow_add]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using he

theorem polynomialHankelSchurOffset_schattenNorm_rpow_le_samples (N r c s : ℕ) [NeZero N]
    (hsize : s+r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelSchurOffset r c s P A)^p≤
      ((N : ℝ)⁻¹)^p*(∑ j : ZMod N,‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p)*
        schattenNorm p A^p := by
  rw [polynomialHankelSchurOffset_eq_sum_phase N r c s hsize P hP A]
  calc
    _ ≤ ∑ j : ZMod N,schattenNorm p
        (((N : ℂ)⁻¹*P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))*
          (fourier (T:=1) 1 (-ZMod.toAddCircle j))^s) •
            polynomialPhaseSandwich r c A (-ZMod.toAddCircle j))^p :=
      finite_schattenNorm_sum_rpow_le Finset.univ _ p hp hp1
    _ = ∑ j : ZMod N,((N : ℝ)⁻¹)^p*
        ‖P.eval (fourier (T:=1) 1 (ZMod.toAddCircle j))‖^p*schattenNorm p A^p := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [schattenNorm_smul_rpow _ _ p hp,schattenNorm_polynomialPhaseSandwich]
      simp only [norm_mul,norm_inv,norm_pow,fourier_apply,Circle.norm_coe,one_pow,mul_one,
        Complex.norm_natCast]
      rw [Real.mul_rpow (inv_nonneg.mpr (Nat.cast_nonneg N)) (norm_nonneg _)]
    _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]


/-- Rotating a shifted mask contributes its exact scalar phase as well as the two coordinate phases. -/
theorem polynomialHankelSchurOffset_rotation (r c s : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (τ : Boundary) :
    polynomialHankelSchurOffset r c s (polynomialCircleRotate P τ) A=
      (fourier (T:=1) 1 τ)^s •
        polynomialPhaseSandwich r c (polynomialHankelSchurOffset r c s P A) τ := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [smul_apply,PiLp.smul_apply,polynomialHankelSchurOffset_single_apply,
    polynomialPhaseSandwich_single_apply,polynomialCircleRotate_coeff,smul_eq_mul,pow_add]
  ring

theorem schattenNorm_polynomialHankelSchurOffset_rotate_rpow (r c s : ℕ) (P : Polynomial ℂ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (τ : Boundary) (p : ℝ) (hp : 0<p) :
    schattenNorm p (polynomialHankelSchurOffset r c s (polynomialCircleRotate P τ) A)^p=
      schattenNorm p (polynomialHankelSchurOffset r c s P A)^p := by
  rw [polynomialHankelSchurOffset_rotation,schattenNorm_smul_rpow _ _ p hp,
    schattenNorm_polynomialPhaseSandwich]
  have hUnit : ‖(fourier (T:=1) 1 τ)^s‖=1 := by
    rw [norm_pow,fourier_apply,Circle.norm_coe,one_pow]
  rw [hUnit,Real.one_rpow,one_mul]

theorem nat_mul_inv_rpow (N : ℕ) [NeZero N] (p : ℝ) :
    (N : ℝ)*((N : ℝ)⁻¹)^p=(N : ℝ)^(1-p) := by
  have hN : 0<(N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [Real.rpow_sub hN,Real.rpow_one,Real.inv_rpow hN.le]
  rfl

/-- Genuine trigonometric/shifted polynomial Schur estimate, with its exact scale N^(1-p). -/
theorem polynomialHankelSchurOffset_schattenNorm_rpow_le_integral (N r c s : ℕ) [NeZero N]
    (hsize : s+r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelSchurOffset r c s P A)^p≤
      (N : ℝ)^(1-p)*(∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
        schattenNorm p A^p := by
  let F : Boundary → ℝ := fun τ => ‖P.eval (fourier (T:=1) 1 τ)‖^p
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
      schattenNorm p (polynomialHankelSchurOffset r c s P A)^p≤
        ((N : ℝ)⁻¹)^p*(∑ j : ZMod N,F (τ+ZMod.toAddCircle j))*schattenNorm p A^p := by
    have hDeg : (polynomialCircleRotate P τ).natDegree<N :=
      (polynomialCircleRotate_natDegree_le P τ).trans_lt hP
    have he := polynomialHankelSchurOffset_schattenNorm_rpow_le_samples N r c s hsize
      (polynomialCircleRotate P τ) hDeg A p hp hp1
    rw [schattenNorm_polynomialHankelSchurOffset_rotate_rpow r c s P A τ p hp] at he
    simpa only [polynomialCircleRotate_eval,F] using he
  calc
    _ = ∫ _τ : Boundary,schattenNorm p (polynomialHankelSchurOffset r c s P A)^p ∂circleMeasure := by simp
    _ ≤ ∫ τ : Boundary,((N : ℝ)⁻¹)^p*(∑ j : ZMod N,F (τ+ZMod.toAddCircle j))*
        schattenNorm p A^p ∂circleMeasure :=
      integral_mono (integrable_const _) ((hSumI.const_mul _).mul_const _) hPoint
    _ = ((N : ℝ)⁻¹)^p*(∑ j : ZMod N,∫ τ : Boundary,F (τ+ZMod.toAddCircle j) ∂circleMeasure)*
        schattenNorm p A^p := by
      rw [integral_mul_const,integral_const_mul,
        integral_finsetSum Finset.univ (fun j _hj => hShift j)]
    _ = ((N : ℝ)*((N : ℝ)⁻¹)^p)*
        (∫ τ : Boundary,F τ ∂circleMeasure)*schattenNorm p A^p := by
      simp_rw [integral_add_right_eq_self (μ:=circleMeasure) F]
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      ring
    _ = _ := by rw [nat_mul_inv_rpow]

/-- The unshifted Hankel Schur estimate is the s=0 specialization of the same full statement. -/
theorem polynomialHankelSchur_schattenNorm_rpow_le_integral (N r c : ℕ) [NeZero N]
    (hsize : r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelSchur r c P A)^p≤
      (N : ℝ)^(1-p)*(∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
        schattenNorm p A^p := by
  simpa only [zero_add,polynomialHankelSchurOffset_zero] using
    polynomialHankelSchurOffset_schattenNorm_rpow_le_integral N r c 0
      (by simpa only [zero_add] using hsize) P hP A p hp hp1


/-- The actual constant-one coordinate vector, including the zero-dimensional case. -/
def euclideanOnes (r : ℕ) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun _ : Fin r => (1 : ℂ))

theorem euclideanOnes_norm (r : ℕ) : ‖euclideanOnes r‖=Real.sqrt (r : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  simp [euclideanOnes]

/-- Actual shifted rectangular Hankel coefficients, independent of any sampling modulus. -/
def polynomialHankelRectangleOffset (r c s : ℕ) (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (Matrix.toEuclideanLin (fun i : Fin r => fun j : Fin c =>
    P.coeff (s+i.val+j.val))).toContinuousLinearMap

theorem polynomialHankelRectangleOffset_single_apply (r c s : ℕ) (P : Polynomial ℂ)
    (i : Fin r) (j : Fin c) :
    polynomialHankelRectangleOffset r c s P (EuclideanSpace.single j (1 : ℂ)) i=
      P.coeff (s+i.val+j.val) := by
  change (∑ k : Fin c,P.coeff (s+i.val+k.val)*
    Pi.single (M:=fun _ : Fin c => ℂ) j (1 : ℂ) k)=_
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem polynomialHankelRectangleOffset_eq_mask (r c s : ℕ) (P : Polynomial ℂ) :
    polynomialHankelRectangleOffset r c s P=
      polynomialHankelSchurOffset r c s P
        (InnerProductSpace.rankOne ℂ (euclideanOnes r) (euclideanOnes c)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [polynomialHankelRectangleOffset_single_apply,polynomialHankelSchurOffset_single_apply]
  simp only [InnerProductSpace.rankOne_apply,EuclideanSpace.inner_single_right,euclideanOnes,
    map_one,mul_one,PiLp.smul_apply,smul_eq_mul]

/-- The full shifted rectangular estimate; no analytic projection of a trigonometric symbol occurs. -/
theorem polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral (N r c s : ℕ)
    [NeZero N] (hsize : s+r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c s P)^p≤
      (N : ℝ)^(1-p)*(∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
        (Real.sqrt (r : ℝ)*Real.sqrt (c : ℝ))^p := by
  have he := polynomialHankelSchurOffset_schattenNorm_rpow_le_integral N r c s hsize P hP
    (InnerProductSpace.rankOne ℂ (euclideanOnes r) (euclideanOnes c)) p hp hp1
  rw [← polynomialHankelRectangleOffset_eq_mask] at he
  rw [schattenNorm_rpow_of_rank_le_one _ (rank_nativeRankOne_le _ _) p hp,
    InnerProductSpace.norm_rankOne,euclideanOnes_norm,euclideanOnes_norm] at he
  exact he


/-- The full circle trigonometric symbol: negative modulation is retained literally. -/
def shiftedPolynomialSymbol (P : Polynomial ℂ) (s : ℕ) (τ : Boundary) : ℂ :=
  (fourier (T:=1) 1 (-τ))^s*P.eval (fourier (T:=1) 1 τ)

theorem shiftedPolynomialSymbol_norm (P : Polynomial ℂ) (s : ℕ) (τ : Boundary) :
    ‖shiftedPolynomialSymbol P s τ‖=‖P.eval (fourier (T:=1) 1 τ)‖ := by
  simp only [shiftedPolynomialSymbol,norm_mul,norm_pow,fourier_apply,Circle.norm_coe,one_pow,one_mul]

/-- The negative modulation and the shifted matrix coefficient agree at the actual Fourier samples. -/
theorem polynomial_coeff_cyclic_inverse_shifted (N : ℕ) [NeZero N]
    (P : Polynomial ℂ) (hP : P.natDegree<N) (s n : ℕ) (hn : s+n<N) :
    P.coeff (s+n)=∑ j : ZMod N,(N : ℂ)⁻¹*shiftedPolynomialSymbol P s (ZMod.toAddCircle j)*
      (fourier (T:=1) 1 (-ZMod.toAddCircle j))^n := by
  rw [polynomial_coeff_cyclic_inverse N P hP (s+n) hn]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [pow_add]
  dsimp only [shiftedPolynomialSymbol]
  ring

/-- The complete low-p multiplier estimate measured in the genuine trigonometric symbol. -/
theorem polynomialHankelSchurOffset_schattenNorm_rpow_le_symbol_integral
    (N r c s : ℕ) [NeZero N] (hsize : s+r+c≤N) (P : Polynomial ℂ) (hP : P.natDegree<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelSchurOffset r c s P A)^p≤
      (N : ℝ)^(1-p)*(∫ τ : Boundary,‖shiftedPolynomialSymbol P s τ‖^p ∂circleMeasure)*
        schattenNorm p A^p := by
  simpa only [shiftedPolynomialSymbol_norm] using
    polynomialHankelSchurOffset_schattenNorm_rpow_le_integral N r c s hsize P hP A p hp hp1

end TTO.Paper.Proved
