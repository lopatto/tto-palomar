/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WideHankelNecessityFoundations

/-! Actual finite Schatten synthesis from low-pass bases and thin positive bands. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem polynomialHankel_prefix_factorization (r c D : ℕ) (P : Polynomial ℂ)
    (hD : P.natDegree<D) :
    polynomialHankelRectangleOffset r c 0 P=
      prefixExtension (min r D) (min c D) r c (min_le_left _ _) (min_le_left _ _)
        (polynomialHankelRectangleOffset (min r D) (min c D) 0 P) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [prefixExtension_single_apply,polynomialHankelRectangleOffset_single_apply]
  by_cases hi : i.val<min r D
  · rw [dite_eq_left hi]
    by_cases hj : j.val<min c D
    · rw [dite_eq_left hj,polynomialHankelRectangleOffset_single_apply]
    · rw [dite_eq_right hj]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hD.trans_le (by omega))
  · rw [dite_eq_right hi]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hD.trans_le (by omega))

theorem polynomialHankel_schatten_rpow_le_circle (r c D : ℕ) (P : Polynomial ℂ)
    (hD : P.natDegree<D) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c 0 P)^p≤
      2^(1-p)*(D : ℝ)*(∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  let rr := min r D
  let cc := min c D
  have hD0 : 0<D := by omega
  have hDr : 0<(D : ℝ) := by exact_mod_cast hD0
  let : NeZero (2*D) := ⟨by omega⟩
  have hNorm : schattenNorm p (polynomialHankelRectangleOffset r c 0 P)≤
      schattenNorm p (polynomialHankelRectangleOffset rr cc 0 P) := by
    rw [polynomialHankel_prefix_factorization r c D P hD]
    exact schattenNorm_prefixExtension_le rr cc r c (min_le_left _ _) (min_le_left _ _) _ p hp
  have hShape : 0+rr+cc≤2*D := by
    have hr := min_le_right r D
    have hc := min_le_right c D
    omega
  have hUpper := polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral
    (2*D) rr cc 0 hShape P (by omega) p hp hp1
  have hrr : (rr : ℝ)≤(D : ℝ) := by exact_mod_cast min_le_right r D
  have hcc : (cc : ℝ)≤(D : ℝ) := by exact_mod_cast min_le_right c D
  have hRoots := mul_le_mul (Real.sqrt_le_sqrt hrr) (Real.sqrt_le_sqrt hcc)
    (Real.sqrt_nonneg (cc : ℝ)) (Real.sqrt_nonneg (D : ℝ))
  rw [Real.mul_self_sqrt hDr.le] at hRoots
  have hRootPow := Real.rpow_le_rpow
    (mul_nonneg (Real.sqrt_nonneg (rr : ℝ)) (Real.sqrt_nonneg (cc : ℝ))) hRoots hp.le
  have hMean : 0≤(∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) p)
  have hPow : ((2*D : ℕ) : ℝ)^(1-p)*(D : ℝ)^p=2^(1-p)*(D : ℝ) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hDr.le]
    rw [mul_assoc,← Real.rpow_add hDr,sub_add_cancel,Real.rpow_one]
  calc
    _ ≤ schattenNorm p (polynomialHankelRectangleOffset rr cc 0 P)^p :=
      Real.rpow_le_rpow (schattenNorm_nonneg p _) hNorm hp.le
    _ ≤ ((2*D : ℕ) : ℝ)^(1-p)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
          (Real.sqrt (rr : ℝ)*Real.sqrt (cc : ℝ))^p := hUpper
    _ ≤ ((2*D : ℕ) : ℝ)^(1-p)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*(D : ℝ)^p :=
      mul_le_mul_of_nonneg_left hRootPow (mul_nonneg (by positivity) hMean)
    _ = _ := by
      calc
        _ = (((2*D : ℕ) : ℝ)^(1-p)*(D : ℝ)^p)*
            (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by ring
        _ = _ := by rw [hPow]

theorem thinWideBand_schatten_rpow_le (m N N' r c : ℕ) (hN : 10≤N)
    (hNN' : N≤N') (hRatio : 5*N'≤6*N) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c 0 (thinWideBandPolynomial m N N' P))^p≤
      (125*((m : ℝ)+1)*2^(1-p))*(N : ℝ)*
        (∫ τ : Boundary,‖(thinWideBandPolynomial m N N' P).eval
          (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  have hDegree : (thinWideBandPolynomial m N N' P).natDegree≤thinWideBandEnd m N' := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact thinWideBandPolynomial_coeff_high m N N' hNN' P k hk
  have hEnd : thinWideBandEnd m N'<125*(m+1)*N := by
    have h := Nat.mul_le_mul_left (101*m+2) hRatio
    dsimp only [thinWideBandEnd]
    nlinarith
  have h := polynomialHankel_schatten_rpow_le_circle r c (125*(m+1)*N)
    (thinWideBandPolynomial m N N' P) (hDegree.trans_lt hEnd) p hp hp1
  apply h.trans_eq
  push_cast
  ring

theorem polynomialHankelRectangleOffset_add (r c s : ℕ) (P Q : Polynomial ℂ) :
    polynomialHankelRectangleOffset r c s (P+Q)=
      polynomialHankelRectangleOffset r c s P+polynomialHankelRectangleOffset r c s Q := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [add_apply,PiLp.add_apply,polynomialHankelRectangleOffset_single_apply,
    Polynomial.coeff_add]

theorem polynomialHankelRectangleOffset_sum {ι : Type*} (t : Finset ι) (P : ι → Polynomial ℂ)
    (r c s : ℕ) :
    polynomialHankelRectangleOffset r c s (∑ i∈t,P i)=
      ∑ i∈t,polynomialHankelRectangleOffset r c s (P i) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,
    polynomialHankelRectangleOffset_single_apply,Polynomial.finsetSum_coeff]

theorem wideHankelPolynomial_natDegree_le (m N : ℕ) (g : BoundaryL2) :
    (wideHankelPolynomial m N g).natDegree≤wideDirichletProductShift m N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [wideHankelPolynomial_coeff,wideDirichletPositiveWeight,
    wideDirichletProductPolynomial_coeff_zero m N k hk,zero_mul]

theorem wideHankelBand_schatten_rpow_le (m N N' r c : ℕ) (hN : 10≤N)
    (hNN' : N≤N') (hRatio : 5*N'≤6*N) (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c 0
      (wideHankelPolynomial m N' g-wideHankelPolynomial m N g))^p≤
      (125*((m : ℝ)+1)*2^(1-p))*(N : ℝ)*
        (∫ τ : Boundary,‖(wideHankelPolynomial m N' g-wideHankelPolynomial m N g).eval
          (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  have hShift : wideDirichletProductShift m N≤wideDirichletProductShift m N' := by
    simp only [wideDirichletProductShift_eq]
    exact Nat.mul_le_mul_left _ hNN'
  have hDegree : (wideHankelPolynomial m N' g-wideHankelPolynomial m N g).natDegree≤
      wideDirichletProductShift m N' :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (wideHankelPolynomial_natDegree_le m N' g)
      ((wideHankelPolynomial_natDegree_le m N g).trans hShift))
  have hEnd : wideDirichletProductShift m N'<125*(m+1)*N := by
    have h := Nat.mul_le_mul_left (101*m+2) hRatio
    rw [wideDirichletProductShift_eq]
    nlinarith
  have h := polynomialHankel_schatten_rpow_le_circle r c (125*(m+1)*N)
    (wideHankelPolynomial m N' g-wideHankelPolynomial m N g) (hDegree.trans_lt hEnd) p hp hp1
  apply h.trans_eq
  push_cast
  ring

theorem integral_finiteHardyPolynomial_rpow_le (D : ℕ) (a : ℕ → ℂ)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    (∫ τ : Boundary,‖(finiteHardyPolynomial D a).eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)≤
      ∑ k∈Finset.range D,‖a k‖^p := by
  have hPoint (τ : Boundary) :
      ‖(finiteHardyPolynomial D a).eval (fourier (T:=1) 1 τ)‖^p≤
        ∑ k∈Finset.range D,‖a k‖^p := by
    rw [eval_finiteHardyPolynomial]
    have h := complex_norm_finset_sum_rpow_le (Finset.range D)
      (fun k => a k*(fourier (T:=1) 1 τ)^k) p hp hp1
    simpa only [norm_mul,norm_pow,show ‖fourier (T:=1) 1 τ‖=1 by simp,one_pow,mul_one] using h
  have hI : Integrable (fun τ : Boundary =>
      ‖(finiteHardyPolynomial D a).eval (fourier (T:=1) 1 τ)‖^p) circleMeasure := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply (Real.continuous_rpow_const hp.le).comp
    fun_prop
  simpa using (integral_mono hI
    (integrable_const (∑ k∈Finset.range D,‖a k‖^p)) hPoint)

def wideHankelBaseBudget (m : ℕ) (g : BoundaryL2) (p : ℝ) : ℝ :=
  2^(1-p)*((wideDirichletProductShift m 10+1 : ℕ) : ℝ)*
    ∑ k∈Finset.range (wideDirichletProductShift m 10+1),
      ‖wideDirichletPositiveWeight m 10 k*fourierCoeff g (k : ℤ)‖^p

theorem wideHankelBaseBudget_nonneg (m : ℕ) (g : BoundaryL2) (p : ℝ) :
    0≤wideHankelBaseBudget m g p := by
  dsimp only [wideHankelBaseBudget]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg _) p)

theorem wideHankelBase_schatten_rpow_le (m r c : ℕ) (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c 0 (wideHankelPolynomial m 10 g))^p≤
      wideHankelBaseBudget m g p := by
  have h := polynomialHankel_schatten_rpow_le_circle r c (wideDirichletProductShift m 10+1)
    (wideHankelPolynomial m 10 g) (Nat.lt_succ_of_le (wideHankelPolynomial_natDegree_le m 10 g)) p hp hp1
  apply h.trans
  exact mul_le_mul_of_nonneg_left
    (integral_finiteHardyPolynomial_rpow_le (wideDirichletProductShift m 10+1)
      (fun k => wideDirichletPositiveWeight m 10 k*fourierCoeff g (k : ℤ)) p hp hp1)
    (by positivity)

def wideHankelBandMass (m j : ℕ) (g : BoundaryL2) (p : ℝ) : ℝ :=
  (thinWideScale j : ℝ)*(∫ τ : Boundary,
    ‖(wideHankelPolynomial m (thinWideScale (j+1)) g-
      wideHankelPolynomial m (thinWideScale j) g).eval
        (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)

theorem wideHankelBandMass_nonneg (m j : ℕ) (g : BoundaryL2) (p : ℝ) :
    0≤wideHankelBandMass m j g p :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg
    (fun _ => Real.rpow_nonneg (norm_nonneg _) p))

theorem wideHankelPolynomial_telescope (m : ℕ) (g : BoundaryL2) (J : ℕ) :
    wideHankelPolynomial m 10 g+
      (∑ j∈Finset.range J,(wideHankelPolynomial m (thinWideScale (j+1)) g-
        wideHankelPolynomial m (thinWideScale j) g))=
          wideHankelPolynomial m (thinWideScale J) g := by
  induction J with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,add_zero,thinWideScale_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih]
    abel

theorem wideHankelPolynomial_schatten_rpow_le_partial_budget (m J r c : ℕ)
    (g : BoundaryL2) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset r c 0
      (wideHankelPolynomial m (thinWideScale J) g))^p≤wideHankelBaseBudget m g p+
        (125*((m : ℝ)+1)*2^(1-p))*(∑ j∈Finset.range J,wideHankelBandMass m j g p) := by
  let C : ℝ := 125*((m : ℝ)+1)*2^(1-p)
  have hEach (j : ℕ) :
      schattenNorm p (polynomialHankelRectangleOffset r c 0
        (wideHankelPolynomial m (thinWideScale (j+1)) g-
          wideHankelPolynomial m (thinWideScale j) g))^p≤C*wideHankelBandMass m j g p := by
    simpa only [C,wideHankelBandMass,mul_assoc] using
      wideHankelBand_schatten_rpow_le m _ _ r c (thinWideScale_ten_le j)
        (thinWideScale_monotone (Nat.le_succ j)) (thinWideScale_ratio j) g p hp hp1
  have hBands :
      (∑ j∈Finset.range J,schattenNorm p (polynomialHankelRectangleOffset r c 0
        (wideHankelPolynomial m (thinWideScale (j+1)) g-
          wideHankelPolynomial m (thinWideScale j) g))^p)≤
            C*(∑ j∈Finset.range J,wideHankelBandMass m j g p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hEach j)
  have hEq : polynomialHankelRectangleOffset r c 0 (wideHankelPolynomial m (thinWideScale J) g)=
      polynomialHankelRectangleOffset r c 0 (wideHankelPolynomial m 10 g)+
        ∑ j∈Finset.range J,polynomialHankelRectangleOffset r c 0
          (wideHankelPolynomial m (thinWideScale (j+1)) g-
            wideHankelPolynomial m (thinWideScale j) g) := by
    rw [← wideHankelPolynomial_telescope m g J,polynomialHankelRectangleOffset_add,
      polynomialHankelRectangleOffset_sum]
  rw [hEq]
  apply (finite_schattenNorm_add_rpow_le _ _ p hp hp1).trans
  apply (add_le_add (wideHankelBase_schatten_rpow_le m r c g p hp hp1)
    (finite_schattenNorm_sum_rpow_le (Finset.range J) _ p hp hp1)).trans
  exact add_le_add le_rfl hBands

theorem wideHankelPolynomial_corner_eq (m K J : ℕ) (g : BoundaryL2) (hJ : 2*K≤J) :
    polynomialHankelRectangleOffset K K 0 (wideHankelPolynomial m (thinWideScale J) g)=
      finiteHankelCoefficientMatrix K (fun k => fourierCoeff g (k : ℤ)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin K) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [polynomialHankelRectangleOffset_single_apply,wideHankelPolynomial_coeff,
    finiteHankelCoefficientMatrix_entry]
  simp only [zero_add]
  have hIndex : i.val+j.val≤(99*m+2)*thinWideScale J := by
    have hScale := thinWideScale_lower J
    nlinarith [i.is_lt,j.is_lt]
  rw [wideDirichletPositiveWeight,
    wideDirichletProductPolynomial_coeff_plateau m (thinWideScale J) (i.val+j.val) hIndex,one_mul]

theorem exists_schattenHankel_of_wide_band_budget (m : ℕ) (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (B : ℝ) (hB : 0≤B)
    (hBudget : ∀ J : ℕ,(∑ j∈Finset.range J,wideHankelBandMass m j g p)≤B) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H^p≤wideHankelBaseBudget m g p+
        (125*((m : ℝ)+1)*2^(1-p))*B := by
  let C : ℝ := 125*((m : ℝ)+1)*2^(1-p)
  let R : ℝ := wideHankelBaseBudget m g p+C*B
  have hC : 0≤C := by dsimp only [C]; positivity
  have hR : 0≤R := add_nonneg (wideHankelBaseBudget_nonneg m g p) (mul_nonneg hC hB)
  have hPower (K : ℕ) : schattenNorm p (finiteHankelCoefficientMatrix K
      (fun k => fourierCoeff g (k : ℤ)))^p≤R := by
    rw [← wideHankelPolynomial_corner_eq m K (2*K) g le_rfl]
    apply (wideHankelPolynomial_schatten_rpow_le_partial_budget m (2*K) K K g p hp hp1).trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hBudget (2*K)) hC)
  have hNorm (K : ℕ) : schattenNorm p (finiteHankelCoefficientMatrix K
      (fun k => fourierCoeff g (k : ℤ)))≤R^(1/p) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (schattenNorm_nonneg p _) p)
      (hPower K) (one_div_pos.mpr hp).le
    rw [← Real.rpow_mul (schattenNorm_nonneg p _),mul_one_div_cancel hp.ne',Real.rpow_one] at h
    exact h
  obtain ⟨H,hH,hS,hNormH⟩ := exists_schattenHankel_of_coefficient_corners g p (R^(1/p)) hp hNorm
  refine ⟨H,hH,hS,?_⟩
  have h := Real.rpow_le_rpow (schattenNorm_nonneg p H) hNormH hp.le
  rw [← Real.rpow_mul hR,one_div_mul_cancel hp.ne',Real.rpow_one] at h
  exact h

end TTO.Paper.Proved
