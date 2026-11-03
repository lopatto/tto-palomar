/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ShortBandHankelLowerFoundations

/-! Literal diagonal contractions and radial bounds for finite short-band Hankel matrices. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

def finiteCoordinateMultiplier (N : ℕ) (c : Fin N→ℂ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Matrix.toEuclideanLin (Matrix.diagonal c)).toContinuousLinearMap

theorem finiteCoordinateMultiplier_apply (N : ℕ) (c : Fin N→ℂ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    finiteCoordinateMultiplier N c x i=c i*x i := by
  change (∑ j : Fin N,(if i=j then c i else 0)*x j)=_
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem norm_finiteCoordinateMultiplier_le (N : ℕ) (c : Fin N→ℂ)
    (C : ℝ) (hC : 0≤C) (hc : ∀ i,‖c i‖≤C) :
    ‖finiteCoordinateMultiplier N c‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hs : ‖finiteCoordinateMultiplier N c x‖^2≤C^2*‖x‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [finiteCoordinateMultiplier_apply,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg (c i)) hC).2 (hc i)) (sq_nonneg _)
  nlinarith [norm_nonneg (finiteCoordinateMultiplier N c x),
    mul_nonneg hC (norm_nonneg x)]

def polynomialRadialScale (P : Polynomial ℂ) (r : ℝ) : Polynomial ℂ :=
  P.comp (Polynomial.C (r : ℂ)*Polynomial.X)

theorem polynomialRadialScale_coeff (P : Polynomial ℂ) (r : ℝ) (n : ℕ) :
    (polynomialRadialScale P r).coeff n=P.coeff n*(r : ℂ)^n :=
  Polynomial.comp_C_mul_X_coeff

theorem polynomialRadialScale_eval (P : Polynomial ℂ) (r : ℝ) (z : ℂ) :
    (polynomialRadialScale P r).eval z=P.eval ((r : ℂ)*z) := by
  simp only [polynomialRadialScale,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]

def finiteRadialMultiplier (N : ℕ) (r : ℝ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  finiteCoordinateMultiplier N (fun i => (r : ℂ)^i.val)

theorem finiteRadialMultiplier_apply (N : ℕ) (r : ℝ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    finiteRadialMultiplier N r x i=(r : ℂ)^i.val*x i :=
  finiteCoordinateMultiplier_apply N _ x i

theorem norm_finiteRadialMultiplier_le_one (N : ℕ) (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) :
    ‖finiteRadialMultiplier N r‖≤1 := by
  apply norm_finiteCoordinateMultiplier_le N _ 1 zero_le_one
  intro i
  simp only [norm_pow,Complex.norm_real,Real.norm_of_nonneg hr0]
  exact pow_le_one₀ hr0 hr1

theorem finiteRadialMultiplier_single (N : ℕ) (r : ℝ) (j : Fin N) :
    finiteRadialMultiplier N r (EuclideanSpace.single j (1 : ℂ))=
      (r : ℂ)^j.val • EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro i
  simp only [finiteRadialMultiplier_apply,PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases hi : i=j
  · subst i
    simp
  · simp only [ite_eq_right hi,mul_zero]

theorem polynomialRectangle_radial_eq (rows cols s : ℕ) (P : Polynomial ℂ) (r : ℝ) :
    polynomialHankelRectangleOffset rows cols s (polynomialRadialScale P r)=
      (r : ℂ)^s • (finiteRadialMultiplier rows r ∘L
        polynomialHankelRectangleOffset rows cols s P ∘L finiteRadialMultiplier cols r) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin cols) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [smul_apply,ContinuousLinearMap.comp_apply,finiteRadialMultiplier_single,
    map_smul,finiteRadialMultiplier_apply,PiLp.smul_apply,smul_eq_mul,
    polynomialHankelRectangleOffset_single_apply,polynomialRadialScale_coeff,pow_add]
  ring!

theorem polynomialRectangle_radial_schatten_rpow_le (rows cols s : ℕ)
    (P : Polynomial ℂ) (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (p : ℝ) (hp : 0<p) :
    schattenNorm p (polynomialHankelRectangleOffset rows cols s (polynomialRadialScale P r))^p≤
      (r^s)^p*schattenNorm p (polynomialHankelRectangleOffset rows cols s P)^p := by
  let A := polynomialHankelRectangleOffset rows cols s P
  have hA : Schatten p A := finiteDim_schatten A p hp
  have hRows := norm_finiteRadialMultiplier_le_one rows r hr0 hr1
  have hCols := norm_finiteRadialMultiplier_le_one cols r hr0 hr1
  have hProd : ‖finiteRadialMultiplier rows r‖*‖finiteRadialMultiplier cols r‖≤1 := by
    nlinarith [norm_nonneg (finiteRadialMultiplier rows r),
      norm_nonneg (finiteRadialMultiplier cols r)]
  have hSand : schattenNorm p
      (finiteRadialMultiplier rows r ∘L A ∘L finiteRadialMultiplier cols r)≤schattenNorm p A := by
    have h := (schattenNorm_comp_le hA (finiteRadialMultiplier rows r)
      (finiteRadialMultiplier cols r)).trans
        (mul_le_mul_of_nonneg_right hProd (schattenNorm_nonneg p A))
    simpa only [one_mul] using h
  rw [polynomialRectangle_radial_eq,schattenNorm_smul_rpow _ _ p hp,
    norm_pow,Complex.norm_real,Real.norm_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (schattenNorm_nonneg p _) hSand hp.le)
      (Real.rpow_nonneg (pow_nonneg hr0 s) p)

theorem shortBand_polynomial_integral_upper (L : ℕ) (hL : 0<L) (P : Polynomial ℂ)
    (hhi : ∀ k : ℕ,6*L≤k → P.coeff k=0)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (2*L) P)^p≤
      (8^(1-p)*3^p)*(L : ℝ)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  have hDeg : P.natDegree≤6*L-1 :=
    (Polynomial.natDegree_le_iff_coeff_eq_zero (p:=P) (n:=6*L-1)).mpr
      (fun k hk => hhi k (by omega))
  let : NeZero (8*L) := ⟨by omega⟩
  have h := polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral
    (8*L) (3*L) (3*L) (2*L) (by omega) P (by omega) p hp hp1
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  rw [Real.mul_self_sqrt (by positivity : 0≤3*(L : ℝ))] at h
  have hPow : (8*(L : ℝ))^(1-p)*(3*(L : ℝ))^p=
      (8^(1-p)*3^p)*(L : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤8) hLr.le,
      Real.mul_rpow (by norm_num : (0 : ℝ)≤3) hLr.le]
    calc
      _ = (8^(1-p)*3^p)*((L : ℝ)^(1-p)*(L : ℝ)^p) := by ring
      _ = _ := by rw [← Real.rpow_add hLr,sub_add_cancel,Real.rpow_one]
  calc
    _ ≤ (8*(L : ℝ))^(1-p)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
          (3*(L : ℝ))^p := h
    _ = _ := by
      calc
        _ = ((8*(L : ℝ))^(1-p)*(3*(L : ℝ))^p)*
          (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by ring
        _ = _ := by rw [hPow]

theorem shortBand_radial_integral_le (L : ℕ) (hL : 0<L) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ,k<4*L → P.coeff k=0)
    (hhi : ∀ k : ℕ,6*L≤k → P.coeff k=0)
    (r : ℝ) (hr0 : 0≤r) (hr1 : r≤1) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    (∫ τ : Boundary,‖P.eval ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure)≤
      (8^(1-p)*3^p)*(r^(2*L))^p*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  have hLo : ∀ k : ℕ,k<4*L → (polynomialRadialScale P r).coeff k=0 := by
    intro k hk
    rw [polynomialRadialScale_coeff,hlo k hk,zero_mul]
  have hHi : ∀ k : ℕ,6*L≤k → (polynomialRadialScale P r).coeff k=0 := by
    intro k hk
    rw [polynomialRadialScale_coeff,hhi k hk,zero_mul]
  have hLower := shortBand_polynomial_integral_lower L (polynomialRadialScale P r)
    hLo hHi p hp hp1
  simp only [polynomialRadialScale_eval] at hLower
  have hNorm := (polynomialRectangle_radial_schatten_rpow_le
    (3*L) (3*L) (2*L) P r hr0 hr1 p hp).trans
      (mul_le_mul_of_nonneg_left
        (shortBand_polynomial_integral_upper L hL P hhi p hp hp1)
          (Real.rpow_nonneg (pow_nonneg hr0 _) p))
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  apply (mul_le_mul_iff_right₀ hLr).mp
  nlinarith

end TTO.Paper.Proved
