/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ShortBandRadialFoundations
public import TTO.OffsetShortBandHankelLowerFoundations
public import TTO.BesovTwoFoundations
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Actual Euler differentiation of short-band polynomials and their coefficient matrices. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

def polynomialEulerStep (k : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X*P.derivative-Polynomial.C (k : ℂ)*P

theorem polynomialEulerStep_coeff (k : ℕ) (P : Polynomial ℂ) (n : ℕ) :
    (polynomialEulerStep k P).coeff n=((n : ℂ)-(k : ℂ))*P.coeff n := by
  cases n with
  | zero => simp [polynomialEulerStep]
  | succ n => simp [polynomialEulerStep,Polynomial.coeff_derivative]; ring

theorem polynomialEulerStep_coeff_zero (k : ℕ) (P : Polynomial ℂ) (n : ℕ)
    (h : P.coeff n=0) : (polynomialEulerStep k P).coeff n=0 := by
  rw [polynomialEulerStep_coeff,h,mul_zero]

theorem finiteCoordinateMultiplier_single (N : ℕ) (c : Fin N→ℂ) (j : Fin N) :
    finiteCoordinateMultiplier N c (EuclideanSpace.single j (1 : ℂ))=
      c j • EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro i
  simp only [finiteCoordinateMultiplier_apply,PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases hi : i=j
  · subst i
    simp
  · simp only [ite_eq_right hi,mul_zero]

theorem polynomialRectangle_eulerStep_eq (rows cols s k : ℕ) (P : Polynomial ℂ) :
    polynomialHankelRectangleOffset rows cols s (polynomialEulerStep k P)=
      finiteCoordinateMultiplier rows (fun i => ((s+i.val : ℕ) : ℂ)-(k : ℂ)) ∘L
        polynomialHankelRectangleOffset rows cols s P+
      polynomialHankelRectangleOffset rows cols s P ∘L
        finiteCoordinateMultiplier cols (fun j => (j.val : ℂ)) := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin cols) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [add_apply,ContinuousLinearMap.comp_apply,finiteCoordinateMultiplier_single,
    map_smul,finiteCoordinateMultiplier_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    polynomialHankelRectangleOffset_single_apply,polynomialEulerStep_coeff,Nat.cast_add]
  ring!

def scaledPolynomialDerivative (P : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.X^n*(Polynomial.derivative^[n]) P

theorem scaledPolynomialDerivative_zero (P : Polynomial ℂ) :
    scaledPolynomialDerivative P 0=P := by
  simp [scaledPolynomialDerivative]

theorem scaledPolynomialDerivative_succ (P : Polynomial ℂ) (n : ℕ) :
    scaledPolynomialDerivative P (n+1)=
      polynomialEulerStep n (scaledPolynomialDerivative P n) := by
  cases n with
  | zero => simp [scaledPolynomialDerivative,polynomialEulerStep]
  | succ n =>
    simp only [scaledPolynomialDerivative,polynomialEulerStep,Polynomial.derivative_mul,
      Polynomial.derivative_X_pow_succ,Function.iterate_succ_apply',
      Nat.cast_add,Nat.cast_one]
    simp only [pow_succ]
    ring!

theorem polynomialIteratedDerivative_eval (P : Polynomial ℂ) (n : ℕ) :
    (fun z : ℂ => ((Polynomial.derivative^[n]) P).eval z)=iteratedDeriv n P.eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',iteratedDeriv_succ,← ih]
    funext z
    exact (Polynomial.deriv _).symm

theorem scaledPolynomialDerivative_eval (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (scaledPolynomialDerivative P n).eval z=z^n*iteratedDeriv n P.eval z := by
  have h := congrFun (polynomialIteratedDerivative_eval P n) z
  simpa only [scaledPolynomialDerivative,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X] using congrArg (fun x : ℂ => z^n*x) h

theorem shortBand_eulerStep_schatten_rpow_le (b L k : ℕ) (hb0 : 4*L≤b) (hb1 : b≤102*L) (hk : k≤L)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L)
      (polynomialEulerStep k P))^p≤
        (105^p+3^p)*(L : ℝ)^p*
          schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p := by
  let A := polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P
  let DL := finiteCoordinateMultiplier (3*L)
    (fun i => ((b-2*L+i.val : ℕ) : ℂ)-(k : ℂ))
  let DR := finiteCoordinateMultiplier (3*L) (fun j => (j.val : ℂ))
  let I := ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (3*L)))
  have hA : Schatten p A := finiteDim_schatten A p hp
  have hI : ‖I‖≤1 := ContinuousLinearMap.norm_id_le
  have hDL : ‖DL‖≤105*(L : ℝ) := by
    apply norm_finiteCoordinateMultiplier_le _ _ _ (by positivity)
    intro i
    have hki : (k : ℝ)≤(L : ℝ) := by exact_mod_cast hk
    have hi : (i.val : ℝ)≤3*(L : ℝ) := by exact_mod_cast i.is_lt.le
    have hsLo : 2*(L : ℝ)≤((b-2*L : ℕ) : ℝ) := by exact_mod_cast (show 2*L≤b-2*L by omega)
    have hsHi : ((b-2*L : ℕ) : ℝ)≤102*(L : ℝ) := by exact_mod_cast (show b-2*L≤102*L by omega)
    have h0 : 0≤((b-2*L : ℕ) : ℝ)+(i.val : ℝ)-(k : ℝ) := by
      have hL0 : 0≤(L : ℝ) := Nat.cast_nonneg L
      have hi0 : 0≤(i.val : ℝ) := Nat.cast_nonneg i.val
      linarith
    have he : ((b-2*L+i.val : ℕ) : ℂ)-(k : ℂ)=
        ((((b-2*L : ℕ) : ℝ)+(i.val : ℝ)-(k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_of_nonneg h0]
    have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
    linarith
  have hDR : ‖DR‖≤3*(L : ℝ) := by
    apply norm_finiteCoordinateMultiplier_le _ _ _ (by positivity)
    intro j
    rw [Complex.norm_natCast]
    exact_mod_cast j.is_lt.le
  have hLeft : schattenNorm p (DL ∘L A)≤(105*(L : ℝ))*schattenNorm p A := by
    have h := schattenNorm_comp_le hA DL I
    simp only [I,ContinuousLinearMap.comp_id] at h
    have hn : ‖DL‖*‖I‖≤105*(L : ℝ) := by
      nlinarith [norm_nonneg DL,norm_nonneg I]
    exact h.trans (mul_le_mul_of_nonneg_right hn (schattenNorm_nonneg p A))
  have hRight : schattenNorm p (A ∘L DR)≤(3*(L : ℝ))*schattenNorm p A := by
    have h := schattenNorm_comp_le hA I DR
    simp only [I,ContinuousLinearMap.id_comp] at h
    have hn : ‖I‖*‖DR‖≤3*(L : ℝ) := by
      nlinarith [norm_nonneg DR,norm_nonneg I]
    exact h.trans (mul_le_mul_of_nonneg_right hn (schattenNorm_nonneg p A))
  rw [polynomialRectangle_eulerStep_eq]
  change schattenNorm p (DL ∘L A+A ∘L DR)^p≤_
  calc
    _ ≤ schattenNorm p (DL ∘L A)^p+schattenNorm p (A ∘L DR)^p :=
      finite_schattenNorm_add_rpow_le _ _ p hp hp1
    _ ≤ ((105*(L : ℝ))*schattenNorm p A)^p+((3*(L : ℝ))*schattenNorm p A)^p :=
      add_le_add (Real.rpow_le_rpow (schattenNorm_nonneg p _) hLeft hp.le)
        (Real.rpow_le_rpow (schattenNorm_nonneg p _) hRight hp.le)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤105*(L : ℝ)) (schattenNorm_nonneg p A),
        Real.mul_rpow (by positivity : 0≤3*(L : ℝ)) (schattenNorm_nonneg p A),
        Real.mul_rpow (by norm_num : (0 : ℝ)≤105) (Nat.cast_nonneg L),
        Real.mul_rpow (by norm_num : (0 : ℝ)≤3) (Nat.cast_nonneg L)]
      ring

theorem shortBand_scaledDerivative_schatten_rpow_le (b L n : ℕ) (hb0 : 4*L≤b) (hb1 : b≤102*L) (hL : 0<L)
    (hn : n≤L) (P : Polynomial ℂ) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L)
      (scaledPolynomialDerivative P n))^p≤
        (105^p+3^p)^n*(L : ℝ)^((n : ℝ)*p)*
          schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p := by
  let B : ℝ := 105^p+3^p
  have hB : 0≤B := by dsimp only [B]; positivity
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  change schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L)
    (scaledPolynomialDerivative P n))^p≤B^n*(L : ℝ)^((n : ℝ)*p)*
      schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p
  revert hn
  induction n with
  | zero =>
    intro _
    simp only [scaledPolynomialDerivative_zero,pow_zero,Nat.cast_zero,zero_mul,
      Real.rpow_zero,one_mul]
    exact le_rfl
  | succ n ih =>
    intro hn
    have hPrev := ih (by omega)
    rw [scaledPolynomialDerivative_succ]
    calc
      _ ≤ B*(L : ℝ)^p*schattenNorm p
          (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L)
            (scaledPolynomialDerivative P n))^p :=
        shortBand_eulerStep_schatten_rpow_le b L n hb0 hb1 (by omega) _ p hp hp1
      _ ≤ B*(L : ℝ)^p*(B^n*(L : ℝ)^((n : ℝ)*p)*
          schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p) :=
        mul_le_mul_of_nonneg_left hPrev
          (mul_nonneg hB (Real.rpow_nonneg hLr.le p))
      _ = _ := by
        have he : ((n+1 : ℕ) : ℝ)*p=(n : ℝ)*p+p := by push_cast; ring
        rw [pow_succ,he,Real.rpow_add hLr]
        ring

theorem scaledPolynomialDerivative_coeff_zero (P : Polynomial ℂ) (n k : ℕ)
    (h : P.coeff k=0) : (scaledPolynomialDerivative P n).coeff k=0 := by
  induction n with
  | zero => simpa only [scaledPolynomialDerivative_zero] using h
  | succ n ih =>
    rw [scaledPolynomialDerivative_succ,polynomialEulerStep_coeff,ih,mul_zero]

theorem offsetShortBand_polynomial_integral_upper (b L : ℕ) (hL : 0<L)
    (hb : b≤102*L) (P : Polynomial ℂ)
    (hhi : ∀ k : ℕ,b+2*L≤k → P.coeff k=0)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (polynomialHankelRectangleOffset (3*L) (3*L) (b-2*L) P)^p≤
      (108^(1-p)*3^p)*(L : ℝ)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  have hDeg : P.natDegree≤b+2*L-1 :=
    (Polynomial.natDegree_le_iff_coeff_eq_zero (p:=P) (n:=b+2*L-1)).mpr
      (fun k hk => hhi k (by omega))
  let : NeZero (108*L) := ⟨by omega⟩
  have h := polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral
    (108*L) (3*L) (3*L) (b-2*L) (by omega) P (by omega) p hp hp1
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  rw [Real.mul_self_sqrt (by positivity : 0≤3*(L : ℝ))] at h
  have hPow : (108*(L : ℝ))^(1-p)*(3*(L : ℝ))^p=
      (108^(1-p)*3^p)*(L : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤108) hLr.le,
      Real.mul_rpow (by norm_num : (0 : ℝ)≤3) hLr.le]
    calc
      _ = (108^(1-p)*3^p)*((L : ℝ)^(1-p)*(L : ℝ)^p) := by ring
      _ = _ := by rw [← Real.rpow_add hLr,sub_add_cancel,Real.rpow_one]
  calc
    _ ≤ (108*(L : ℝ))^(1-p)*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*
          (3*(L : ℝ))^p := h
    _ = _ := by
      calc
        _ = ((108*(L : ℝ))^(1-p)*(3*(L : ℝ))^p)*
          (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by ring
        _ = _ := by rw [hPow]

theorem offsetShortBand_derivative_radial_integral_le (b L n : ℕ)
    (hb0 : 4*L≤b) (hb1 : b≤102*L) (hL : 0<L)
    (hn : n≤L) (P : Polynomial ℂ)
    (hlo : ∀ k : ℕ,k<b → P.coeff k=0) (hhi : ∀ k : ℕ,b+2*L≤k → P.coeff k=0)
    (r : ℝ) (hr : 0<r) (hr1 : r≤1) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    (∫ τ : Boundary,‖iteratedDeriv n P.eval ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure)≤
      (108^(1-p)*3^p)*(105^p+3^p)^n*(L : ℝ)^((n : ℝ)*p)*(r^(b-2*L-n))^p*
        (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
  let Q := scaledPolynomialDerivative P n
  have hLo : ∀ k : ℕ,k<b → (polynomialRadialScale Q r).coeff k=0 := by
    intro k hk
    rw [polynomialRadialScale_coeff]
    change (scaledPolynomialDerivative P n).coeff k*(r : ℂ)^k=0
    rw [scaledPolynomialDerivative_coeff_zero P n k (hlo k hk),zero_mul]
  have hHi : ∀ k : ℕ,b+2*L≤k → (polynomialRadialScale Q r).coeff k=0 := by
    intro k hk
    rw [polynomialRadialScale_coeff]
    change (scaledPolynomialDerivative P n).coeff k*(r : ℂ)^k=0
    rw [scaledPolynomialDerivative_coeff_zero P n k (hhi k hk),zero_mul]
  have hEval (τ : Boundary) :
      ‖(polynomialRadialScale Q r).eval (fourier (T:=1) 1 τ)‖^p=
        (r^n)^p*‖iteratedDeriv n P.eval ((r : ℂ)*fourier (T:=1) 1 τ)‖^p := by
    rw [polynomialRadialScale_eval]
    dsimp only [Q]
    rw [scaledPolynomialDerivative_eval,norm_mul,norm_pow,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hr.le,show ‖fourier (T:=1) 1 τ‖=1 by simp,mul_one,
      Real.mul_rpow (pow_nonneg hr.le n) (norm_nonneg _)]
  have hInt :
      (∫ τ : Boundary,‖(polynomialRadialScale Q r).eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)=
        (r^n)^p*(∫ τ : Boundary,‖iteratedDeriv n P.eval
          ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by
    simp_rw [hEval]
    exact integral_const_mul _ _
  have hLower := offsetShortBand_polynomial_integral_lower b L (by omega) (polynomialRadialScale Q r)
    hLo hHi p hp hp1
  rw [hInt] at hLower
  have hQBound := shortBand_scaledDerivative_schatten_rpow_le b L n hb0 hb1 hL hn P p hp hp1
  have hPBound := offsetShortBand_polynomial_integral_upper b L hL hb1 P hhi p hp hp1
  have hQN := hQBound.trans (mul_le_mul_of_nonneg_left hPBound (by positivity))
  have hAll := (polynomialRectangle_radial_schatten_rpow_le
    (3*L) (3*L) (b-2*L) Q r hr.le hr1 p hp).trans
      (mul_le_mul_of_nonneg_left hQN (Real.rpow_nonneg (pow_nonneg hr.le _) p))
  have hNat : n+(b-2*L-n)=b-2*L := by omega
  have hPow : (r^(b-2*L))^p=(r^n)^p*(r^(b-2*L-n))^p := by
    calc
      _ = (r^(n+(b-2*L-n)))^p := by rw [hNat]
      _ = _ := by rw [pow_add,Real.mul_rpow (pow_nonneg hr.le n) (pow_nonneg hr.le _)]
  rw [hPow] at hAll
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  have hR : 0<(r^n)^p := Real.rpow_pos_of_pos (pow_pos hr n) p
  apply (mul_le_mul_iff_right₀ (mul_pos hLr hR)).mp
  nlinarith only [hLower,hAll]

theorem lintegral_scaled_boundary_distance (f : ℝ → ℝ≥0∞) (L : ℝ) (hL : 0<L) :
    (∫⁻ r in Ioo (0 : ℝ) 1,f (L*(1-r)))=
      ENNReal.ofReal L⁻¹*∫⁻ u in Ioo (0 : ℝ) L,f u := by
  have he : MeasurableEmbedding (fun r : ℝ => L*(1-r)) :=
    ((Homeomorph.subLeft (1 : ℝ)).trans
      (Homeomorph.mulLeft₀ L hL.ne')).measurableEmbedding
  have hmap : Measure.map (fun r : ℝ => L*(1-r)) volume=
      ENNReal.ofReal L⁻¹ • volume := by
    calc
      _ = Measure.map (fun r : ℝ => L*r) (Measure.map (fun r : ℝ => 1-r) volume) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = _ := by
        rw [(Measure.measurePreserving_sub_left volume (1 : ℝ)).map_eq,
          Real.map_volume_mul_left hL.ne',abs_of_pos (inv_pos.mpr hL)]
  have hmp : MeasurePreserving (fun r : ℝ => L*(1-r)) volume
      (ENNReal.ofReal L⁻¹ • volume) := ⟨he.measurable,hmap⟩
  have hpre : (fun r : ℝ => L*(1-r)) ⁻¹' Ioo (0 : ℝ) L=Ioo (0 : ℝ) 1 := by
    ext r
    simp only [mem_preimage,mem_Ioo]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]
  have h := hmp.setLIntegral_comp_preimage_emb he f (Ioo (0 : ℝ) L)
  rw [hpre,Measure.restrict_smul,lintegral_smul_measure] at h
  exact h

theorem lintegral_unit_rpow (α : ℝ) (hα : -1<α) :
    (∫⁻ u in Ioc (0 : ℝ) 1,ENNReal.ofReal (u^α))=
      ENNReal.ofReal (1/(α+1)) := by
  have hI : IntegrableOn (fun u : ℝ => u^α) (Ioo (0 : ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr hα
  have hJ : IntegrableOn (fun u : ℝ => u^α) (Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (f:=fun u : ℝ => u^α)).mpr hI
  rw [← ofReal_integral_eq_lintegral_ofReal hJ
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => Real.rpow_nonneg hu.1.le α))]
  rw [← intervalIntegral.integral_of_le zero_le_one,integral_rpow (Or.inl hα)]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : α+1≠0)]
  simp only [sub_zero]

theorem lintegral_positive_exp (p : ℝ) (hp : 0<p) :
    (∫⁻ u in Ioi (0 : ℝ),ENNReal.ofReal (Real.exp (-p*u)))=ENNReal.ofReal (1/p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (a:=-p) (by linarith) 0)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_exp_mul_Ioi (by linarith : -p<0)]
  simp

theorem lintegral_exp_negative_rpow_le (p α : ℝ) (hp : 0<p)
    (hα : -1<α) (hα0 : α≤0) :
    (∫⁻ u in Ioi (0 : ℝ),ENNReal.ofReal (Real.exp (-p*u)*u^α))≤
      ENNReal.ofReal (1/(α+1)+1/p) := by
  have hNear :
      (∫⁻ u in Ioc (0 : ℝ) 1,ENNReal.ofReal (Real.exp (-p*u)*u^α))≤
        ∫⁻ u in Ioc (0 : ℝ) 1,ENNReal.ofReal (u^α) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-p*u)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
    nlinarith [Real.rpow_nonneg hu.1.le α]
  have hFar :
      (∫⁻ u in Ioi (1 : ℝ),ENNReal.ofReal (Real.exp (-p*u)*u^α))≤
        ∫⁻ u in Ioi (1 : ℝ),ENNReal.ofReal (Real.exp (-p*u)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.rpow_le_one_of_one_le_of_nonpos hu.le hα0)
  rw [← Ioc_union_Ioi_eq_Ioi (a:=(0 : ℝ)) zero_le_one,
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  calc
    _ ≤ (∫⁻ u in Ioc (0 : ℝ) 1,ENNReal.ofReal (u^α))+
        ∫⁻ u in Ioi (1 : ℝ),ENNReal.ofReal (Real.exp (-p*u)) := add_le_add hNear hFar
    _ ≤ (∫⁻ u in Ioc (0 : ℝ) 1,ENNReal.ofReal (u^α))+
        ∫⁻ u in Ioi (0 : ℝ),ENNReal.ofReal (Real.exp (-p*u)) := by
      exact add_le_add le_rfl (lintegral_mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤1)))
    _ = _ := by
      have hαp : 0<α+1 := by linarith
      rw [lintegral_unit_rpow α hα,lintegral_positive_exp p hp,
        ENNReal.ofReal_add (by positivity : 0≤1/(α+1)) (by positivity : 0≤1/p)]

theorem radial_power_exp_scale_le (L p α r : ℝ) (hL : 0<L) (hp : 0<p)
    (hr : r∈Ioo (0 : ℝ) 1) :
    r^(L*p)*(1-r)^α≤
      L^(-α)*(Real.exp (-p*(L*(1-r)))*(L*(1-r))^α) := by
  have hδ : 0<1-r := by linarith [hr.2]
  have hExp : r^(L*p)≤Real.exp (-p*(L*(1-r))) := by
    rw [Real.rpow_def_of_pos hr.1]
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hr.1)
      (mul_nonneg hL.le hp.le)
    nlinarith
  have hScale : (1-r)^α=L^(-α)*(L*(1-r))^α := by
    rw [Real.mul_rpow hL.le hδ.le]
    rw [← mul_assoc,← Real.rpow_add hL,neg_add_cancel,Real.rpow_zero,one_mul]
  calc
    _ ≤ Real.exp (-p*(L*(1-r)))*(1-r)^α :=
      mul_le_mul_of_nonneg_right hExp (Real.rpow_nonneg hδ.le α)
    _ = _ := by rw [hScale]; ring

theorem lintegral_radial_power_weight_le (L p α : ℝ) (hL : 0<L) (hp : 0<p)
    (hα : -1<α) (hα0 : α≤0) :
    (∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (r^(L*p)*(1-r)^α))≤
      ENNReal.ofReal ((1/(α+1)+1/p)*L^(-α-1)) := by
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-p*u)*u^α)
  have hPoint :
      (∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (r^(L*p)*(1-r)^α))≤
        ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (L^(-α))*f (L*(1-r)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    dsimp only [f]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
    exact ENNReal.ofReal_le_ofReal (radial_power_exp_scale_le L p α r hL hp hr)
  calc
    _ ≤ _ := hPoint
    _ = ENNReal.ofReal (L^(-α))*(ENNReal.ofReal L⁻¹*
        ∫⁻ u in Ioo (0 : ℝ) L,f u) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_scaled_boundary_distance f L hL]
    _ ≤ ENNReal.ofReal (L^(-α))*(ENNReal.ofReal L⁻¹*
        ∫⁻ u in Ioi (0 : ℝ),f u) := by
      gcongr
      exact fun _ h => h.1
    _ ≤ ENNReal.ofReal (L^(-α))*(ENNReal.ofReal L⁻¹*
        ENNReal.ofReal (1/(α+1)+1/p)) := by
      gcongr
      exact lintegral_exp_negative_rpow_le p α hp hα hα0
    _ = _ := by
      have hαp : 0<α+1 := by linarith
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
      congr 1
      rw [← mul_assoc,← Real.rpow_neg_one L,← Real.rpow_add hL]
      rw [show -α+(-1)=-α-1 by ring]
      ring

theorem polynomialDerivative_weighted_polar (P : Polynomial ℂ) (n : ℕ)
    (p α : ℝ) (hp : 0<p) :
    (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*(1-‖z‖)^α) ∂diskArea)=
      ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal
        (2*r*(∫ τ : Boundary,‖iteratedDeriv n P.eval
          ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure)*(1-r)^α) := by
  have hD : Continuous (iteratedDeriv n P.eval) := by
    rw [← polynomialIteratedDerivative_eval]
    fun_prop
  have hM : Measurable (disk.indicator (fun z : ℂ =>
      ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*(1-‖z‖)^α))) := by
    apply Measurable.indicator
    · exact (((hD.norm.measurable.pow_const p).mul
        ((measurable_const.sub measurable_norm).pow_const α)).ennreal_ofReal)
    · exact (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [lintegral_diskArea_polar _ hM]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hI : Integrable (fun τ : Boundary => ‖iteratedDeriv n P.eval
      ((r : ℂ)*fourier (T:=1) 1 τ)‖^p) circleMeasure := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply (Real.continuous_rpow_const hp.le).comp
    exact (hD.comp (by fun_prop)).norm
  have he (τ : Boundary) :
      ENNReal.ofReal (‖iteratedDeriv n P.eval
          ((r : ℂ)*fourier (T:=1) 1 τ)‖^p*
            (1-‖(r : ℂ)*fourier (T:=1) 1 τ‖)^α)=
        ENNReal.ofReal ((1-r)^α)*ENNReal.ofReal
          (‖iteratedDeriv n P.eval ((r : ℂ)*fourier (T:=1) 1 τ)‖^p) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1.le,
      fourier_one,Circle.norm_coe,mul_one]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
    exact mul_comm _ _
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) p)]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hr.2] : 0≤1-r) α),
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ)≤2) hr.1.le)]
  congr 1
  ring

theorem offsetShortBand_derivative_area_le (b L n : ℕ)
    (hb0 : 4*L≤b) (hb1 : b≤102*L) (hL : 0<L) (hn : n≤L)
    (P : Polynomial ℂ) (hlo : ∀ k : ℕ,k<b → P.coeff k=0)
    (hhi : ∀ k : ℕ,b+2*L≤k → P.coeff k=0)
    (p α : ℝ) (hp : 0<p) (hp1 : p≤1) (hα : -1<α) (hα0 : α≤0) :
    (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*(1-‖z‖)^α) ∂diskArea)≤
      ENNReal.ofReal (2*(108^(1-p)*3^p)*(105^p+3^p)^n*
        (1/(α+1)+1/p)*(L : ℝ)^((n : ℝ)*p-α-1)*
          (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)) := by
  let C : ℝ := (108^(1-p)*3^p)*(105^p+3^p)^n
  let M : ℝ := ∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure
  have hC : 0≤C := by dsimp only [C]; positivity
  have hM : 0≤M := integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) p)
  have hLr : 0<(L : ℝ) := by exact_mod_cast hL
  let A : ℝ := 2*C*(L : ℝ)^((n : ℝ)*p)*M
  have hA : 0≤A := by dsimp only [A]; positivity
  rw [polynomialDerivative_weighted_polar P n p α hp]
  calc
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal A*
        ENNReal.ofReal (r^((L : ℝ)*p)*(1-r)^α) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [← ENNReal.ofReal_mul hA]
      apply ENNReal.ofReal_le_ofReal
      have h0 := offsetShortBand_derivative_radial_integral_le b L n hb0 hb1 hL hn
        P hlo hhi r hr.1 hr.2.le p hp hp1
      have hR : (r^(b-2*L-n))^p≤r^((L : ℝ)*p) := by
        rw [← Real.rpow_natCast_mul hr.1.le]
        apply Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2.le
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact_mod_cast (show L≤b-2*L-n by omega)
      have hI : (∫ τ : Boundary,‖iteratedDeriv n P.eval
          ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure)≤
            C*(L : ℝ)^((n : ℝ)*p)*r^((L : ℝ)*p)*M := by
        exact h0.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR (mul_nonneg hC (by positivity))) hM)
      have hIn : 0≤(∫ τ : Boundary,‖iteratedDeriv n P.eval
          ((r : ℂ)*fourier (T:=1) 1 τ)‖^p ∂circleMeasure) :=
        integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) p)
      have hW : 0≤(1-r)^α := Real.rpow_nonneg (by linarith [hr.2]) α
      calc
        _ ≤ (2*(C*(L : ℝ)^((n : ℝ)*p)*r^((L : ℝ)*p)*M))*(1-r)^α :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (by linarith [hr.2] : 2*r≤2) hI hIn (by norm_num)) hW
        _ = _ := by dsimp only [A]; ring
    _ = ENNReal.ofReal A*
        ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (r^((L : ℝ)*p)*(1-r)^α) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal A*ENNReal.ofReal
        ((1/(α+1)+1/p)*(L : ℝ)^(-α-1)) :=
      mul_le_mul_right (lintegral_radial_power_weight_le (L : ℝ) p α hLr hp hα hα0) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp only [A,C,M]
      have he : (L : ℝ)^((n : ℝ)*p)*(L : ℝ)^(-α-1)=
          (L : ℝ)^((n : ℝ)*p-α-1) := by
        rw [← Real.rpow_add hLr]
        congr 1
        ring
      calc
        _ = 2*(108^(1-p)*3^p)*(105^p+3^p)^n*(1/(α+1)+1/p)*
            ((L : ℝ)^((n : ℝ)*p)*(L : ℝ)^(-α-1))*
              (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) := by ring
        _ = _ := by rw [he]

theorem offsetShortBand_derivative_besov_weight_le (b L n : ℕ)
    (hb0 : 4*L≤b) (hb1 : b≤102*L) (hL : 0<L) (hn : n≤L)
    (P : Polynomial ℂ) (hlo : ∀ k : ℕ,k<b → P.coeff k=0)
    (hhi : ∀ k : ℕ,b+2*L≤k → P.coeff k=0)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hnp : 1<(n : ℝ)*p) (hnp2 : (n : ℝ)*p≤2) :
    (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*
      (1-‖z‖)^((n : ℝ)*p-2)) ∂diskArea)≤
      ENNReal.ofReal (2*(108^(1-p)*3^p)*(105^p+3^p)^n*
        (1/((n : ℝ)*p-1)+1/p)*(L : ℝ)*
          (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)) := by
  have h := offsetShortBand_derivative_area_le b L n hb0 hb1 hL hn P hlo hhi
    p ((n : ℝ)*p-2) hp hp1 (by linarith) (by linarith)
  simpa only [show (n : ℝ)*p-((n : ℝ)*p-2)-1=1 by ring,
    show (n : ℝ)*p-2+1=(n : ℝ)*p-1 by ring,Real.rpow_one] using h

theorem besovOrder_product_bounds (p : ℝ) (hp : 0<p) :
    1<(besovOrder p : ℝ)*p ∧ (besovOrder p : ℝ)*p≤1+p := by
  have h0 : 0≤1/p := by positivity
  have hLo := Nat.lt_floor_add_one (1/p)
  have hHi := Nat.floor_le h0
  have hMulLo := (mul_lt_mul_iff_left₀ hp).2 hLo
  have hMulHi := mul_le_mul_of_nonneg_right hHi hp.le
  have hInv : (1/p)*p=1 := div_mul_cancel₀ 1 hp.ne'
  simp only [besovOrder,Nat.cast_add,Nat.cast_one]
  constructor <;> nlinarith

theorem polynomialIteratedDerivative_zero_of_coeff_zero (P : Polynomial ℂ) (n : ℕ)
    (hn : P.coeff n=0) : iteratedDeriv n P.eval 0=0 := by
  rw [← polynomialIteratedDerivative_eval]
  change ((Polynomial.derivative^[n]) P).eval 0=0
  rw [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative]
  simp only [zero_add,hn,smul_zero]

theorem lintegral_frozen_weight_le_physical_of_nonpos
    (U : ℂ → ℝ) (hU : ∀ z∈disk,0≤U z) (α : ℝ) (hα : α≤0) :
    (∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖^2)^α) ∂diskArea)≤
      ∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖)^α) ∂diskArea := by
  have hAE : ∀ᵐ z ∂diskArea,z∈disk := by
    rw [diskArea]
    exact Measure.ae_smul_measure
      (ae_restrict_mem (isOpen_lt continuous_norm continuous_const).measurableSet) _
  apply lintegral_mono_ae
  filter_upwards [hAE] with z hz
  change ‖z‖<1 at hz
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (hU z hz)
  apply Real.rpow_le_rpow_of_nonpos (by linarith) _ hα
  nlinarith [norm_nonneg z]

def shortBandBesovConstant (p : ℝ) : ℝ :=
  2*(108^(1-p)*3^p)*(105^p+3^p)^(besovOrder p)*
    (1/((besovOrder p : ℝ)*p-1)+1/p)

theorem shortBandBesovConstant_pos (p : ℝ) (hp : 0<p) :
    0<shortBandBesovConstant p := by
  have hnp : 0<(besovOrder p : ℝ)*p-1 := by
    linarith [(besovOrder_product_bounds p hp).1]
  dsimp only [shortBandBesovConstant]
  positivity

theorem offsetShortBand_besovEnergy_le (b L : ℕ)
    (hb0 : 4*L≤b) (hb1 : b≤102*L) (hL : 0<L)
    (P : Polynomial ℂ) (hlo : ∀ k : ℕ,k<b → P.coeff k=0)
    (hhi : ∀ k : ℕ,b+2*L≤k → P.coeff k=0)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hn : besovOrder p≤L) :
    besovEnergy p P.eval≤ENNReal.ofReal (shortBandBesovConstant p*(L : ℝ)*
      (∫ τ : Boundary,‖P.eval (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)) := by
  have hJet : (∑ j∈Finset.range (besovOrder p),
      ENNReal.ofReal (‖iteratedDeriv j P.eval 0‖^p))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjb : j<b := by have hjn := Finset.mem_range.mp hj; omega
    rw [polynomialIteratedDerivative_zero_of_coeff_zero P j (hlo j hjb)]
    simp only [norm_zero,Real.zero_rpow hp.ne',ENNReal.ofReal_zero]
  rw [besovEnergy,hJet,zero_add]
  have hnp := besovOrder_product_bounds p hp
  have hnp2 : (besovOrder p : ℝ)*p≤2 := by linarith [hnp.2]
  have hCompare := lintegral_frozen_weight_le_physical_of_nonpos
    (fun z => ‖iteratedDeriv (besovOrder p) P.eval z‖^p)
    (fun z _ => Real.rpow_nonneg (norm_nonneg _) p) ((besovOrder p : ℝ)*p-2)
    (by linarith)
  exact hCompare.trans (offsetShortBand_derivative_besov_weight_le b L (besovOrder p)
    hb0 hb1 hL hn P hlo hhi p hp hp1 hnp.1 hnp2)

end TTO.Paper.Proved
