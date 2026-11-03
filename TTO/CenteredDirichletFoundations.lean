/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialSchurFoundations
public import TTO.HardyMaximalFoundations
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual centered finite Fourier kernels for localization below p=1. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The literal polynomial before negative-frequency modulation. -/
def centeredDirichletPolynomial (L : ℕ) : Polynomial ℂ :=
  ∑ j∈Finset.range (2*L+1),Polynomial.X^j

theorem centeredDirichletPolynomial_eval (L : ℕ) (z : ℂ) :
    (centeredDirichletPolynomial L).eval z=∑ j∈Finset.range (2*L+1),z^j := by
  simp only [centeredDirichletPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_pow,Polynomial.eval_X]

/-- This symbol retains the full negative modulation, not an analytic projection. -/
def centeredDirichlet (L : ℕ) (t : Boundary) : ℂ :=
  (fourier (T := 1) 1 (-t))^L*(∑ j∈Finset.range (2*L+1),(fourier (T := 1) 1 t)^j)

theorem centeredDirichlet_eq_shiftedSymbol (L : ℕ) (t : Boundary) :
    centeredDirichlet L t=shiftedPolynomialSymbol (centeredDirichletPolynomial L) L t := by
  rw [shiftedPolynomialSymbol,centeredDirichletPolynomial_eval]
  rfl

theorem continuous_centeredDirichlet (L : ℕ) : Continuous (centeredDirichlet L) := by
  exact (((fourier (T := 1) 1).continuous.comp continuous_neg).pow L).mul
    (continuous_finsetSum _ (fun j _ => (fourier (T := 1) 1).continuous.pow j))

/-- Exact finite geometric identity; no division by a possibly vanishing character difference. -/
theorem centeredDirichlet_geometric (L : ℕ) (t : Boundary) :
    (fourier (T := 1) 1 t-1)*centeredDirichlet L t=
      (fourier (T := 1) 1 (-t))^L*((fourier (T := 1) 1 t)^(2*L+1)-1) := by
  dsimp only [centeredDirichlet]
  rw [mul_left_comm, mul_geom_sum]

theorem norm_centeredDirichlet_le (L : ℕ) (t : Boundary) :
    ‖centeredDirichlet L t‖≤2*(L : ℝ)+1 := by
  rw [centeredDirichlet,norm_mul,norm_pow]
  simp only [fourier_apply,Circle.norm_coe,one_pow,one_mul]
  calc
    _ ≤ ∑ j∈Finset.range (2*L+1),‖(fourier (T := 1) 1 t)^j‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The inverse-chord bound holds independently of the cutoff width. -/
theorem norm_centeredDirichlet_mul_chord_le (L : ℕ) (t : Boundary) :
    ‖centeredDirichlet L t‖*‖fourier (T := 1) 1 t-1‖≤2 := by
  rw [mul_comm,← norm_mul,centeredDirichlet_geometric,norm_mul,norm_pow]
  simp only [fourier_apply,Circle.norm_coe,one_pow,one_mul]
  calc
    _ ≤ ‖(fourier (T := 1) 1 t)^(2*L+1)‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by simp only [norm_pow,fourier_apply,Circle.norm_coe,one_pow,norm_one]; norm_num

/-- Actual period-one circle normalization: centered width L has the standard
inverse-distance bound on every real fundamental interval, with its center excluded. -/
theorem norm_centeredDirichlet_real_le (L : ℕ) (x : ℝ) (hx : 0 < |x|) (hx1 : |x| ≤ 1/2) :
    ‖centeredDirichlet L (x : Boundary)‖≤1/(2*|x|) := by
  have hChord : 4*|x|≤‖fourier (T := 1) 1 (x : Boundary)-1‖ := by
    simpa using circle_chord_lower_real x 0 (by simpa only [sub_zero] using hx1)
  have hMul := (mul_le_mul_of_nonneg_left hChord (norm_nonneg (centeredDirichlet L (x : Boundary)))).trans
    (norm_centeredDirichlet_mul_chord_le L (x : Boundary))
  apply (le_div_iff₀ (by positivity : 0<2*|x|)).mpr
  nlinarith

theorem centeredDirichletPolynomial_coeff (L n : ℕ) :
    (centeredDirichletPolynomial L).coeff n=if n≤2*L then 1 else 0 := by
  simp only [centeredDirichletPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,
    Finset.sum_ite_eq,Finset.mem_range]
  by_cases hn : n≤2*L
  · rw [ite_eq_left (by omega),ite_eq_left hn]
  · rw [ite_eq_right (by omega),ite_eq_right hn]

theorem centeredDirichletPolynomial_natDegree_le (L : ℕ) :
    (centeredDirichletPolynomial L).natDegree≤2*L := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  simp only [Polynomial.natDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)

theorem centeredDirichletPolynomial_eval_one (L : ℕ) :
    (centeredDirichletPolynomial L).eval 1=((2*L+1 : ℕ) : ℂ) := by
  rw [centeredDirichletPolynomial_eval]
  simp only [one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

/-- A long coefficient block convoluted with a shorter polynomial has an exact flat plateau. -/
theorem centeredDirichletPolynomial_mul_coeff_flat (L n : ℕ) (Q : Polynomial ℂ)
    (hQ : Q.natDegree≤n) (hn : n≤2*L) :
    (centeredDirichletPolynomial L*Q).coeff n=Q.eval 1 := by
  rw [mul_comm,Polynomial.coeff_mul]
  have hAnti : (∑ x∈Finset.antidiagonal n,Q.coeff x.1*(centeredDirichletPolynomial L).coeff x.2)=
      ∑ j∈Finset.range (n+1),Q.coeff j*(centeredDirichletPolynomial L).coeff (n-j) := by
    simpa only [Nat.succ_eq_add_one] using! Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => Q.coeff i*(centeredDirichletPolynomial L).coeff j) n
  rw [hAnti,Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [centeredDirichletPolynomial_coeff,ite_eq_left (by omega : n-j≤2*L),one_pow,mul_one]

/-- The negative frequency shift of the full product mask. -/
def dirichletProductShift (m N : ℕ) : ℕ := (m+2)*N+m*N

/-- A finite-order flat low-pass mask; neither its negative nor its positive modes are discarded. -/
def dirichletProductPolynomial (m N : ℕ) : Polynomial ℂ :=
  ((((2*N+1 : ℕ) : ℂ)⁻¹)^m) •
    (centeredDirichletPolynomial ((m+2)*N)*(centeredDirichletPolynomial N)^m)

def dirichletProductKernel (m N : ℕ) (t : Boundary) : ℂ :=
  centeredDirichlet ((m+2)*N) t*
    (centeredDirichlet N t/((2*N+1 : ℕ) : ℂ))^m

/-- The actual polynomial degree is controlled by twice the literal negative shift. -/
theorem dirichletProductPolynomial_natDegree_le (m N : ℕ) :
    (dirichletProductPolynomial m N).natDegree≤2*dirichletProductShift m N := by
  refine (Polynomial.natDegree_smul_le _ _).trans (Polynomial.natDegree_mul_le.trans ?_)
  have hPow := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
    (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
  exact (Nat.add_le_add (centeredDirichletPolynomial_natDegree_le ((m+2)*N)) hPow).trans_eq (by
    dsimp only [dirichletProductShift]
    ring)

/-- Exact one plateau on all the Hankel frequencies up to 2N, with no asymptotic premise. -/
theorem dirichletProductPolynomial_coeff_plateau (m N k : ℕ) (hk : k≤2*N) :
    (dirichletProductPolynomial m N).coeff (dirichletProductShift m N+k)=1 := by
  have hDeg : ((centeredDirichletPolynomial N)^m).natDegree≤dirichletProductShift m N+k := by
    have h := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
      (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
    dsimp only [dirichletProductShift]
    nlinarith
  have hUpper : dirichletProductShift m N+k≤2*((m+2)*N) := by
    dsimp only [dirichletProductShift]
    nlinarith
  rw [dirichletProductPolynomial,Polynomial.coeff_smul,
    centeredDirichletPolynomial_mul_coeff_flat _ _ _ hDeg hUpper,
    Polynomial.eval_pow,centeredDirichletPolynomial_eval_one,smul_eq_mul,← mul_pow]
  have hDen : (((2*N+1 : ℕ) : ℂ))≠0 := by exact_mod_cast (by omega : 2*N+1≠0)
  rw [inv_mul_cancel₀ hDen,one_pow]

/-- Exact full symbol identity; the shift includes the negative modes of every factor. -/
theorem dirichletProductKernel_eq_shiftedSymbol (m N : ℕ) (t : Boundary) :
    dirichletProductKernel m N t=
      shiftedPolynomialSymbol (dirichletProductPolynomial m N) (dirichletProductShift m N) t := by
  rw [shiftedPolynomialSymbol,dirichletProductPolynomial,Polynomial.eval_smul,
    Polynomial.eval_mul,Polynomial.eval_pow,centeredDirichletPolynomial_eval,
    centeredDirichletPolynomial_eval,smul_eq_mul,dirichletProductShift,pow_add,pow_mul]
  dsimp only [dirichletProductKernel,centeredDirichlet]
  rw [div_pow,mul_pow]
  ring

theorem continuous_dirichletProductKernel (m N : ℕ) : Continuous (dirichletProductKernel m N) :=
  (continuous_centeredDirichlet ((m+2)*N)).mul
    (((continuous_centeredDirichlet N).div_const _).pow m)

theorem norm_centeredDirichlet_denominator (N : ℕ) :
    ‖((2*N+1 : ℕ) : ℂ)‖=2*(N : ℝ)+1 := by
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using!
    (Complex.norm_natCast (2*N+1))

theorem norm_centeredDirichlet_normalized_le_one (N : ℕ) (t : Boundary) :
    ‖centeredDirichlet N t/((2*N+1 : ℕ) : ℂ)‖≤1 := by
  rw [norm_div,norm_centeredDirichlet_denominator]
  exact (div_le_one (by positivity)).mpr (norm_centeredDirichlet_le N t)

/-- Peak height is proportional to N, with a constant depending only on the finite smoothing order. -/
theorem norm_dirichletProductKernel_le (m N : ℕ) (hN : 0<N) (t : Boundary) :
    ‖dirichletProductKernel m N t‖≤(2*(m : ℝ)+5)*(N : ℝ) := by
  rw [dirichletProductKernel,norm_mul,norm_pow]
  calc
    _ ≤ (2*(((m+2)*N : ℕ) : ℝ)+1)*1^m :=
      mul_le_mul (norm_centeredDirichlet_le _ t)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_centeredDirichlet_normalized_le_one N t) m)
        (pow_nonneg (norm_nonneg _) m) (by positivity)
    _ ≤ _ := by
      simp only [one_pow,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have hNR : (1 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
      nlinarith

/-- The normalized short factor gains one inverse distance and one inverse scale. -/
theorem norm_centeredDirichlet_normalized_real_le (N : ℕ) (hN : 0<N) (x : ℝ)
    (hx : 0 < |x|) (hx1 : |x|≤1/2) :
    ‖centeredDirichlet N (x : Boundary)/((2*N+1 : ℕ) : ℂ)‖≤1/((N : ℝ)*|x|) := by
  rw [norm_div,norm_centeredDirichlet_denominator]
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  calc
    _ ≤ (1/(2*|x|))/(2*(N : ℝ)+1) :=
      div_le_div_of_nonneg_right (norm_centeredDirichlet_real_le N x hx hx1) (by positivity)
    _ ≤ _ := by
      rw [div_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos hNR hx]

/-- Arbitrary finite decay order, without differentiating a cutoff or dropping negative frequencies. -/
theorem norm_dirichletProductKernel_real_tail (m N : ℕ) (hN : 0<N) (x : ℝ)
    (hx : 0 < |x|) (hx1 : |x|≤1/2) :
    ‖dirichletProductKernel m N (x : Boundary)‖≤(N : ℝ)/((N : ℝ)*|x|)^(m+1) := by
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  rw [dirichletProductKernel,norm_mul,norm_pow]
  calc
    _ ≤ (1/(2*|x|))*(1/((N : ℝ)*|x|))^m :=
      mul_le_mul (norm_centeredDirichlet_real_le ((m+2)*N) x hx hx1)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_centeredDirichlet_normalized_real_le N hN x hx hx1) m)
        (pow_nonneg (norm_nonneg _) m) (by positivity)
    _ ≤ (1/|x|)*(1/((N : ℝ)*|x|))^m :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hx (by linarith)) (by positivity)
    _ = _ := by
      rw [one_div_pow,pow_succ]
      field_simp

/-- A completely explicit scalar interpolation between the peak and algebraic tail. -/
theorem two_scale_integer_decay_bound (b C S y : ℝ) (k : ℕ)
    (hC : 1≤C) (hS : 0<S) (hy : 0≤y) (hPeak : b≤C*S)
    (hTail : 0<y→b≤S/y^k) : b≤C*S*2^k/(1+y)^k := by
  have hDen : 0<(1+y)^k := pow_pos (by linarith) k
  by_cases hy1 : y≤1
  · apply hPeak.trans
    apply (le_div_iff₀ hDen).mpr
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0≤1+y) (by linarith : 1+y≤2) k) (by positivity)
  · have hyPos : 0<y := lt_of_lt_of_le zero_lt_one (le_of_not_ge hy1)
    apply (hTail hyPos).trans
    apply (div_le_div_iff₀ (pow_pos hyPos k) hDen).mpr
    calc
      S*(1+y)^k ≤ S*(2*y)^k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : 0≤1+y) (by linarith : 1+y≤2*y) k) hS.le
      _ = (S*2^k)*y^k := by rw [mul_pow]; ring
      _ ≤ (C*S*2^k)*y^k := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by nlinarith : S≤C*S) (by positivity)) (by positivity)

/-- Everywhere on the real unit window, the actual kernel has a scale-invariant decaying profile. -/
theorem norm_dirichletProductKernel_real_decay (m N : ℕ) (hN : 0<N) (x : ℝ) (hx : |x|≤1/2) :
    ‖dirichletProductKernel m N (x : Boundary)‖≤
      (2*(m : ℝ)+5)*(N : ℝ)*2^(m+1)/(1+(N : ℝ)*|x|)^(m+1) := by
  exact two_scale_integer_decay_bound _ _ _ _ _ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    (Nat.cast_pos.mpr hN) (by positivity) (norm_dirichletProductKernel_le m N hN _)
    (fun hy => norm_dirichletProductKernel_real_tail m N hN x
      (by nlinarith [abs_nonneg x,Nat.cast_nonneg (α := ℝ) N]) hx)

/-- Exact scalar decay integration on a bounded positive interval. -/
theorem integral_one_add_mul_rpow_neg_le (S q T : ℝ) (hS : 0<S) (hq : 1<q) (hT : 0≤T) :
    IntervalIntegrable (fun x => (1+S*x)^(-q)) volume 0 T ∧
      (∫ x in (0 : ℝ)..T,(1+S*x)^(-q))≤1/(S*(q-1)) := by
  have hCont : ContinuousOn (fun x : ℝ => (1+S*x)^(-q)) (uIcc 0 T) := by
    apply (continuous_const.add (continuous_const.mul continuous_id)).continuousOn.rpow_const
    intro x hx
    rw [uIcc_of_le hT] at hx
    left
    change 1+S*x≠0
    exact ne_of_gt (by nlinarith [mul_nonneg hS.le hx.1])
  have hUpper : 1≤S*T+1 := by nlinarith
  have hAway : (0 : ℝ)∉uIcc 1 (S*T+1) := by
    rw [uIcc_of_le hUpper]
    intro h
    linarith [h.1]
  have hFormula := integral_rpow (a := (1 : ℝ)) (b := S*T+1) (r := -q)
    (Or.inr ⟨by linarith,hAway⟩)
  have hBound : ((S*T+1)^(-q+1)-1)/(-q+1)≤1/(q-1) := by
    have hEq : ((S*T+1)^(-q+1)-1)/(-q+1)=(1-(S*T+1)^(-q+1))/(q-1) := by
      have hq0 : q-1≠0 := by linarith
      have hq1 : -q+1≠0 := by linarith
      field_simp
      ring
    rw [hEq]
    apply div_le_div_of_nonneg_right _ (by linarith : 0≤q-1)
    linarith [Real.rpow_nonneg (by linarith : 0≤S*T+1) (-q+1)]
  refine ⟨hCont.intervalIntegrable,?_⟩
  calc
    _ = ∫ x in (0 : ℝ)..T,(S*x+1)^(-q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [add_comm 1]
    _ = S⁻¹*(∫ x in (1 : ℝ)..(S*T+1),x^(-q)) := by
      simpa only [mul_zero,zero_add,smul_eq_mul] using!
        (intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := T)
          (fun x : ℝ => x^(-q)) hS.ne' 1)
    _ = S⁻¹*(((S*T+1)^(-q+1)-1)/(-q+1)) := by rw [hFormula,Real.one_rpow]
    _ ≤ S⁻¹*(1/(q-1)) := mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr hS.le)
    _ = _ := by simp only [one_div,mul_inv_rev]; ring

/-- Even scalar decay on a complete real period, with the correct scale factor. -/
theorem integral_one_add_mul_abs_rpow_neg_le (S q T : ℝ) (hS : 0<S) (hq : 1<q) (hT : 0≤T) :
    IntervalIntegrable (fun x => (1+S*|x|)^(-q)) volume (-T) T ∧
      (∫ x in (-T)..T,(1+S*|x|)^(-q))≤2/(S*(q-1)) := by
  have hCont : Continuous (fun x : ℝ => (1+S*|x|)^(-q)) := by
    apply (continuous_const.add (continuous_const.mul continuous_abs)).rpow_const
    intro x
    left
    change 1+S*|x|≠0
    exact ne_of_gt (by nlinarith [mul_nonneg hS.le (abs_nonneg x)])
  have hNeg : (∫ x in (-T)..0,(1+S*|x|)^(-q))=(∫ x in (0 : ℝ)..T,(1+S*x)^(-q)) := by
    have he : (∫ x in (-T)..0,(1+S*|x|)^(-q))=
        ∫ x in (0 : ℝ)..T,(1+S*|-x|)^(-q) := by
      simpa only [neg_zero] using! (intervalIntegral.integral_comp_neg
        (a := (0 : ℝ)) (b := T) (fun x : ℝ => (1+S*|x|)^(-q))).symm
    rw [he]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hT] at hx
    dsimp only
    rw [abs_neg,abs_of_nonneg hx.1]
  have hPos : (∫ x in (0 : ℝ)..T,(1+S*|x|)^(-q))=(∫ x in (0 : ℝ)..T,(1+S*x)^(-q)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hT] at hx
    dsimp only
    rw [abs_of_nonneg hx.1]
  refine ⟨hCont.intervalIntegrable _ _,?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hCont.intervalIntegrable (-T) 0)
    (hCont.intervalIntegrable 0 T),hNeg,hPos]
  have h := (integral_one_add_mul_rpow_neg_le S q T hS hq hT).2
  calc
    _ ≤ 1/(S*(q-1))+1/(S*(q-1)) := add_le_add h h
    _ = _ := by ring

theorem norm_dirichletProductKernel_rpow_real_decay (m N : ℕ) (hN : 0<N)
    (p : ℝ) (hp : 0<p) (x : ℝ) (hx : |x|≤1/2) :
    ‖dirichletProductKernel m N (x : Boundary)‖^p≤
      ((2*(m : ℝ)+5)*2^(m+1))^p*(N : ℝ)^p*
        (1+(N : ℝ)*|x|)^(-(((m+1 : ℕ) : ℝ)*p)) := by
  have hBase : 0≤1+(N : ℝ)*|x| := by positivity
  calc
    _ ≤ ((2*(m : ℝ)+5)*(N : ℝ)*2^(m+1)/(1+(N : ℝ)*|x|)^(m+1))^p :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_dirichletProductKernel_real_decay m N hN x hx) hp.le
    _ = _ := by
      rw [show (2*(m : ℝ)+5)*(N : ℝ)*2^(m+1)=((2*(m : ℝ)+5)*2^(m+1))*(N : ℝ) by ring,
        Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (Nat.cast_nonneg N),
        ← Real.rpow_natCast_mul hBase,Real.rpow_neg hBase,div_eq_mul_inv]

/-- Explicit finite-order Lp localization constant, independent of the positive scale N. -/
def dirichletProductLpConstant (m : ℕ) (p : ℝ) : ℝ :=
  2*((2*(m : ℝ)+5)*2^(m+1))^p/((((m+1 : ℕ) : ℝ)*p)-1)

theorem dirichletProductLpConstant_pos (m : ℕ) (p : ℝ)
    (hOrder : 1<((m+1 : ℕ) : ℝ)*p) : 0<dirichletProductLpConstant m p := by
  unfold dirichletProductLpConstant
  positivity

/-- The genuine signed product kernel satisfies the sharp scale N^(p−1).
Finite smoothing order can depend on p; no analytic projection or Jensen step is used. -/
theorem integral_dirichletProductKernel_rpow_le (m N : ℕ) (hN : 0<N)
    (p : ℝ) (hp : 0<p) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    Integrable (fun t => ‖dirichletProductKernel m N t‖^p) circleMeasure ∧
      (∫ t,‖dirichletProductKernel m N t‖^p ∂circleMeasure)≤
        dirichletProductLpConstant m p*(N : ℝ)^(p-1) := by
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  let q : ℝ := ((m+1 : ℕ) : ℝ)*p
  let D : ℝ := ((2*(m : ℝ)+5)*2^(m+1))^p*(N : ℝ)^p
  have hD : 0≤D := by dsimp only [D]; positivity
  have hCont : Continuous (fun t => ‖dirichletProductKernel m N t‖^p) :=
    (continuous_dirichletProductKernel m N).norm.rpow_const (fun _ => Or.inr hp.le)
  have hRealCont : Continuous (fun x : ℝ => ‖dirichletProductKernel m N (x : Boundary)‖^p) :=
    hCont.comp QuotientAddGroup.continuous_mk
  have hProfile := integral_one_add_mul_abs_rpow_neg_le (N : ℝ) q (1/2) hNR hOrder (by norm_num)
  have hHaar : (∫ t,‖dirichletProductKernel m N t‖^p ∂circleMeasure)=
      ∫ x in (-(1/2 : ℝ))..(1/2),‖dirichletProductKernel m N (x : Boundary)‖^p := by
    have hμ : circleMeasure=(volume : Measure Boundary) := by
      simpa only [ENNReal.ofReal_one,one_smul] using
        (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
    rw [hμ]
    symm
    convert AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1/2 : ℝ))
      (fun t => ‖dirichletProductKernel m N t‖^p) using 1; norm_num
  refine ⟨hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  calc
    _ = ∫ x in (-(1/2 : ℝ))..(1/2),‖dirichletProductKernel m N (x : Boundary)‖^p := hHaar
    _ ≤ ∫ x in (-(1/2 : ℝ))..(1/2),D*(1+(N : ℝ)*|x|)^(-q) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hRealCont.intervalIntegrable _ _) (hProfile.1.const_mul D)
      intro x hx
      exact norm_dirichletProductKernel_rpow_real_decay m N hN p hp x (abs_le.mpr hx)
    _ = D*(∫ x in (-(1/2 : ℝ))..(1/2),(1+(N : ℝ)*|x|)^(-q)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ D*(2/((N : ℝ)*(q-1))) := mul_le_mul_of_nonneg_left hProfile.2 hD
    _ = _ := by
      dsimp only [D,q,dirichletProductLpConstant]
      rw [Real.rpow_sub hNR,Real.rpow_one]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- Every positive p admits a concrete finite smoothing order and a uniform scale bound. -/
theorem exists_dirichletProduct_low_p_bound (p : ℝ) (hp : 0<p) :
    ∃ m : ℕ, ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N→
      (∫ t,‖dirichletProductKernel m N t‖^p ∂circleMeasure)≤C*(N : ℝ)^(p-1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/p)
  have hOrder : 1<((m+1 : ℕ) : ℝ)*p := by
    have h := (div_lt_iff₀ hp).mp hm
    push_cast
    nlinarith
  exact ⟨m,dirichletProductLpConstant m p,dirichletProductLpConstant_pos m p hOrder,
    fun N hN => (integral_dirichletProductKernel_rpow_le m N hN p hp hOrder).2⟩

/-- The flat plateau also includes the negative frequencies; this is not the analytic part of a kernel. -/
theorem dirichletProductPolynomial_coeff_negative_plateau (m N k : ℕ) (hk : k≤2*N) :
    (dirichletProductPolynomial m N).coeff (dirichletProductShift m N-k)=1 := by
  have hkS : k≤dirichletProductShift m N := by
    dsimp only [dirichletProductShift]
    nlinarith
  have hSub := Nat.sub_add_cancel hkS
  have hDeg : ((centeredDirichletPolynomial N)^m).natDegree≤dirichletProductShift m N-k := by
    have h := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
      (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
    dsimp only [dirichletProductShift] at hSub ⊢
    nlinarith
  have hUpper : dirichletProductShift m N-k≤2*((m+2)*N) := by
    dsimp only [dirichletProductShift] at hSub ⊢
    nlinarith
  rw [dirichletProductPolynomial,Polynomial.coeff_smul,
    centeredDirichletPolynomial_mul_coeff_flat _ _ _ hDeg hUpper,
    Polynomial.eval_pow,centeredDirichletPolynomial_eval_one,smul_eq_mul,← mul_pow]
  have hDen : (((2*N+1 : ℕ) : ℂ))≠0 := by exact_mod_cast (by omega : 2*N+1≠0)
  rw [inv_mul_cancel₀ hDen,one_pow]

/-- The actual centered mask vanishes beyond its finite localization window. -/
theorem dirichletProductPolynomial_coeff_zero (m N k : ℕ) (hk : dirichletProductShift m N<k) :
    (dirichletProductPolynomial m N).coeff (dirichletProductShift m N+k)=0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((dirichletProductPolynomial_natDegree_le m N).trans_lt (by omega))

/-- A dimension-free finite Schatten localization constant for the literal product mask. -/
def dirichletProductSchurConstant (m : ℕ) (p : ℝ) : ℝ :=
  dirichletProductLpConstant m p*(6*(m : ℝ)+8)^(1-p)

theorem dirichletProductSchurConstant_pos (m : ℕ) (p : ℝ)
    (hOrder : 1<((m+1 : ℕ) : ℝ)*p) : 0<dirichletProductSchurConstant m p := by
  unfold dirichletProductSchurConstant
  exact mul_pos (dirichletProductLpConstant_pos m p hOrder) (Real.rpow_pos_of_pos (by positivity) _)

/-- Actual uniform low-p Schur localization on a full finite window. The constant
is independent of the positive scale, both dimensions and the operator. -/
theorem dirichletProductSchur_schattenNorm_rpow_le (m N r c : ℕ) (hN : 0<N)
    (hSize : r+c≤2*dirichletProductShift m N+2)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelSchurOffset r c (dirichletProductShift m N)
      (dirichletProductPolynomial m N) A)^p≤dirichletProductSchurConstant m p*schattenNorm p A^p := by
  let sample : ℕ := 3*dirichletProductShift m N+2
  have hSamplePos : 0<sample := by dsimp only [sample]; omega
  let : NeZero sample := ⟨Nat.ne_of_gt hSamplePos⟩
  have hSampleSize : dirichletProductShift m N+r+c≤sample := by dsimp only [sample]; omega
  have hDegree : (dirichletProductPolynomial m N).natDegree<sample :=
    (dirichletProductPolynomial_natDegree_le m N).trans_lt (by dsimp only [sample]; omega)
  have hSchur := polynomialHankelSchurOffset_schattenNorm_rpow_le_symbol_integral
    sample r c (dirichletProductShift m N) hSampleSize (dirichletProductPolynomial m N) hDegree A p hp hp1
  have hIntegral : (∫ t,‖shiftedPolynomialSymbol (dirichletProductPolynomial m N)
      (dirichletProductShift m N) t‖^p ∂circleMeasure)=
        ∫ t,‖dirichletProductKernel m N t‖^p ∂circleMeasure := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by dsimp only; rw [dirichletProductKernel_eq_shiftedSymbol]
  rw [hIntegral] at hSchur
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  have hSampleBound : (sample : ℝ)≤(6*(m : ℝ)+8)*(N : ℝ) := by
    dsimp only [sample,dirichletProductShift]
    push_cast
    have hNR1 : (1 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hPow : (sample : ℝ)^(1-p)≤((6*(m : ℝ)+8)*(N : ℝ))^(1-p) :=
    Real.rpow_le_rpow (Nat.cast_nonneg sample) hSampleBound (by linarith)
  have hLp := (integral_dirichletProductKernel_rpow_le m N hN p hp hOrder).2
  apply hSchur.trans
  calc
    _ ≤ ((6*(m : ℝ)+8)*(N : ℝ))^(1-p)*
        (dirichletProductLpConstant m p*(N : ℝ)^(p-1))*schattenNorm p A^p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hPow hLp (integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (Reduction.schattenNorm_nonneg p A) _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hNR.le]
      have hCancel : (N : ℝ)^(1-p)*(N : ℝ)^(p-1)=1 := by
        rw [← Real.rpow_add hNR,show 1-p+(p-1)=0 by ring,Real.rpow_zero]
      dsimp only [dirichletProductSchurConstant]
      calc
        _ = dirichletProductLpConstant m p*(6*(m : ℝ)+8)^(1-p)*
            ((N : ℝ)^(1-p)*(N : ℝ)^(p-1))*schattenNorm p A^p := by ring
        _ = _ := by rw [hCancel,mul_one]

/-- The actual low-pass map is exactly the identity on its stated plateau, including empty dimensions. -/
theorem dirichletProductSchur_eq_self (m N r c : ℕ) (hSize : r+c≤2*N+2)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchurOffset r c (dirichletProductShift m N) (dirichletProductPolynomial m N) A=A := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [polynomialHankelSchurOffset_single_apply,Nat.add_assoc,
    dirichletProductPolynomial_coeff_plateau m N (i.val+j.val) (by omega),one_mul]

/-- Literal matrix entries vanish outside the localization window. -/
theorem dirichletProductSchur_single_apply_zero (m N r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (i : Fin r) (j : Fin c) (hij : dirichletProductShift m N < i.val+j.val) :
    polynomialHankelSchurOffset r c (dirichletProductShift m N) (dirichletProductPolynomial m N) A
      (EuclideanSpace.single j (1 : ℂ)) i=0 := by
  rw [polynomialHankelSchurOffset_single_apply,Nat.add_assoc,dirichletProductPolynomial_coeff_zero m N _ hij,zero_mul]

/-- For each 0<p≤1, one finite smoothing order works uniformly for all positive scales,
all full-window dimensions and every actual finite operator. -/
theorem exists_uniform_dirichletProductSchur_bound (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ m : ℕ,∃ C : ℝ,0 < C ∧ ∀ N r c : ℕ,0 < N → r+c≤2*dirichletProductShift m N+2 →
      ∀ A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r),
        schattenNorm p (polynomialHankelSchurOffset r c (dirichletProductShift m N)
          (dirichletProductPolynomial m N) A)^p≤C*schattenNorm p A^p := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/p)
  have hOrder : 1<((m+1 : ℕ) : ℝ)*p := by
    have h := (div_lt_iff₀ hp).mp hm
    push_cast
    nlinarith
  exact ⟨m,dirichletProductSchurConstant m p,dirichletProductSchurConstant_pos m p hOrder,
    fun N r c hN hSize A => dirichletProductSchur_schattenNorm_rpow_le m N r c hN hSize A p hp hp1 hOrder⟩

end TTO.Paper.Proved
