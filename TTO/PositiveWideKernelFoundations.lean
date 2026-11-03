/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ThinWideBandFoundations
public import TTO.ThinWideSchurFoundations

/-! Actual nonnegative-frequency generating polynomials and division-free edge identities.
Their coefficients are the previously defined full signed-kernel coefficients. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The exact normalized short smoothing polynomial. -/
def wideSmoothingPolynomial (m N : ℕ) : Polynomial ℂ :=
  ((((2*N+1 : ℕ) : ℂ)⁻¹)^m) • (centeredDirichletPolynomial N)^m

/-- The actual positive-frequency generating kernel, including coefficient zero. -/
def positiveWideKernel (m N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (wideDirichletProductShift m N+1),
    Polynomial.monomial k (wideDirichletPositiveWeight m N k)

/-- The actual positive band generating polynomial. -/
def positiveWideBandKernel (m N N' : ℕ) : Polynomial ℂ :=
  positiveWideKernel m N'-positiveWideKernel m N

theorem positiveWideKernel_coeff (m N k : ℕ) :
    (positiveWideKernel m N).coeff k = wideDirichletPositiveWeight m N k := by
  classical
  simp only [positiveWideKernel,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq',Finset.mem_range]
  by_cases hk : k ≤ wideDirichletProductShift m N
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega),wideDirichletPositiveWeight,
      wideDirichletProductPolynomial_coeff_zero m N k (by omega)]

theorem positiveWideKernel_natDegree_le (m N : ℕ) :
    (positiveWideKernel m N).natDegree ≤ wideDirichletProductShift m N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [positiveWideKernel_coeff,wideDirichletPositiveWeight,
    wideDirichletProductPolynomial_coeff_zero m N k hk]

theorem positiveWideBandKernel_coeff (m N N' k : ℕ) :
    (positiveWideBandKernel m N N').coeff k =
      wideDirichletPositiveWeight m N' k-wideDirichletPositiveWeight m N k := by
  rw [positiveWideBandKernel,Polynomial.coeff_sub,positiveWideKernel_coeff,positiveWideKernel_coeff]

/-- These are exactly the multipliers of the actual thin-band polynomial, not new masks. -/
theorem thinWideBandPolynomial_coeff_eq_positiveKernel (m N N' : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    (thinWideBandPolynomial m N N' P).coeff k = (positiveWideBandKernel m N N').coeff k*P.coeff k := by
  rw [positiveWideBandKernel_coeff,thinWideBandPolynomial_coeff]

/-- Finite geometric identity as an equality of actual polynomials, with no division. -/
theorem one_sub_X_mul_centeredDirichletPolynomial (N : ℕ) :
    (1-Polynomial.X)*centeredDirichletPolynomial N = 1-Polynomial.X^(2*N+1) := by
  have h := geom_sum_mul (Polynomial.X : Polynomial ℂ) (2*N+1)
  dsimp only [centeredDirichletPolynomial]
  linear_combination -h

theorem wideDirichletProductPolynomial_eq_smoothing (m N : ℕ) :
    wideDirichletProductPolynomial m N =
      centeredDirichletPolynomial ((100*m+2)*N)*wideSmoothingPolynomial m N := by
  rw [wideDirichletProductPolynomial,wideSmoothingPolynomial,mul_smul_comm]

theorem wideSmoothingPolynomial_natDegree_le (m N : ℕ) :
    (wideSmoothingPolynomial m N).natDegree ≤ 2*m*N := by
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
  have h := Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N)
  nlinarith

theorem wideSmoothingPolynomial_eval (m N : ℕ) (z : ℂ) :
    (wideSmoothingPolynomial m N).eval z =
      ((∑ j ∈ Finset.range (2*N+1),z^j)/((2*N+1 : ℕ) : ℂ))^m := by
  rw [wideSmoothingPolynomial,Polynomial.eval_smul,Polynomial.eval_pow,
    centeredDirichletPolynomial_eval,smul_eq_mul,div_pow]
  ring

/-- The original full signed polynomial has an exact geometric edge recurrence. -/
theorem one_sub_X_mul_wideDirichletProductPolynomial (m N : ℕ) :
    (1-Polynomial.X)*wideDirichletProductPolynomial m N =
      (1-Polynomial.X^(2*((100*m+2)*N)+1))*wideSmoothingPolynomial m N := by
  rw [wideDirichletProductPolynomial_eq_smoothing,← mul_assoc,
    one_sub_X_mul_centeredDirichletPolynomial]

/-- Division-free generating identity for the actual positive Laurent coefficients. -/
theorem one_sub_X_mul_positiveWideKernel (m N : ℕ) :
    (1-Polynomial.X)*positiveWideKernel m N =
      1-Polynomial.X^(thinWideBandStart m N)*wideSmoothingPolynomial m N := by
  have hFull := one_sub_X_mul_wideDirichletProductPolynomial m N
  have hShift : 2*((100*m+2)*N)+1 = wideDirichletProductShift m N+thinWideBandStart m N := by
    dsimp only [wideDirichletProductShift,thinWideBandStart]
    ring
  have hDeg : (wideSmoothingPolynomial m N).natDegree ≤ wideDirichletProductShift m N := by
    apply (wideSmoothingPolynomial_natDegree_le m N).trans
    dsimp only [wideDirichletProductShift]
    nlinarith
  have hStart : 0 < thinWideBandStart m N := by dsimp only [thinWideBandStart]; omega
  ext k
  cases k with
  | zero =>
    simp only [sub_mul,one_mul,Polynomial.coeff_sub,Polynomial.coeff_X_mul_zero,
      positiveWideKernel_coeff,wideDirichletPositiveWeight]
    rw [wideDirichletProductPolynomial_coeff_plateau m N 0 (by omega)]
    simp only [Polynomial.coeff_one_zero,Polynomial.coeff_X_pow_mul',Nat.not_le.mpr hStart,
      ite_false,sub_zero]
  | succ k =>
    have hCoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff (wideDirichletProductShift m N+(k+1))) hFull
    simp only [sub_mul,one_mul,Polynomial.coeff_sub] at hCoeff ⊢
    rw [show wideDirichletProductShift m N+(k+1) = (wideDirichletProductShift m N+k)+1 by omega,
      Polynomial.coeff_X_mul] at hCoeff
    simp only [Nat.add_assoc] at hCoeff
    have hOne : (1 : Polynomial ℂ).coeff (k+1) = 0 := by
      rw [Polynomial.coeff_one]
      exact ite_eq_right (by omega)
    rw [Polynomial.coeff_X_mul,positiveWideKernel_coeff,positiveWideKernel_coeff,
      hOne,Polynomial.coeff_X_pow_mul']
    have hQzero : (wideSmoothingPolynomial m N).coeff (wideDirichletProductShift m N+(k+1)) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hDeg.trans_lt (by omega))
    rw [hQzero,Polynomial.coeff_X_pow_mul',hShift] at hCoeff
    dsimp only [wideDirichletPositiveWeight]
    by_cases hk : thinWideBandStart m N ≤ k+1
    · rw [ite_eq_left hk]
      rw [ite_eq_left (by omega : wideDirichletProductShift m N+thinWideBandStart m N ≤
        wideDirichletProductShift m N+(k+1))] at hCoeff
      simpa only [Nat.add_sub_add_left] using hCoeff
    · rw [ite_eq_right hk]
      rw [ite_eq_right (by omega : ¬wideDirichletProductShift m N+thinWideBandStart m N ≤
        wideDirichletProductShift m N+(k+1))] at hCoeff
      exact hCoeff

/-- The short smoothing factor also has its exact division-free edge formula. -/
theorem one_sub_X_pow_mul_wideSmoothingPolynomial (m N : ℕ) :
    (1-Polynomial.X)^m*wideSmoothingPolynomial m N =
      ((((2*N+1 : ℕ) : ℂ)⁻¹)^m) • (1-Polynomial.X^(2*N+1))^m := by
  rw [wideSmoothingPolynomial,mul_smul_comm,← mul_pow,one_sub_X_mul_centeredDirichletPolynomial]

/-- The constant term cancels in the actual band, leaving its two precise edges. -/
theorem one_sub_X_mul_positiveWideBandKernel (m N N' : ℕ) :
    (1-Polynomial.X)*positiveWideBandKernel m N N' =
      Polynomial.X^(thinWideBandStart m N)*wideSmoothingPolynomial m N-
      Polynomial.X^(thinWideBandStart m N')*wideSmoothingPolynomial m N' := by
  rw [positiveWideBandKernel,mul_sub,one_sub_X_mul_positiveWideKernel,one_sub_X_mul_positiveWideKernel]
  ring

/-- Complete division-free band identity, valid also at X=1 and at zero scale. -/
theorem one_sub_X_pow_mul_positiveWideBandKernel (m N N' : ℕ) :
    (1-Polynomial.X)^(m+1)*positiveWideBandKernel m N N' =
      ((((2*N+1 : ℕ) : ℂ)⁻¹)^m) •
        (Polynomial.X^(thinWideBandStart m N)*(1-Polynomial.X^(2*N+1))^m)-
      ((((2*N'+1 : ℕ) : ℂ)⁻¹)^m) •
        (Polynomial.X^(thinWideBandStart m N')*(1-Polynomial.X^(2*N'+1))^m) := by
  rw [pow_succ,mul_assoc,one_sub_X_mul_positiveWideBandKernel,mul_sub]
  calc
    _ = Polynomial.X^(thinWideBandStart m N)*((1-Polynomial.X)^m*wideSmoothingPolynomial m N)-
        Polynomial.X^(thinWideBandStart m N')*((1-Polynomial.X)^m*wideSmoothingPolynomial m N') := by ring
    _ = _ := by rw [one_sub_X_pow_mul_wideSmoothingPolynomial,one_sub_X_pow_mul_wideSmoothingPolynomial,
      mul_smul_comm,mul_smul_comm]

/-- Evaluation of the genuine positive kernel identity at ANY complex point. -/
theorem positiveWideKernel_geometric_eval (m N : ℕ) (z : ℂ) :
    (1-z)*(positiveWideKernel m N).eval z = 1-z^(thinWideBandStart m N)*
      ((∑ j ∈ Finset.range (2*N+1),z^j)/((2*N+1 : ℕ) : ℂ))^m := by
  have h := congrArg (Polynomial.eval z) (one_sub_X_mul_positiveWideKernel m N)
  simpa only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,
    Polynomial.eval_pow,wideSmoothingPolynomial_eval] using h

/-- Literal two-edge evaluation of the actual band; no denominator 1-z is introduced. -/
theorem positiveWideBandKernel_geometric_eval (m N N' : ℕ) (z : ℂ) :
    (1-z)^(m+1)*(positiveWideBandKernel m N N').eval z =
      z^(thinWideBandStart m N)*((1-z^(2*N+1))/((2*N+1 : ℕ) : ℂ))^m-
      z^(thinWideBandStart m N')*((1-z^(2*N'+1))/((2*N'+1 : ℕ) : ℂ))^m := by
  have h := congrArg (Polynomial.eval z) (one_sub_X_pow_mul_positiveWideBandKernel m N N')
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,
    Polynomial.eval_pow,Polynomial.eval_smul,smul_eq_mul] at h
  rw [h]
  rw [div_pow,div_pow,div_eq_mul_inv,div_eq_mul_inv]
  ring

/-- A raw complex edge bound keeps the full radial power before any scale estimate. -/
theorem positiveWideBandKernel_chord_norm_bound (m N N' : ℕ) (z : ℂ) :
    ‖1-z‖^(m+1)*‖(positiveWideBandKernel m N N').eval z‖ ≤
      ‖z‖^(thinWideBandStart m N)*((1+‖z‖^(2*N+1))/(2*(N : ℝ)+1))^m+
      ‖z‖^(thinWideBandStart m N')*((1+‖z‖^(2*N'+1))/(2*(N' : ℝ)+1))^m := by
  have hEdge (T : ℕ) : ‖z^(thinWideBandStart m T)*((1-z^(2*T+1))/((2*T+1 : ℕ) : ℂ))^m‖ ≤
      ‖z‖^(thinWideBandStart m T)*((1+‖z‖^(2*T+1))/(2*(T : ℝ)+1))^m := by
    rw [norm_mul,norm_pow,norm_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div,norm_centeredDirichlet_denominator]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [norm_one,norm_pow] using norm_sub_le (1 : ℂ) (z^(2*T+1))
  calc
    _ = ‖(1-z)^(m+1)*(positiveWideBandKernel m N N').eval z‖ := by rw [norm_mul,norm_pow]
    _ = _ := congrArg norm (positiveWideBandKernel_geometric_eval m N N' z)
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (hEdge N) (hEdge N'))

/-- Moving radially along a unit direction loses at most a factor two in its chord. -/
theorem unit_chord_le_twice_radial (t : ℝ) (ht : 0 ≤ t) (u : ℂ) (hu : ‖u‖ = 1) :
    ‖1-u‖ ≤ 2*‖1-(t : ℂ)*u‖ := by
  have hRev := abs_norm_sub_norm_le ((t : ℂ)*u) (1 : ℂ)
  rw [norm_sub_rev ((t : ℂ)*u) 1] at hRev
  have hReal : |t-1| ≤ ‖1-(t : ℂ)*u‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,hu,mul_one,norm_one] using hRev
  have hFactor : (t : ℂ)*u-u = ((t-1 : ℝ) : ℂ)*u := by push_cast; ring
  have hSmall : ‖(t : ℂ)*u-u‖ = |t-1| := by
    rw [hFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,hu,mul_one]
  have hTri := norm_add_le (1-(t : ℂ)*u) ((t : ℂ)*u-u)
  rw [show 1-(t : ℂ)*u+((t : ℂ)*u-u) = 1-u by ring,hSmall] at hTri
  nlinarith

/-- The actual period-one angular denominator bound holds at EVERY nonnegative radius. -/
theorem radial_circle_denominator_lower (t x : ℝ) (ht : 0 ≤ t) (hx : |x| ≤ 1/2) :
    2*|x| ≤ ‖1-(t : ℂ)*fourier (T := 1) 1 (x : Boundary)‖ := by
  have hChord : 4*|x| ≤ ‖fourier (T := 1) 1 (x : Boundary)-1‖ := by
    simpa using circle_chord_lower_real x 0 (by simpa only [sub_zero] using hx)
  have hRad := unit_chord_le_twice_radial t ht (fourier (T := 1) 1 (x : Boundary))
    (by rw [fourier_apply,Circle.norm_coe])
  rw [norm_sub_rev 1 (fourier (T := 1) 1 (x : Boundary))] at hRad
  nlinarith

/-- A fully complex angular far bound, keeping the exact two radial edge powers. -/
theorem positiveWideBandKernel_angular_far (m N N' : ℕ) (t x : ℝ)
    (ht : 0 ≤ t) (hx : 0 < |x|) (hx1 : |x| ≤ 1/2) :
    ‖(positiveWideBandKernel m N N').eval ((t : ℂ)*fourier (T := 1) 1 (x : Boundary))‖ ≤
      (t^(thinWideBandStart m N)*((1+t^(2*N+1))/(2*(N : ℝ)+1))^m+
       t^(thinWideBandStart m N')*((1+t^(2*N'+1))/(2*(N' : ℝ)+1))^m)/(2*|x|)^(m+1) := by
  let z : ℂ := (t : ℂ)*fourier (T := 1) 1 (x : Boundary)
  have hz : ‖z‖ = t := by
    simp only [z,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,
      fourier_apply,Circle.norm_coe,mul_one]
  have hRaw := positiveWideBandKernel_chord_norm_bound m N N' z
  rw [hz] at hRaw
  have hDen := radial_circle_denominator_lower t x ht hx1
  have hPow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*|x|) hDen (m+1)
  have hBound := (mul_le_mul_of_nonneg_right hPow (norm_nonneg ((positiveWideBandKernel m N N').eval z))).trans hRaw
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2*|x|)^(m+1))).mpr
  calc
    _ = (2*|x|)^(m+1)*‖(positiveWideBandKernel m N N').eval z‖ := by ring
    _ ≤ _ := hBound

/-- The inward radius used only for the polynomial kernel deformation. -/
def positiveKernelRadius (N : ℕ) : ℝ := 1-4/(N : ℝ)

theorem positiveKernelRadius_bounds (N : ℕ) (hN : 10 ≤ N) :
    3/5 ≤ positiveKernelRadius N ∧ positiveKernelRadius N < 1 := by
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hFour : 4/(N : ℝ) ≤ 2/5 := (div_le_iff₀ hNp).mpr (by nlinarith)
  dsimp only [positiveKernelRadius]
  constructor
  · linarith
  · have hPos : (0 : ℝ) < 4/N := div_pos (by norm_num) hNp
    linarith

theorem positiveKernelRadius_neg_log_le (N : ℕ) (hN : 10 ≤ N) :
    -Real.log (positiveKernelRadius N) ≤ 7/(N : ℝ) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < positiveKernelRadius N := by linarith [hBounds.1]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog := Real.one_sub_inv_le_log_of_pos hr
  have hRat : (positiveKernelRadius N)⁻¹-1 ≤ 7/(N : ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    apply (mul_le_mul_iff_right₀ hr).mp
    calc
      _ = (positiveKernelRadius N*(positiveKernelRadius N)⁻¹-positiveKernelRadius N)*(N : ℝ) := by ring
      _ = (1-positiveKernelRadius N)*(N : ℝ) := by rw [mul_inv_cancel₀ hr.ne']
      _ = 4 := by dsimp only [positiveKernelRadius]; field_simp; ring
      _ ≤ _ := by linarith [hBounds.1]
  linarith

/-- Uniform exponential control of every deformation exponent of order m N. -/
theorem positiveKernelRadius_inv_pow_le (m N E : ℕ) (hN : 10 ≤ N)
    (hE : E ≤ 125*(m+1)*N) :
    ((positiveKernelRadius N)^E)⁻¹ ≤ Real.exp (1000*((m : ℝ)+1)) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < positiveKernelRadius N := by linarith [hBounds.1]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hEr : (E : ℝ) ≤ 125*((m : ℝ)+1)*N := by exact_mod_cast hE
  have hExp : (E : ℝ)*(-Real.log (positiveKernelRadius N)) ≤ 1000*((m : ℝ)+1) := by
    calc
      _ ≤ (E : ℝ)*(7/(N : ℝ)) := mul_le_mul_of_nonneg_left (positiveKernelRadius_neg_log_le N hN) (by positivity)
      _ ≤ (125*((m : ℝ)+1)*N)*(7/(N : ℝ)) := mul_le_mul_of_nonneg_right hEr (by positivity)
      _ ≤ _ := by field_simp; nlinarith
  rw [← inv_pow,← Real.exp_log (inv_pos.mpr hr),← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  simpa only [Real.log_inv] using hExp

/-- A deliberately coarse coefficient constant obtained from the proved p=1 Schur estimate. -/
def positiveWideCoefficientConstant (m : ℕ) : ℝ :=
  wideLocalSchurConstant m 1*(|schattenNorm 1
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))|+1)

theorem positiveWideCoefficientConstant_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < positiveWideCoefficientConstant m := by
  apply mul_pos
  · exact wideLocalSchurConstant_pos m 1 (by simp only [mul_one]; exact_mod_cast (show 1 < m+1 by omega))
  · positivity

/-- The positive coefficients are uniformly bounded independently of the scale and frequency. -/
theorem norm_wideDirichletPositiveWeight_le (m N k : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N) :
    ‖wideDirichletPositiveWeight m N k‖ ≤ positiveWideCoefficientConstant m := by
  by_cases hk : k ≤ wideDirichletProductShift m N
  · let A := ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))
    let B := polynomialHankelSchurOffset 1 1 (wideDirichletProductShift m N+k)
      (wideDirichletProductPolynomial m N) A
    have hShape : k+1+1 ≤ 250*m*N := by
      rw [wideDirichletProductShift_eq] at hk
      nlinarith
    have hSp := wide_local_schur_schattenNorm_rpow_le m N N 1 1 k (by omega) le_rfl
      (by omega) hShape A 1 (by norm_num) le_rfl (by simp only [mul_one]; exact_mod_cast (show 1 < m+1 by omega))
    simp only [Real.rpow_one] at hSp
    have hEntry : B (EuclideanSpace.single (0 : Fin 1) (1 : ℂ)) 0 =
        wideDirichletPositiveWeight m N k := by
      dsimp only [B]
      rw [polynomialHankelSchurOffset_single_apply]
      simp only [Fin.val_zero,add_zero,A,ContinuousLinearMap.id_apply,
        PiLp.single_apply,ite_true,mul_one,wideDirichletPositiveWeight]
    have hUnit : ‖EuclideanSpace.single (0 : Fin 1) (1 : ℂ)‖ = 1 := by simp
    calc
      _ = ‖B (EuclideanSpace.single (0 : Fin 1) (1 : ℂ)) 0‖ := congrArg norm hEntry.symm
      _ ≤ ‖B (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖B‖ := by simpa only [hUnit,mul_one] using B.le_opNorm (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
      _ ≤ schattenNorm 1 B := opNorm_le_schattenNorm 1 B (finiteDim_schatten B 1 (by norm_num))
      _ ≤ wideLocalSchurConstant m 1*schattenNorm 1 A := hSp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [le_abs_self (schattenNorm 1 A)])
        (wideLocalSchurConstant_pos m 1 (by simp only [mul_one]; exact_mod_cast (show 1 < m+1 by omega))).le
  · have hZero : wideDirichletPositiveWeight m N k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact (wideDirichletProductPolynomial_natDegree_le m N).trans_lt (by omega)
    rw [hZero,norm_zero]
    exact (positiveWideCoefficientConstant_pos m hm).le

theorem positiveWideBandKernel_coeff_low (m N N' k : ℕ) (hNN' : N ≤ N')
    (hk : k < thinWideBandStart m N) : (positiveWideBandKernel m N N').coeff k = 0 := by
  have hkN : k ≤ (99*m+2)*N := by dsimp only [thinWideBandStart] at hk; omega
  have hkN' : k ≤ (99*m+2)*N' := hkN.trans (Nat.mul_le_mul_left _ hNN')
  rw [positiveWideBandKernel_coeff]
  simp only [wideDirichletPositiveWeight,wideDirichletProductPolynomial_coeff_plateau m N k hkN,
    wideDirichletProductPolynomial_coeff_plateau m N' k hkN',sub_self]

theorem positiveWideBandKernel_natDegree_le (m N N' : ℕ) (hNN' : N ≤ N') :
    (positiveWideBandKernel m N N').natDegree ≤ wideDirichletProductShift m N' := by
  dsimp only [positiveWideBandKernel]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le (positiveWideKernel_natDegree_le m N')
  exact (positiveWideKernel_natDegree_le m N).trans (by
    rw [wideDirichletProductShift_eq,wideDirichletProductShift_eq]
    exact Nat.mul_le_mul_left _ hNN')

theorem norm_positiveWideBandKernel_coeff_le (m N N' k : ℕ) (hm : 1 ≤ m)
    (hN : 10 ≤ N) (hNN' : N ≤ N') :
    ‖(positiveWideBandKernel m N N').coeff k‖ ≤ 2*positiveWideCoefficientConstant m := by
  rw [positiveWideBandKernel_coeff]
  exact (norm_sub_le _ _).trans (by linarith [norm_wideDirichletPositiveWeight_le m N' k hm (hN.trans hNN'),
    norm_wideDirichletPositiveWeight_le m N k hm hN])

/-- Finite coefficient control after a genuine radial deformation; the positive gap is retained. -/
theorem polynomial_deformed_eval_norm_le (P : Polynomial ℂ) (b D : ℕ) (C s r : ℝ) (u : ℂ)
    (hD : P.natDegree ≤ D) (hLow : ∀ k < b,P.coeff k = 0)
    (hCoeff : ∀ k,‖P.coeff k‖ ≤ C) (hC : 0 ≤ C)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hu : ‖u‖ = 1) :
    ‖P.eval (((s/r : ℝ) : ℂ)*u)‖ ≤ ((D : ℝ)+1)*C*s^b*(r^D)⁻¹ := by
  classical
  have hNorm : ‖((s/r : ℝ) : ℂ)*u‖ = s/r := by
    rw [norm_mul,hu,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hs hr.le)]
  rw [Polynomial.eval_eq_sum_range' (n := D+1) (by omega)]
  calc
    _ ≤ ∑ k ∈ Finset.range (D+1),‖P.coeff k*(((s/r : ℝ) : ℂ)*u)^k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (D+1),C*s^b*(r^D)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkb : k < b
      · rw [hLow k hkb,zero_mul,norm_zero]
        positivity
      · have hkD : k ≤ D := by have := Finset.mem_range.mp hk; omega
        have hsp : s^k ≤ s^b := pow_le_pow_of_le_one hs hs1 (by omega)
        have hrp : (r^k)⁻¹ ≤ (r^D)⁻¹ := by
          rw [← inv_pow,← inv_pow]
          exact pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hr1) hkD
        rw [norm_mul,norm_pow,hNorm,div_pow,div_eq_mul_inv]
        simpa only [mul_assoc] using mul_le_mul (hCoeff k)
          (mul_le_mul hsp hrp (by positivity) (by positivity)) (by positivity) hC
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

/-- A coarse positive constant for the deformed near-angle estimate. -/
def positiveWideNearConstant (m : ℕ) : ℝ :=
  500*((m : ℝ)+1)*positiveWideCoefficientConstant m*Real.exp (1000*((m : ℝ)+1))

theorem positiveWideNearConstant_pos (m : ℕ) (hm : 1 ≤ m) : 0 < positiveWideNearConstant m := by
  exact mul_pos (mul_pos (mul_pos (by norm_num) (by positivity))
    (positiveWideCoefficientConstant_pos m hm)) (Real.exp_pos _)

/-- The actual complex deformed band has peak O(N), with its full positive gap factor. -/
theorem positiveWideBandKernel_deformed_near (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ‖(positiveWideBandKernel m N N').eval (((s/positiveKernelRadius N : ℝ) : ℂ)*u)‖ ≤
      positiveWideNearConstant m*(N : ℝ)*s^(thinWideBandStart m N) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < positiveKernelRadius N := by linarith [hBounds.1]
  have hD : wideDirichletProductShift m N' ≤ 125*(m+1)*N := by
    rw [wideDirichletProductShift_eq]
    nlinarith
  have hPeak := polynomial_deformed_eval_norm_le (positiveWideBandKernel m N N')
    (thinWideBandStart m N) (wideDirichletProductShift m N') (2*positiveWideCoefficientConstant m)
    s (positiveKernelRadius N) u (positiveWideBandKernel_natDegree_le m N N' hNN')
    (fun k hk => positiveWideBandKernel_coeff_low m N N' k hNN' hk)
    (fun k => norm_positiveWideBandKernel_coeff_le m N N' k hm hN hNN')
    (by positivity [positiveWideCoefficientConstant_pos m hm]) hs hs1 hr hBounds.2.le hu
  have hPower := positiveKernelRadius_inv_pow_le m N (wideDirichletProductShift m N') hN hD
  have hSize : ((wideDirichletProductShift m N' : ℕ) : ℝ)+1 ≤ 250*((m : ℝ)+1)*N := by
    have hDr : ((wideDirichletProductShift m N' : ℕ) : ℝ) ≤ 125*((m : ℝ)+1)*N := by exact_mod_cast hD
    have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ _ := hPeak
    _ ≤ (250*((m : ℝ)+1)*N)*(2*positiveWideCoefficientConstant m)*
        s^(thinWideBandStart m N)*Real.exp (1000*((m : ℝ)+1)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSize
        (by positivity [positiveWideCoefficientConstant_pos m hm])) (by positivity)) hPower
        (by positivity) (by positivity [positiveWideCoefficientConstant_pos m hm])
    _ = _ := by dsimp only [positiveWideNearConstant]; ring

/-- Pure scalar edge domination retains its numerator power of s. -/
theorem deformed_geometric_edge_bound (a d m : ℕ) (s r v : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hv : 0 < v) :
    (s/r)^a*((1+(s/r)^d)/v)^m ≤ s^a*2^m*(r^(a+d*m))⁻¹/v^m := by
  have hrd : 0 < r^d := pow_pos hr d
  have hNum : 1+(s/r)^d ≤ 2/r^d := by
    apply (le_div_iff₀ hrd).mpr
    rw [div_pow]
    calc
      _ = r^d+s^d := by field_simp
      _ ≤ 2 := by linarith [(show s^d ≤ 1 from pow_le_one₀ hs hs1),(show r^d ≤ 1 from pow_le_one₀ hr.le hr1)]
  calc
    _ ≤ (s/r)^a*((2/r^d)/v)^m := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hNum hv.le) m) (by positivity)
    _ = _ := by rw [pow_add,pow_mul,div_pow,div_pow,div_pow]; field_simp

/-- The sum of the two far-edge constants. -/
def positiveWideFarConstant (m : ℕ) : ℝ := 2*2^m*Real.exp (1000*((m : ℝ)+1))

theorem positiveWideFarConstant_pos (m : ℕ) : 0 < positiveWideFarConstant m := by
  dsimp only [positiveWideFarConstant]
  positivity

/-- Uniform deformed far-angle estimate for the genuine positive-frequency band. -/
theorem positiveWideBandKernel_deformed_far (m N N' : ℕ) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (s x : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : 0 < |x|) (hx1 : |x| ≤ 1/2) :
    ‖(positiveWideBandKernel m N N').eval (((s/positiveKernelRadius N : ℝ) : ℂ)*
      fourier (T := 1) 1 (x : Boundary))‖ ≤
      positiveWideFarConstant m*s^(thinWideBandStart m N)/((N : ℝ)^m*(2*|x|)^(m+1)) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < positiveKernelRadius N := by linarith [hBounds.1]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hEdge (T : ℕ) (hNT : N ≤ T) (hT : 5*T ≤ 6*N) :
      (s/positiveKernelRadius N)^(thinWideBandStart m T)*
        ((1+(s/positiveKernelRadius N)^(2*T+1))/(2*(T : ℝ)+1))^m ≤
        s^(thinWideBandStart m N)*2^m*Real.exp (1000*((m : ℝ)+1))/(N : ℝ)^m := by
    have hE : thinWideBandStart m T+(2*T+1)*m ≤ 125*(m+1)*N := by
      dsimp only [thinWideBandStart]
      nlinarith [Nat.mul_le_mul_left (101*m+2) hT]
    have hPower := positiveKernelRadius_inv_pow_le m N _ hN hE
    have ha : thinWideBandStart m N ≤ thinWideBandStart m T := by
      dsimp only [thinWideBandStart]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hNT) _
    have hsPower : s^(thinWideBandStart m T) ≤ s^(thinWideBandStart m N) :=
      pow_le_pow_of_le_one hs hs1 ha
    have hDen : (N : ℝ)^m ≤ (2*(T : ℝ)+1)^m := by
      apply pow_le_pow_left₀ hNp.le
      have hTr : (N : ℝ) ≤ T := by exact_mod_cast hNT
      linarith
    calc
      _ ≤ s^(thinWideBandStart m T)*2^m*
          (positiveKernelRadius N^(thinWideBandStart m T+(2*T+1)*m))⁻¹/(2*(T : ℝ)+1)^m :=
        deformed_geometric_edge_bound _ _ _ s (positiveKernelRadius N) _ hs hs1 hr hBounds.2.le (by positivity)
      _ ≤ s^(thinWideBandStart m N)*2^m*Real.exp (1000*((m : ℝ)+1))/(N : ℝ)^m := by
        apply div_le_div₀ (by positivity) _ (by positivity) hDen
        exact mul_le_mul (mul_le_mul_of_nonneg_right hsPower (by positivity)) hPower (by positivity) (by positivity)
  have hRaw := positiveWideBandKernel_angular_far m N N' (s/positiveKernelRadius N) x
    (div_nonneg hs hr.le) hx hx1
  calc
    _ ≤ _ := hRaw
    _ ≤ (s^(thinWideBandStart m N)*2^m*Real.exp (1000*((m : ℝ)+1))/(N : ℝ)^m+
          s^(thinWideBandStart m N)*2^m*Real.exp (1000*((m : ℝ)+1))/(N : ℝ)^m)/(2*|x|)^(m+1) := by
      exact div_le_div_of_nonneg_right (add_le_add (hEdge N le_rfl (by omega)) (hEdge N' hNN' hRatio)) (by positivity)
    _ = _ := by dsimp only [positiveWideFarConstant]; field_simp; ring

/-- Near and far bounds combine without dividing by a possibly zero radial gap factor. -/
theorem two_scale_decay_of_peak_tail (b P T y : ℝ) (k : ℕ)
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hy : 0 ≤ y) (hPeak : b ≤ P)
    (hTail : 0 < y → b ≤ T/y^k) : b ≤ (P+T)*2^k/(1+y)^k := by
  have hDen : 0 < (1+y)^k := pow_pos (by linarith) k
  by_cases hy1 : y ≤ 1
  · apply hPeak.trans
    apply (le_div_iff₀ hDen).mpr
    calc
      P*(1+y)^k ≤ P*2^k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) k) hP
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
  · have hyPos : 0 < y := lt_trans zero_lt_one (lt_of_not_ge hy1)
    apply (hTail hyPos).trans
    apply (div_le_div_iff₀ (pow_pos hyPos k) hDen).mpr
    calc
      T*(1+y)^k ≤ T*(2*y)^k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) k) hT
      _ = (T*2^k)*y^k := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by linarith : T ≤ P+T) (by positivity)) (by positivity)

/-- One constant for the genuine deformed positive-band angular localization. -/
def positiveWideDecayConstant (m : ℕ) : ℝ :=
  (positiveWideNearConstant m+positiveWideFarConstant m)*2^(m+1)

theorem positiveWideDecayConstant_pos (m : ℕ) (hm : 1 ≤ m) : 0 < positiveWideDecayConstant m := by
  exact mul_pos (add_pos (positiveWideNearConstant_pos m hm) (positiveWideFarConstant_pos m)) (by positivity)

/-- Actual off-circle localization, uniform in both scales and the full radial parameter. -/
theorem positiveWideBandKernel_deformed_decay (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (s x : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : |x| ≤ 1/2) :
    ‖(positiveWideBandKernel m N N').eval (((s/positiveKernelRadius N : ℝ) : ℂ)*
      fourier (T := 1) 1 (x : Boundary))‖ ≤
      positiveWideDecayConstant m*(N : ℝ)*s^(thinWideBandStart m N)/(1+(N : ℝ)*|x|)^(m+1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNear := positiveWideBandKernel_deformed_near m N N' hm hN hNN' hRatio s hs hs1
    (fourier (T := 1) 1 (x : Boundary)) (by rw [fourier_apply,Circle.norm_coe])
  have hTail (hy : 0 < (N : ℝ)*|x|) :
      ‖(positiveWideBandKernel m N N').eval (((s/positiveKernelRadius N : ℝ) : ℂ)*
        fourier (T := 1) 1 (x : Boundary))‖ ≤
      (positiveWideFarConstant m*(N : ℝ)*s^(thinWideBandStart m N))/((N : ℝ)*|x|)^(m+1) := by
    have hxPos : 0 < |x| := (mul_pos_iff_of_pos_left hNp).mp hy
    have hFar := positiveWideBandKernel_deformed_far m N N' hN hNN' hRatio s x hs hs1 hxPos hx
    calc
      _ ≤ _ := hFar
      _ ≤ positiveWideFarConstant m*s^(thinWideBandStart m N)/((N : ℝ)^m*|x|^(m+1)) := by
        apply div_le_div_of_nonneg_left (by positivity [positiveWideFarConstant_pos m]) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxPos.le (by linarith) (m+1)) (by positivity)
      _ = _ := by rw [mul_pow]; field_simp; simp only [pow_succ]; ring
  have h := two_scale_decay_of_peak_tail _
    (positiveWideNearConstant m*(N : ℝ)*s^(thinWideBandStart m N))
    (positiveWideFarConstant m*(N : ℝ)*s^(thinWideBandStart m N)) ((N : ℝ)*|x|) (m+1)
    (by positivity [positiveWideNearConstant_pos m hm]) (by positivity [positiveWideFarConstant_pos m])
    (by positivity) hNear hTail
  convert h using 1
  dsimp only [positiveWideDecayConstant]
  ring

end TTO.Paper.Proved
