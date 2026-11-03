/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PositiveWideKernelFoundations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Actual inverse falling-factorial polynomial kernels and their endpoint-safe integral formula. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- An ordinary continuous integer Beta moment on the closed unit interval. -/
def integerBetaMoment (q b : ℕ) : ℝ := ∫ s : ℝ in 0..1,s^q*(1-s)^b

theorem integerBetaMoment_succ (q b : ℕ) :
    ((q : ℝ)+1)*integerBetaMoment q (b+1) = ((b : ℝ)+1)*integerBetaMoment (q+1) b := by
  have hu (x : ℝ) : HasDerivAt (fun s : ℝ => (1-s)^(b+1))
      (-((b : ℝ)+1)*(1-x)^b) x := by
    convert! ((hasDerivAt_id x).const_sub 1).pow (b+1) using 1
    simp
    ring
  have hv (x : ℝ) : HasDerivAt (fun s : ℝ => s^(q+1)) (((q : ℝ)+1)*x^q) x := by
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq] using! (hasDerivAt_id x).pow (q+1)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (u := fun s : ℝ => (1-s)^(b+1)) (v := fun s : ℝ => s^(q+1))
    (u' := fun s : ℝ => -((b : ℝ)+1)*(1-s)^b) (v' := fun s : ℝ => ((q : ℝ)+1)*s^q)
    (by fun_prop) (by fun_prop) (fun x _ => hu x) (fun x _ => hv x)
    ((by fun_prop : Continuous (fun s : ℝ => -((b : ℝ)+1)*(1-s)^b)).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun s : ℝ => ((q : ℝ)+1)*s^q)).intervalIntegrable 0 1)
  have hL : (∫ s : ℝ in 0..1,(1-s)^(b+1)*(((q : ℝ)+1)*s^q)) =
      ((q : ℝ)+1)*integerBetaMoment q (b+1) := by
    rw [integerBetaMoment,← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  have hR : (∫ s : ℝ in 0..1,(-((b : ℝ)+1)*(1-s)^b)*s^(q+1)) =
      -((b : ℝ)+1)*integerBetaMoment (q+1) b := by
    rw [integerBetaMoment,← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [hL,hR] at h
  simp only [sub_self,zero_pow (Nat.succ_ne_zero b),zero_pow (Nat.succ_ne_zero q),
    one_pow,zero_mul,mul_zero,sub_zero] at h
  linarith

/-- Exact integer Beta value, proved using polynomial integration by parts only. -/
theorem integerBetaMoment_eq_factorials (q b : ℕ) :
    integerBetaMoment q b = ((q.factorial : ℝ)*(b.factorial : ℝ))/((q+b+1).factorial : ℝ) := by
  induction b generalizing q with
  | zero =>
    simp only [integerBetaMoment,pow_zero,mul_one,integral_pow,
      one_pow,zero_pow (Nat.succ_ne_zero q),sub_zero,Nat.factorial_zero,Nat.cast_one,mul_one,add_zero]
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  | succ b ih =>
    have h := integerBetaMoment_succ q b
    rw [ih] at h
    have hq : (q : ℝ)+1 ≠ 0 := by positivity
    have hf : ((q+b+2).factorial : ℝ) ≠ 0 := by positivity
    have he : q+1+b+1 = q+b+2 := by omega
    rw [he,Nat.factorial_succ q,Nat.cast_mul,Nat.cast_add,Nat.cast_one] at h
    apply (eq_div_iff (by positivity : ((q+(b+1)+1).factorial : ℝ) ≠ 0)).mpr
    rw [show q+(b+1)+1=q+b+2 by omega,Nat.factorial_succ b,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    apply (mul_left_cancel₀ hq)
    rw [← mul_div_assoc] at h
    have hh := (eq_div_iff hf).mp h
    nlinarith [hh]

/-- The normalized integer Beta moment is exactly an inverse falling factorial. -/
theorem integerBetaMoment_div_factorial (q n : ℕ) (hn : 1 ≤ n) :
    integerBetaMoment q (n-1)/((n-1).factorial : ℝ) = 1/((q+n).descFactorial n : ℝ) := by
  rw [integerBetaMoment_eq_factorials,show q+(n-1)+1=q+n by omega]
  have hf : ((n-1).factorial : ℝ) ≠ 0 := by positivity
  have hF : ((q+n).factorial : ℝ) ≠ 0 := by positivity
  have hd : ((q+n).descFactorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : n ≤ q+n)).ne'
  have hNat := Nat.factorial_mul_descFactorial (show n ≤ q+n by omega)
  have hCast : (q.factorial : ℝ)*((q+n).descFactorial n : ℝ) = ((q+n).factorial : ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_right] using hNat)
  field_simp
  nlinarith [hCast]

/-- A uniform quantitative integer Beta estimate, including all zero-degree cases. -/
theorem integerBetaMoment_div_factorial_le (q n N : ℕ) (hn : 1 ≤ n) (hN : 0 < N)
    (hNq : N ≤ q+1) :
    integerBetaMoment q (n-1)/((n-1).factorial : ℝ) ≤ 1/(N : ℝ)^n := by
  rw [integerBetaMoment_div_factorial q n hn]
  have hNat : N^n ≤ (q+n).descFactorial n := by
    apply (Nat.pow_le_pow_left hNq n).trans
    simpa only [show q+n+1-n=q+1 by omega] using Nat.pow_sub_le_descFactorial (q+n) n
  have hBound : (N : ℝ)^n ≤ ((q+n).descFactorial n : ℝ) := by exact_mod_cast hNat
  exact one_div_le_one_div_of_le (by positivity) hBound

/-- Literal removal of the first n polynomial coefficients. -/
def polynomialCoefficientShift (P : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (P.natDegree+1),Polynomial.monomial k (P.coeff (k+n))

/-- Inverse falling-factorial multiplier, with its genuine radial deformation. -/
def polynomialInverseFallingKernel (P : Polynomial ℂ) (n : ℕ) (r : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (P.natDegree+1),Polynomial.monomial k
    (P.coeff (k+n)/((((k+n).descFactorial n : ℕ) : ℂ)*(r : ℂ)^k))

theorem polynomialCoefficientShift_coeff (P : Polynomial ℂ) (n k : ℕ) :
    (polynomialCoefficientShift P n).coeff k = P.coeff (k+n) := by
  classical
  simp only [polynomialCoefficientShift,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  by_cases hk : k < P.natDegree+1
  · simp only [Finset.mem_range,hk,ite_true]
  · simp only [Finset.mem_range,hk,ite_false]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k+n)).symm

theorem polynomialInverseFallingKernel_coeff (P : Polynomial ℂ) (n k : ℕ) (r : ℝ) :
    (polynomialInverseFallingKernel P n r).coeff k =
      P.coeff (k+n)/((((k+n).descFactorial n : ℕ) : ℂ)*(r : ℂ)^k) := by
  classical
  simp only [polynomialInverseFallingKernel,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  by_cases hk : k < P.natDegree+1
  · simp only [Finset.mem_range,hk,ite_true]
  · simp only [Finset.mem_range,hk,ite_false]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k+n),zero_div]

theorem X_pow_mul_polynomialCoefficientShift (P : Polynomial ℂ) (n : ℕ)
    (hLow : ∀ k < n,P.coeff k=0) : Polynomial.X^n*polynomialCoefficientShift P n = P := by
  ext k
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hnk : n ≤ k
  · rw [ite_eq_left hnk,polynomialCoefficientShift_coeff,Nat.sub_add_cancel hnk]
  · rw [ite_eq_right hnk,hLow k (by omega)]

/-- Actual pointwise factorization after shifting, without division at z=0. -/
theorem polynomialCoefficientShift_eval_factor (P : Polynomial ℂ) (n : ℕ)
    (hLow : ∀ k < n,P.coeff k=0) (z : ℂ) :
    P.eval z = z^n*(polynomialCoefficientShift P n).eval z := by
  have h := congrArg (Polynomial.eval z) (X_pow_mul_polynomialCoefficientShift P n hLow)
  simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X] using h.symm

theorem polynomialCoefficientShift_eval (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (polynomialCoefficientShift P n).eval z =
      ∑ k ∈ Finset.range (P.natDegree+1),P.coeff (k+n)*z^k := by
  simp only [polynomialCoefficientShift,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem polynomialInverseFallingKernel_eval (P : Polynomial ℂ) (n : ℕ) (r : ℝ) (u : ℂ) :
    (polynomialInverseFallingKernel P n r).eval u =
      ∑ k ∈ Finset.range (P.natDegree+1),
        (P.coeff (k+n)/((((k+n).descFactorial n : ℕ) : ℂ)*(r : ℂ)^k))*u^k := by
  simp only [polynomialInverseFallingKernel,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

/-- Exact continuous integral representation of the literal inverse multiplier.
The integrand is a polynomial even at s=0; r=0 is allowed by totalized division. -/
theorem polynomialInverseFallingKernel_integral (P : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (u : ℂ) :
    (polynomialInverseFallingKernel P n r).eval u =
      (((n-1).factorial : ℕ) : ℂ)⁻¹ *
        ∫ s : ℝ in 0..1,((1-s : ℝ) : ℂ)^(n-1)*
          (polynomialCoefficientShift P n).eval (((s/r : ℝ) : ℂ)*u) := by
  classical
  have hFun : (fun s : ℝ => ((1-s : ℝ) : ℂ)^(n-1)*
      (polynomialCoefficientShift P n).eval (((s/r : ℝ) : ℂ)*u)) =
      fun s : ℝ => ∑ k ∈ Finset.range (P.natDegree+1),
        (P.coeff (k+n)/(r : ℂ)^k*u^k)*((s^k*(1-s)^(n-1) : ℝ) : ℂ) := by
    funext s
    rw [polynomialCoefficientShift_eval,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow,Complex.ofReal_div,div_pow]
    push_cast
    ring
  rw [hFun,intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
    rw [polynomialInverseFallingKernel_eval,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hBeta : ((integerBetaMoment k (n-1) : ℝ) : ℂ)/(((n-1).factorial : ℕ) : ℂ) =
        1/(((k+n).descFactorial n : ℕ) : ℂ) := by
      have h := congrArg Complex.ofReal (integerBetaMoment_div_factorial k n hn)
      simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_one] using h
    dsimp only [integerBetaMoment] at hBeta
    have hRearrange : ((((n-1).factorial : ℕ) : ℂ)⁻¹ *
      ((P.coeff (k+n)/(r : ℂ)^k*u^k)*((∫ s : ℝ in 0..1,s^k*(1-s)^(n-1) : ℝ) : ℂ))) =
      (P.coeff (k+n)/(r : ℂ)^k*u^k)*
        (((∫ s : ℝ in 0..1,s^k*(1-s)^(n-1) : ℝ) : ℂ)/(((n-1).factorial : ℕ) : ℂ)) := by ring
    rw [hRearrange,hBeta]
    ring
  · intro k _
    exact (by fun_prop : Continuous (fun s : ℝ =>
      (P.coeff (k+n)/(r : ℂ)^k*u^k)*((s^k*(1-s)^(n-1) : ℝ) : ℂ))).intervalIntegrable 0 1

/-- The actual inverse derivative kernel for the previously fixed positive-frequency band. -/
def positiveWideInverseKernel (m N N' n : ℕ) : Polynomial ℂ :=
  polynomialInverseFallingKernel (positiveWideBandKernel m N N') n (positiveKernelRadius N)

/-- The actual shifted band inherits the full radial gap, with no division at s=0. -/
theorem positiveWideBandShift_deformed_decay (m N N' n : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (hnm : n ≤ m)
    (s x : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hx : |x| ≤ 1/2) :
    ‖(polynomialCoefficientShift (positiveWideBandKernel m N N') n).eval
        (((s/positiveKernelRadius N : ℝ) : ℂ)*fourier (T := 1) 1 (x : Boundary))‖ ≤
      positiveWideDecayConstant m*(N : ℝ)*(positiveKernelRadius N)^n*
        s^(thinWideBandStart m N-n)/(1+(N : ℝ)*|x|)^(m+1) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < positiveKernelRadius N := by linarith [hBounds.1]
  have hna : n < thinWideBandStart m N := by
    dsimp only [thinWideBandStart]
    nlinarith
  have hLow : ∀ k < n,(positiveWideBandKernel m N N').coeff k=0 := by
    intro k hk
    exact positiveWideBandKernel_coeff_low m N N' k hNN' (hk.trans hna)
  by_cases hsZero : s=0
  · rw [hsZero,zero_div,Complex.ofReal_zero,zero_mul,
      ← Polynomial.coeff_zero_eq_eval_zero,polynomialCoefficientShift_coeff,zero_add,
      positiveWideBandKernel_coeff_low m N N' n hNN' hna,norm_zero]
    positivity [positiveWideDecayConstant_pos m hm]
  · have hsPos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsZero)
    let z : ℂ := ((s/positiveKernelRadius N : ℝ) : ℂ)*fourier (T := 1) 1 (x : Boundary)
    have hz : ‖z‖=s/positiveKernelRadius N := by
      simp only [z,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hs hr.le),
        fourier_apply,Circle.norm_coe,mul_one]
    have hFactor := congrArg norm (polynomialCoefficientShift_eval_factor
      (positiveWideBandKernel m N N') n hLow z)
    rw [norm_mul,norm_pow,hz] at hFactor
    have hDecay := positiveWideBandKernel_deformed_decay m N N' hm hN hNN' hRatio s x hs hs1 hx
    have hDiv : ‖(polynomialCoefficientShift (positiveWideBandKernel m N N') n).eval z‖ ≤
        (positiveWideDecayConstant m*(N : ℝ)*s^(thinWideBandStart m N)/
          (1+(N : ℝ)*|x|)^(m+1))/(s/positiveKernelRadius N)^n := by
      apply (le_div_iff₀ (pow_pos (div_pos hsPos hr) n)).mpr
      calc
        _ = ‖(positiveWideBandKernel m N N').eval z‖ := by rw [hFactor]; ring
        _ ≤ _ := hDecay
    calc
      _ ≤ _ := hDiv
      _ = _ := by
        rw [show thinWideBandStart m N=(thinWideBandStart m N-n)+n by omega,pow_add,div_pow,Nat.add_sub_cancel_right]
        field_simp

/-- Actual inverse-falling localization, with a uniform constant before ALL scales and orders. -/
theorem positiveWideInverseKernel_decay (m N N' n : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (hn : 1 ≤ n) (hnm : n ≤ m)
    (x : ℝ) (hx : |x| ≤ 1/2) :
    ‖(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 (x : Boundary))‖ ≤
      positiveWideDecayConstant m*(N : ℝ)/((N : ℝ)^n*(1+(N : ℝ)*|x|)^(m+1)) := by
  let P := positiveWideBandKernel m N N'
  let u := fourier (T := 1) 1 (x : Boundary)
  let r := positiveKernelRadius N
  let q := thinWideBandStart m N-n
  let A : ℝ := positiveWideDecayConstant m*(N : ℝ)*r^n/(1+(N : ℝ)*|x|)^(m+1)
  let f : ℝ → ℂ := fun s => ((1-s : ℝ) : ℂ)^(n-1)*
    (polynomialCoefficientShift P n).eval (((s/r : ℝ) : ℂ)*u)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrBounds := positiveKernelRadius_bounds N hN
  have hr : 0 < r := by dsimp only [r]; linarith [hrBounds.1]
  have hA : 0 ≤ A := by dsimp only [A]; positivity [positiveWideDecayConstant_pos m hm]
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hInt : ‖∫ s : ℝ in 0..1,f s‖ ≤ A*integerBetaMoment q (n-1) := by
    calc
      _ ≤ ∫ s : ℝ in 0..1,‖f s‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ s : ℝ in 0..1,A*(s^q*(1-s)^(n-1)) := by
        apply intervalIntegral.integral_mono_on zero_le_one (hf.norm.intervalIntegrable 0 1)
          ((by fun_prop : Continuous (fun s : ℝ => A*(s^q*(1-s)^(n-1)))).intervalIntegrable 0 1)
        intro s hs
        have hShift := positiveWideBandShift_deformed_decay m N N' n hm hN hNN' hRatio hnm s x hs.1 hs.2 hx
        change ‖((1-s : ℝ) : ℂ)^(n-1)*(polynomialCoefficientShift P n).eval (((s/r : ℝ) : ℂ)*u)‖ ≤ _
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hs.2])]
        calc
          _ ≤ (1-s)^(n-1)*(positiveWideDecayConstant m*(N : ℝ)*r^n*s^q/
              (1+(N : ℝ)*|x|)^(m+1)) := mul_le_mul_of_nonneg_left hShift (pow_nonneg (by linarith [hs.2]) _)
          _ = _ := by dsimp only [A]; ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
  have hBase : N ≤ q+1 := by
    have hLarge : n+N ≤ thinWideBandStart m N := by dsimp only [thinWideBandStart]; nlinarith
    dsimp only [q]
    omega
  have hBeta := integerBetaMoment_div_factorial_le q n N hn (by omega) hBase
  have hRadius : r^n ≤ 1 := pow_le_one₀ hr.le hrBounds.2.le
  calc
    _ = ‖((((n-1).factorial : ℕ) : ℂ)⁻¹)*(∫ s : ℝ in 0..1,f s)‖ := by
      rw [positiveWideInverseKernel,polynomialInverseFallingKernel_integral _ n hn]
    _ = ((n-1).factorial : ℝ)⁻¹*‖∫ s : ℝ in 0..1,f s‖ := by rw [norm_mul,norm_inv,Complex.norm_natCast]
    _ ≤ ((n-1).factorial : ℝ)⁻¹*(A*integerBetaMoment q (n-1)) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = A*(integerBetaMoment q (n-1)/((n-1).factorial : ℝ)) := by ring
    _ ≤ A*(1/(N : ℝ)^n) := mul_le_mul_of_nonneg_left hBeta hA
    _ ≤ _ := by
      dsimp only [A]
      have hConst : 0 ≤ positiveWideDecayConstant m*(N : ℝ)/(1+(N : ℝ)*|x|)^(m+1) := by
        positivity [positiveWideDecayConstant_pos m hm]
      have hScale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRadius hConst)
        (by positivity : 0 ≤ 1/(N : ℝ)^n)
      convert hScale using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

/-- The inverse multiplier restores the ACTUAL derivative coefficients at the inward radius. -/
theorem positiveWideInverseKernel_derivative_coeff (m N N' n k : ℕ) (hN : 10 ≤ N)
    (P : Polynomial ℂ) :
    (positiveWideInverseKernel m N N' n).coeff k * (Polynomial.derivative^[n] P).coeff k *
      ((positiveKernelRadius N : ℝ) : ℂ)^k = (thinWideBandPolynomial m N N' P).coeff (k+n) := by
  have hr : positiveKernelRadius N ≠ 0 := by linarith [(positiveKernelRadius_bounds N hN).1]
  have hrc : ((positiveKernelRadius N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd : (((k+n).descFactorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : n ≤ k+n)).ne'
  rw [positiveWideInverseKernel,polynomialInverseFallingKernel_coeff,
    Polynomial.coeff_iterate_derivative,thinWideBandPolynomial_coeff_eq_positiveKernel]
  simp only [nsmul_eq_mul]
  field_simp

/-- Uniform constants precede every scale, inverse derivative order, and angle. -/
theorem exists_positiveWideInverseKernel_decay (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ,0 < C ∧ ∀ N N' n : ℕ,10 ≤ N → N ≤ N' → 5*N' ≤ 6*N → 1 ≤ n → n ≤ m →
      ∀ x : ℝ,|x| ≤ 1/2 →
      ‖(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 (x : Boundary))‖ ≤
        C*(N : ℝ)/((N : ℝ)^n*(1+(N : ℝ)*|x|)^(m+1)) :=
  ⟨positiveWideDecayConstant m,positiveWideDecayConstant_pos m hm,
    fun N N' n hN hNN' hRatio hn hnm x hx =>
      positiveWideInverseKernel_decay m N N' n hm hN hNN' hRatio hn hnm x hx⟩

end TTO.Paper.Proved
