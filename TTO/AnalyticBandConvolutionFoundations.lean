/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PositiveBandConvolutionFoundations

/-! Actual analytic radial moments reconstruct finite Taylor bands without boundary-series limits. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Actual finite Taylor-coefficient multiplier; no boundary representative is substituted. -/
def analyticCoefficientMultiplier (K : Polynomial ℂ) (F : ℂ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ K.support,Polynomial.monomial j (K.coeff j*diskTaylorCoeff F j)

theorem analyticCoefficientMultiplier_coeff (K : Polynomial ℂ) (F : ℂ → ℂ) (j : ℕ) :
    (analyticCoefficientMultiplier K F).coeff j = K.coeff j*diskTaylorCoeff F j := by
  classical
  simp only [analyticCoefficientMultiplier,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  by_cases hj : K.coeff j=0
  · simp only [Polynomial.mem_support_iff,hj,ne_eq,not_true_eq_false,ite_false,zero_mul]
  · simp only [Polynomial.mem_support_iff,hj,ne_eq,not_false_eq_true,ite_true]

theorem analyticCoefficientMultiplier_natDegree_le (K : Polynomial ℂ) (F : ℂ → ℂ) :
    (analyticCoefficientMultiplier K F).natDegree ≤ K.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [analyticCoefficientMultiplier_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt hj,zero_mul]

/-- The actual finite wide Taylor band. -/
def analyticWideBandPolynomial (m N N' : ℕ) (F : ℂ → ℂ) : Polynomial ℂ :=
  analyticCoefficientMultiplier (positiveWideBandKernel m N N') F

theorem analyticWideBandPolynomial_coeff (m N N' : ℕ) (F : ℂ → ℂ) (k : ℕ) :
    (analyticWideBandPolynomial m N N' F).coeff k =
      (wideDirichletPositiveWeight m N' k-wideDirichletPositiveWeight m N k)*diskTaylorCoeff F k := by
  rw [analyticWideBandPolynomial,analyticCoefficientMultiplier_coeff,positiveWideBandKernel_coeff]

/-- The finite Taylor band of the frozen analyticValue uses exactly g's positive Fourier coefficients. -/
theorem analyticWideBandPolynomial_analyticValue_coeff (m N N' : ℕ) (g : BoundaryL2) (k : ℕ) :
    (analyticWideBandPolynomial m N N' (analyticValue g)).coeff k =
      (wideDirichletPositiveWeight m N' k-wideDirichletPositiveWeight m N k)*fourierCoeff g (k : ℤ) := by
  rw [analyticWideBandPolynomial_coeff,diskTaylorCoeff_analyticValue]

/-- Taylor coefficients of the actual iterated derivative, including order zero. -/
theorem diskTaylorCoeff_iteratedDeriv (F : ℂ → ℂ) (n k : ℕ) :
    diskTaylorCoeff (iteratedDeriv n F) k =
      (((k+n).descFactorial n : ℕ) : ℂ)*diskTaylorCoeff F (k+n) := by
  have hD : iteratedDeriv k (iteratedDeriv n F) 0=iteratedDeriv (k+n) F 0 := by
    simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]
  have hFactor : (k.factorial : ℂ)*(((k+n).descFactorial n : ℕ) : ℂ) = ((k+n).factorial : ℂ) := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_right] using
      Nat.factorial_mul_descFactorial (show n ≤ k+n by omega))
  dsimp only [diskTaylorCoeff]
  rw [hD,← hFactor]
  have hd : (((k+n).descFactorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : n ≤ k+n)).ne'
  field_simp

/-- Analyticity only inside the disk suffices for genuine continuous radial circle values. -/
theorem continuous_analytic_circle (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun t : Boundary => F ((r : ℂ)*fourier (T := 1) 1 t)) := by
  apply hF.continuousOn.comp_continuous (by fun_prop)
  intro t
  change ‖(r : ℂ)*fourier (T := 1) 1 t‖ < 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,fourier_apply,Circle.norm_coe,mul_one]
  exact hr1

/-- Finite-kernel convolution with an ACTUAL analytic function is fixed by local radial moments. -/
theorem polynomial_analytic_circle_convolution (K : Polynomial ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (x : Boundary) :
    (∫ t : Boundary,K.eval (fourier (T := 1) 1 t)*
      F ((r : ℂ)*fourier (T := 1) 1 (x-t)) ∂circleMeasure) =
      ∑ j ∈ Finset.range (K.natDegree+1),
        K.coeff j*diskTaylorCoeff F j*(r : ℂ)^j*(fourier (T := 1) 1 x)^j := by
  classical
  have hCont := continuous_analytic_circle F hF r hr hr1
  have hFourier : Continuous (fun t : Boundary => fourier (T := 1) 1 t) := (fourier (T := 1) 1).continuous
  have hMove := integral_sub_left_eq_self
    (fun t : Boundary => K.eval (fourier (T := 1) 1 (x-t))*F ((r : ℂ)*fourier (T := 1) 1 t)) circleMeasure x
  have hFun : (fun t : Boundary => K.eval (fourier (T := 1) 1 (x-t))*F ((r : ℂ)*fourier (T := 1) 1 t)) =
      fun t : Boundary => ∑ j ∈ Finset.range (K.natDegree+1),
        (K.coeff j*(fourier (T := 1) 1 x)^j)*
          (conj (fourier (T := 1) 1 t)^j*F ((r : ℂ)*fourier (T := 1) 1 t)) := by
    funext t
    rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [circle_character_sub,mul_pow]
    ring
  calc
    _ = ∫ t : Boundary,K.eval (fourier (T := 1) 1 (x-t))*F ((r : ℂ)*fourier (T := 1) 1 t) ∂circleMeasure := by
      simpa only [sub_sub_cancel] using hMove
    _ = _ := by
      rw [hFun,integral_finsetSum]
      · simp_rw [integral_const_mul,analytic_radial_circle_coefficient F hF r hr hr1]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · intro j _
        have hPow : Continuous (fun t : Boundary => conj (fourier (T := 1) 1 t)^j) :=
          (Complex.continuous_conj.comp hFourier).pow j
        have hTerm : Continuous (fun t : Boundary =>
          (K.coeff j*(fourier (T := 1) 1 x)^j)*
            (conj (fourier (T := 1) 1 t)^j*F ((r : ℂ)*fourier (T := 1) 1 t))) :=
          continuous_const.mul (hPow.mul hCont)
        exact hTerm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Literal inverse-kernel restoration of the actual analytic derivative's Taylor coefficients. -/
theorem positiveWideInverseKernel_taylor_coeff (m N N' n k : ℕ) (hN : 10 ≤ N) (F : ℂ → ℂ) :
    (positiveWideInverseKernel m N N' n).coeff k*diskTaylorCoeff (iteratedDeriv n F) k*
      ((positiveKernelRadius N : ℝ) : ℂ)^k = (analyticWideBandPolynomial m N N' F).coeff (k+n) := by
  have hr : positiveKernelRadius N ≠ 0 := by linarith [(positiveKernelRadius_bounds N hN).1]
  have hrc : ((positiveKernelRadius N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd : (((k+n).descFactorial n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : n ≤ k+n)).ne'
  rw [positiveWideInverseKernel,polynomialInverseFallingKernel_coeff,diskTaylorCoeff_iteratedDeriv,
    analyticWideBandPolynomial,analyticCoefficientMultiplier_coeff]
  field_simp

/-- Exact inverse convolution reconstructs the genuine finite Taylor band of EVERY disk-analytic F. -/
theorem analyticWideBand_inverse_convolution (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (m N N' n : ℕ) (hN : 10 ≤ N) (hNN' : N ≤ N') (hnm : n ≤ m) (x : Boundary) :
    (analyticWideBandPolynomial m N N' F).eval (fourier (T := 1) 1 x) =
      (fourier (T := 1) 1 x)^n *
        ∫ t : Boundary,(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 t)*
          iteratedDeriv n F (((positiveKernelRadius N : ℝ) : ℂ)*
            fourier (T := 1) 1 (x-t)) ∂circleMeasure := by
  let Q := analyticWideBandPolynomial m N N' F
  let K := positiveWideInverseKernel m N N' n
  have hLow : ∀ k < n,Q.coeff k=0 := by
    intro k hk
    dsimp only [Q]
    rw [analyticWideBandPolynomial,analyticCoefficientMultiplier_coeff,
      positiveWideBandKernel_coeff_low m N N' k hNN',zero_mul]
    have hna : n < thinWideBandStart m N := by dsimp only [thinWideBandStart]; nlinarith
    omega
  have hDegree : (polynomialCoefficientShift Q n).natDegree ≤ K.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [polynomialCoefficientShift_coeff]
    have h := positiveWideInverseKernel_taylor_coeff m N N' n j hN F
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,zero_mul,zero_mul] at h
    exact h.symm
  have hDeriv : AnalyticOnNhd ℂ (iteratedDeriv n F) disk := by
    simpa only [iteratedDeriv_eq_iterate] using hF.iterated_deriv n
  have hr := positiveKernelRadius_bounds N hN
  rw [polynomialCoefficientShift_eval_factor Q n hLow,
    polynomial_analytic_circle_convolution _ _ hDeriv _ (by linarith [hr.1]) hr.2]
  congr 1
  rw [Polynomial.eval_eq_sum_range' (n := K.natDegree+1) (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  rw [polynomialCoefficientShift_coeff,positiveWideInverseKernel_taylor_coeff m N N' n j hN F]

/-- The exact analytic reconstruction preserves the norm; no polynomial-density argument is used. -/
theorem norm_analyticWideBand_inverse_convolution (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (m N N' n : ℕ) (hN : 10 ≤ N) (hNN' : N ≤ N') (hnm : n ≤ m) (x : Boundary) :
    ‖(analyticWideBandPolynomial m N N' F).eval (fourier (T := 1) 1 x)‖ =
      ‖∫ t : Boundary,(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 t)*
          iteratedDeriv n F (((positiveKernelRadius N : ℝ) : ℂ)*
            fourier (T := 1) 1 (x-t)) ∂circleMeasure‖ := by
  rw [analyticWideBand_inverse_convolution F hF m N N' n hN hNN' hnm x,norm_mul,norm_pow,
    fourier_apply,Circle.norm_coe,one_pow,one_mul]

end TTO.Paper.Proved
