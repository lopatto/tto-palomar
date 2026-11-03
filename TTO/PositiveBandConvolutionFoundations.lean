/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PositiveBandInverseFoundations
public import TTO.AnalyticAreaSubmeanFoundations
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Literal polynomial circle convolution and local analytic arc estimates. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Exact unnormalized character orthogonality for the actual probability Haar measure. -/
theorem circle_character_power_pair_integral (k j : ℕ) :
    (∫ t : Boundary,(fourier (T := 1) 1 t)^k*conj ((fourier (T := 1) 1 t)^j) ∂circleMeasure) =
      if k=j then 1 else 0 := by
  have h := congrArg (fun f : ℤ → ℂ => f (j : ℤ)) (fourierCoeff_fourier (T := 1) (k : ℤ))
  change (∫ t : Boundary,fourier (T := 1) (-(j : ℤ)) t*fourier (k : ℤ) t ∂circleMeasure) = _ at h
  simpa only [fourier_neg,fourier_nat_pow,Pi.single_apply,Nat.cast_inj,mul_comm,eq_comm] using! h

/-- Character subtraction is the literal group law, with the conjugation explicit. -/
theorem circle_character_sub (x t : Boundary) :
    fourier (T := 1) 1 (x-t)=fourier (T := 1) 1 x*conj (fourier (T := 1) 1 t) := by
  rw [sub_eq_add_neg,fourier_position_add]
  have h : fourier (T := 1) 1 (-t)=conj (fourier (T := 1) 1 t) := by
    simpa only [fourier_apply,one_zsmul] using (fourier_neg' (T := 1) (n := (1 : ℤ)) (x := t))
  rw [h]

/-- A polynomial's nonnegative Haar Fourier coefficients are its actual coefficients. -/
theorem polynomial_circle_fourierCoeff (K : Polynomial ℂ) (j : ℕ) :
    (∫ t : Boundary,K.eval (fourier (T := 1) 1 t)*conj ((fourier (T := 1) 1 t)^j) ∂circleMeasure)=K.coeff j := by
  classical
  have hFun : (fun t : Boundary => K.eval (fourier (T := 1) 1 t)*conj ((fourier (T := 1) 1 t)^j)) =
      fun t : Boundary => ∑ k ∈ Finset.range (K.natDegree+1),
        K.coeff k*((fourier (T := 1) 1 t)^k*conj ((fourier (T := 1) 1 t)^j)) := by
    funext t
    rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hFun,integral_finsetSum]
  · simp_rw [integral_const_mul,circle_character_power_pair_integral,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hj : j < K.natDegree+1
    · simp only [Finset.mem_range,hj,ite_true]
    · simp only [Finset.mem_range,hj,ite_false]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : K.natDegree < j)).symm
  · intro k _
    exact (by fun_prop : Continuous (fun t : Boundary =>
      K.coeff k*((fourier (T := 1) 1 t)^k*conj ((fourier (T := 1) 1 t)^j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Literal polynomial circle convolution selects equal coefficient indices. -/
theorem polynomial_circle_convolution (K H : Polynomial ℂ) (r : ℝ) (x : Boundary) :
    (∫ t : Boundary,K.eval (fourier (T := 1) 1 t)*
      H.eval ((r : ℂ)*fourier (T := 1) 1 (x-t)) ∂circleMeasure) =
      ∑ j ∈ Finset.range (H.natDegree+1),
        K.coeff j*H.coeff j*(r : ℂ)^j*(fourier (T := 1) 1 x)^j := by
  classical
  have hFun : (fun t : Boundary => K.eval (fourier (T := 1) 1 t)*
      H.eval ((r : ℂ)*fourier (T := 1) 1 (x-t))) =
      fun t : Boundary => ∑ j ∈ Finset.range (H.natDegree+1),
        (H.coeff j*(r : ℂ)^j*(fourier (T := 1) 1 x)^j)*
          (K.eval (fourier (T := 1) 1 t)*conj ((fourier (T := 1) 1 t)^j)) := by
    funext t
    rw [Polynomial.eval_eq_sum_range (p := H),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [circle_character_sub,mul_pow,mul_pow,map_pow]
    ring
  rw [hFun,integral_finsetSum]
  · simp_rw [integral_const_mul,polynomial_circle_fourierCoeff]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact (by fun_prop : Continuous (fun t : Boundary =>
      (H.coeff j*(r : ℂ)^j*(fourier (T := 1) 1 x)^j)*
        (K.eval (fourier (T := 1) 1 t)*conj ((fourier (T := 1) 1 t)^j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The actual inverse kernel reconstructs the actual band from the derivative at rN.
All scalar phases and the probability Haar normalization are explicit. -/
theorem positiveWideBand_inverse_convolution (m N N' n : ℕ) (hN : 10 ≤ N) (hNN' : N ≤ N')
    (hnm : n ≤ m) (P : Polynomial ℂ) (x : Boundary) :
    (thinWideBandPolynomial m N N' P).eval (fourier (T := 1) 1 x) =
      (fourier (T := 1) 1 x)^n *
        ∫ t : Boundary,(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 t)*
          (Polynomial.derivative^[n] P).eval (((positiveKernelRadius N : ℝ) : ℂ)*
            fourier (T := 1) 1 (x-t)) ∂circleMeasure := by
  let H := Polynomial.derivative^[n] P
  let Q := thinWideBandPolynomial m N N' P
  have hLow : ∀ k < n,Q.coeff k=0 := by
    intro k hk
    apply thinWideBandPolynomial_coeff_low m N N' hNN' P k
    have hna : n < thinWideBandStart m N := by dsimp only [thinWideBandStart]; nlinarith
    omega
  have hDegree : (polynomialCoefficientShift Q n).natDegree ≤ H.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [polynomialCoefficientShift_coeff]
    have h := positiveWideInverseKernel_derivative_coeff m N N' n j hN P
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,mul_zero,zero_mul] at h
    exact h.symm
  rw [polynomialCoefficientShift_eval_factor Q n hLow,polynomial_circle_convolution]
  congr 1
  rw [Polynomial.eval_eq_sum_range' (n := H.natDegree+1) (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  rw [polynomialCoefficientShift_coeff]
  rw [positiveWideInverseKernel_derivative_coeff m N N' n j hN P]

/-- The leading character in the reconstruction has unit modulus, including order zero. -/
theorem norm_positiveWideBand_inverse_convolution (m N N' n : ℕ) (hN : 10 ≤ N) (hNN' : N ≤ N')
    (hnm : n ≤ m) (P : Polynomial ℂ) (x : Boundary) :
    ‖(thinWideBandPolynomial m N N' P).eval (fourier (T := 1) 1 x)‖ =
      ‖∫ t : Boundary,(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 t)*
          (Polynomial.derivative^[n] P).eval (((positiveKernelRadius N : ℝ) : ℂ)*
            fourier (T := 1) 1 (x-t)) ∂circleMeasure‖ := by
  rw [positiveWideBand_inverse_convolution m N N' n hN hNN' hnm P x,norm_mul,norm_pow,
    fourier_apply,Circle.norm_coe,one_pow,one_mul]

/-- Period-one character geometry at arbitrary real arguments, including wrapping arcs. -/
theorem circle_character_chord_upper_real (t θ : ℝ) :
    ‖fourier (T := 1) 1 (t : Boundary)-fourier (T := 1) 1 (θ : Boundary)‖ ≤ 2*Real.pi*|t-θ| := by
  have hMul : fourier (T := 1) 1 ((t-θ : ℝ) : Boundary)*fourier (T := 1) 1 (θ : Boundary) =
      fourier (T := 1) 1 (t : Boundary) := by
    rw [← fourier_position_add]
    congr 1
    change ((t-θ+θ : ℝ) : Boundary)=(t : Boundary)
    rw [sub_add_cancel]
  have hNorm : ‖fourier (T := 1) 1 (t : Boundary)-fourier (T := 1) 1 (θ : Boundary)‖ =
      ‖fourier (T := 1) 1 ((t-θ : ℝ) : Boundary)-1‖ := by
    calc
      _ = ‖(fourier (T := 1) 1 ((t-θ : ℝ) : Boundary)-1)*fourier (T := 1) 1 (θ : Boundary)‖ := by rw [sub_mul,hMul,one_mul]
      _ = _ := by rw [norm_mul,show ‖fourier (T := 1) 1 (θ : Boundary)‖ = 1 by simp,mul_one]
  have hExp : fourier (T := 1) 1 ((t-θ : ℝ) : Boundary) =
      Complex.exp (Complex.I*((2*Real.pi*(t-θ) : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [hNorm,hExp]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq (by
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)])

/-- Each Q=10N short angular cell fits the literal inner analytic disk of radius 1/N. -/
theorem deformed_arc_mem_closedBall (N : ℕ) (hN : 10 ≤ N) (θ t : ℝ)
    (ht : |t-θ| ≤ 1/(10*(N : ℝ))) :
    ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (t : Boundary)) ∈
      Metric.closedBall ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)) (1/(N : ℝ)) := by
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 ≤ positiveKernelRadius N := by linarith [hBounds.1]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Metric.mem_closedBall,dist_eq_norm,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ positiveKernelRadius N*(2*Real.pi*|t-θ|) :=
      mul_le_mul_of_nonneg_left (circle_character_chord_upper_real t θ) hr
    _ ≤ 2*Real.pi*|t-θ| := mul_le_of_le_one_left (by positivity) hBounds.2.le
    _ ≤ 2*Real.pi*(1/(10*(N : ℝ))) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ 1/(N : ℝ) := by
      apply (le_div_iff₀ hNp).mpr
      field_simp
      linarith [Real.pi_lt_four]

/-- The twice larger analytic disk stays strictly inside the actual open unit disk. -/
theorem deformed_arc_closedBall_subset_disk (N : ℕ) (hN : 10 ≤ N) (θ : ℝ) :
    Metric.closedBall ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary))
      (2/(N : ℝ)) ⊆ disk := by
  intro z hz
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 ≤ positiveKernelRadius N := by linarith [hBounds.1]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : ‖(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)‖ = positiveKernelRadius N := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,fourier_apply,Circle.norm_coe,mul_one]
  have hDist := Metric.mem_closedBall.mp hz
  rw [dist_eq_norm] at hDist
  change ‖z‖ < 1
  calc
    _ ≤ ‖z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)‖+
        ‖(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary))
        ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary))
    _ ≤ 2/(N : ℝ)+positiveKernelRadius N := by rw [hc]; linarith
    _ < 1 := by
      dsimp only [positiveKernelRadius]
      have hPos := div_pos (by norm_num : (0 : ℝ) < 2) hNp
      have hFour : 4/(N : ℝ)=2*(2/(N : ℝ)) := by ring
      linarith

/-- A genuine local area bound controls EVERY point of a short arc for every p>0. -/
theorem analytic_short_arc_rpow_le_area (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (N : ℕ) (hN : 10 ≤ N) (p : ℝ) (hp : 0 < p) (θ t : ℝ)
    (ht : |t-θ| ≤ 1/(10*(N : ℝ))) :
    ‖F ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (t : Boundary))‖^p ≤
      ((N : ℝ)^2/Real.pi)*∫ z in Metric.ball
        ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)) (2/(N : ℝ)),‖F z‖^p := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 0 < 1/(N : ℝ) := by positivity
  have hSub := deformed_arc_closedBall_subset_disk N hN θ
  have h := analytic_norm_rpow_le_local_area F
    ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (θ : Boundary)) (1/(N : ℝ)) p hR
    (by simpa only [show (2 : ℝ)*(1/(N : ℝ))=2/(N : ℝ) by ring] using hF.mono hSub) hp
    ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (t : Boundary)) (deformed_arc_mem_closedBall N hN θ t ht)
  have hConst : (Real.pi*(1/(N : ℝ))^2)⁻¹ = (N : ℝ)^2/Real.pi := by field_simp
  simpa only [hConst,show (2 : ℝ)*(1/(N : ℝ))=2/(N : ℝ) by ring] using h

end TTO.Paper.Proved
