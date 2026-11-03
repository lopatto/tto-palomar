/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BesovAreaFoundations

/-! Actual normalized disk moments for the trace-class Hankel synthesis route.
This is a supporting analytic construction, not an all-p Peller theorem. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The radial probability distribution for normalized area on the open disk. -/
def diskRadialMeasure : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun r => ENNReal.ofReal (2*r))

/-- The literal polar map, with the source's probability Haar angle. -/
def diskPolar (p : ℝ × Boundary) : ℂ :=
  (p.1 : ℂ) * fourier (T := 1) 1 p.2

theorem continuous_diskPolar : Continuous diskPolar := by
  unfold diskPolar
  fun_prop

/-- Equality of measures supplies signed and complex polar integration without
assuming a square-integrable integrand. -/
theorem diskArea_eq_map_diskPolar :
    diskArea = Measure.map diskPolar (diskRadialMeasure.prod circleMeasure) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map' hf.aemeasurable continuous_diskPolar.measurable.aemeasurable]
  rw [lintegral_diskArea_polar f
    (hf.indicator (isOpen_lt continuous_norm continuous_const).measurableSet)]
  change _ = ∫⁻ p, (f ∘ diskPolar) p ∂diskRadialMeasure.prod circleMeasure
  rw [lintegral_prod _ (hf.comp continuous_diskPolar.measurable).aemeasurable]
  rw [diskRadialMeasure,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)]
  · rfl
  · exact (hf.comp continuous_diskPolar.measurable).lintegral_prod_right'

instance diskRadialMeasure_isProbabilityMeasure : IsProbabilityMeasure diskRadialMeasure := by
  constructor
  rw [diskRadialMeasure,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  convert lintegral_radial_monomial 0 using 1 <;> norm_num

/-- Genuine Bochner/Fubini polar integration, under only ordinary L¹ integrability. -/
theorem integral_diskArea_polar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E) (hf : Integrable f diskArea) :
    (∫ z, f z ∂diskArea) =
      ∫ r, ∫ t : Boundary, f ((r : ℂ)*fourier (T := 1) 1 t) ∂circleMeasure ∂diskRadialMeasure := by
  rw [diskArea_eq_map_diskPolar] at hf ⊢
  rw [integral_map continuous_diskPolar.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ((integrable_map_measure hf.aestronglyMeasurable
    continuous_diskPolar.measurable.aemeasurable).mp hf)

/-- Every local circle coefficient uses the actual analytic radial representative. -/
theorem analytic_radial_circle_coefficient (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∫ t : Boundary, conj (fourier (T := 1) 1 t)^n *
      F ((r : ℂ)*fourier (T := 1) 1 t) ∂circleMeasure) =
      diskTaylorCoeff F n * (r : ℂ)^n := by
  calc
    _ = fourierCoeff (diskRadialHardy F r).val (n : ℤ) := by
      change _ = ∫ t : Boundary, fourier (T := 1) (-(n : ℤ)) t *
        (diskRadialHardy F r).val t ∂circleMeasure
      apply integral_congr_ae
      filter_upwards [diskRadialHardy_ae_local F hF r hr hr1] with t ht
      rw [ht,fourier_neg]
      simp only [fourier_apply,natCast_zsmul,AddCircle.toCircle_nsmul,
        Circle.coe_pow,map_pow,one_zsmul]
    _ = _ := by
      rw [← hardyBasis_repr_eq_fourierCoeff,
        hardyBasis_repr_diskRadialHardy_local F hF r hr hr1]
      rfl

theorem ae_mem_diskArea : ∀ᵐ z ∂diskArea, z ∈ disk := by
  rw [diskArea]
  exact Measure.ae_smul_measure
    (ae_restrict_mem (isOpen_lt continuous_norm continuous_const).measurableSet) _

/-- The weighted coefficient kernel is bounded by one on the actual disk. -/
theorem weighted_moment_kernel_norm_le (z : ℂ) (hz : z ∈ disk) (n : ℕ) :
    ‖conj z^n * ((1-‖z‖^2 : ℝ) : ℂ)‖ ≤ 1 := by
  have hz1 : ‖z‖ < 1 := hz
  have hz2 : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [norm_mul,norm_pow,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hz2)]
  calc
    _ ≤ 1*(1-‖z‖^2) := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg z) hz1.le) (sub_nonneg.mpr hz2)
    _ ≤ 1 := by nlinarith [sq_nonneg ‖z‖]

theorem integrable_weighted_moment (F : ℂ → ℂ) (hf : Integrable F diskArea) (n : ℕ) :
    Integrable (fun z => (conj z^n * ((1-‖z‖^2 : ℝ) : ℂ))*F z) diskArea := by
  apply hf.bdd_mul (by fun_prop : Continuous (fun z : ℂ =>
    conj z^n * ((1-‖z‖^2 : ℝ) : ℂ))).aestronglyMeasurable
  filter_upwards [ae_mem_diskArea] with z hz
  exact weighted_moment_kernel_norm_le z hz n

theorem integral_diskRadialMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ r, f r ∂diskRadialMeasure) = ∫ r in Ioo (0 : ℝ) 1, (2*r) • f r := by
  rw [diskRadialMeasure,integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hr.1.le)]

/-- The normalized weighted Bergman moment has no omitted π or factor two. -/
theorem integral_weighted_radial_monomial (n : ℕ) :
    (∫ r : ℝ, (1-r^2)*r^(2*n) ∂diskRadialMeasure) =
      1/(((n : ℝ)+1)*((n : ℝ)+2)) := by
  rw [integral_diskRadialMeasure]
  have he (r : ℝ) : (2*r) • ((1-r^2)*r^(2*n)) =
      2*r^(2*n+1)-2*r^(2*n+3) := by
    simp only [smul_eq_mul,pow_succ]
    ring
  simp_rw [he]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun r : ℝ => 2*r^(2*n+1))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun r : ℝ => 2*r^(2*n+3))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_pow_zero_one,integral_pow_zero_one]
  push_cast
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem ae_mem_diskRadialMeasure : ∀ᵐ r ∂diskRadialMeasure, r ∈ Ioo (0 : ℝ) 1 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- Weighted Bergman reproducing coefficient for an arbitrary analytic L¹ function.
No Hardy or square-integrability hypothesis is imposed. -/
theorem analytic_weighted_disk_moment (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (hf : Integrable F diskArea) (n : ℕ) :
    (∫ z, (conj z^n * ((1-‖z‖^2 : ℝ) : ℂ))*F z ∂diskArea) =
      diskTaylorCoeff F n / (((n : ℂ)+1)*((n : ℂ)+2)) := by
  rw [integral_diskArea_polar _ (integrable_weighted_moment F hf n)]
  calc
    _ = ∫ r : ℝ, diskTaylorCoeff F n * (((1-r^2)*r^(2*n) : ℝ) : ℂ) ∂diskRadialMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_mem_diskRadialMeasure] with r hr
      have he (t : Boundary) :
          (conj ((r : ℂ)*fourier (T := 1) 1 t)^n *
            ((1-‖(r : ℂ)*fourier (T := 1) 1 t‖^2 : ℝ) : ℂ))*
              F ((r : ℂ)*fourier (T := 1) 1 t) =
          ((r : ℂ)^n*((1-r^2 : ℝ) : ℂ)) *
            (conj (fourier (T := 1) 1 t)^n*F ((r : ℂ)*fourier (T := 1) 1 t)) := by
        simp only [map_mul,Complex.conj_ofReal,mul_pow,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg hr.1.le,fourier_one,Circle.norm_coe,mul_one]
        ring
      simp_rw [he]
      rw [integral_const_mul,analytic_radial_circle_coefficient F hF r hr.1.le hr.2 n]
      push_cast
      rw [pow_mul]
      ring
    _ = _ := by
      rw [integral_const_mul,integral_complex_ofReal,integral_weighted_radial_monomial]
      push_cast
      ring

/-- Conjugation convention needed by the actual classical Hankel matrix. -/
theorem conjugate_analytic_weighted_disk_moment (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (hf : Integrable F diskArea) (n : ℕ) :
    (∫ z, (conj (F z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n ∂diskArea) =
      conj (diskTaylorCoeff F n) / (((n : ℂ)+1)*((n : ℂ)+2)) := by
  calc
    _ = ∫ z, conj ((conj z^n * ((1-‖z‖^2 : ℝ) : ℂ))*F z) ∂diskArea := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simp only [map_mul,map_pow,Complex.conj_conj,Complex.conj_ofReal]
        ring
    _ = _ := by
      rw [integral_conj,analytic_weighted_disk_moment F hF hf n]
      simp [show (2 : ℂ)=1+1 by ring]

/-- The two derivative factors exactly cancel the weighted moment denominators. -/
theorem second_derivative_weighted_moment (g : BoundaryL2)
    (hInt : Integrable (deriv (deriv (analyticValue g))) diskArea) (n : ℕ) :
    (∫ z, (conj (deriv (deriv (analyticValue g)) z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n ∂diskArea) =
      conj (fourierCoeff g ((n+2 : ℕ) : ℤ)) := by
  have hD : AnalyticOnNhd ℂ (deriv (deriv (analyticValue g))) disk :=
    fun z hz => ((analyticOnNhd_analyticValue g z hz).deriv).deriv
  rw [conjugate_analytic_weighted_disk_moment _ hD hInt n,
    diskTaylorCoeff_deriv,diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue]
  simp only [map_mul,map_natCast]
  push_cast
  have hn1 : (n : ℂ)+1 ≠ 0 := by exact_mod_cast (show (n : ℝ)+1 ≠ 0 by positivity)
  have hn2 : (n : ℂ)+2 ≠ 0 := by exact_mod_cast (show (n : ℝ)+2 ≠ 0 by positivity)
  field_simp
  simp only [add_assoc,one_add_one_eq_two]

theorem besovOrder_one : besovOrder 1=2 := by norm_num [besovOrder]

theorem besovEnergy_one (F : ℂ → ℂ) :
    besovEnergy 1 F = ENNReal.ofReal ‖F 0‖+ENNReal.ofReal ‖deriv F 0‖+
      ∫⁻ z, ENNReal.ofReal ‖deriv (deriv F) z‖ ∂diskArea := by
  simp only [besovEnergy,besovOrder_one,Finset.sum_range_succ,Finset.sum_range_zero,
    iteratedDeriv_zero,iteratedDeriv_one,Real.rpow_one,Nat.cast_ofNat,mul_one,
    sub_self,Real.rpow_zero,mul_one,zero_add]
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]

theorem integrable_of_analytic_disk_lintegral_norm_lt_top (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk)
    (hFin : (∫⁻ z, ENNReal.ofReal ‖F z‖ ∂diskArea) < ∞) : Integrable F diskArea := by
  have hM : AEStronglyMeasurable F diskArea := by
    rw [diskArea]
    exact (hF.continuousOn.aestronglyMeasurable
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul_measure _
  refine ⟨hM,?_⟩
  simpa only [hasFiniteIntegral_iff_enorm,← ofReal_norm] using hFin

/-- The frozen p=1 Besov hypothesis supplies exactly the ordinary L¹ second derivative. -/
theorem integrable_second_derivative_of_besov_one (g : BoundaryL2)
    (hg : besovEnergy 1 (analyticValue g) < ∞) :
    Integrable (deriv (deriv (analyticValue g))) diskArea := by
  apply integrable_of_analytic_disk_lintegral_norm_lt_top
    _ (fun z hz => ((analyticOnNhd_analyticValue g z hz).deriv).deriv)
  rw [besovEnergy_one] at hg
  exact lt_of_le_of_lt (le_add_self :
    (∫⁻ z, ENNReal.ofReal ‖deriv (deriv (analyticValue g)) z‖ ∂diskArea) ≤ _) hg

theorem second_derivative_weighted_moment_of_besov_one (g : BoundaryL2)
    (hg : besovEnergy 1 (analyticValue g) < ∞) (n : ℕ) :
    (∫ z, (conj (deriv (deriv (analyticValue g)) z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n ∂diskArea) =
      conj (fourierCoeff g ((n+2 : ℕ) : ℤ)) :=
  second_derivative_weighted_moment g (integrable_second_derivative_of_besov_one g hg) n

/-- Exact low-coefficient bookkeeping for the frozen inhomogeneous p=1 norm. -/
theorem besovNorm_one_eq (g : BoundaryL2) (hg : besovEnergy 1 (analyticValue g)<∞) :
    besovNorm 1 g = ‖fourierCoeff g 0‖+‖fourierCoeff g 1‖+
      ∫ z, ‖deriv (deriv (analyticValue g)) z‖ ∂diskArea := by
  have hI := integrable_second_derivative_of_besov_one g hg
  have he := ofReal_integral_norm_eq_lintegral_enorm hI
  simp only [← ofReal_norm] at he
  rw [besovNorm,div_one,Real.rpow_one,besovEnergy_one,← he]
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => norm_nonneg _)),analyticValue_at_zero]
  congr 2
  have hc := diskTaylorCoeff_analyticValue g 1
  simpa only [diskTaylorCoeff,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,div_one] using
    congrArg norm hc

end TTO.Paper.Proved
