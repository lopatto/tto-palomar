/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBoundaryFoundations
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! The normalized disk-area/Dirichlet bridge for the p=2 Besov endpoint.
This module is partial preparation for the all-p Peller obligation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem besovOrder_two : besovOrder 2=1 := by norm_num [besovOrder]

theorem circleMeasure_eq_volume : circleMeasure=(volume : Measure Boundary) := by
  simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm

theorem diskTaylorCoeff_deriv (F : ℂ → ℂ) (n : ℕ) :
    diskTaylorCoeff (deriv F) n = ((n+1 : ℕ) : ℂ)*diskTaylorCoeff F (n+1) := by
  unfold diskTaylorCoeff
  rw [← iteratedDeriv_succ',Nat.factorial_succ,Nat.cast_mul]
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp

theorem polar_angle_fourier (t : ℝ) :
    (Real.cos (2*Real.pi*t) : ℂ)+(Real.sin (2*Real.pi*t) : ℂ)*Complex.I =
      fourier (T := 1) 1 (t : Boundary) := by
  rw [fourier_coe_apply]
  simp only [Int.cast_one,mul_one]
  rw [show (2 : ℂ)*Real.pi*Complex.I*t = ((2*Real.pi*t : ℝ) : ℂ)*Complex.I by push_cast; ring]
  simpa only [Complex.ofReal_cos,Complex.ofReal_sin,Complex.ofReal_one,div_one] using
    (Complex.exp_mul_I ((2*Real.pi*t : ℝ) : ℂ)).symm

/-- Positive real scaling of a literal interval lower integral, retaining infinite values. -/
theorem setLIntegral_scaled_Ioc (a : ℝ) (ha : 0 < a) (l u : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Ioc (a*l) (a*u), f θ) = ENNReal.ofReal a * ∫⁻ t in Ioc l u, f (a*t) := by
  have hvol := Real.smul_map_volume_mul_left ha.ne'
  rw [abs_of_pos ha] at hvol
  have hSet : (fun t : ℝ => a*t) ⁻¹' Ioc (a*l) (a*u)=Ioc l u := by
    ext t
    simp only [mem_preimage,Set.mem_Ioc,mul_lt_mul_iff_right₀ ha,mul_le_mul_iff_right₀ ha]
  have hm : MeasurableEmbedding (fun t : ℝ => a*t) := by
    simpa only [Homeomorph.coe_mulLeft₀] using (Homeomorph.mulLeft₀ a ha.ne').measurableEmbedding
  calc
    _ = ∫⁻ θ, f θ ∂((ENNReal.ofReal a • Measure.map (fun t : ℝ => a*t) volume).restrict (Ioc (a*l) (a*u))) := by rw [hvol]
    _ = _ := by
      rw [Measure.restrict_smul,lintegral_smul_measure,Measure.restrict_map (measurable_const_mul a) measurableSet_Ioc,hSet,
        hm.lintegral_map]
      rfl

/-- The physical polar angle has total length 2π, whereas the source circle measure has mass one. -/
theorem lintegral_polar_angle (f : ℂ → ℝ≥0∞) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, f ((Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I)) =
      ENNReal.ofReal (2*Real.pi) * ∫⁻ t : Boundary, f (fourier (T := 1) 1 t) ∂circleMeasure := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (-Real.pi) Real.pi =ᵐ[volume] Ioc (-Real.pi) Real.pi)]
  have hSet : Ioc (-Real.pi) Real.pi=Ioc ((2*Real.pi)*(-1/2)) ((2*Real.pi)*(1/2)) := by
    congr 1 <;> ring
  rw [hSet]
  rw [setLIntegral_scaled_Ioc (2*Real.pi) (by positivity)]
  simp_rw [polar_angle_fourier]
  rw [circleMeasure_eq_volume]
  congr 1
  convert AddCircle.lintegral_preimage 1 (-1/2) (fun t : Boundary => f (fourier (T := 1) 1 t)) using 1; norm_num

/-- Polar Tonelli on the open unit disk, before normalizing area or angle. -/
theorem lintegral_disk_polar_angle (f : ℂ → ℝ≥0∞) (hf : Measurable (disk.indicator f)) :
    (∫⁻ z in disk, f z ∂(volume : Measure ℂ)) =
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f ((r : ℂ)*((Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I)) := by
  have hd : MeasurableSet disk := (isOpen_lt continuous_norm continuous_const).measurableSet
  let g := disk.indicator f
  have hg : Measurable g := hf
  have hc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1*g (Complex.polarCoord.symm p)) :=
    measurable_fst.ennreal_ofReal.mul (hg.comp hc.measurable)
  have hp := Complex.lintegral_comp_polarCoord_symm g
  change (∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1*g (Complex.polarCoord.symm p)) =
    ∫⁻ z : ℂ, g z at hp
  rw [show (∫⁻ z : ℂ, g z) = ∫⁻ z in disk, f z from lintegral_indicator hd f] at hp
  calc
    _ = ∫⁻ p in (Ioi (0 : ℝ)) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1*g (Complex.polarCoord.symm p) := by
      simpa only [Complex.polarCoord_target] using hp.symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r*g (Complex.polarCoord.symm (r,θ)) :=
      setLIntegral_prod _ hm.aemeasurable
    _ = ∫⁻ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator
        (fun r : ℝ => ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          f (Complex.polarCoord.symm (r,θ))) r := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      by_cases h1 : r<1
      · rw [indicator_of_mem (show r ∈ Iio (1 : ℝ) from h1)]
        have he (θ : ℝ) : g (Complex.polarCoord.symm (r,θ))=f (Complex.polarCoord.symm (r,θ)) := by
          apply indicator_of_mem
          change ‖Complex.polarCoord.symm (r,θ)‖<1
          simpa only [Complex.norm_polarCoord_symm,abs_of_pos hr] using h1
        simp_rw [he]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      · rw [indicator_of_notMem (show r ∉ Iio (1 : ℝ) from h1)]
        have he (θ : ℝ) : g (Complex.polarCoord.symm (r,θ))=0 := by
          apply indicator_of_notMem
          change ¬‖Complex.polarCoord.symm (r,θ)‖<1
          simpa only [Complex.norm_polarCoord_symm,abs_of_pos hr] using h1
        simp_rw [he,mul_zero]
        exact lintegral_zero
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        f (Complex.polarCoord.symm (r,θ)) := by
      rw [lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio (1 : ℝ) ∩ Ioi (0 : ℝ)=Ioo (0 : ℝ) 1 := by
        ext r
        simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Ioi,Set.mem_Ioo]
        tauto
      rw [hs]
    _ = _ := by simp only [Complex.polarCoord_symm_apply]

/-- Normalized area is π⁻¹ times planar volume; the radial factor is therefore exactly 2r. -/
theorem lintegral_diskArea_polar (f : ℂ → ℝ≥0∞) (hf : Measurable (disk.indicator f)) :
    (∫⁻ z, f z ∂diskArea) = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r) *
      ∫⁻ t : Boundary, f ((r : ℂ)*fourier (T := 1) 1 t) ∂circleMeasure := by
  have hπ0 : ENNReal.ofReal Real.pi ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
  have hπT : ENNReal.ofReal Real.pi ≠ ∞ := ENNReal.ofReal_ne_top
  have hInvT : (ENNReal.ofReal Real.pi)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hπ0
  have hConst : (ENNReal.ofReal Real.pi)⁻¹*ENNReal.ofReal (2*Real.pi)=2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    calc
      _ = ((ENNReal.ofReal Real.pi)⁻¹*ENNReal.ofReal Real.pi)*2 := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hπ0 hπT,one_mul]
  rw [diskArea,lintegral_smul_measure]
  change (ENNReal.ofReal Real.pi)⁻¹*(∫⁻ z in disk, f z) = _
  rw [lintegral_disk_polar_angle f hf]
  have hAngle (r : ℝ) := lintegral_polar_angle (fun z => f ((r : ℂ)*z))
  simp_rw [hAngle]
  rw [← lintegral_const_mul' _ _ hInvT]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  calc
    _ = ((ENNReal.ofReal Real.pi)⁻¹*ENNReal.ofReal (2*Real.pi))*ENNReal.ofReal r *
        (∫⁻ t : Boundary, f ((r : ℂ)*fourier (T := 1) 1 t) ∂circleMeasure) := by ring
    _ = _ := by rw [hConst,← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem measurable_disk_indicator_norm_sq (F : ℂ → ℂ) (hF : ContinuousOn F disk) :
    Measurable (disk.indicator (fun z => ENNReal.ofReal (‖F z‖^2))) := by
  classical
  change Measurable (disk.piecewise (fun z => ENNReal.ofReal (‖F z‖^2)) (fun _ => 0))
  exact (ENNReal.continuous_ofReal.comp_continuousOn (hF.norm.pow 2)).measurable_piecewise
    continuousOn_const (isOpen_lt continuous_norm continuous_const).measurableSet

theorem integral_pow_zero_one (k : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x^k)=1/((k+1 : ℕ) : ℝ) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y^(k+1)) (((k+1 : ℕ) : ℝ)*x^k) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k+1) x
  have hi : IntervalIntegrable (fun x : ℝ => ((k+1 : ℕ) : ℝ)*x^k) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => ((k+1 : ℕ) : ℝ)*x^k)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simp only [intervalIntegral.integral_const_mul,one_pow,zero_pow (Nat.succ_ne_zero k),sub_zero] at he
  apply (eq_div_iff (by exact_mod_cast (Nat.succ_ne_zero k) : ((k+1 : ℕ) : ℝ) ≠ 0)).mpr
  nlinarith

theorem lintegral_radial_monomial (n : ℕ) :
    (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r)*ENNReal.ofReal (r^(2*n))) =
      ENNReal.ofReal (1/((n : ℝ)+1)) := by
  have hi : IntegrableOn (fun r : ℝ => 2*r^(2*n+1)) (Ioo (0 : ℝ) 1) :=
    ((by fun_prop : Continuous (fun r : ℝ => 2*r^(2*n+1))).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have he : (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r)*ENNReal.ofReal (r^(2*n))) =
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r^(2*n+1)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hr.1.le : 0 ≤ 2*r)]
    congr 1
    rw [pow_succ]
    ring
  rw [he,← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg (by norm_num) (pow_nonneg hr.1.le _))]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,integral_pow_zero_one]
  congr 1
  push_cast
  field_simp
  ring

end TTO.Paper.Proved
