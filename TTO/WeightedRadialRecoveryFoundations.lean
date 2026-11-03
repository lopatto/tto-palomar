/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedBergmanFoundations
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Radial Euler recovery and its actual normalized disk-area bound.
These are analytic ingredients for the trace-class necessary direction. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea := by
  constructor
  rw [diskArea_eq_map_diskPolar,Measure.map_apply continuous_diskPolar.measurable
    MeasurableSet.univ,preimage_univ,measure_univ]

/-- The coefficient multiplier (n+3)/6 has an elementary radial inverse. -/
def radialEulerTransform (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z*deriv G z+3*G z)/6

theorem analyticOnNhd_radialEulerTransform (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) :
    AnalyticOnNhd ℂ (radialEulerTransform G) disk := by
  intro z hz
  exact ((analyticAt_id.mul (hG z hz).deriv).add (analyticAt_const.mul (hG z hz))).div_const

/-- Every closed radial segment lies strictly inside the disk, including its endpoints. -/
theorem radial_Icc_mapsTo_disk (z : Disk) :
    MapsTo (fun t : ℝ => (t : ℂ)*z.val) (Icc (0 : ℝ) 1) disk := by
  intro t ht
  change ‖(t : ℂ)*z.val‖<1
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.1]
  exact lt_of_le_of_lt (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z.val)) z.property

/-- Exact recovery uses ordinary Bochner integration on a compact real interval. -/
theorem radialEuler_recovery (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (z : Disk) :
    G z.val=6*∫ t : ℝ in (0 : ℝ)..1, (t : ℂ)^2*radialEulerTransform G ((t : ℂ)*z.val) := by
  have hD (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => (s : ℂ)^3*G ((s : ℂ)*z.val))
        (6*(t : ℂ)^2*radialEulerTransform G ((t : ℂ)*z.val)) t := by
    have hGd := (hG _ (radial_Icc_mapsTo_disk z ht)).differentiableAt.hasDerivAt
    have hc := (hasDerivAt_pow 3 (t : ℂ)).mul
      (hGd.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z.val))
    convert hc.comp_ofReal using 1
    · rfl
    · norm_num [radialEulerTransform,Function.comp_apply]
      ring
  have hC : ContinuousOn (fun t : ℝ =>
      (6 : ℂ)*(t : ℂ)^2*radialEulerTransform G ((t : ℂ)*z.val)) (Icc (0 : ℝ) 1) :=
    (continuous_const.mul (Complex.continuous_ofReal.pow 2)).continuousOn.mul
      ((analyticOnNhd_radialEulerTransform G hG).continuousOn.comp
        (by fun_prop) (radial_Icc_mapsTo_disk z))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hD t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (hC.intervalIntegrable_of_Icc zero_le_one)
  simp only [Complex.ofReal_one,one_pow,one_mul,Complex.ofReal_zero,
    zero_pow (by decide : 3≠0),zero_mul,sub_zero] at he
  simp_rw [mul_assoc] at he
  rw [intervalIntegral.integral_const_mul] at he
  exact he.symm

/-- Positive planar dilation, with its exact real dimension-two Jacobian. -/
theorem lintegral_disk_volume_rescale (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (t : ℝ) (ht : 0<t) :
    (∫⁻ w in Metric.ball (0 : ℂ) t,f w ∂volume) =
      ENNReal.ofReal (t^2)*(∫⁻ z in disk,f ((t : ℂ)*z) ∂volume) := by
  have hVol : ENNReal.ofReal (t^2) •
      Measure.map (fun z : ℂ => t • z) volume = volume := by
    rw [Measure.map_addHaar_smul (volume : Measure ℂ) ht.ne',smul_smul]
    have hC : ENNReal.ofReal (t^2)*
        ENNReal.ofReal |(t^Module.finrank ℝ ℂ)⁻¹|=1 := by
      rw [Complex.finrank_real_complex,abs_inv,abs_of_nonneg (sq_nonneg t),
        ← ENNReal.ofReal_mul (sq_nonneg t),mul_inv_cancel₀ (pow_ne_zero 2 ht.ne'),
        ENNReal.ofReal_one]
    rw [hC,one_smul]
  have hSet : (fun z : ℂ => t • z) ⁻¹' Metric.ball (0 : ℂ) t=disk := by
    ext z
    simp only [mem_preimage,Metric.mem_ball,dist_zero_right,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht,disk,Set.mem_ofPred_eq]
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ ht : t*‖z‖<t*1 ↔ ‖z‖<1)
  calc
    _ = ∫⁻ w,f w ∂((ENNReal.ofReal (t^2) •
        Measure.map (fun z : ℂ => t • z) volume).restrict (Metric.ball (0 : ℂ) t)) := by rw [hVol]
    _ = _ := by
      rw [Measure.restrict_smul,Measure.restrict_map (measurable_const_smul t) measurableSet_ball,
        hSet,lintegral_smul_measure,lintegral_map' hf.aemeasurable (measurable_const_smul t).aemeasurable]
      rfl

/-- Dilation of the normalized open disk includes exactly the smaller disk. -/
theorem lintegral_diskArea_rescale (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    ENNReal.ofReal (t^2)*(∫⁻ z,f ((t : ℂ)*z) ∂diskArea) =
      ∫⁻ z,(Metric.ball (0 : ℂ) t).indicator f z ∂diskArea := by
  have hSub : Metric.ball (0 : ℂ) t ⊆ disk := by
    intro z hz
    exact lt_of_lt_of_le (by simpa only [Metric.mem_ball,dist_zero_right] using hz) ht1
  rw [diskArea,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_indicator measurableSet_ball,Measure.restrict_restrict measurableSet_ball,
    Set.inter_eq_left.mpr hSub,lintegral_disk_volume_rescale f hf t ht]
  ring

/-- Tonelli plus the planar Jacobian gives the exact radial averaging identity,
including infinite integrals. -/
theorem lintegral_diskArea_radial_average (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*f ((t : ℂ)*z) ∂volume ∂diskArea) =
      ∫⁻ z,ENNReal.ofReal (1-‖z‖)*f z ∂diskArea := by
  have hM : Measurable (fun p : ℂ × ℝ =>
      ENNReal.ofReal (p.2^2)*f ((p.2 : ℂ)*p.1)) :=
    (by fun_prop : Measurable (fun p : ℂ × ℝ => ENNReal.ofReal (p.2^2))).mul
      (hf.comp (by fun_prop))
  have hSet : MeasurableSet {p : ℝ × ℂ | ‖p.2‖<p.1} :=
    measurableSet_lt measurable_snd.norm measurable_fst
  have hM2 : Measurable (fun p : ℝ × ℂ => (Metric.ball (0 : ℂ) p.1).indicator f p.2) := by
    have he : (fun p : ℝ × ℂ => (Metric.ball (0 : ℂ) p.1).indicator f p.2) =
        {p : ℝ × ℂ | ‖p.2‖<p.1}.indicator (f ∘ Prod.snd) := by
      funext p
      classical
      by_cases h : ‖p.2‖<p.1 <;>
        simp [Metric.mem_ball,dist_zero_right,h]
    rw [he]
    exact (hf.comp measurable_snd).indicator hSet
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) 1,∫⁻ z,ENNReal.ofReal (t^2)*f ((t : ℂ)*z) ∂diskArea :=
      lintegral_lintegral_swap hM.aemeasurable
    _ = ∫⁻ t in Ioo (0 : ℝ) 1,∫⁻ z,(Metric.ball (0 : ℂ) t).indicator f z ∂diskArea := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_diskArea_rescale f hf t ht.1 ht.2.le]
    _ = ∫⁻ z,∫⁻ t in Ioo (0 : ℝ) 1,(Metric.ball (0 : ℂ) t).indicator f z ∂volume ∂diskArea :=
      lintegral_lintegral_swap hM2.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      have hInd (t : ℝ) : (Metric.ball (0 : ℂ) t).indicator f z =
          (Ioi ‖z‖).indicator (fun _ : ℝ => f z) t := by
        by_cases ht : ‖z‖<t
        · rw [indicator_of_mem (by simpa only [Metric.mem_ball,dist_zero_right] using ht),
            indicator_of_mem (show t∈Ioi ‖z‖ from ht)]
        · rw [indicator_of_notMem (by simpa only [Metric.mem_ball,dist_zero_right] using ht),
            indicator_of_notMem (show t∉Ioi ‖z‖ from ht)]
      simp_rw [hInd]
      rw [lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
      have hs : Ioi ‖z‖ ∩ Ioo (0 : ℝ) 1=Ioo ‖z‖ 1 := by
        ext t
        constructor
        · intro h
          exact ⟨h.1,h.2.2⟩
        · intro h
          exact ⟨h.1,lt_of_le_of_lt (norm_nonneg z) h.1,h.2⟩
      rw [hs]
      simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
      exact mul_comm _ _

/-- Pointwise radial inversion gives an extended nonnegative integral estimate. -/
theorem radialEuler_norm_le_lintegral (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (z : Disk) :
    ENNReal.ofReal ‖G z.val‖ ≤ 6*(∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t^2)*ENNReal.ofReal ‖radialEulerTransform G ((t : ℂ)*z.val)‖) := by
  have hC : ContinuousOn (fun t : ℝ =>
      t^2*‖radialEulerTransform G ((t : ℂ)*z.val)‖) (Icc (0 : ℝ) 1) :=
    (continuous_pow 2).continuousOn.mul
      (((analyticOnNhd_radialEulerTransform G hG).continuousOn.comp
        (by fun_prop) (radial_Icc_mapsTo_disk z)).norm)
  have hI : IntegrableOn (fun t : ℝ => t^2*‖radialEulerTransform G ((t : ℂ)*z.val)‖)
      (Ioo (0 : ℝ) 1) := hC.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hRec := radialEuler_recovery G hG z
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo] at hRec
  have hReal : ‖G z.val‖≤6*∫ t in Ioo (0 : ℝ) 1,
      t^2*‖radialEulerTransform G ((t : ℂ)*z.val)‖ := by
    calc
      _ = 6*‖∫ t in Ioo (0 : ℝ) 1,(t : ℂ)^2*radialEulerTransform G ((t : ℂ)*z.val)‖ := by
        rw [hRec,norm_mul]
        norm_num
      _ ≤ 6*∫ t in Ioo (0 : ℝ) 1,‖(t : ℂ)^2*radialEulerTransform G ((t : ℂ)*z.val)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)
      _ = _ := by simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hEN := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤6),ENNReal.ofReal_ofNat,
    ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun t =>
      mul_nonneg (sq_nonneg t) (norm_nonneg _))] at hEN
  have he (t : ℝ) : ENNReal.ofReal (t^2*‖radialEulerTransform G ((t : ℂ)*z.val)‖) =
      ENNReal.ofReal (t^2)*ENNReal.ofReal ‖radialEulerTransform G ((t : ℂ)*z.val)‖ :=
    ENNReal.ofReal_mul (sq_nonneg t)
  simpa only [he] using hEN

/-- The radial inverse is bounded from the literal weighted area L¹ space to area L¹.
Infinite energies are retained until a later application supplies finiteness. -/
theorem radialEuler_area_norm_le (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) :
    (∫⁻ z,ENNReal.ofReal ‖G z‖ ∂diskArea) ≤
      6*∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖radialEulerTransform G z‖) ∂diskArea := by
  classical
  let f : ℂ → ℝ≥0∞ := disk.indicator (fun z => ENNReal.ofReal ‖radialEulerTransform G z‖)
  have hF := (analyticOnNhd_radialEulerTransform G hG).continuousOn
  have hf : Measurable f := by
    change Measurable (disk.piecewise (fun z => ENNReal.ofReal ‖radialEulerTransform G z‖) (fun _ => 0))
    exact (ENNReal.continuous_ofReal.comp_continuousOn hF.norm).measurable_piecewise
      continuousOn_const (isOpen_lt continuous_norm continuous_const).measurableSet
  have hfOn (z : ℂ) (hz : z∈disk) : f z=ENNReal.ofReal ‖radialEulerTransform G z‖ :=
    indicator_of_mem hz _
  have hB (z : ℂ) (hz : z∈disk) : ENNReal.ofReal ‖G z‖ ≤
      6*(∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*f ((t : ℂ)*z)) := by
    have h := radialEuler_norm_le_lintegral G hG ⟨z,hz⟩
    have he : (∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*
        ENNReal.ofReal ‖radialEulerTransform G ((t : ℂ)*z)‖) =
        ∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*f ((t : ℂ)*z) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [hfOn _ (radial_Icc_mapsTo_disk ⟨z,hz⟩ ⟨ht.1.le,ht.2.le⟩)]
    exact h.trans_eq (congrArg (fun q : ℝ≥0∞ => 6*q) he)
  have hW : (∫⁻ z,ENNReal.ofReal (1-‖z‖)*f z ∂diskArea) ≤
      ∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖radialEulerTransform G z‖) ∂diskArea := by
    apply lintegral_mono_ae
    filter_upwards [ae_mem_diskArea] with z hz
    have hz1 : ‖z‖<1 := hz
    rw [hfOn z hz,← ENNReal.ofReal_mul (sub_nonneg.mpr hz1.le)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hz1.le (norm_nonneg z)]
  calc
    _ ≤ ∫⁻ z,6*(∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*f ((t : ℂ)*z)) ∂diskArea :=
      lintegral_mono_ae (ae_mem_diskArea.mono (fun z hz => hB z hz))
    _ = 6*(∫⁻ z,∫⁻ t in Ioo (0 : ℝ) 1,ENNReal.ofReal (t^2)*f ((t : ℂ)*z) ∂volume ∂diskArea) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ = 6*∫⁻ z,ENNReal.ofReal (1-‖z‖)*f z ∂diskArea := by
      rw [lintegral_diskArea_radial_average f hf]
    _ ≤ _ := mul_le_mul_right hW 6

/-- Actual weighted L¹ integrability implies ordinary area L¹ integrability of the
radial inverse, with the explicit constant six. -/
theorem radialEuler_integrable_area (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk)
    (hI : Integrable (radialEulerTransform G)
      (diskArea.withDensity (fun z => ENNReal.ofReal (1-‖z‖^2)))) :
    Integrable G diskArea ∧ (∫ z,‖G z‖ ∂diskArea) ≤
      6*∫ z,‖radialEulerTransform G z‖ ∂(diskArea.withDensity (fun z => ENNReal.ofReal (1-‖z‖^2))) := by
  let ν := diskArea.withDensity (fun z : ℂ => ENNReal.ofReal (1-‖z‖^2))
  have hNorm := ofReal_integral_norm_eq_lintegral_enorm hI
  simp only [← ofReal_norm] at hNorm
  have hEq : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖radialEulerTransform G z‖) ∂diskArea) =
      ENNReal.ofReal (∫ z,‖radialEulerTransform G z‖ ∂ν) := by
    calc
      _ = ∫⁻ z,ENNReal.ofReal (1-‖z‖^2)*ENNReal.ofReal ‖radialEulerTransform G z‖ ∂diskArea := by
        apply lintegral_congr_ae
        filter_upwards [ae_mem_diskArea] with z hz
        have hz1 : ‖z‖<1 := hz
        have hz2 : ‖z‖^2≤1 := by nlinarith [norm_nonneg z]
        exact ENNReal.ofReal_mul (sub_nonneg.mpr hz2)
      _ = ∫⁻ z,ENNReal.ofReal ‖radialEulerTransform G z‖ ∂ν := by
        symm
        exact lintegral_withDensity_eq_lintegral_mul₀' (by fun_prop)
          hI.norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = _ := hNorm.symm
  have hB := radialEuler_area_norm_le G hG
  rw [hEq] at hB
  have hFin : (6 : ℝ≥0∞)*ENNReal.ofReal (∫ z,‖radialEulerTransform G z‖ ∂ν)<∞ := by finiteness
  have hGI := integrable_of_analytic_disk_lintegral_norm_lt_top G hG (hB.trans_lt hFin)
  refine ⟨hGI,?_⟩
  have hGN := ofReal_integral_norm_eq_lintegral_enorm hGI
  simp only [← ofReal_norm] at hGN
  rw [← hGN] at hB
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num : (0 : ℝ)≤6)
    (integral_nonneg (fun _ => norm_nonneg _)))).mp
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤6),ENNReal.ofReal_ofNat] using hB

end TTO.Paper.Proved
