/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticPSubmeanFoundations
public import Mathlib.Analysis.Complex.Liouville
public import TTO.WeightedBergmanFoundations
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual local area submeans and derivative power estimates for every positive p. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric Real
open scoped ENNReal NNReal ComplexConjugate Topology
namespace TTO.Paper.Proved

/-- The period-one Haar integral is exactly the normalized native circle average. -/
theorem circleAverage_eq_boundary_integral (u : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    Real.circleAverage u c R =
      ∫ t : Boundary, u (c + (R : ℂ) * fourier (T := 1) 1 t) ∂circleMeasure := by
  rw [circleMeasure_eq_volume, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [zero_add]
  have h := intervalIntegral.integral_comp_mul_right
    (a := 0) (b := 1) (f := fun θ : ℝ => u (circleMap c R θ))
    (by positivity : 2 * Real.pi ≠ 0)
  simp only [zero_mul, one_mul, smul_eq_mul] at h
  rw [Real.circleAverage, smul_eq_mul, ← h]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  congr 1
  rw [circleMap, fourier_coe_apply]
  simp only [Int.cast_one, mul_one]
  congr 2
  push_cast
  ring_nf

/-- Continuity only on the closed unit disk gives genuine ordinary normalized-area integrability. -/
theorem integrable_real_disk_of_continuousOn_closedBall (u : ℂ → ℝ)
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) : Integrable u diskArea := by
  have hI := hu.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)
  have hi : IntegrableOn u disk volume := hI.mono_set (fun z hz => by
    simpa only [mem_closedBall, dist_zero_right] using (show ‖z‖ < 1 from hz).le)
  exact hi.smul_measure (by finiteness)

/-- Affine real-radius rescaling sends the closed unit disk into its actual closed ball. -/
theorem affine_disk_mem_closedBall {c z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : z ∈ closedBall (0 : ℂ) 1) : c + (R : ℂ) * z ∈ closedBall c R := by
  rw [mem_closedBall, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR]
  have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 hR

/-- Actual ordinary L¹ integrability on the rescaled local disk, without a global bound on F. -/
theorem integrable_analytic_local_area_power (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (hR : 0 ≤ R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 ≤ p) :
    Integrable (fun z => ‖F (c + (R : ℂ) * z)‖ ^ p) diskArea := by
  apply integrable_real_disk_of_continuousOn_closedBall
  exact ((hF.continuousOn.comp (by fun_prop : ContinuousOn
    (fun z : ℂ => c + (R : ℂ) * z) (closedBall (0 : ℂ) 1))
    (fun z hz => affine_disk_mem_closedBall hR hz)).norm).rpow_const
      (fun _ _ => Or.inr hp)

/-- A local analytic power submean for normalized area on the literal affine disk. -/
theorem analytic_norm_rpow_area_submean (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 < p) :
    ‖F c‖ ^ p ≤ ∫ z, ‖F (c + (R : ℂ) * z)‖ ^ p ∂diskArea := by
  let u : ℂ → ℝ := fun z => ‖F (c + (R : ℂ) * z)‖ ^ p
  have hu : Integrable u diskArea := integrable_analytic_local_area_power F c R p hR.le hF hp.le
  have hpI : Integrable (fun q : ℝ × Boundary => u (diskPolar q))
      (diskRadialMeasure.prod circleMeasure) := by
    have hm := hu
    rw [diskArea_eq_map_diskPolar] at hm
    exact (integrable_map_measure hm.aestronglyMeasurable
      continuous_diskPolar.measurable.aemeasurable).mp hm
  have hrad : Integrable (fun r : ℝ => ∫ t : Boundary,
      u ((r : ℂ) * fourier (T := 1) 1 t) ∂circleMeasure) diskRadialMeasure :=
    hpI.integral_prod_left
  rw [integral_diskArea_polar u hu]
  calc
    ‖F c‖ ^ p = ∫ _ : ℝ, ‖F c‖ ^ p ∂diskRadialMeasure := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hrad
      have hrAE : ∀ᵐ r ∂diskRadialMeasure, r ∈ Ioo (0 : ℝ) 1 := by
        exact (withDensity_absolutelyContinuous
          (volume.restrict (Ioo (0 : ℝ) 1)) (fun r => ENNReal.ofReal (2*r))).ae_le
            (ae_restrict_mem measurableSet_Ioo)
      filter_upwards [hrAE] with r hr
      have hRr : 0 < R * r := mul_pos hR hr.1
      have hFr : AnalyticOnNhd ℂ F (closedBall c (R * r)) :=
        hF.mono (closedBall_subset_closedBall (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2.le hR.le))
      have he := TTO.ComplexAnalysis.analytic_norm_rpow_submean hRr hFr hp
      rw [circleAverage_eq_boundary_integral] at he
      convert he using 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp [u]
        push_cast
        ring_nf

/-- Literal affine-disk change of variables, with the source's π-normalized area. -/
theorem integral_affine_diskArea (u : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R) :
    (∫ z, u (c + (R : ℂ) * z) ∂diskArea) =
      (Real.pi * R^2)⁻¹ * ∫ z in ball c R, u z := by
  let v : ℂ → ℝ := (ball c R).indicator u
  have hmem (z : ℂ) : c + R • z ∈ ball c R ↔ z ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hR.le, sub_zero]
    constructor <;> intro h <;> nlinarith
  have hfun : (fun z : ℂ => v (c + R • z)) =
      (ball (0 : ℂ) 1).indicator (fun z => u (c + R • z)) := by
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · simp only [v, indicator_of_mem hz, indicator_of_mem ((hmem z).2 hz)]
    · simp only [v, indicator_of_notMem hz, indicator_of_notMem (not_iff_not.mpr (hmem z) |>.2 hz)]
  have hs := Measure.integral_comp_smul (volume : Measure ℂ) (fun x => v (c + x)) R
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg R)),
    hfun, integral_indicator measurableSet_ball, integral_add_left_eq_self,
    show (∫ z, v z) = ∫ z in ball c R, u z from integral_indicator measurableSet_ball] at hs
  rw [diskArea, integral_smul_measure]
  change (ENNReal.ofReal Real.pi)⁻¹.toReal * (∫ z in disk, u (c + (R : ℂ) * z)) = _
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hd : disk = ball (0 : ℂ) 1 := by ext z; simp [disk, mem_ball, dist_zero_right]
  rw [hd]
  have he : (∫ z in ball (0 : ℂ) 1, u (c + (R : ℂ) * z)) =
      (R^2)⁻¹ * ∫ z in ball c R, u z := by
    simpa only [Complex.real_smul, smul_eq_mul] using hs
  rw [he]
  simp only [mul_inv_rev]
  ring

/-- The actual volume-ball form of analytic submean; no ordinary L¹ hypothesis is added. -/
theorem analytic_norm_rpow_volume_submean (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 < p) :
    ‖F c‖ ^ p ≤ (Real.pi * R^2)⁻¹ * ∫ z in ball c R, ‖F z‖ ^ p := by
  simpa only [integral_affine_diskArea (fun z => ‖F z‖ ^ p) c R hR] using
    analytic_norm_rpow_area_submean F c R p hR hF hp

/-- Every analytic local norm power is genuinely volume-integrable on its closed ball. -/
theorem integrableOn_analytic_norm_rpow_closedBall (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 ≤ p) :
    IntegrableOn (fun z => ‖F z‖ ^ p) (closedBall c R) := by
  exact (hF.continuousOn.norm.rpow_const (fun _ _ => Or.inr hp)).integrableOn_compact
    (isCompact_closedBall _ _)

/-- Local analytic power control is uniform on the entire inner closed ball.
The right-hand side is a genuine Lp area integral on the twice larger ball. -/
theorem analytic_norm_rpow_le_local_area (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c (2*R))) (hp : 0 < p)
    (z : ℂ) (hz : z ∈ closedBall c R) :
    ‖F z‖ ^ p ≤ (Real.pi * R^2)⁻¹ * ∫ x in ball c (2*R), ‖F x‖ ^ p := by
  have hS : closedBall z R ⊆ closedBall c (2*R) := by
    intro x hx
    rw [mem_closedBall] at hx hz ⊢
    exact (dist_triangle x z c).trans (by linarith)
  have hB : ball z R ⊆ ball c (2*R) := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have hzc : dist z c ≤ R := hz
    exact (dist_triangle x z c).trans_lt (by linarith)
  have hI : IntegrableOn (fun x => ‖F x‖ ^ p) (ball c (2*R)) :=
    (integrableOn_analytic_norm_rpow_closedBall F c (2*R) p hF hp.le).mono_set
      ball_subset_closedBall
  have hle : (∫ x in ball z R, ‖F x‖ ^ p) ≤
      ∫ x in ball c (2*R), ‖F x‖ ^ p :=
    setIntegral_mono_set hI (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Eventually.of_forall fun x hx => hB hx)
  exact (analytic_norm_rpow_volume_submean F z R p hR (hF.mono hS) hp).trans
    (mul_le_mul_of_nonneg_left hle (by positivity))

/-- Cauchy's estimate followed by the actual area submean controls arbitrary derivatives
by local Lp energy, including the full range 0 < p < 1. -/
theorem analytic_iteratedDeriv_rpow_le_local_area (F : ℂ → ℂ) (c : ℂ) (R p : ℝ)
    (n : ℕ) (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c (2*R))) (hp : 0 < p) :
    ‖iteratedDeriv n F c‖ ^ p ≤
      ((n.factorial : ℝ) / R^n) ^ p *
        ((Real.pi * R^2)⁻¹ * ∫ x in ball c (2*R), ‖F x‖ ^ p) := by
  let E : ℝ := (Real.pi * R^2)⁻¹ * ∫ x in ball c (2*R), ‖F x‖ ^ p
  have hE : 0 ≤ E := mul_nonneg (by positivity)
    (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hC : ∀ z ∈ sphere c R, ‖F z‖ ≤ E ^ p⁻¹ := by
    intro z hz
    exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hE hp).2
      (analytic_norm_rpow_le_local_area F c R p hR hF hp z (sphere_subset_closedBall hz))
  have hSmall : AnalyticOnNhd ℂ F (closedBall c R) :=
    hF.mono (closedBall_subset_closedBall (by linarith))
  have hDiff : DiffContOnCl ℂ F (ball c R) := by
    constructor
    · exact (hSmall.mono ball_subset_closedBall).differentiableOn
    · exact hSmall.continuousOn.mono
        (closure_minimal ball_subset_closedBall isClosed_closedBall)
  have hN := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hDiff hC
  have hpower := Real.rpow_le_rpow (norm_nonneg _) hN hp.le
  calc
    _ ≤ ((n.factorial : ℝ) * E ^ p⁻¹ / R^n) ^ p := hpower
    _ = ((n.factorial : ℝ) / R^n) ^ p * E := by
      rw [show (n.factorial : ℝ) * E ^ p⁻¹ / R^n =
        ((n.factorial : ℝ) / R^n) * E ^ p⁻¹ by ring]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hE _),
        Real.rpow_inv_rpow hE hp.ne']

/-- The local radius used in disk smoothing is a fixed quarter of the actual boundary distance. -/
def analyticLocalRadius (z : Disk) : ℝ := (1 - ‖z.val‖) / 4

theorem analyticLocalRadius_pos (z : Disk) : 0 < analyticLocalRadius z := by
  dsimp [analyticLocalRadius]
  have hz : ‖z.val‖ < 1 := z.property
  linarith

theorem closedBall_twice_analyticLocalRadius_subset_disk (z : Disk) :
    closedBall z.val (2 * analyticLocalRadius z) ⊆ disk := by
  intro x hx
  have hdist : dist x z.val ≤ 2 * analyticLocalRadius z := hx
  have hnorm : ‖x‖ ≤ dist x z.val + ‖z.val‖ := by
    simpa only [dist_zero_right] using dist_triangle x z.val (0 : ℂ)
  change ‖x‖ < 1
  dsimp [analyticLocalRadius] at hdist
  have hz : ‖z.val‖ < 1 := z.property
  linarith

/-- Arbitrary analytic derivatives in the actual open disk satisfy a genuine local Lp estimate. -/
theorem analytic_iteratedDeriv_rpow_le_disk_local_area (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (z : Disk) (p : ℝ) (n : ℕ) (hp : 0 < p) :
    ‖iteratedDeriv n F z.val‖ ^ p ≤
      ((n.factorial : ℝ) / analyticLocalRadius z ^ n) ^ p *
        ((Real.pi * analyticLocalRadius z ^ 2)⁻¹ *
          ∫ x in ball z.val (2 * analyticLocalRadius z), ‖F x‖ ^ p) :=
  analytic_iteratedDeriv_rpow_le_local_area F z.val (analyticLocalRadius z) p n
    (analyticLocalRadius_pos z) (hF.mono (closedBall_twice_analyticLocalRadius_subset_disk z)) hp

end TTO.Paper.Proved
