/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBoundaryFoundations

/-! Local radial circle Parseval for arbitrary disk-analytic functions.
Every coefficient estimate uses a larger compact radius; no global disk bound is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Cauchy's bound requires only a bound on this one compact circle. -/
theorem norm_diskTaylorCoeff_le_sphere (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) (M : ℝ)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖F z‖ ≤ M) (n : ℕ) :
    ‖diskTaylorCoeff F n‖ ≤ M / R ^ n := by
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ disk := by
    intro z hz
    exact lt_of_le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hR1
  have hd := hF.differentiableOn.diffContOnCl_ball hsub
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hd hM
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  calc
    ‖diskTaylorCoeff F n‖ = ‖iteratedDeriv n F 0‖ / (n.factorial : ℝ) := by
      simp only [diskTaylorCoeff,norm_div,Complex.norm_natCast]
    _ ≤ ((n.factorial : ℝ) * M / R ^ n) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right hc hn.le
    _ = M / R ^ n := by field_simp

theorem summable_norm_diskRadialCoeff_local (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖diskRadialCoeff F r n‖) := by
  obtain ⟨R,hrR,hR1⟩ := exists_between hr1
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ disk := by
    intro z hz
    exact lt_of_le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hR1
  have hFC : ContinuousOn F (Metric.closedBall (0 : ℂ) R) := hF.continuousOn.mono hsub
  obtain ⟨M,hMb⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hFC.norm
  have hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖F z‖ ≤ M :=
    fun z hz => hMb ⟨z,Metric.sphere_subset_closedBall hz,rfl⟩
  have hgeom : Summable (fun n : ℕ => M * (r/R)^n) :=
    (summable_geometric_of_lt_one (div_nonneg hr hR.le) ((div_lt_one hR).mpr hrR)).mul_left M
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hgeom
  calc
    ‖diskRadialCoeff F r n‖ = ‖diskTaylorCoeff F n‖ * r^n := by
      simp only [diskRadialCoeff,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr]
    _ ≤ (M/R^n)*r^n :=
      mul_le_mul_of_nonneg_right (norm_diskTaylorCoeff_le_sphere F hF R hR hR1 M hM n)
        (pow_nonneg hr n)
    _ = M*(r/R)^n := by rw [div_pow]; ring

theorem summable_diskRadialHardy_local (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => diskRadialCoeff F r n • hardyBasis n) := by
  refine Summable.of_norm_bounded (summable_norm_diskRadialCoeff_local F hF r hr hr1) fun n => ?_
  rw [norm_smul,hardyBasis.orthonormal.norm_eq_one,mul_one]

theorem hardyBasis_repr_diskRadialHardy_local (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    hardyBasis.repr (diskRadialHardy F r) n = diskRadialCoeff F r n := by
  rw [HilbertBasis.repr_apply_apply,diskRadialHardy,← innerSL_apply_apply ℂ,
    ContinuousLinearMap.map_tsum _ (summable_diskRadialHardy_local F hF r hr hr1),
    tsum_eq_single n fun m hm => by
      rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
        (orthonormal_iff_ite.mp hardyBasis.orthonormal n m).trans (ite_eq_right (Ne.symm hm)),
        mul_zero]]
  rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
    inner_self_eq_one_of_norm_eq_one (hardyBasis.orthonormal.norm_eq_one n),mul_one]

/-- The existing radial Hardy vector has its literal continuous circle representative, proved
from a compact local coefficient bound instead of an H∞ hypothesis. -/
theorem diskRadialHardy_ae_local (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (diskRadialHardy F r).val =ᵐ[circleMeasure] fun t => F ((r : ℂ) * fourier (T := 1) 1 t) := by
  let g : ℕ → C(Boundary, ℂ) := fun n => diskRadialCoeff F r n • fourier (T := 1) (n : ℤ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_norm_diskRadialCoeff_local F hF r hr hr1) fun n => ?_
    rw [norm_smul,fourier_norm,mul_one]
  have hcoe : (diskRadialHardy F r).val = ContinuousMap.toLp 2 circleMeasure ℂ (∑' n,g n) := by
    rw [diskRadialHardy,← hardy.subtypeL_apply,
      ContinuousLinearMap.map_tsum _ (summable_diskRadialHardy_local F hF r hr hr1),
      ContinuousLinearMap.map_tsum _ hg]
    congr 1
    funext n
    simp [g,coe_fourierBasis,hardyMode]
  rw [hcoe]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure (∑' n,g n)] with t ht
  rw [ht]
  refine (ContinuousMap.tsum_apply hg t).symm.trans ?_
  have hz : (r : ℂ) * fourier (T := 1) 1 t ∈ disk := by
    simpa only [disk,Set.mem_ofPred_eq,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_one,Circle.norm_coe,mul_one] using hr1
  have hs := hasSum_diskTaylorCoeff F hF hz
  rw [← hs.tsum_eq]
  congr 1
  funext n
  simp only [g,diskRadialCoeff,ContinuousMap.smul_apply,smul_eq_mul,fourier_apply,
    natCast_zsmul,AddCircle.toCircle_nsmul,Circle.coe_pow,one_zsmul,mul_pow]
  ring

/-- Exact radial circle Parseval with the native probability Haar measure and genuine Taylor
coefficients. It holds for every disk-analytic function, including functions unbounded on the disk. -/
theorem analytic_radial_circle_parseval (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫⁻ t, ENNReal.ofReal (‖F ((r : ℂ) * fourier (T := 1) 1 t)‖^2) ∂circleMeasure) =
      ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2 * r^(2*n)) := by
  have hs := hasSum_basis_inner_norm_sq hardyBasis (diskRadialHardy F r)
  simp_rw [← HilbertBasis.repr_apply_apply,
    hardyBasis_repr_diskRadialHardy_local F hF r hr hr1] at hs
  calc
    _ = ∫⁻ t, ENNReal.ofReal (‖(diskRadialHardy F r).val t‖^2) ∂circleMeasure := by
      apply lintegral_congr_ae
      exact ((diskRadialHardy_ae_local F hF r hr hr1).symm).fun_comp (fun z => ENNReal.ofReal (‖z‖^2))
    _ = ENNReal.ofReal (‖diskRadialHardy F r‖^2) := fourier_lintegral_norm_sq _
    _ = ∑' n : ℕ, ENNReal.ofReal (‖diskRadialCoeff F r n‖^2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖diskRadialCoeff F r n‖)
        hs.summable,hs.tsum_eq]
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      rw [diskRadialCoeff,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr,
        mul_pow,← pow_mul,Nat.mul_comm n 2]

/-- The literal Taylor coefficients of the frozen analytic extension are exactly its original
nonnegative Fourier coefficients, for every L² boundary function without a Hardy restriction. -/
theorem diskTaylorCoeff_analyticValue (f : BoundaryL2) (n : ℕ) :
    diskTaylorCoeff (analyticValue f) n = fourierCoeff f (n : ℤ) := by
  have hSeries := (hasFPowerSeriesOnBall_analyticValue f).hasFPowerSeriesAt
  have hTaylor := ((analyticOnNhd_analyticValue f) 0 (by norm_num [disk])).hasFPowerSeriesAt
  have he := hSeries.eq_formalMultilinearSeries hTaylor
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [analyticSeries,FormalMultilinearSeries.coeff_ofScalars,diskTaylorCoeff] using hc.symm

end TTO.Paper.Proved
