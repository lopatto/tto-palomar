/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Native Jensen theory gives analytic power submeans for every positive exponent.
Boundary zeros are handled by codiscrete invariance, rather than a nonvanishing
or logarithmic-integrability assumption on the theorem's inputs. -/
@[expose] public section
noncomputable section
open Filter MeasureTheory Metric Set Real MeromorphicOn
open scoped Topology
namespace TTO.ComplexAnalysis

/-- The elementary exponential Jensen inequality for normalized circle averages. -/
theorem exp_circleAverage_le {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : CircleIntegrable u c R)
    (he : CircleIntegrable (fun z => Real.exp (u z)) c R) :
    Real.exp (circleAverage u c R) ≤
      circleAverage (fun z => Real.exp (u z)) c R := by
  let A := circleAverage u c R
  have hsub : CircleIntegrable (fun z => u z - A) c R :=
    hu.sub (circleIntegrable_const A c R)
  have hlin : CircleIntegrable (fun z => (u z - A) + 1) c R :=
    hsub.add (circleIntegrable_const 1 c R)
  have hexp : CircleIntegrable (fun z => Real.exp (u z - A)) c R := by
    have hh := he.div_const (Real.exp A)
    change IntervalIntegrable (fun θ => Real.exp (u (circleMap c R θ) - A)) volume 0 (2 * Real.pi)
    simpa only [Real.exp_sub] using hh
  have hm := circleAverage_mono hlin hexp (fun z _ => Real.add_one_le_exp (u z - A))
  have hleft : circleAverage (fun z => (u z - A) + 1) c R = 1 := by
    rw [circleAverage_fun_add hsub (circleIntegrable_const 1 c R),
      circleAverage_fun_sub hu (circleIntegrable_const A c R)]
    simp only [circleAverage_const]
    dsimp [A]
    ring
  have hright : circleAverage (fun z => Real.exp (u z - A)) c R =
      circleAverage (fun z => Real.exp (u z)) c R / Real.exp A := by
    simp only [Real.exp_sub, div_eq_mul_inv]
    simpa only [smul_eq_mul, mul_comm] using
      (circleAverage_fun_smul (a := (Real.exp A)⁻¹)
        (f := fun z => Real.exp (u z)) (c := c) (R := R))
  rw [hleft, hright] at hm
  simpa only [one_mul] using (le_div_iff₀ (Real.exp_pos A)).mp hm

/-- Native analytic Jensen formula, with its nonnegative zero contribution retained. -/
theorem log_norm_center_le_circleAverage {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ circleAverage (fun z => Real.log ‖F z‖) c R := by
  have hFa : AnalyticOnNhd ℂ F (closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hF
  have hsum : 0 ≤ ∑ᶠ z, (MeromorphicOn.divisor F (closedBall c |R|) z : ℝ) *
      Real.log (R * ‖c - z‖⁻¹) := by
    apply finsum_nonneg
    intro z
    by_cases hz : z ∈ closedBall c |R|
    · apply mul_nonneg (by exact_mod_cast hFa.divisor_nonneg z)
      by_cases hn : ‖c - z‖ = 0
      · simp only [hn, inv_zero, mul_zero, Real.log_zero, le_refl]
      · apply Real.log_nonneg
        have hnorm : 0 < ‖c - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
        have hle : ‖c - z‖ ≤ R := by
          simpa only [mem_closedBall, dist_eq_norm', abs_of_pos hR] using hz
        simpa only [div_eq_mul_inv] using (one_le_div hnorm).2 hle
    · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
        (MeromorphicOn.divisor F (closedBall c |R|)) hz,
        Int.cast_zero, zero_mul, le_refl]
  rw [hFa.circleAverage_log_norm hR.ne' hc]
  linarith

/-- Every positive real power of the norm of an analytic function is circle integrable. -/
theorem analytic_circleIntegrable_norm_rpow {F : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hR : 0 ≤ R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 ≤ p) :
    CircleIntegrable (fun z => ‖F z‖ ^ p) c R := by
  apply ContinuousOn.circleIntegrable hR
  exact (hF.continuousOn.mono sphere_subset_closedBall).norm.rpow_const
    (fun _ _ => Or.inr hp)

/-- The power-submean inequality has no restriction p ≥ 1 and permits boundary zeros. -/
theorem analytic_norm_rpow_submean {F : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hp : 0 < p) :
    ‖F c‖ ^ p ≤ circleAverage (fun z => ‖F z‖ ^ p) c R := by
  by_cases hc : F c = 0
  · rw [hc, norm_zero, Real.zero_rpow hp.ne']
    exact circleAverage_nonneg_of_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hFa : AnalyticOnNhd ℂ F (closedBall c |R|) := by
    simpa only [abs_of_pos hR] using hF
  have hNZ : ∀ᶠ z in codiscreteWithin (closedBall c |R|), F z ≠ 0 := by
    rcases hFa.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_closedBall c |R|).isPreconnected with hzero | hnz
    · exact (hc (hzero (by simp))).elim
    · exact hnz
  have hEq : (fun z => Real.exp (p * Real.log ‖F z‖)) =ᶠ[
      codiscreteWithin (sphere c |R|)] (fun z => ‖F z‖ ^ p) := by
    filter_upwards [codiscreteWithin_mono sphere_subset_closedBall hNZ] with z hz
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 1
    ring
  have hpow := analytic_circleIntegrable_norm_rpow hR.le hF hp.le
  have hlog : CircleIntegrable (fun z => Real.log ‖F z‖) c R :=
    (hFa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hplog : CircleIntegrable (fun z => p * Real.log ‖F z‖) c R := hlog.const_mul p
  have hexp : CircleIntegrable (fun z => Real.exp (p * Real.log ‖F z‖)) c R :=
    CircleIntegrable.congr_codiscreteWithin hEq.symm hpow
  calc
    ‖F c‖ ^ p = Real.exp (p * Real.log ‖F c‖) := by
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hc)]
      congr 1
      ring
    _ ≤ Real.exp (p * circleAverage (fun z => Real.log ‖F z‖) c R) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (log_norm_center_le_circleAverage hR hF hc) hp.le)
    _ = Real.exp (circleAverage (fun z => p * Real.log ‖F z‖) c R) := by
      congr 1
      simpa only [smul_eq_mul] using
        (circleAverage_fun_smul (a := p) (f := fun z => Real.log ‖F z‖)
          (c := c) (R := R)).symm
    _ ≤ circleAverage (fun z => Real.exp (p * Real.log ‖F z‖)) c R :=
      exp_circleAverage_le hplog hexp
    _ = circleAverage (fun z => ‖F z‖ ^ p) c R :=
      circleAverage_congr_codiscreteWithin hEq hR.ne'

end TTO.ComplexAnalysis
