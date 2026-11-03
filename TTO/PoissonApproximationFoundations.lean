/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PoissonRadialAverageFoundations
public import TTO.PoissonConcentrationFoundations
public import TTO.VMOAAverageFoundations
public import TTO.VMOATranslationFoundations

/-! Checked compatibility of actual Poisson averages, translations and closed-tail mass. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem circleTranslate_eq_boundaryTranslate (s : ℝ) (f : BoundaryL2) :
    circleTranslate s f=boundaryTranslate (s : Boundary) f :=
  (boundaryTranslate_eq_domAddAct (s : Boundary) f).symm

theorem radialPoissonMeasure_real_set (n : ℕ) (K : Set Boundary) (hK : MeasurableSet K) :
    (radialPoissonMeasure n).real K=
      ∫ s in K,atomicPoissonKernel (hankelRadius n : ℂ) s ∂circleMeasure := by
  unfold Measure.real radialPoissonMeasure
  rw [withDensity_apply _ hK,
    ← ofReal_integral_eq_lintegral_ofReal (radialPoisson_integrable n).integrableOn
      (Eventually.of_forall (radialPoisson_tail_nonneg n))]
  exact ENNReal.toReal_ofReal (setIntegral_nonneg hK (fun s _ => radialPoisson_tail_nonneg n s))

theorem tendsto_radialPoissonMeasure_real_closed_tail (K : Set Boundary) (hK : IsClosed K)
    (h0 : (0 : Boundary)∉K) :
    Tendsto (fun n => (radialPoissonMeasure n).real K) atTop (𝓝 0) := by
  have he (n : ℕ) : (radialPoissonMeasure n).real K=
      ∫ s in K,atomicPoissonKernel (hankelRadius n : ℂ) s ∂circleMeasure :=
    radialPoissonMeasure_real_set n K hK.measurableSet
  simpa only [he] using tendsto_radialPoisson_closed_tail K hK h0


theorem meanOscillation_radialPoisson_residual_le (n : ℕ) (f : BoundaryL2)
    (a b : ℝ) (hab : a<b) (hLen : b-a≤1) :
    meanOscillation (f-radialPoissonAverage n f) a b≤
      ∫ s,meanOscillation (f-boundaryTranslate s f) a b ∂radialPoissonMeasure n := by
  have hConst : Integrable (fun _ : Boundary => f) (radialPoissonMeasure n) := integrable_const f
  have hTrans := integrable_radialPoisson_boundaryTranslate n f
  have hc : Continuous (fun s : Boundary => meanOscillation (f-boundaryTranslate s f) a b) :=
    (lipschitzWith_meanOscillation a b hab hLen).continuous.comp
      (continuous_const.sub (continuous_boundaryTranslate f))
  have hMO : Integrable (fun s : Boundary => meanOscillation (f-boundaryTranslate s f) a b)
      (radialPoissonMeasure n) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj := meanOscillation_integral_le (radialPoissonMeasure n)
    (fun s => f-boundaryTranslate s f) a b hab hLen (hConst.sub hTrans) hMO
  simpa [integral_sub hConst hTrans,radialPoissonAverage] using hj

theorem uniform_meanOscillation_boundaryTranslate (f : BoundaryL2) (hf : InVMOA f) :
    ∀ ε : ℝ,0<ε → ∃ η : ℝ,0<η ∧ ∀ s : Boundary,‖s‖<η →
      ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation (f-boundaryTranslate s f) a b<ε := by
  intro ε hε
  obtain ⟨η,hη,hU⟩ := uniform_meanOscillation_translation f hf ε hε
  refine ⟨η/2,half_pos hη,?_⟩
  intro s hs a b hab hLen
  obtain ⟨x,hx,hNorm⟩ := QuotientAddGroup.exists_norm_mk_lt s (half_pos hη)
  have hxNorm : ‖x‖<η := by linarith
  have h := hU x hxNorm a b hab hLen
  rw [circleTranslate_eq_boundaryTranslate,hx] at h
  exact h

end TTO.Paper.Proved
