/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PoissonApproximationFoundations
public import TTO.VMOABoundsFoundations

/-! Uniform literal arc-oscillation convergence of actual Hardy Poisson radials. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved


theorem uniform_radialPoisson_oscillation_of_bound (f : BoundaryL2) (hf : InVMOA f)
    (B : ℝ) (hB : 0<B)
    (hBound : ∀ s : Boundary,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (f-boundaryTranslate s f) a b≤B) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (f-radialPoissonAverage n f) a b<ε := by
  intro ε hε
  obtain ⟨η,hη,hNear⟩ := uniform_meanOscillation_boundaryTranslate f hf (ε/2) (half_pos hε)
  let K : Set Boundary := {s | η≤‖s‖}
  have hK : IsClosed K := isClosed_le continuous_const continuous_norm
  have h0 : (0 : Boundary)∉K := by simpa only [K,mem_ofPred_eq,norm_zero,not_le] using hη
  have hTail := tendsto_radialPoissonMeasure_real_closed_tail K hK h0
  filter_upwards [hTail.eventually (gt_mem_nhds (div_pos (half_pos hε) hB))] with n hn
  intro a b hab hLen
  have hc : Continuous (fun s : Boundary => meanOscillation (f-boundaryTranslate s f) a b) :=
    (lipschitzWith_meanOscillation a b hab hLen).continuous.comp
      (continuous_const.sub (continuous_boundaryTranslate f))
  have hF : Integrable (fun s : Boundary => meanOscillation (f-boundaryTranslate s f) a b)
      (radialPoissonMeasure n) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : Integrable (K.indicator (fun _ : Boundary => B)) (radialPoissonMeasure n) :=
    (integrable_const B).indicator hK.measurableSet
  have hC : Integrable (fun _ : Boundary => ε/2) (radialPoissonMeasure n) := integrable_const _
  have hG : Integrable (fun s : Boundary => ε/2+K.indicator (fun _ => B) s)
      (radialPoissonMeasure n) := hC.add hI
  have hp : ∀ s : Boundary,meanOscillation (f-boundaryTranslate s f) a b≤
      ε/2+K.indicator (fun _ => B) s := by
    intro s
    by_cases hs : s∈K
    · rw [indicator_of_mem hs]
      linarith [hBound s a b hab hLen]
    · rw [indicator_of_notMem hs,add_zero]
      exact (hNear s (lt_of_not_ge hs) a b hab hLen).le
  have hInt := integral_mono_ae hF hG (Eventually.of_forall hp)
  have hEq : (∫ s,ε/2+K.indicator (fun _ : Boundary => B) s ∂radialPoissonMeasure n)=
      ε/2+B*(radialPoissonMeasure n).real K := by
    simp [integral_add hC hI,integral_indicator hK.measurableSet,smul_eq_mul,mul_comm]
  rw [hEq] at hInt
  have hSmall : B*(radialPoissonMeasure n).real K<ε/2 := by
    calc
      _ < B*((ε/2)/B) := mul_lt_mul_of_pos_left hn hB
      _ = _ := mul_div_cancel₀ _ hB.ne'
  have hj := meanOscillation_radialPoisson_residual_le n f a b hab hLen
  linarith


/-- Actual Poisson residuals converge uniformly over all literal real arcs. -/
theorem uniform_radialPoisson_meanOscillation (f : BoundaryL2) (hf : InVMOA f) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (f-radialPoissonAverage n f) a b<ε := by
  obtain ⟨B,hB,hBound⟩ := exists_uniform_translation_oscillation_bound f hf
  exact uniform_radialPoisson_oscillation_of_bound f hf B hB hBound

/-- The averages are the unchanged native Hardy radial boundary classes. -/
theorem uniform_hardyRadial_meanOscillation (g : Hardy) (hg : InVMOA g.val) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (g.val-(hardyRadialBoundary g (hankelRadius n)).val) a b<ε := by
  intro ε hε
  filter_upwards [uniform_radialPoisson_meanOscillation g.val hg ε hε] with n hn
  simpa only [radialPoisson_average_eq_hardyRadialBoundary n g] using hn


theorem inVMOA_iff_hardyRadial_approximation (g : Hardy) :
    InVMOA g.val ↔ ∀ ε : ℝ,0<ε → ∃ n : ℕ,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (g.val-(hardyRadialBoundary g (hankelRadius n)).val) a b<ε := by
  constructor
  · intro hg ε hε
    exact (uniform_hardyRadial_meanOscillation g hg ε hε).exists
  · intro hApprox
    apply inVMOA_of_uniform_meanOscillation_approximation g.val g.property
      (fun n => (hardyRadialBoundary g (hankelRadius n)).val) ?_ hApprox
    intro n
    rw [← hankelRadialContinuous_toL2 g n]
    apply continuous_toLp_inVMOA
    rw [hankelRadialContinuous_toL2]
    exact (hardyRadialBoundary g (hankelRadius n)).property

end TTO.Paper.Proved
