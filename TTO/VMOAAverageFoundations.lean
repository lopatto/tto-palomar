/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcL2OscillationFoundations
public import Mathlib.Analysis.Convex.Integral

/-! Native convex averaging of the literal real-arc mean oscillation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem meanOscillation_abs_sub_le_l2 (f g : BoundaryL2) (a b : ℝ)
    (hab : a<b) (hLen : b-a≤1) :
    |meanOscillation f a b-meanOscillation g a b|≤2*‖f-g‖/Real.sqrt (b-a) := by
  have hFirst := meanOscillation_add_le (f-g) g a b hab hLen
  rw [sub_add_cancel] at hFirst
  have hSecond := meanOscillation_add_le (g-f) f a b hab hLen
  rw [sub_add_cancel] at hSecond
  have hFG := meanOscillation_le_l2 (f-g) a b hab hLen
  have hGF := meanOscillation_le_l2 (g-f) a b hab hLen
  rw [norm_sub_rev] at hGF
  rw [abs_le]
  constructor <;> linarith

theorem lipschitzWith_meanOscillation (a b : ℝ) (hab : a<b) (hLen : b-a≤1) :
    LipschitzWith (Real.toNNReal (2/Real.sqrt (b-a)))
      (fun f : BoundaryL2 => meanOscillation f a b) := by
  apply LipschitzWith.of_dist_le'
  intro f g
  simp only [dist_eq_norm,Real.norm_eq_abs]
  convert meanOscillation_abs_sub_le_l2 f g a b hab hLen using 1; ring

theorem convexOn_meanOscillation (a b : ℝ) (hab : a<b) (hLen : b-a≤1) :
    ConvexOn ℝ univ (fun f : BoundaryL2 => meanOscillation f a b) := by
  refine ⟨convex_univ,?_⟩
  intro f hf g hg r s hr hs hrs
  change meanOscillation ((r : ℂ) • f+(s : ℂ) • g) a b≤
    r*meanOscillation f a b+s*meanOscillation g a b
  have h := meanOscillation_add_le ((r : ℂ) • f) ((s : ℂ) • g) a b hab hLen
  rw [meanOscillation_smul _ _ _ _ hLen,meanOscillation_smul _ _ _ _ hLen,
    Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hr,Real.norm_of_nonneg hs] at h
  exact h

/-- Jensen's inequality for actual L²-valued Bochner averaging and the frozen arc formula. -/
theorem meanOscillation_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → BoundaryL2)
    (a b : ℝ) (hab : a<b) (hLen : b-a≤1)
    (hF : Integrable F μ)
    (hMO : Integrable (fun t => meanOscillation (F t) a b) μ) :
    meanOscillation (∫ t,F t ∂μ) a b≤∫ t,meanOscillation (F t) a b ∂μ := by
  exact (convexOn_meanOscillation a b hab hLen).map_integral_le
    (lipschitzWith_meanOscillation a b hab hLen).continuous.continuousOn
    isClosed_univ (Eventually.of_forall fun _ => mem_univ _) hF hMO

end TTO.Paper.Proved
