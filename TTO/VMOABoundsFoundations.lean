/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PoissonApproximationFoundations

/-! Finite global bounds for the literal VMOA arc oscillations and all translations. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem exists_uniform_meanOscillation_bound (f : BoundaryL2) (hf : InVMOA f) :
    ∃ B : ℝ, 0<B ∧ ∀ a b : ℝ, a<b → b-a≤1 → meanOscillation f a b≤B := by
  obtain ⟨δ,hδ,hSmall⟩ := hf.2 1 zero_lt_one
  let d := min δ 1
  have hd : 0<d := lt_min hδ zero_lt_one
  have hSqrt : 0<Real.sqrt d := Real.sqrt_pos.mpr hd
  have hQ : 0≤2*‖f‖/Real.sqrt d := by positivity
  refine ⟨1+2*‖f‖/Real.sqrt d,by positivity,?_⟩
  intro a b hab hLen
  by_cases hShort : b-a≤d
  · have h := hSmall a b hab hShort
    linarith
  · have hLong : d≤b-a := (lt_of_not_ge hShort).le
    have hD := Real.sqrt_le_sqrt hLong
    have hBound := meanOscillation_le_l2 f a b hab hLen
    have hRatio : 2*‖f‖/Real.sqrt (b-a)≤2*‖f‖/Real.sqrt d :=
      div_le_div_of_nonneg_left (by positivity) hSqrt hD
    linarith

theorem exists_uniform_translation_oscillation_bound (f : BoundaryL2) (hf : InVMOA f) :
    ∃ B : ℝ, 0<B ∧ ∀ s : Boundary, ∀ a b : ℝ, a<b → b-a≤1 →
      meanOscillation (f-boundaryTranslate s f) a b≤B := by
  obtain ⟨B,hB,hBound⟩ := exists_uniform_meanOscillation_bound f hf
  refine ⟨2*B,by positivity,?_⟩
  intro s a b hab hLen
  obtain ⟨x,hx,hNorm⟩ := QuotientAddGroup.exists_norm_mk_lt s zero_lt_one
  have hShift : meanOscillation (boundaryTranslate s f) a b≤B := by
    have h := hBound (a+x) (b+x) (by linarith) (by linarith)
    rw [← meanOscillation_circleTranslate f x a b hab hLen,
      circleTranslate_eq_boundaryTranslate,hx] at h
    exact h
  have hNeg : meanOscillation (-boundaryTranslate s f) a b=
      meanOscillation (boundaryTranslate s f) a b := by
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using
      meanOscillation_smul (-1 : ℂ) (boundaryTranslate s f) a b hLen
  have hSum := meanOscillation_add_le f (-boundaryTranslate s f) a b hab hLen
  rw [hNeg] at hSum
  have hSum' : meanOscillation (f-boundaryTranslate s f) a b≤
      meanOscillation f a b+meanOscillation (boundaryTranslate s f) a b := by
    simpa only [sub_eq_add_neg] using hSum
  have hF := hBound a b hab hLen
  linarith

end TTO.Paper.Proved
