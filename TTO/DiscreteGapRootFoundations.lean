/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FractionalSingularFoundations
public import TTO.ModelNestFoundations

/-! An actual fractional root and Hardy high factor for the finite gap decomposition. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The actual boundary power has its literal analytic power value. -/
theorem innerValue_powerInf (v : BoundaryLInf) (hv : IsInner v) (n : ℕ) (z : Disk) :
    innerValue (powerInf v n) z.val = innerValue v z.val ^ n := by
  induction n with
  | zero =>
    change analyticValue (toL2 (constLInf 1)) z.val = _
    rw [toL2_constLInf, analyticValue_constL2_disk, pow_zero]
  | succ n ih =>
    change innerValue (multiplyInf v (powerInf v n)) z.val = _
    rw [innerValue_multiplyInf v (powerInf v n) hv.1 (isInner_powerInf v hv n).1 z,
      ih, pow_succ']

/-- The actual bounded multiplication operator is linear in its boundary symbol. -/
theorem multiply_symbol_smul (c : ℂ) (a : BoundaryLInf) (f : BoundaryL2) :
    multiply (c • a) f = c • multiply a f := by
  simp only [multiply, map_smul, smul_apply]

/-- A nonzero scalar phase leaves the literal model submodule unchanged. -/
theorem model_smul_of_ne_zero (c : ℂ) (hc : c ≠ 0) (a : BoundaryLInf) :
    model (c • a) = model a := by
  have hspan : Submodule.span ℂ (Set.range (fun n : ℕ =>
        multiply (c • a) (fourierBasis (T := 1) (n : ℤ)))) =
      Submodule.span ℂ (Set.range (fun n : ℕ =>
        multiply a (fourierBasis (T := 1) (n : ℤ)))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      dsimp only
      rw [multiply_symbol_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨n, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      dsimp only
      have he : multiply a (fourierBasis (T := 1) (n : ℤ)) =
          c⁻¹ • multiply (c • a) (fourierBasis (T := 1) (n : ℤ)) := by
        rw [multiply_symbol_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [he]
      exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span ⟨n, rfl⟩)
  unfold model
  rw [hspan]

/-- A true positive discrete root of the given singular symbol and an actual Hardy factor of φ.
No operator splitting or ideal-membership conclusion is included in this prerequisite. -/
theorem exists_discreteSingularGapRoot (u : BoundaryLInf) (hu : IsInner u) (_hn : Nonconstant u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (φ : Hardy)
    (r : ℝ) (hr : 0 < r) (_hr1 : r < 1) (hg : HasAnalyticGap μ r φ.val) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ)⁻¹ < r ∧
      ∃ v : BoundaryLInf, IsInner v ∧ ∃ α : ℂ, ‖α‖ = 1 ∧
        u = α • powerInf v N ∧ model u = model (powerInf v N) ∧
          ∃ q : Hardy, φ.val = multiply v q.val := by
  obtain ⟨N, hN, hNr⟩ := Real.exists_nat_pos_inv_lt hr
  let δ : ℝ := (N : ℝ)⁻¹
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < δ := inv_pos.mpr hNc
  have hδr : δ < r := hNr
  obtain ⟨v, hv, hvalv, _hTv⟩ := exists_fractionalSingularBoundary u hu μ hμ δ hδ
  obtain ⟨w, hw, hvalw, _hTw⟩ :=
    exists_fractionalSingularBoundary u hu μ hμ (r - δ) (sub_pos.mpr hδr)
  obtain ⟨α, hα, hueval⟩ := hμ.2
  have hphaseHardy : toL2 (α • powerInf v N) ∈ hardy := by
    rw [malmquist_toL2_smul]
    exact hardy.smul_mem α (isInner_powerInf v hv N).1
  have huEq : u = α • powerInf v N := by
    apply hardyBoundary_ext _ _ hu.1 hphaseHardy
    intro z hz
    rw [hueval z hz]
    change α * singularInnerValue μ 1 z = analyticValue (toL2 (α • powerInf v N)) z
    rw [malmquist_toL2_smul, analyticValue_smul _ _ hz]
    change α * singularInnerValue μ 1 z = α * innerValue (powerInf v N) z
    rw [innerValue_powerInf v hv N ⟨z, hz⟩, hvalv z hz, ← singularInnerValue_nat_mul]
    have hNδ : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hNc.ne'
    rw [hNδ]
  have hαne : α ≠ 0 := by
    intro he
    rw [he, norm_zero] at hα
    exact zero_ne_one hα
  have hmodels : model u = model (powerInf v N) := by
    rw [huEq, model_smul_of_ne_zero α hαne]
  obtain ⟨h, hgap⟩ := hg
  let q : Hardy := ⟨multiply w h.val, multiply_mem_hardy w hw.1 h.val h.property⟩
  have hφ : φ.val = multiply v q.val := by
    have he : φ = (⟨multiply v q.val, multiply_mem_hardy v hv.1 q.val q.property⟩ : Hardy) := by
      apply hardy_analyticValue_injective
      intro z hz
      rw [analyticValue_multiply v hv.1 q ⟨z, hz⟩]
      change analyticValue φ.val z = innerValue v z * analyticValue (multiply w h.val) z
      rw [analyticValue_multiply w hw.1 h ⟨z, hz⟩, hvalv z hz, hvalw z hz,
        ← mul_assoc, ← singularInnerValue_add]
      have hrs : δ + (r - δ) = r := by ring
      rw [hrs]
      exact hgap z hz
    exact congrArg Subtype.val he
  exact ⟨N, hN, hNr, v, hv, α, hα, huEq, hmodels, q, hφ⟩

end TTO.Paper.Proved
