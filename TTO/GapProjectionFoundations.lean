/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FractionalSingularFoundations

/-! The manuscript's canonical low-frequency projection and genuine fractional high factor. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The frozen Taylor-defined power model is the native model of its actual boundary factor. -/
theorem powerModel_eq_model (μ : Measure Boundary) (r : ℝ) (v : BoundaryLInf)
    (hTaylor : toL2 v = analyticBoundary (singularInnerValue μ r)) :
    powerModel μ r = model v := by
  have hg : (fun n : ℕ => multiply (mode (n : ℤ))
      (analyticBoundary (singularInnerValue μ r))) =
      (fun n : ℕ => multiply v (fourierBasis (T := 1) (n : ℤ))) := by
    funext n
    rw [← hTaylor, ← toL2_multiplyInf, multiplyInf_comm, toL2_multiplyInf, toL2_mode]
  unfold powerModel model
  rw [hg]

theorem powerProjection_eq_modelProjection (μ : Measure Boundary) (r : ℝ) (v : BoundaryLInf)
    (hTaylor : toL2 v = analyticBoundary (singularInnerValue μ r)) (f : BoundaryL2) :
    powerProjection μ r f = ((model v).orthogonalProjectionOnto f).val := by
  have hK := powerModel_eq_model μ r v hTaylor
  have hp : ((model v).orthogonalProjectionOnto f).val ∈ powerModel μ r := by
    rw [hK]
    exact ((model v).orthogonalProjectionOnto f).property
  have ho : f - ((model v).orthogonalProjectionOnto f).val ∈ (powerModel μ r).orthogonal := by
    rw [hK]
    exact (model v).sub_starProjection_mem_orthogonal f
  exact (powerModel μ r).eq_starProjection_of_mem_orthogonal hp ho

/-- Conjugation of a Hardy function with zero constant coefficient is strictly negative spectrum. -/
theorem star_hardy_zero_mem_negative (ψ : Hardy) (hψ : analyticValue ψ.val 0 = 0) :
    star ψ.val ∈ hardy.orthogonal := by
  apply (mem_hardy_orthogonal_iff _).mpr
  intro n
  have hzero : fourierCoeff ψ.val 0 = 0 := (analyticValue_at_zero ψ.val).symm.trans hψ
  have hc : fourierCoeff ψ.val (-(n : ℤ)) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero, neg_zero] using hzero
    · exact (mem_hardy_iff ψ.val).mp ψ.property _ (by omega)
  rw [fourierCoeff_star_L2, hc, map_zero]

/-- The exact frozen canonical projection obligation, with all original manuscript hypotheses. -/
theorem gapProjection : GapProjectionObligation := by
  intro u hu _hn μ hμ φ ψ hψ r hr _hr1
  obtain ⟨v, hv, hval, hTaylor⟩ := exists_fractionalSingularBoundary u hu μ hμ r hr
  have hneg : star ψ.val ∈ hardy.orthogonal :=
    star_hardy_zero_mem_negative ⟨ψ.val, ψ.property.1⟩ hψ
  have hprojneg : (model v).orthogonalProjectionOnto (star ψ.val) = 0 :=
    (model v).orthogonalProjectionOnto_eq_zero_iff.mpr
      (Submodule.orthogonal_le (show model v ≤ hardy from inf_le_left) hneg)
  have heq : powerProjection μ r (splitSymbol φ.val ψ.val) = powerProjection μ r φ.val := by
    rw [powerProjection_eq_modelProjection μ r v hTaylor,
      powerProjection_eq_modelProjection μ r v hTaylor]
    unfold splitSymbol
    rw [map_add, hprojneg, add_zero]
  have hp : powerProjection μ r φ.val ∈ hardy :=
    ((powerModel μ r).orthogonalProjectionOnto φ.val).property.1
  have hh : φ.val - powerProjection μ r φ.val ∈ hardy :=
    hardy.sub_mem φ.property.1 hp
  have hzero : (model v).orthogonalProjectionOnto (φ.val - powerProjection μ r φ.val) = 0 := by
    rw [powerProjection_eq_modelProjection μ r v hTaylor, map_sub,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, sub_self]
  obtain ⟨q, hq⟩ := innerFactor_of_modelProjection_zero v hv
    ⟨φ.val - powerProjection μ r φ.val, hh⟩ hzero
  change φ.val - powerProjection μ r φ.val = multiply v q.val at hq
  refine ⟨heq, hp, hh, ⟨q, ?_⟩⟩
  intro z hz
  rw [hq, analyticValue_multiply v hv.1 q ⟨z, hz⟩, hval z hz]

end TTO.Paper.Proved
