/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.GraphFoundations

/-! The actual diagonal quotient and the manuscript's explicit graph-core implication. -/

@[expose] public section
noncomputable section
open Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

/-- Native Hilbert projection facts, without assuming the subspace itself is closed. -/
theorem projectionLaws : ProjectionLaws where
  span_orthogonal := by
    intro H W _ _ k x
    constructor
    · intro hx w
      exact (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨w,rfl⟩)
    · intro h
      apply (Submodule.mem_orthogonal _ _).mpr
      intro v hv
      have hle : Submodule.span ℂ (Set.range k) ≤ (innerSL ℂ x).ker := by
        apply Submodule.span_le.mpr
        rintro y ⟨w,rfl⟩
        exact inner_eq_zero_symm.mp (h w)
      exact inner_eq_zero_symm.mp (hle hv)
  double := fun K => K.orthogonal_orthogonal_eq_closure
  norm_le := fun Z x => Z.orthogonal.norm_orthogonalProjectionOnto_apply_le x
  norm_eq := by
    intro H _ _ _ Z x
    change ‖Z.orthogonal.starProjection x‖ = ‖x‖ ↔ x ∈ Z.orthogonal
    exact (Z.orthogonal.mem_iff_norm_starProjection x).symm
  fix := fun Z x => Z.orthogonal.orthogonalProjectionOnto_mem_subspace_eq_self x
  modulo := by
    intro H _ _ _ Z x y hxy
    have hz : Z.orthogonal.orthogonalProjectionOnto (x-y) = 0 :=
      Z.orthogonal.orthogonalProjectionOnto_eq_zero_iff.mpr
        (Z.le_orthogonal_orthogonal hxy)
    rwa [map_sub,sub_eq_zero] at hz
  inner := by
    intro H _ _ _ Z x z hz
    exact Z.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨z,hz⟩ x

/-- Linear tests extend through their actual closed graph, retaining the core hypothesis. -/
theorem graphCoreLaws : GraphCoreLaws where
  range := by
    intro H K W _ _ _ _ _ _ Q a b hcore Z hZ hb x
    let V := Z.comap (ContinuousLinearMap.snd ℂ H K).toLinearMap
    have hv : IsClosed (V : Set (H × K)) := hZ.preimage continuous_snd
    have hle : Submodule.span ℂ (Set.range (fun w => (a w,b w))) ≤ V := by
      apply Submodule.span_le.mpr
      rintro y ⟨w,rfl⟩
      exact hb w
    have hg : Q.graph ≤ V := by
      rw [← hcore]
      exact Submodule.topologicalClosure_minimal _ hle hv
    exact hg (Q.mem_graph x)
  form := by
    intro H K W _ _ _ _ _ _ Q a b hcore x y htests γ
    let L : H × K →L[ℂ] ℂ :=
      (innerSL ℂ (Q x)).comp (ContinuousLinearMap.snd ℂ H K)-
        (innerSL ℂ y).comp (ContinuousLinearMap.fst ℂ H K)
    have hle : Submodule.span ℂ (Set.range (fun w => (a w,b w))) ≤ L.ker := by
      apply Submodule.span_le.mpr
      rintro p ⟨w,rfl⟩
      change inner ℂ (Q x) (b w)-inner ℂ y (a w) = 0
      apply sub_eq_zero.mpr
      simpa only [inner_conj_symm] using congrArg conj (htests w)
    have hg : Q.graph ≤ L.ker := by
      rw [← hcore]
      exact Submodule.topologicalClosure_minimal _ hle L.isClosed_ker
    have he := hg (Q.mem_graph γ)
    change inner ℂ (Q x) (Q γ)-inner ℂ y γ.val = 0 at he
    have hf := congrArg conj (sub_eq_zero.mp he)
    simpa only [inner_conj_symm] using hf

/-- Actual diagonal model kernels, rather than an abstract product-kernel assumption. -/
theorem diagonalKernel : DiagonalKernelObligation := by
  intro u hu _ Q hQ
  refine ⟨{
    kernel := ambientKernel u hu
    tensorKernel := reproducingTensor u hu
    kernel_value := ?_
    product_value := ?_
    graph := fun w => (hQ _ _).mpr (ambientKernel_graph u hu w)
    diagonal_reproduces := fun G w => analyticValue₂_tensor_kernels u hu G w w
    ambient_reproduces := ?_ }⟩
  · intro w z
    exact analyticValue_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w z.property
  · intro w z t
    rw [analyticValue₂_tensor_kernels]
    change inner ℂ
      (separatedProduct (modelReproducingKernel u hu z).val (modelReproducingKernel u hu t).val)
      (separatedProduct (modelReproducingKernel u hu w).val (modelReproducingKernel u hu w).val) = _
    rw [inner_separatedProduct]
    change inner ℂ (modelReproducingKernel u hu z) (modelReproducingKernel u hu w)*
      inner ℂ (modelReproducingKernel u hu t) (modelReproducingKernel u hu w) = _
    rw [inner_modelReproducingKernel,inner_modelReproducingKernel,
      analyticValue_modelReproducingKernel u hu w z.property,
      analyticValue_modelReproducingKernel u hu w t.property]
  · intro η w
    exact (inner_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w η).symm

/-- Full squared-kernel quotient conclusion; the source's graph-core condition remains explicit. -/
theorem squaredKernelQuotientTheorem : SquaredKernelConclusion :=
  Reduction.squaredKernelQuotient (fun u hu hn =>
    ⟨(hilbertSchmidtEnergyTheorem u hu hn).1,differentialRealizationTheorem u hu hn⟩)
    diagonalKernel projectionLaws graphCoreLaws

end TTO.Paper.Proved
