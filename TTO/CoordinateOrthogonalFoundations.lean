/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.Proofs

/-! Orthogonal coordinate resolutions transported by an actual finite-sum unitary. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section UnitaryCoordinates
variable {m : ℕ} {H : Fin m → Type}
variable [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)]
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A literal coordinate inclusion has its usual right inner-product meaning. -/
theorem inner_finiteSingle_right (f : PiLp 2 H) (j : Fin m) (x : H j) :
    inner ℂ f (finiteSingle H j x) = inner ℂ (f j) x := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [finiteSingle_apply, Pi.single_eq_same]
  · intro i _hi hij
    rw [finiteSingle_apply, Pi.single_eq_of_ne hij, inner_zero_right]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- A literal coordinate inclusion has its usual left inner-product meaning. -/
theorem inner_finiteSingle_left (j : Fin m) (x : H j) (f : PiLp 2 H) :
    inner ℂ (finiteSingle H j x) f = inner ℂ x (f j) := by
  rw [← inner_conj_symm, inner_finiteSingle_right, inner_conj_symm]

/-- The existing coordinateResolution is the transported literal coordinate projection. -/
theorem coordinateResolution_unitary_apply (W : PiLp 2 H ≃ₗᵢ[ℂ] K)
    (j : Fin m) (f : PiLp 2 H) :
    coordinateResolution W.toContinuousLinearEquiv j (W f) = W (finiteSingle H j (f j)) := by
  simp [coordinateResolution]

/-- Unitary transport makes the existing coordinate resolutions genuinely selfadjoint. -/
theorem coordinateResolution_unitary_inner (W : PiLp 2 H ≃ₗᵢ[ℂ] K)
    (j : Fin m) (x y : K) :
    inner ℂ x (coordinateResolution W.toContinuousLinearEquiv j y) =
      inner ℂ (coordinateResolution W.toContinuousLinearEquiv j x) y := by
  obtain ⟨f, rfl⟩ := W.surjective x
  obtain ⟨g, rfl⟩ := W.surjective y
  rw [coordinateResolution_unitary_apply, coordinateResolution_unitary_apply,
    W.inner_map_map, W.inner_map_map, inner_finiteSingle_right, inner_finiteSingle_left]

/-- An actual matrix corner has exactly its single-coordinate input/output pairing. -/
theorem coordinateResolution_unitary_block_inner (W : PiLp 2 H ≃ₗᵢ[ℂ] K)
    (A : K →L[ℂ] K) (i j : Fin m) (f g : PiLp 2 H) :
    inner ℂ (W g) (coordinateResolution W.toContinuousLinearEquiv i
      (A (coordinateResolution W.toContinuousLinearEquiv j (W f)))) =
      inner ℂ (W (finiteSingle H i (g i))) (A (W (finiteSingle H j (f j)))) := by
  rw [coordinateResolution_unitary_inner, coordinateResolution_unitary_apply,
    coordinateResolution_unitary_apply]

end UnitaryCoordinates
end TTO.Paper.Proved
