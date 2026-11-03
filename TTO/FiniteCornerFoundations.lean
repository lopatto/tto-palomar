/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations

/-! Simultaneous finite source cuts for two compact operators. -/
@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal InnerProductSpace Topology
namespace TTO.Paper.Proved

section HilbertCuts
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An operator ignores the orthogonal complement of any subspace containing its adjoint range. -/
theorem comp_starProjection_eq_of_adjoint_range (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (R : H →L[ℂ] H) (hR : ∀ y, R.adjoint y ∈ M) :
    R ∘L M.starProjection = R := by
  ext x
  change R (M.starProjection x) = R x
  apply ext_inner_left ℂ
  intro y
  rw [← ContinuousLinearMap.adjoint_inner_left R (M.starProjection x) y,
    ← ContinuousLinearMap.adjoint_inner_left R x y]
  exact M.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨R.adjoint y,hR y⟩ x

omit [CompleteSpace H] in
/-- A source cut fixing a nearby operator changes the approximation error by at most a factor two. -/
theorem norm_sub_comp_starProjection_le (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (A R : H →L[ℂ] H) (hR : R ∘L M.starProjection = R) (δ : ℝ)
    (hError : ‖A-R‖ ≤ δ) :
    ‖A-A ∘L M.starProjection‖ ≤ 2*δ := by
  have he : A-A ∘L M.starProjection = (A-R)-(A-R) ∘L M.starProjection := by
    rw [ContinuousLinearMap.sub_comp,hR]
    abel
  have hc : ‖(A-R) ∘L M.starProjection‖ ≤ ‖A-R‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left M.starProjection_norm_le (norm_nonneg (A-R)))
  rw [he]
  have hn := norm_sub_le (A-R) ((A-R) ∘L M.starProjection)
  linarith

/-- Two compact operators admit a common actual finite-dimensional orthogonal source cut.
Only their compositions converge; no approximation to the identity on the ambient space is claimed. -/
theorem simultaneous_compact_source_cut (A B : H →L[ℂ] H)
    (hA : IsCompactOperator A) (hB : IsCompactOperator B) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : Submodule ℂ H, FiniteDimensional ℂ M ∧ ∃ P : H →L[ℂ] M,
      ‖P‖ ≤ 1 ∧ (∀ x : M, P x.val = x) ∧
      ‖A-A ∘L M.subtypeL ∘L P‖ ≤ ε ∧ ‖B-B ∘L M.subtypeL ∘L P‖ ≤ ε := by
  obtain ⟨R,⟨r,hr⟩,hAR⟩ := compact_finiteRank_approx A hA (ε/2) (half_pos hε)
  obtain ⟨S,⟨s,hs⟩,hBS⟩ := compact_finiteRank_approx B hB (ε/2) (half_pos hε)
  have hr' := rank_adjoint_le_of_rank_le R hr
  have hs' := rank_adjoint_le_of_rank_le S hs
  let : FiniteDimensional ℂ R.adjoint.range := Module.rank_lt_aleph0_iff.mp
    (hr'.trans_lt (Cardinal.natCast_lt_aleph0 (n := r)))
  let : FiniteDimensional ℂ S.adjoint.range := Module.rank_lt_aleph0_iff.mp
    (hs'.trans_lt (Cardinal.natCast_lt_aleph0 (n := s)))
  let M : Submodule ℂ H := R.adjoint.range ⊔ S.adjoint.range
  let : FiniteDimensional ℂ M := inferInstance
  let : CompleteSpace M := FiniteDimensional.complete ℂ M
  let P : H →L[ℂ] M := M.orthogonalProjectionOnto
  have hRfix : R ∘L M.starProjection = R := comp_starProjection_eq_of_adjoint_range M R
    (fun y => (show R.adjoint.range ≤ M from le_sup_left) ⟨y,rfl⟩)
  have hSfix : S ∘L M.starProjection = S := comp_starProjection_eq_of_adjoint_range M S
    (fun y => (show S.adjoint.range ≤ M from le_sup_right) ⟨y,rfl⟩)
  refine ⟨M,inferInstance,P,M.orthogonalProjectionOnto_norm_le,?_,?_,?_⟩
  · intro x
    exact M.orthogonalProjectionOnto_mem_subspace_eq_self x
  · have h := norm_sub_comp_starProjection_le M A R hRfix (ε/2) hAR
    change ‖A-A ∘L M.starProjection‖ ≤ ε
    linarith
  · have h := norm_sub_comp_starProjection_le M B S hSfix (ε/2) hBS
    change ‖B-B ∘L M.starProjection‖ ≤ ε
    linarith

end HilbertCuts

section RightRetraction
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A contractive source projection and inclusion preserve all approximation infima exactly. -/
theorem approximationNumber_comp_right_retract (P : G →L[ℂ] E) (J : E →L[ℂ] G)
    (hP : ‖P‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hPJ : ∀ x, P (J x) = x)
    (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (A ∘L P) n = approximationNumber A n := by
  apply le_antisymm (approximationNumber_comp_right_contraction A P hP n)
  have he : (A ∘L P) ∘L J = A := by
    ext x
    change A (P (J x)) = A x
    rw [hPJ]
  have h := approximationNumber_comp_right_contraction (A ∘L P) J hJ n
  rw [he] at h
  exact h

/-- The literal power-sum gauges are also preserved by a contractive source retraction. -/
theorem schattenNorm_comp_right_retract (P : G →L[ℂ] E) (J : E →L[ℂ] G)
    (hP : ‖P‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hPJ : ∀ x, P (J x) = x)
    (A : E →L[ℂ] F) (p : ℝ) :
    schattenNorm p (A ∘L P) = schattenNorm p A := by
  unfold schattenNorm
  congr 1
  apply tsum_congr
  intro n
  rw [approximationNumber_comp_right_retract P J hP hJ hPJ]

end RightRetraction
end TTO.Paper.Proved
