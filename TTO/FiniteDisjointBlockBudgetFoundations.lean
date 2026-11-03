/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FiniteOrthogonalBlocksFoundations
public import TTO.CappedSchattenFoundations

/-! An errorful finite orthogonal-block budget for 0<p≤1. Actual off-diagonal
corners remain on the right; no contractive pinching assertion is made. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section HilbertCoordinates
variable {η : Type} [Fintype η] [DecidableEq η] {E : η → Type}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

/-- The actual isometric inclusion of one Hilbert summand. -/
def hilbertCoordinateInclusion (E : η → Type) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (i : η) : E i →ₗᵢ[ℂ] PiLp 2 E where
  toFun := PiLp.single 2 i
  map_add' x y := PiLp.single_add 2 i
  map_smul' c x := by
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [hji]
  norm_map' x := PiLp.norm_single 2 E i x

@[simp] theorem hilbertCoordinateInclusion_apply (i : η) (x : E i) :
    hilbertCoordinateInclusion E i x = PiLp.single 2 i x := rfl

theorem inner_hilbertCoordinateInclusion (i : η) (x : E i) (y : PiLp 2 E) :
    inner ℂ (hilbertCoordinateInclusion E i x) y = inner ℂ x (y i) := by
  rw [hilbertCoordinateInclusion_apply,PiLp.inner_apply,Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [PiLp.ofLp_single,Pi.single_eq_of_ne hji]
  · simp

theorem sum_hilbertCoordinateInclusion (x : PiLp 2 E) :
    (∑ i, hilbertCoordinateInclusion E i (x i)) = x := by
  ext j
  simp [hilbertCoordinateInclusion_apply]

variable [∀ i, CompleteSpace (E i)]

@[simp] theorem hilbertCoordinateInclusion_adjoint_apply (i : η) (x : PiLp 2 E) :
    (hilbertCoordinateInclusion E i).toContinuousLinearMap.adjoint x = x i := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_hilbertCoordinateInclusion i y x

end HilbertCoordinates

section BlockBudget
variable {η : Type} [Fintype η] [DecidableEq η] {E F : η → Type}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)]

/-- The actual i,j coordinate corner of a finite Hilbert product operator. -/
def hilbertCoordinateCorner (T : PiLp 2 E →L[ℂ] PiLp 2 F) (i j : η) : E j →L[ℂ] F i :=
  (hilbertCoordinateInclusion F i).toContinuousLinearMap.adjoint ∘L T ∘L
    (hilbertCoordinateInclusion E j).toContinuousLinearMap

omit [∀ i, CompleteSpace (E i)] in
@[simp] theorem hilbertCoordinateCorner_apply (T : PiLp 2 E →L[ℂ] PiLp 2 F)
    (i j : η) (x : E j) : hilbertCoordinateCorner T i j x = T (PiLp.single 2 j x) i := by
  simp only [hilbertCoordinateCorner,ContinuousLinearMap.comp_apply,
    hilbertCoordinateInclusion_adjoint_apply,LinearIsometry.coe_toContinuousLinearMap,
    hilbertCoordinateInclusion_apply]

/-- A single actual corner placed back into its two coordinate summands. -/
def hilbertPlacedCorner (T : PiLp 2 E →L[ℂ] PiLp 2 F) (i j : η) : PiLp 2 E →L[ℂ] PiLp 2 F :=
  (hilbertCoordinateInclusion F i).toContinuousLinearMap ∘L hilbertCoordinateCorner T i j ∘L
    (hilbertCoordinateInclusion E j).toContinuousLinearMap.adjoint

@[simp] theorem hilbertPlacedCorner_apply (T : PiLp 2 E →L[ℂ] PiLp 2 F)
    (i j : η) (x : PiLp 2 E) :
    hilbertPlacedCorner T i j x = PiLp.single 2 i (hilbertCoordinateCorner T i j (x j)) := by
  simp only [hilbertPlacedCorner,ContinuousLinearMap.comp_apply,
    hilbertCoordinateInclusion_adjoint_apply,LinearIsometry.coe_toContinuousLinearMap,
    hilbertCoordinateInclusion_apply]

theorem hilbertPlacedCorner_schattenNorm_rpow (T : PiLp 2 E →L[ℂ] PiLp 2 F)
    (i j : η) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (hilbertPlacedCorner T i j)^p = schattenNorm p (hilbertCoordinateCorner T i j)^p :=
  schattenNorm_isometric_placement_rpow _ _ _ p hp

/-- Reconstruction of every actual product operator from ALL its actual corners. -/
theorem hilbertPlacedCorner_sum (T : PiLp 2 E →L[ℂ] PiLp 2 F) :
    (∑ i, ∑ j, hilbertPlacedCorner T i j) = T := by
  ext x k
  simp only [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,hilbertPlacedCorner_apply]
  simp only [PiLp.ofLp_single]
  rw [Finset.sum_comm]
  simp only [Finset.sum_pi_single,Finset.mem_univ,ite_true]
  simp only [hilbertCoordinateCorner_apply]
  have he := congrArg (fun y : PiLp 2 E => T y k) (sum_hilbertCoordinateInclusion x)
  simpa only [map_sum,WithLp.ofLp_sum,Finset.sum_apply,hilbertCoordinateInclusion_apply] using he

/-- The diagonal part is exactly the proved native block map. -/
theorem hilbertPlacedCorner_diagonal (T : PiLp 2 E →L[ℂ] PiLp 2 F) :
    (∑ i, hilbertPlacedCorner T i i) = finiteHilbertBlockMap (fun i => hilbertCoordinateCorner T i i) := by
  ext x k
  simp [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,hilbertPlacedCorner_apply]

/-- The literal finite sum of all off-diagonal corners. -/
def hilbertOffDiagonal (T : PiLp 2 E →L[ℂ] PiLp 2 F) : PiLp 2 E →L[ℂ] PiLp 2 F :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, hilbertPlacedCorner T i j

/-- Actual diagonal-plus-error identity, prior to any norm estimate. -/
theorem hilbert_diagonal_add_offDiagonal (T : PiLp 2 E →L[ℂ] PiLp 2 F) :
    finiteHilbertBlockMap (fun i => hilbertCoordinateCorner T i i)+hilbertOffDiagonal T = T := by
  rw [← hilbertPlacedCorner_diagonal,hilbertOffDiagonal,← Finset.sum_add_distrib]
  have hRow (i : η) : hilbertPlacedCorner T i i+
      (∑ j ∈ Finset.univ.erase i,hilbertPlacedCorner T i j) = ∑ j,hilbertPlacedCorner T i j := by
    exact Finset.add_sum_erase Finset.univ (fun j => hilbertPlacedCorner T i j) (Finset.mem_univ i)
  simp_rw [hRow]
  exact hilbertPlacedCorner_sum T

variable [∀ i, FiniteDimensional ℂ (E i)]

/-- Exact finite-sum p-power control of the literal off-diagonal error. -/
theorem hilbertOffDiagonal_schattenNorm_rpow_le (T : PiLp 2 E →L[ℂ] PiLp 2 F)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    schattenNorm p (hilbertOffDiagonal T)^p ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, schattenNorm p (hilbertCoordinateCorner T i j)^p := by
  calc
    _ ≤ ∑ i, schattenNorm p (∑ j ∈ Finset.univ.erase i,hilbertPlacedCorner T i j)^p :=
      finite_schattenNorm_sum_rpow_le Finset.univ _ p hp hp1
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, schattenNorm p (hilbertPlacedCorner T i j)^p := by
      apply Finset.sum_le_sum
      intro i _hi
      exact finite_schattenNorm_sum_rpow_le _ _ p hp hp1
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      exact hilbertPlacedCorner_schattenNorm_rpow T i j p hp

/-- The true finite block budget: off-diagonal corners are an explicit error cost.
This is not a contractive pinching inequality. -/
theorem hilbert_diagonal_schattenNorm_budget (T : PiLp 2 E →L[ℂ] PiLp 2 F)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i,schattenNorm p (hilbertCoordinateCorner T i i)^p) ≤ schattenNorm p T^p+
      ∑ i, ∑ j ∈ Finset.univ.erase i,schattenNorm p (hilbertCoordinateCorner T i j)^p := by
  have hDecomp : finiteHilbertBlockMap (fun i => hilbertCoordinateCorner T i i) =
      T+(-hilbertOffDiagonal T) := by
    calc
      _ = (finiteHilbertBlockMap (fun i => hilbertCoordinateCorner T i i)+hilbertOffDiagonal T)+
          (-hilbertOffDiagonal T) := by abel
      _ = _ := by rw [hilbert_diagonal_add_offDiagonal]
  rw [← finiteHilbertBlockMap_schattenNorm_rpow (fun i => hilbertCoordinateCorner T i i) p hp]
  calc
    _ = schattenNorm p (T+(-hilbertOffDiagonal T))^p := congrArg (fun A => schattenNorm p A^p) hDecomp
    _ ≤ schattenNorm p T^p+schattenNorm p (-hilbertOffDiagonal T)^p :=
      finite_schattenNorm_add_rpow_le _ _ p hp hp1
    _ = schattenNorm p T^p+schattenNorm p (hilbertOffDiagonal T)^p := by
      simp only [schattenNorm,approximationNumber_neg]
    _ ≤ _ := add_le_add_right (hilbertOffDiagonal_schattenNorm_rpow_le T p hp hp1) _

end BlockBudget

section ActualDisjointCoordinates
variable {η : Type} [Fintype η] [DecidableEq η]

/-- Actual coordinate embedding of one member of a disjoint coordinate family. -/
def disjointCoordinateInclusion (d : η → ℕ) (N : ℕ)
    (e : (Σ i,Fin (d i)) ↪ Fin N) (i : η) :
    EuclideanSpace ℂ (Fin (d i)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (finiteCoordinateBlockInclusion d N e).comp
    (hilbertCoordinateInclusion (fun i => EuclideanSpace ℂ (Fin (d i))) i)

theorem disjointCoordinateInclusion_single (d : η → ℕ) (N : ℕ)
    (e : (Σ i,Fin (d i)) ↪ Fin N) (i : η) (j : Fin (d i)) :
    disjointCoordinateInclusion d N e i (EuclideanSpace.single j (1 : ℂ)) =
      EuclideanSpace.single (e ⟨i,j⟩) (1 : ℂ) :=
  finiteCoordinateBlockInclusion_single d N e i j 1

/-- The actual corner formed from the ambient matrix and its two coordinate inclusions. -/
def disjointCoordinateCorner (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) (i j : η) :
    EuclideanSpace ℂ (Fin (c j)) →L[ℂ] EuclideanSpace ℂ (Fin (r i)) :=
  (disjointCoordinateInclusion r R er i).toContinuousLinearMap.adjoint ∘L A ∘L
    (disjointCoordinateInclusion c C ec j).toContinuousLinearMap

/-- Literal matrix entries of each actual corner, with row and column orientations explicit. -/
theorem disjointCoordinateCorner_single_apply (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R))
    (i j : η) (a : Fin (r i)) (b : Fin (c j)) :
    disjointCoordinateCorner r c R C er ec A i j (EuclideanSpace.single b (1 : ℂ)) a =
      A (EuclideanSpace.single (ec ⟨j,b⟩) (1 : ℂ)) (er ⟨i,a⟩) := by
  have he := ContinuousLinearMap.adjoint_inner_right
    (disjointCoordinateInclusion r R er i).toContinuousLinearMap (EuclideanSpace.single a (1 : ℂ))
    (A (disjointCoordinateInclusion c C ec j (EuclideanSpace.single b (1 : ℂ))))
  simp only [LinearIsometry.coe_toContinuousLinearMap,disjointCoordinateInclusion_single,
    EuclideanSpace.inner_single_left,map_one,one_mul] at he
  simpa only [disjointCoordinateCorner,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,disjointCoordinateInclusion_single] using he

/-- Actual union compression onto the two disjoint coordinate families. -/
def disjointUnionCompression (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) :
    PiLp 2 (fun i => EuclideanSpace ℂ (Fin (c i))) →L[ℂ]
      PiLp 2 (fun i => EuclideanSpace ℂ (Fin (r i))) :=
  (finiteCoordinateBlockInclusion r R er).toContinuousLinearMap.adjoint ∘L A ∘L
    (finiteCoordinateBlockInclusion c C ec).toContinuousLinearMap

/-- Every corner of the union compression is exactly the stated ambient matrix corner. -/
theorem disjointUnionCompression_corner (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) (i j : η) :
    hilbertCoordinateCorner (disjointUnionCompression r c R C er ec A) i j =
      disjointCoordinateCorner r c R C er ec A i j := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (c j)) ℂ).toBasis.ext
  intro b
  rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  ext a
  change (hilbertCoordinateCorner (disjointUnionCompression r c R C er ec A) i j
    (EuclideanSpace.single b (1 : ℂ))) a =
    disjointCoordinateCorner r c R C er ec A i j (EuclideanSpace.single b (1 : ℂ)) a
  rw [hilbertCoordinateCorner_apply,disjointCoordinateCorner_single_apply]
  simp only [disjointUnionCompression,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,finiteCoordinateBlockInclusion_single,
    finiteCoordinateBlockInclusion_adjoint_apply]

omit [DecidableEq η] in
/-- Compression controls the actual Schatten p-power by two native coordinate contractions. -/
theorem disjointUnionCompression_schattenNorm_rpow_le (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (disjointUnionCompression r c R C er ec A)^p ≤ schattenNorm p A^p := by
  let B := disjointUnionCompression r c R C er ec A
  have hB := finiteDim_schatten B p hp
  have hA := finiteDim_schatten A p hp
  rw [schattenNorm_rpow hp,schattenNorm_rpow hp]
  apply Summable.tsum_le_tsum _ hB.2.2 hA.2.2
  intro n
  apply Real.rpow_le_rpow (NNReal.coe_nonneg _) _ hp.le
  exact_mod_cast approximationNumber_comp_contractions
    (finiteCoordinateBlockInclusion r R er).toContinuousLinearMap.adjoint A
    (finiteCoordinateBlockInclusion c C ec).toContinuousLinearMap
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le
      (finiteCoordinateBlockInclusion r R er).norm_toContinuousLinearMap_le)
    (finiteCoordinateBlockInclusion c C ec).norm_toContinuousLinearMap_le n

/-- True budget for every actual finite ambient matrix and disjoint row/column families.
The explicit error is the sum over ALL off-diagonal ambient corners. Empty families are allowed. -/
theorem finite_disjoint_coordinate_block_budget (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i,Fin (r i)) ↪ Fin R) (ec : (Σ i,Fin (c i)) ↪ Fin C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i,schattenNorm p (disjointCoordinateCorner r c R C er ec A i i)^p) ≤ schattenNorm p A^p+
      ∑ i, ∑ j ∈ Finset.univ.erase i,schattenNorm p (disjointCoordinateCorner r c R C er ec A i j)^p := by
  have h := hilbert_diagonal_schattenNorm_budget (disjointUnionCompression r c R C er ec A) p hp hp1
  simp only [disjointUnionCompression_corner] at h
  exact h.trans (add_le_add_left (disjointUnionCompression_schattenNorm_rpow_le r c R C er ec A p hp) _)

end ActualDisjointCoordinates

end TTO.Paper.Proved
