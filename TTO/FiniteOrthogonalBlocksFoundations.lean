/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.FiniteSchattenInterpolationFoundations

/-! Exact positive Schatten power sums for orthogonal columns and genuine finite
orthogonal block sums. No pinching inequality is used. -/

@[expose] public section
noncomputable section
open Filter Finset
open scoped NNReal ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section OrthogonalColumns
variable {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Actual column lengths in the given orthonormal coordinates, extended by zero. -/
def orthogonalColumnWeights (b : OrthonormalBasis (Fin N) ℂ E) (A : E →L[ℂ] F) (n : ℕ) : ℂ :=
  if hn : n < N then (‖A (b ⟨n,hn⟩)‖ : ℂ) else 0

def orthogonalColumnDiagonal (b : OrthonormalBasis (Fin N) ℂ E) (A : E →L[ℂ] F) : SequenceOperator :=
  diagonalTruncation (orthogonalColumnWeights b A) (Finset.range N)

@[simp] theorem orthogonalColumnWeights_at (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (i : Fin N) :
    orthogonalColumnWeights b A i.val = (‖A (b i)‖ : ℂ) := by
  simp [orthogonalColumnWeights,i.isLt]

@[simp] theorem orthogonalColumnDiagonal_single (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (i : Fin N) :
    orthogonalColumnDiagonal b A (lp.single 2 i.val (1 : ℂ)) =
      (‖A (b i)‖ : ℂ) • (lp.single 2 i.val (1 : ℂ) : SequenceL2) := by
  have h := diagonalTruncation_isDiagonal (orthogonalColumnWeights b A) (Finset.range N) i.val
  simpa only [orthogonalColumnDiagonal,Finset.mem_range,i.isLt,ite_true,orthogonalColumnWeights_at] using h

theorem orthogonalColumnDiagonal_single_outside (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (n : ℕ) (hn : N ≤ n) :
    orthogonalColumnDiagonal b A (lp.single 2 n (1 : ℂ)) = 0 := by
  have h := diagonalTruncation_isDiagonal (orthogonalColumnWeights b A) (Finset.range N) n
  simpa only [orthogonalColumnDiagonal,Finset.mem_range,not_lt.mpr hn,ite_false,zero_smul] using h

variable [CompleteSpace F] [FiniteDimensional ℂ E]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

omit [FiniteDimensional ℂ E] in
/-- Reconstruction from normalized actual columns, including zero columns. -/
theorem orthogonalColumn_factorization (b : OrthonormalBasis (Fin N) ℂ E) (A : E →L[ℂ] F) :
    A = (finiteAnalysis (fun i => NormedSpace.normalize (A (b i)))).adjoint ∘L
      orthogonalColumnDiagonal b A ∘L finiteAnalysis (fun i => b i) := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change A (b i) = (finiteAnalysis (fun j => NormedSpace.normalize (A (b j)))).adjoint
    (orthogonalColumnDiagonal b A (finiteAnalysis (fun j => b j) (b i)))
  rw [finiteAnalysis_orthonormal_column _ b.orthonormal,orthogonalColumnDiagonal_single,
    map_smul,finiteAnalysis_adjoint_single,complex_norm_smul_normalize]

omit [CompleteSpace F] in
/-- Orthogonality recovers the same diagonal through the actual operator. -/
theorem orthogonalColumn_diagonal_factorization (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (hOrth : Pairwise (fun i j => inner ℂ (A (b i)) (A (b j)) = 0)) :
    orthogonalColumnDiagonal b A = finiteAnalysis (fun i => NormedSpace.normalize (A (b i))) ∘L
      A ∘L (finiteAnalysis (fun i => b i)).adjoint := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro n
  apply ContinuousLinearMap.ext_ring
  change orthogonalColumnDiagonal b A (lp.single 2 n (1 : ℂ)) =
    finiteAnalysis (fun i => NormedSpace.normalize (A (b i)))
      (A ((finiteAnalysis (fun i => b i)).adjoint (lp.single 2 n (1 : ℂ))))
  by_cases hn : n < N
  · let i : Fin N := ⟨n,hn⟩
    change orthogonalColumnDiagonal b A (lp.single 2 i.val (1 : ℂ)) =
      finiteAnalysis (fun j => NormedSpace.normalize (A (b j)))
        (A ((finiteAnalysis (fun j => b j)).adjoint (lp.single 2 i.val (1 : ℂ))))
    rw [orthogonalColumnDiagonal_single,finiteAnalysis_adjoint_single,
      finiteAnalysis_normalized_column _ hOrth]
  · rw [orthogonalColumnDiagonal_single_outside b A n (not_lt.mp hn),
      finiteAnalysis_adjoint_single_outside _ n (not_lt.mp hn),map_zero,map_zero]

/-- Each approximation number is preserved by the two contractive factorizations. -/
theorem approximationNumber_orthogonalColumn (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (hOrth : Pairwise (fun i j => inner ℂ (A (b i)) (A (b j)) = 0)) (n : ℕ) :
    approximationNumber A n = approximationNumber (orthogonalColumnDiagonal b A) n := by
  let R := finiteAnalysis (fun i => b i)
  let C := finiteAnalysis (fun i => NormedSpace.normalize (A (b i)))
  have hR : ‖R‖ ≤ 1 := norm_finiteAnalysis_le_one _ (fun x => (b.sum_sq_norm_inner_right x).le)
  have hC : ‖C‖ ≤ 1 := norm_finiteAnalysis_le_one _ (normalizedFamily_bessel _ hOrth)
  have hR' : ‖R.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map R).trans_le hR
  have hC' : ‖C.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map C).trans_le hC
  apply le_antisymm
  · calc
      _ = approximationNumber (C.adjoint ∘L orthogonalColumnDiagonal b A ∘L R) n :=
        congrArg (fun T => approximationNumber T n) (orthogonalColumn_factorization b A)
      _ ≤ _ := approximationNumber_comp_contractions C.adjoint (orthogonalColumnDiagonal b A) R hC' hR n
  · calc
      _ = approximationNumber (C ∘L A ∘L R.adjoint) n :=
        congrArg (fun T => approximationNumber T n) (orthogonalColumn_diagonal_factorization b A hOrth)
      _ ≤ _ := approximationNumber_comp_contractions C A R.adjoint hC hR' n

/-- Exact power sum of orthogonal actual columns; all positive exponents are allowed. -/
theorem orthogonalColumns_power_sum (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (hOrth : Pairwise (fun i j => inner ℂ (A (b i)) (A (b j)) = 0))
    (p : ℝ) (hp : 0 < p) :
    (∑' n, (approximationNumber A n : ℝ)^p) = ∑ i : Fin N, ‖A (b i)‖^p := by
  calc
    _ = ∑' n, (approximationNumber (orthogonalColumnDiagonal b A) n : ℝ)^p :=
      tsum_congr (fun n => by rw [approximationNumber_orthogonalColumn b A hOrth])
    _ = ∑ n ∈ Finset.range N, ‖orthogonalColumnWeights b A n‖^p :=
      diagonalTruncation_power_sum _ _ p hp
    _ = ∑ i : Fin N, ‖orthogonalColumnWeights b A i.val‖^p :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = _ := Finset.sum_congr rfl (fun i _hi => by simp [orthogonalColumnWeights_at])

theorem orthogonalColumns_schattenNorm_rpow (b : OrthonormalBasis (Fin N) ℂ E)
    (A : E →L[ℂ] F) (hOrth : Pairwise (fun i j => inner ℂ (A (b i)) (A (b j)) = 0))
    (p : ℝ) (hp : 0 < p) : schattenNorm p A ^ p = ∑ i : Fin N, ‖A (b i)‖^p := by
  rw [schattenNorm_rpow hp,orthogonalColumns_power_sum b A hOrth p hp]

/-- Finite index relabelling does not change the actual orthogonal-column formula. -/
theorem orthogonalColumns_schattenNorm_rpow_fintype {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] F)
    (hOrth : Pairwise (fun i j => inner ℂ (A (b i)) (A (b j)) = 0))
    (p : ℝ) (hp : 0 < p) : schattenNorm p A ^ p = ∑ i : ι, ‖A (b i)‖^p := by
  classical
  let e := Fintype.equivFin ι
  let c := b.reindex e
  have hc : Pairwise (fun i j => inner ℂ (A (c i)) (A (c j)) = 0) := by
    intro i j hij
    simpa only [c,OrthonormalBasis.reindex_apply] using hOrth (e.symm.injective.ne hij)
  rw [orthogonalColumns_schattenNorm_rpow c A hc p hp]
  exact Fintype.sum_equiv e.symm _ _ (fun i => by rw [OrthonormalBasis.reindex_apply])

end OrthogonalColumns

section OrthogonalBlocks
variable {η : Type*} [Fintype η] {E F : η → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]

/-- The native finite Hilbert product map, with the actual blocks on its coordinates. -/
def finiteHilbertBlockMap (A : ∀ i, E i →L[ℂ] F i) : PiLp 2 E →L[ℂ] PiLp 2 F :=
  (PiLp.continuousLinearEquiv 2 ℂ F).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi (fun i => (A i) ∘L ContinuousLinearMap.proj i)) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ E).toContinuousLinearMap

omit [Fintype η] in
@[simp] theorem finiteHilbertBlockMap_apply (A : ∀ i, E i →L[ℂ] F i)
    (x : PiLp 2 E) (i : η) : finiteHilbertBlockMap A x i = A i (x i) := rfl

omit [Fintype η] in
@[simp] theorem finiteHilbertBlockMap_single (A : ∀ i, E i →L[ℂ] F i)
    [DecidableEq η] (i : η) (x : E i) :
    finiteHilbertBlockMap A (PiLp.single 2 i x) = PiLp.single 2 i (A i x) := by
  ext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Inner products of vectors placed in different Hilbert blocks vanish. -/
theorem inner_piLp_single_of_ne [DecidableEq η] (i j : η) (hij : i ≠ j)
    (x : F i) (y : F j) :
    inner ℂ (PiLp.single 2 i x) (PiLp.single 2 j y) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro k _hk
  by_cases hki : k = i
  · subst k
    simp [PiLp.ofLp_single,Pi.single_eq_of_ne hij]
  · simp [PiLp.ofLp_single,Pi.single_eq_of_ne hki]

/-- The same-block inner product is the native component inner product. -/
theorem inner_piLp_single_same [DecidableEq η] (i : η) (x y : F i) :
    inner ℂ (PiLp.single 2 i x) (PiLp.single 2 i y) = inner ℂ x y := by
  rw [PiLp.inner_apply,Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [PiLp.ofLp_single,Pi.single_eq_of_ne hji]
  · simp

variable [∀ i, CompleteSpace (F i)] [∀ i, FiniteDimensional ℂ (E i)]

/-- The joined Gram basis has genuinely pairwise orthogonal images, including zero blocks. -/
theorem finiteHilbertBlockMap_gram_orthogonal (A : ∀ i, E i →L[ℂ] F i) :
    Pairwise (fun i j => inner ℂ
      (finiteHilbertBlockMap A (Pi.orthonormalBasis (fun k => gramBasis (A k)) i))
      (finiteHilbertBlockMap A (Pi.orthonormalBasis (fun k => gramBasis (A k)) j)) = 0) := by
  classical
  intro i j hij
  rw [Pi.orthonormalBasis_apply,Pi.orthonormalBasis_apply,
    finiteHilbertBlockMap_single,finiteHilbertBlockMap_single]
  obtain ⟨i,k⟩ := i
  obtain ⟨j,l⟩ := j
  by_cases he : i = j
  · subst j
    rw [inner_piLp_single_same]
    apply gramBasis_images_orthogonal (A i)
    intro hkl
    change k = l at hkl
    exact hij (by cases hkl; rfl)
  · exact inner_piLp_single_of_ne i j he _ _

/-- Exact positive Schatten-power additivity for an actual orthogonal finite block sum.
The component codomains may be infinite-dimensional; the index set and blocks may be empty. -/
theorem finiteHilbertBlockMap_schattenNorm_rpow (A : ∀ i, E i →L[ℂ] F i)
    (p : ℝ) (hp : 0 < p) :
    schattenNorm p (finiteHilbertBlockMap A) ^ p = ∑ i, schattenNorm p (A i) ^ p := by
  classical
  rw [orthogonalColumns_schattenNorm_rpow_fintype
    (Pi.orthonormalBasis (fun i => gramBasis (A i))) (finiteHilbertBlockMap A)
    (finiteHilbertBlockMap_gram_orthogonal A) p hp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    _ = ∑ j, ‖A i (gramBasis (A i) j)‖^p := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Pi.orthonormalBasis_apply,finiteHilbertBlockMap_single,PiLp.norm_single]
    _ = schattenNorm p (A i)^p :=
      (finiteGram_power_sum (A i) p hp).symm.trans (schattenNorm_rpow hp).symm

end OrthogonalBlocks

section IsometricBlockPlacements
variable {E F H K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Isometric placement in larger Hilbert spaces preserves every approximation number. -/
theorem approximationNumber_isometric_placement (A : E →L[ℂ] F)
    (I : E →ₗᵢ[ℂ] H) (J : F →ₗᵢ[ℂ] K) (n : ℕ) :
    approximationNumber (J.toContinuousLinearMap ∘L A ∘L I.toContinuousLinearMap.adjoint) n =
      approximationNumber A n := by
  let B := J.toContinuousLinearMap ∘L A ∘L I.toContinuousLinearMap.adjoint
  have hI := I.norm_toContinuousLinearMap_le
  have hJ := J.norm_toContinuousLinearMap_le
  have hIa : ‖I.toContinuousLinearMap.adjoint‖ ≤ 1 :=
    (ContinuousLinearMap.adjoint.norm_map _).trans_le hI
  have hJa : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 :=
    (ContinuousLinearMap.adjoint.norm_map _).trans_le hJ
  have hRecover : A = J.toContinuousLinearMap.adjoint ∘L B ∘L I.toContinuousLinearMap := by
    have hIx (x : E) : I.toContinuousLinearMap.adjoint (I x) = x :=
      congrArg (fun T : E →L[ℂ] E => T x) I.adjoint_comp_self
    have hJy (y : F) : J.toContinuousLinearMap.adjoint (J y) = y :=
      congrArg (fun T : F →L[ℂ] F => T y) J.adjoint_comp_self
    ext x
    change A x = J.toContinuousLinearMap.adjoint (J (A (I.toContinuousLinearMap.adjoint (I x))))
    rw [hIx,hJy]
  apply le_antisymm
  · exact approximationNumber_comp_contractions J.toContinuousLinearMap A
      I.toContinuousLinearMap.adjoint hJ hIa n
  · rw [congrArg (fun T => approximationNumber T n) hRecover]
    exact approximationNumber_comp_contractions J.toContinuousLinearMap.adjoint B
      I.toContinuousLinearMap hJa hI n

theorem schattenNorm_isometric_placement_rpow (A : E →L[ℂ] F)
    (I : E →ₗᵢ[ℂ] H) (J : F →ₗᵢ[ℂ] K) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (J.toContinuousLinearMap ∘L A ∘L I.toContinuousLinearMap.adjoint)^p =
      schattenNorm p A ^p := by
  simp only [schattenNorm_rpow hp,approximationNumber_isometric_placement]

end IsometricBlockPlacements

section CoordinateBlockPlacements
variable {η : Type*} [Fintype η]

/-- Flatten the finite Hilbert blocks and place them in distinct actual coordinates.
An injective placement expresses disjointness, without any interval convention. -/
def finiteCoordinateBlockInclusion (d : η → ℕ) (N : ℕ)
    (e : (Σ i, Fin (d i)) ↪ Fin N) :
    PiLp 2 (fun i => EuclideanSpace ℂ (Fin (d i))) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (LinearIsometry.piLpExtendByZero 2 ℂ ℂ e).comp
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun i (_j : Fin (d i)) => ℂ)).symm.toLinearIsometry

theorem finiteCoordinateBlockInclusion_apply (d : η → ℕ) (N : ℕ)
    (e : (Σ i, Fin (d i)) ↪ Fin N)
    (x : PiLp 2 (fun i => EuclideanSpace ℂ (Fin (d i)))) (i : Σ i, Fin (d i)) :
    finiteCoordinateBlockInclusion d N e x (e i) = x i.fst i.snd := by
  change Function.extend e (fun j : Σ i, Fin (d i) => x j.fst j.snd) 0 (e i) = _
  rw [e.injective.extend_apply]

theorem finiteCoordinateBlockInclusion_apply_zero (d : η → ℕ) (N : ℕ)
    (e : (Σ i, Fin (d i)) ↪ Fin N)
    (x : PiLp 2 (fun i => EuclideanSpace ℂ (Fin (d i)))) (j : Fin N)
    (hj : j ∉ Set.range e) : finiteCoordinateBlockInclusion d N e x j = 0 := by
  apply LinearIsometry.piLpExtendByZero_apply_eq_zero
  exact hj

/-- A coordinate vector lands at exactly its specified ambient coordinate. -/
theorem finiteCoordinateBlockInclusion_single (d : η → ℕ) (N : ℕ)
    (e : (Σ i, Fin (d i)) ↪ Fin N) [DecidableEq η]
    (i : η) (j : Fin (d i)) (z : ℂ) :
    finiteCoordinateBlockInclusion d N e (PiLp.single 2 i (EuclideanSpace.single j z)) =
      EuclideanSpace.single (e ⟨i,j⟩) z := by
  have hFlat : (LinearIsometryEquiv.piLpCurry ℂ 2 (fun i (_j : Fin (d i)) => ℂ)).symm
      (PiLp.single 2 i (EuclideanSpace.single j z)) =
      (EuclideanSpace.single ⟨i,j⟩ z : EuclideanSpace ℂ (Σ i, Fin (d i))) := by
    ext k
    obtain ⟨k,l⟩ := k
    by_cases hki : k = i
    · subst k
      simp [LinearIsometryEquiv.piLpCurry_symm_apply,PiLp.ofLp_single,Sigma.uncurry]
    · simp [LinearIsometryEquiv.piLpCurry_symm_apply,PiLp.ofLp_single,Sigma.uncurry,hki]
  change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ e)
    ((LinearIsometryEquiv.piLpCurry ℂ 2 (fun i (_j : Fin (d i)) => ℂ)).symm
      (PiLp.single 2 i (EuclideanSpace.single j z))) = _
  rw [hFlat,LinearIsometry.piLpExtendByZero_apply_single]

/-- The adjoint is literal restriction to the assigned coordinates. -/
theorem finiteCoordinateBlockInclusion_adjoint_apply (d : η → ℕ) (N : ℕ)
    (e : (Σ i, Fin (d i)) ↪ Fin N) (f : EuclideanSpace ℂ (Fin N))
    (i : η) (j : Fin (d i)) :
    (finiteCoordinateBlockInclusion d N e).toContinuousLinearMap.adjoint f i j = f (e ⟨i,j⟩) := by
  classical
  have he := ContinuousLinearMap.adjoint_inner_right
    (finiteCoordinateBlockInclusion d N e).toContinuousLinearMap
    (PiLp.single 2 i (EuclideanSpace.single j (1 : ℂ))) f
  rw [LinearIsometry.coe_toContinuousLinearMap,finiteCoordinateBlockInclusion_single,
    EuclideanSpace.inner_single_left] at he
  have hInner (y : PiLp 2 (fun i => EuclideanSpace ℂ (Fin (d i)))) :
      inner ℂ (PiLp.single 2 i (EuclideanSpace.single j (1 : ℂ))) y = y i j := by
    rw [PiLp.inner_apply,Finset.sum_eq_single i]
    · simp [EuclideanSpace.inner_single_left]
    · intro k _hk hki
      simp [PiLp.ofLp_single,Pi.single_eq_of_ne hki]
    · simp
  simpa only [map_one,one_mul,hInner] using he

/-- Exact Schatten-power sum for arbitrary disjoint finite coordinate placements. -/
theorem finiteCoordinateBlockMap_schattenNorm_rpow (r c : η → ℕ) (R C : ℕ)
    (er : (Σ i, Fin (r i)) ↪ Fin R) (ec : (Σ i, Fin (c i)) ↪ Fin C)
    (A : ∀ i, EuclideanSpace ℂ (Fin (c i)) →L[ℂ] EuclideanSpace ℂ (Fin (r i)))
    (p : ℝ) (hp : 0 < p) :
    schattenNorm p ((finiteCoordinateBlockInclusion r R er).toContinuousLinearMap ∘L
      finiteHilbertBlockMap A ∘L (finiteCoordinateBlockInclusion c C ec).toContinuousLinearMap.adjoint)^p =
      ∑ i, schattenNorm p (A i)^p := by
  rw [schattenNorm_isometric_placement_rpow _ _ _ p hp,
    finiteHilbertBlockMap_schattenNorm_rpow A p hp]

end CoordinateBlockPlacements

end TTO.Paper.Proved
