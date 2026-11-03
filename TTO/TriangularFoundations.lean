/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations

/-! The exact Hilbert–Schmidt triangular contraction. General p remains separate. -/
@[expose] public section
noncomputable section
open Set Filter Finset
open scoped ENNReal NNReal InnerProductSpace Topology
namespace TTO.Paper.Proved

section OrthogonalEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Finite Pythagoras, retaining zero vectors. -/
theorem norm_sum_sq_of_orthogonal {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖^2 = ∑ i ∈ s, ‖v i‖^2 := by
  classical
  have he : inner ℂ (∑ i ∈ s, v i) (∑ i ∈ s, v i) = ∑ i ∈ s, inner ℂ (v i) (v i) := by
    rw [sum_inner]
    apply sum_congr rfl
    intro i hi
    rw [inner_sum]
    exact sum_eq_single i (fun j hj hji => hv i hi j hj (Ne.symm hji))
      (fun hn => False.elim (hn hi))
  have h := congrArg Complex.re he
  change RCLike.re (inner ℂ (∑ i ∈ s, v i) (∑ i ∈ s, v i)) =
    RCLike.re (∑ i ∈ s, inner ℂ (v i) (v i)) at h
  simpa only [map_sum,inner_self_eq_norm_sq] using h

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- Orthogonal operator ranges give exact additivity of literal HS column energy. -/
theorem columnEnergy_sum_of_orthogonal {I : Type*} (b : HilbertBasis I ℂ H) {N : ℕ}
    (S : Fin N → H →L[ℂ] H)
    (hS : ∀ i j, i ≠ j → ∀ x y, inner ℂ (S i x) (S j y) = 0) :
    columnEnergy (∑ i, S i) b = ∑ i, columnEnergy (S i) b := by
  have hpoint (k : I) : ‖(∑ i, S i) (b k)‖ₑ^2 = ∑ i, ‖S i (b k)‖ₑ^2 := by
    have h := norm_sum_sq_of_orthogonal univ (fun i => S i (b k))
      (fun i _ j _ hij => hS i j hij _ _)
    have he := congrArg ENNReal.ofReal h
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖S i (b k)‖)] at he
    convert he using 1
    · rw [_root_.sum_apply,← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg _)]
    · apply sum_congr rfl
      intro i _
      rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg _)]
  unfold columnEnergy
  simp_rw [hpoint]
  calc
    (∑' k, ∑ i, ‖S i (b k)‖ₑ^2) = ∑' k, ∑' i, ‖S i (b k)‖ₑ^2 := by simp only [tsum_fintype]
    _ = ∑' i, ∑' k, ‖S i (b k)‖ₑ^2 := ENNReal.tsum_comm
    _ = ∑ i, ∑' k, ‖S i (b k)‖ₑ^2 := by rw [tsum_fintype]

/-- Right multiplication by any contraction cannot increase literal HS column energy. -/
theorem columnEnergy_comp_right_contraction {I : Type*} (b : HilbertBasis I ℂ H)
    (A R : H →L[ℂ] H) (hR : ‖R‖ ≤ 1) :
    columnEnergy (A ∘L R) b ≤ columnEnergy A b := by
  rw [← columnEnergy_adjoint (A ∘L R) b b,← columnEnergy_adjoint A b b,
    ContinuousLinearMap.adjoint_comp]
  unfold columnEnergy
  apply ENNReal.tsum_le_tsum
  intro i
  have hnorm : ‖R.adjoint (A.adjoint (b i))‖ ≤ ‖A.adjoint (b i)‖ := by
    apply (R.adjoint.le_opNorm _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (norm_nonneg (A.adjoint (b i)))
  change ‖R.adjoint (A.adjoint (b i))‖ₑ^2 ≤ ‖A.adjoint (b i)‖ₑ^2
  rw [← ofReal_norm,← ofReal_norm]
  exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hnorm) 2

end OrthogonalEnergy

section TriangularTwo
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Selfadjoint mutually annihilating blocks have orthogonal ranges. -/
theorem orthogonal_block_ranges {N : ℕ} (Q : Fin N → H →L[ℂ] H)
    (hself : ∀ i, (Q i).adjoint = Q i)
    (horth : ∀ i j, i ≠ j → Q i ∘L Q j = 0) :
    ∀ i j, i ≠ j → ∀ x y, inner ℂ (Q i x) (Q j y) = 0 := by
  intro i j hij x y
  rw [← ContinuousLinearMap.adjoint_inner_right,hself i]
  have he := congrArg (fun T : H →L[ℂ] H => T y) (horth i j hij)
  change Q i (Q j y) = 0 at he
  rw [he,inner_zero_right]

/-- Every partial sum of a complete orthogonal block decomposition is a contraction. -/
theorem norm_sum_blocks_le_one {N : ℕ} (Q : Fin N → H →L[ℂ] H)
    (hsum : (∑ i, Q i) = ContinuousLinearMap.id ℂ H)
    (hself : ∀ i, (Q i).adjoint = Q i)
    (horth : ∀ i j, i ≠ j → Q i ∘L Q j = 0) (s : Finset (Fin N)) :
    ‖∑ i ∈ s, Q i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have ho := orthogonal_block_ranges Q hself horth
  have hs := norm_sum_sq_of_orthogonal s (fun i => Q i x) (fun i _ j _ hij => ho i j hij x x)
  have hall := norm_sum_sq_of_orthogonal univ (fun i => Q i x) (fun i _ j _ hij => ho i j hij x x)
  have hfull : (∑ i, Q i x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hsum
    simpa only [_root_.sum_apply,ContinuousLinearMap.id_apply] using h
  rw [hfull] at hall
  have hle : (∑ i ∈ s, ‖Q i x‖^2) ≤ ∑ i, ‖Q i x‖^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => sq_nonneg _)
  have he : ‖(∑ i ∈ s, Q i) x‖^2 ≤ ‖x‖^2 := by
    rw [_root_.sum_apply,hs]
    exact hle.trans_eq hall.symm
  change ‖(∑ i ∈ s, Q i) x‖ ≤ 1*‖x‖
  rw [one_mul]
  exact le_of_sq_le_sq he (norm_nonneg x)

/-- Deleting the upper and diagonal block entries contracts actual HS energy. -/
theorem triangularCut_columnEnergy_le {I : Type*} (b : HilbertBasis I ℂ H) {N : ℕ}
    (Q : Fin N → H →L[ℂ] H) (hsum : (∑ i, Q i) = ContinuousLinearMap.id ℂ H)
    (hself : ∀ i, (Q i).adjoint = Q i)
    (horth : ∀ i j, i ≠ j → Q i ∘L Q j = 0) (A : H →L[ℂ] H) :
    columnEnergy (triangularCut Q A) b ≤ columnEnergy A b := by
  classical
  let P (i : Fin N) : H →L[ℂ] H := ∑ j ∈ univ.filter (fun j => j < i), Q j
  let C (i : Fin N) : H →L[ℂ] H := Q i ∘L A
  let B (i : Fin N) : H →L[ℂ] H := C i ∘L P i
  have hPn (i : Fin N) : ‖P i‖ ≤ 1 := norm_sum_blocks_le_one Q hsum hself horth _
  have ho := orthogonal_block_ranges Q hself horth
  have hC : ∀ i j, i ≠ j → ∀ x y, inner ℂ (C i x) (C j y) = 0 :=
    fun i j hij x y => ho i j hij (A x) (A y)
  have hB : ∀ i j, i ≠ j → ∀ x y, inner ℂ (B i x) (B j y) = 0 :=
    fun i j hij x y => ho i j hij (A (P i x)) (A (P j y))
  have hCs : (∑ i, C i) = A := by
    ext x
    have h := congrArg (fun T : H →L[ℂ] H => T (A x)) hsum
    simpa only [C,_root_.sum_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] using h
  have htri : triangularCut Q A = ∑ i, B i := by
    ext x
    simp only [triangularCut,B,C,P,_root_.sum_apply,ContinuousLinearMap.comp_apply,sum_filter]
    simp_rw [map_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  rw [htri,columnEnergy_sum_of_orthogonal b B hB]
  calc
    ∑ i, columnEnergy (B i) b ≤ ∑ i, columnEnergy (C i) b :=
      sum_le_sum (fun i _ => columnEnergy_comp_right_contraction b (C i) (P i) (hPn i))
    _ = columnEnergy (∑ i, C i) b := (columnEnergy_sum_of_orthogonal b C hC).symm
    _ = columnEnergy A b := by rw [hCs]

/-- The exact p=2 base case of the uniform triangular bound, on arbitrary Hilbert space. -/
theorem triangularConstant_two : TriangularConstant (2 : ℝ) 1 := by
  intro H _ _ _ N Q hsum hQ horth A hA
  obtain ⟨I,b,_⟩ := exists_hilbertBasis ℂ H
  have he := triangularCut_columnEnergy_le b Q hsum (fun i => (hQ i).1) horth A
  have hSp : Schatten 2 (triangularCut Q A) := (schatten_two_iff_columnEnergy _ b).mpr
    (he.trans_lt ((schatten_two_iff_columnEnergy A b).mp hA))
  refine ⟨hSp,?_⟩
  have hsq : ENNReal.ofReal (schattenNorm 2 (triangularCut Q A)^2) ≤
      ENNReal.ofReal (schattenNorm 2 A^2) := by
    rw [schattenNorm_two_sq_columnEnergy _ b hSp,schattenNorm_two_sq_columnEnergy _ b hA]
    exact he
  have hreal : schattenNorm 2 (triangularCut Q A)^2 ≤ schattenNorm 2 A^2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (schattenNorm 2 A))).mp hsq
  simpa only [one_mul] using le_of_sq_le_sq hreal (by unfold schattenNorm; positivity)

end TriangularTwo
end TTO.Paper.Proved
