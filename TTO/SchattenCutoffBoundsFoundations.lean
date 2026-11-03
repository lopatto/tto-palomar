/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CappedSchattenFoundations

/-! Actual low/high spectral-cut bounds for the finite weak-to-strong Schatten argument. -/
@[expose] public section
noncomputable section
open scoped NNReal InnerProductSpace
namespace TTO.Paper.Proved
open Reduction

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ E]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Removing the singular columns above t leaves an actual operator of norm at most t. -/
theorem norm_sub_singularCutoff_le (A : E →L[ℂ] F) (t : ℝ) (ht : 0≤t) :
    ‖A-singularCutoff A t‖≤t := by
  let D := diagonalTruncation (singularResidualWeights A t) (Finset.range (Module.finrank ℂ E))
  let R := finiteAnalysis (fun i => gramBasis A i)
  let L := (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint
  have hR : ‖R‖≤1 := (gramBasis_analysis_contractions A).1
  have hL : ‖L‖≤1 := (ContinuousLinearMap.adjoint.norm_map
    (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i))))).trans_le
      (gramBasis_analysis_contractions A).2
  have hD : ‖D‖≤t := by
    apply norm_diagonalTruncation_le _ _ t ht
    intro i hi
    by_cases hs : i∈singularCutoffSet A t
    · simpa only [singularResidualWeights,ite_eq_left hs,norm_zero] using ht
    · have hn : ‖finiteGramWeights A i‖≤t := le_of_not_gt (fun h =>
        hs (Finset.mem_filter.mpr ⟨hi,h⟩))
      simpa only [singularResidualWeights,ite_eq_right hs] using hn
  rw [sub_singularCutoff_factorization]
  change ‖L ∘L D ∘L R‖≤t
  have hDR : ‖D ∘L R‖≤t := by
    calc
      _ ≤ ‖D‖*‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ t*1 := mul_le_mul hD hR (norm_nonneg R) ht
      _ = t := mul_one t
  calc
    _ ≤ ‖L‖*‖D ∘L R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*t := mul_le_mul hL hDR (norm_nonneg _) zero_le_one
    _ = t := one_mul t

/-- Retained singular columns have their literal high-singular-value trace budget. -/
theorem schattenNorm_one_singularCutoff_le (A : E →L[ℂ] F) (t : ℝ) :
    schattenNorm 1 (singularCutoff A t)≤
      ∑ i∈Finset.range (Module.finrank ℂ E),
        if t<‖finiteGramWeights A i‖ then ‖finiteGramWeights A i‖ else 0 := by
  let w : ℕ → ℂ := fun i => if t<‖finiteGramWeights A i‖ then finiteGramWeights A i else 0
  let D := diagonalTruncation w (Finset.range (Module.finrank ℂ E))
  let R := finiteAnalysis (fun i => gramBasis A i)
  let L := (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint
  have hR : ‖R‖≤1 := (gramBasis_analysis_contractions A).1
  have hL : ‖L‖≤1 := (ContinuousLinearMap.adjoint.norm_map
    (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i))))).trans_le
      (gramBasis_analysis_contractions A).2
  have hEq : diagonalTruncation (finiteGramWeights A) (singularCutoffSet A t)=D := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    by_cases hi : i∈Finset.range (Module.finrank ℂ E)
    · by_cases hb : t<‖finiteGramWeights A i‖
      · simp [D,w,diagonalTruncation_apply,singularCutoffSet,hi,hb]
      · simp [D,w,diagonalTruncation_apply,singularCutoffSet,hi,hb]
    · simp [D,diagonalTruncation_apply,singularCutoffSet,hi]
  have hD : Schatten 1 D := finiteRankSchatten D
    ⟨Module.finrank ℂ E,by simpa only [D,Finset.card_range] using
      (rank_diagonalTruncation_le w (Finset.range (Module.finrank ℂ E)))⟩ 1 (by norm_num)
  rw [singularCutoff,hEq]
  change schattenNorm 1 (L ∘L D ∘L R)≤_
  calc
    _ ≤ (‖L‖*‖R‖)*schattenNorm 1 D := schattenNorm_comp_le hD L R
    _ ≤ schattenNorm 1 D := by
      have hm := mul_le_mul hL hR (norm_nonneg R) zero_le_one
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (schattenNorm_nonneg 1 D)
    _ = ∑ i∈Finset.range (Module.finrank ℂ E),‖w i‖ := schattenNorm_one_diagonalTruncation w _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hb : t<‖finiteGramWeights A i‖ <;> simp [w,hb]

end TTO.Paper.Proved
