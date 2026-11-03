/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelTailCompletionFoundations
public import TTO.TraceHankelSynthesisFoundations

/-! Actual one-step shift and unshift of trace-class classical Hankel operators. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance shiftHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance shiftHankelNormedSpace : NormedSpace ℂ HankelOperator := inferInstance
local instance shiftSequenceNormed : NormedAddCommGroup SequenceOperator := inferInstance
local instance shiftSequenceNormedSpace : NormedSpace ℂ SequenceOperator := inferInstance

theorem sequenceForwardOne_single (j : ℕ) :
    (sequenceBackwardShift 1).adjoint (lp.single 2 j 1)=lp.single 2 (j+1) 1 := by
  apply lp.ext
  funext i
  rw [sequenceBackwardShift_adjoint_apply]
  simp only [lp.single_apply,Pi.single_apply]
  by_cases hi : 1 ≤ i
  · rw [ite_eq_left hi]
    have he : (i-1=j)↔(i=j+1) := by omega
    simp only [he]
  · rw [ite_eq_right hi,ite_eq_right (show i≠j+1 by omega)]

theorem fourierCoeff_coordinate_product (g : BoundaryL2) (m : ℤ) :
    fourierCoeff (multiply coordinate g) m=fourierCoeff g (m-1) := by
  change fourierCoeff (multiply (mode 1) g) m=_
  exact fourierCoeff_mode_multiply 1 m g

theorem hankelSequenceOperator_coefficient (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) (i j : ℕ) :
    hankelSequenceOperator H (lp.single 2 j 1) i=conj (fourierCoeff g ((i+j : ℕ) : ℤ)) := by
  change negativeBasis.repr (H (hardyBasis.repr.symm (lp.single 2 j 1))) i=_
  rw [hardyBasis.repr_symm_single,HilbertBasis.repr_apply_apply,
    representsHankel_columns _ H hH,hankelColumn_coefficient]

theorem hankelFromSequence_coefficient (A : SequenceOperator) (i j : ℕ) :
    inner ℂ (negativeBasis i) (hankelFromSequence A (hardyBasis j))=A (lp.single 2 j 1) i := by
  rw [←negativeBasis.repr_apply_apply]
  change negativeBasis.repr (negativeBasis.repr.symm (A (hardyBasis.repr (hardyBasis j)))) i=_
  rw [LinearIsometryEquiv.apply_symm_apply,hardyBasis.repr_self]

theorem representsHankel_fromSequence_coefficients (g : BoundaryL2) (A : SequenceOperator)
    (hA : ∀ i j,A (lp.single 2 j 1) i=conj (fourierCoeff g ((i+j : ℕ) : ℤ))) :
    RepresentsHankel (star (multiply coordinate g)) (hankelFromSequence A) := by
  apply representsHankel_of_columns
  intro j
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  rw [negativeBasis.repr_apply_apply,negativeBasis.repr_apply_apply,
    hankelFromSequence_coefficient,hA,hankelColumn_coefficient]

def hankelShiftSequence (H : HankelOperator) : SequenceOperator :=
  hankelSequenceOperator H ∘L sequenceBackwardShift 1+
    sequenceColumn 0 ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1)))

theorem hankelShiftSequence_single (H : HankelOperator) (j : ℕ) :
    hankelShiftSequence H (lp.single 2 j 1)=
      if j=0 then (sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1))
      else hankelSequenceOperator H (lp.single 2 (j-1) 1) := by
  change hankelSequenceOperator H (sequenceBackwardShift 1 (lp.single 2 j 1))+
    sequenceColumn 0 ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1))) (lp.single 2 j 1)=_
  rw [sequenceBackwardShift_single,sequenceColumn_apply]
  by_cases h0 : j=0
  · subst j
    simp [lp.single_apply]
  · have hj : 1 ≤ j := by omega
    simp only [ite_eq_left hj,ite_eq_right h0,lp.single_apply,Pi.single_apply,
      ite_eq_right (Ne.symm h0),zero_smul,add_zero]

theorem hankelShiftSequence_matrix (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (i j : ℕ) :
    hankelShiftSequence H (lp.single 2 j 1) i=
      conj (fourierCoeff (multiply coordinate g.val) ((i+j : ℕ) : ℤ)) := by
  rw [hankelShiftSequence_single,fourierCoeff_coordinate_product]
  by_cases hj : j=0
  · subst j
    rw [ite_eq_left rfl,sequenceBackwardShift_adjoint_apply]
    by_cases hi : i=0
    · subst i
      have hg : fourierCoeff g.val (-1)=0 := (mem_hardy_iff g.val).mp g.property _ (by norm_num)
      simp only [Nat.add_zero,Nat.cast_zero,zero_sub,ite_eq_right (by norm_num : ¬1 ≤ (0 : ℕ)),hg,map_zero]
    · have hi1 : 1 ≤ i := by omega
      rw [ite_eq_left hi1,hankelSequenceOperator_coefficient g.val H hH]
      congr 2
      omega
  · rw [ite_eq_right hj,hankelSequenceOperator_coefficient g.val H hH]
    congr 2
    omega

theorem hankelShiftSequence_schatten (H : HankelOperator) (hH : Schatten 1 H) :
    Schatten 1 (hankelShiftSequence H) ∧ schattenNorm 1 (hankelShiftSequence H)≤2*schattenNorm 1 H := by
  obtain ⟨hSeq,hSeqN⟩ := schatten_hankelSequenceOperator H hH
  have hTail : Schatten 1 (hankelSequenceOperator H ∘L sequenceBackwardShift 1) ∧
      schattenNorm 1 (hankelSequenceOperator H ∘L sequenceBackwardShift 1)≤schattenNorm 1 H := by
    have h := schatten_contracting_composition hSeq (ContinuousLinearMap.id ℂ SequenceL2)
      (sequenceBackwardShift 1) ContinuousLinearMap.norm_id_le (norm_sequenceBackwardShift_le_one 1)
    simp only [ContinuousLinearMap.id_comp] at h
    exact ⟨h.1,h.2.trans hSeqN⟩
  obtain ⟨hCol,hColN⟩ := sequenceColumn_traceNorm 0
    ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1)))
  have hColBound : schattenNorm 1
      (sequenceColumn 0 ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1))))≤
      schattenNorm 1 H := by
    rw [hColN]
    exact (norm_sequenceBackwardShift_adjoint_apply_le 1 _).trans (norm_hankelSequence_tail_column H hH)
  refine ⟨schatten_add hTail.1 hCol,?_⟩
  have hAdd := schattenNorm_add_le_sharp 1 le_rfl _ _ hTail.1 hCol
  change schattenNorm 1 (hankelSequenceOperator H ∘L sequenceBackwardShift 1+
    sequenceColumn 0 ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1))))≤_
  linarith [hTail.2]

theorem traceClassHankel_coordinate_shift (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hS : Schatten 1 H) :
    ∃ K : HankelOperator, RepresentsHankel (star (multiply coordinate (multiply coordinate g.val))) K ∧
      Schatten 1 K ∧ schattenNorm 1 K≤2*schattenNorm 1 H := by
  obtain ⟨hSeq,hN⟩ := hankelShiftSequence_schatten H hS
  obtain ⟨hK,hKN⟩ := schatten_hankelFromSequence (hankelShiftSequence H) hSeq
  exact ⟨hankelFromSequence (hankelShiftSequence H),
    representsHankel_fromSequence_coefficients _ _ (hankelShiftSequence_matrix g H hH),hK,hKN.trans hN⟩

def hankelUnshiftSequence (K : HankelOperator) : SequenceOperator :=
  hankelSequenceOperator K ∘L (sequenceBackwardShift 1).adjoint

theorem hankelUnshiftSequence_matrix (g : BoundaryL2) (K : HankelOperator)
    (hK : RepresentsHankel (star (multiply coordinate (multiply coordinate g))) K) (i j : ℕ) :
    hankelUnshiftSequence K (lp.single 2 j 1) i=conj (fourierCoeff g ((i+j : ℕ) : ℤ)) := by
  change hankelSequenceOperator K ((sequenceBackwardShift 1).adjoint (lp.single 2 j 1)) i=_
  rw [sequenceForwardOne_single,hankelSequenceOperator_coefficient (multiply coordinate g) K hK,
    fourierCoeff_coordinate_product]
  congr 2
  omega

theorem traceClassHankel_coordinate_unshift (g : BoundaryL2) (K : HankelOperator)
    (hK : RepresentsHankel (star (multiply coordinate (multiply coordinate g))) K) (hS : Schatten 1 K) :
    ∃ H : HankelOperator, RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten 1 H ∧ schattenNorm 1 H≤schattenNorm 1 K := by
  obtain ⟨hSeq,hSeqN⟩ := schatten_hankelSequenceOperator K hS
  have hShift : ‖(sequenceBackwardShift 1).adjoint‖≤1 :=
    (ContinuousLinearMap.adjoint.norm_map (sequenceBackwardShift 1)).trans_le (norm_sequenceBackwardShift_le_one 1)
  have h := schatten_contracting_composition hSeq (ContinuousLinearMap.id ℂ SequenceL2)
    (sequenceBackwardShift 1).adjoint ContinuousLinearMap.norm_id_le hShift
  simp only [ContinuousLinearMap.id_comp] at h
  obtain ⟨hH,hHN⟩ := schatten_hankelFromSequence (hankelUnshiftSequence K) h.1
  exact ⟨hankelFromSequence (hankelUnshiftSequence K),
    representsHankel_fromSequence_coefficients _ _ (hankelUnshiftSequence_matrix g K hK),
    hH,hHN.trans (h.2.trans hSeqN)⟩

end TTO.Paper.Proved
