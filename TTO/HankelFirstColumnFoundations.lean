/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelStrongNecessityFoundations

/-! Literal first-column restoration and all-p coordinate shifts for actual Hankel operators. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance columnHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance columnHankelNormedSpace : NormedSpace ℂ HankelOperator := inferInstance
local instance columnSequenceNormed : NormedAddCommGroup SequenceOperator := inferInstance
local instance columnSequenceNormedSpace : NormedSpace ℂ SequenceOperator := inferInstance

theorem sequenceColumn_schatten {p : ℝ} (hp : 0<p) (j : ℕ) (v : SequenceL2) :
    Schatten p (sequenceColumn j v) ∧ schattenNorm p (sequenceColumn j v)=‖v‖ := by
  have hRange : (sequenceColumn j v).range≤Submodule.span ℂ ({v} : Set SequenceL2) := by
    rintro _ ⟨x,rfl⟩
    rw [ContinuousLinearMap.coe_coe,sequenceColumn_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hRank : (sequenceColumn j v).rank≤(1 : Cardinal) :=
    (Submodule.rank_mono hRange).trans
      (by simpa only [Cardinal.mk_singleton] using rank_span_le ({v} : Set SequenceL2))
  refine ⟨finiteRankSchatten _ ⟨1,hRank⟩ p hp,?_⟩
  unfold schattenNorm
  rw [tsum_eq_single 0]
  · simp only [approximationNumber_index_zero,coe_nnnorm,one_div]
    rw [Real.rpow_rpow_inv (norm_nonneg _) hp.ne',sequenceColumn,
      InnerProductSpace.norm_rankOne,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),
      norm_one,mul_one]
  · intro n hn
    have h1n : (1 : Cardinal)≤(n : Cardinal) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    rw [approximationNumber_eq_zero_of_rank_le _ n (hRank.trans h1n),NNReal.coe_zero,
      Real.zero_rpow hp.ne']

theorem schattenHankel_coordinate_unshift {p : ℝ} (g : BoundaryL2) (K : HankelOperator)
    (hK : RepresentsHankel (star (multiply coordinate (multiply coordinate g))) K)
    (hS : Schatten p K) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤schattenNorm p K := by
  obtain ⟨hSeq,hSeqN⟩ := schatten_hankelSequenceOperator K hS
  have hShift : ‖(sequenceBackwardShift 1).adjoint‖≤1 :=
    (ContinuousLinearMap.adjoint.norm_map (sequenceBackwardShift 1)).trans_le
      (norm_sequenceBackwardShift_le_one 1)
  have h := schatten_contracting_composition hSeq (ContinuousLinearMap.id ℂ SequenceL2)
    (sequenceBackwardShift 1).adjoint ContinuousLinearMap.norm_id_le hShift
  simp only [ContinuousLinearMap.id_comp] at h
  obtain ⟨hH,hHN⟩ := schatten_hankelFromSequence (hankelUnshiftSequence K) h.1
  exact ⟨hankelFromSequence (hankelUnshiftSequence K),
    representsHankel_fromSequence_coefficients _ _ (hankelUnshiftSequence_matrix g K hK),
    hH,hHN.trans (h.2.trans hSeqN)⟩

theorem exists_schattenHankel_of_positive_sequence (g : BoundaryL2) (Z : SequenceOperator)
    {p : ℝ} (hZ : Schatten p Z)
    (hEntry : ∀ i j : ℕ,Z (lp.single 2 j (1 : ℂ)) i=fourierCoeff g ((i+j : ℕ) : ℤ)) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤schattenNorm p Z := by
  have hAdj : Schatten p Z.adjoint := (schatten_adjoint_iff Z p).mpr hZ
  obtain ⟨hHS,hHN⟩ := schatten_hankelFromSequence Z.adjoint hAdj
  refine ⟨hankelFromSequence Z.adjoint,?_,hHS,?_⟩
  · apply representsHankel_fromSequence_coefficients
    intro i j
    rw [sequenceAdjoint_single_entry,hEntry,Nat.add_comm]
  · exact hHN.trans (le_of_eq (schattenNorm_adjoint_eq Z p))

def hankelRestoreFirstColumn (K : SequenceOperator) (a0 : ℂ) : SequenceOperator :=
  K ∘L sequenceBackwardShift 1+
    sequenceColumn 0 (a0 • lp.single 2 0 (1 : ℂ)+
      (sequenceBackwardShift 1).adjoint (K (lp.single 2 0 (1 : ℂ))))

theorem hankelRestoreFirstColumn_single (K : SequenceOperator) (a0 : ℂ) (j : ℕ) :
    hankelRestoreFirstColumn K a0 (lp.single 2 j (1 : ℂ))=
      if j=0 then a0 • lp.single 2 0 (1 : ℂ)+
        (sequenceBackwardShift 1).adjoint (K (lp.single 2 0 (1 : ℂ)))
      else K (lp.single 2 (j-1) (1 : ℂ)) := by
  simp only [hankelRestoreFirstColumn,add_apply,
    ContinuousLinearMap.comp_apply,sequenceBackwardShift_single,sequenceColumn_apply]
  by_cases h0 : j=0
  · subst j
    simp [lp.single_apply]
  · have hj : 1≤j := by omega
    simp only [ite_eq_left hj,ite_eq_right h0,lp.single_apply,Pi.single_apply,
      ite_eq_right (Ne.symm h0),zero_smul,add_zero]

theorem hankelRestoreFirstColumn_entry (a : ℕ→ℂ) (K : SequenceOperator)
    (hK : ∀ i j : ℕ,K (lp.single 2 j (1 : ℂ)) i=a (i+j+1)) (i j : ℕ) :
    hankelRestoreFirstColumn K (a 0) (lp.single 2 j (1 : ℂ)) i=a (i+j) := by
  rw [hankelRestoreFirstColumn_single]
  by_cases hj : j=0
  · subst j
    rw [ite_eq_left rfl]
    simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_apply,sequenceBackwardShift_adjoint_apply]
    by_cases hi : i=0
    · subst i
      simp
    · have hi1 : 1 ≤ i := by omega
      rw [ite_eq_right hi,ite_eq_left hi1,hK]
      simp only [mul_zero,zero_add,Nat.add_zero]
      congr 1
      omega
  · rw [ite_eq_right hj,hK]
    congr 1
    omega

theorem hankelRestoreFirstColumn_schatten {p : ℝ} (hp : 1≤p)
    (K : SequenceOperator) (hK : Schatten p K) (a0 : ℂ) :
    Schatten p (hankelRestoreFirstColumn K a0) ∧
      schattenNorm p (hankelRestoreFirstColumn K a0)≤2*schattenNorm p K+‖a0‖ := by
  have hp0 : 0<p := lt_of_lt_of_le zero_lt_one hp
  have hTail : Schatten p (K ∘L sequenceBackwardShift 1) ∧
      schattenNorm p (K ∘L sequenceBackwardShift 1)≤schattenNorm p K := by
    have h := schatten_contracting_composition hK (ContinuousLinearMap.id ℂ SequenceL2)
      (sequenceBackwardShift 1) ContinuousLinearMap.norm_id_le
      (norm_sequenceBackwardShift_le_one 1)
    simpa only [ContinuousLinearMap.id_comp] using h
  let v := a0 • lp.single 2 0 (1 : ℂ)+
    (sequenceBackwardShift 1).adjoint (K (lp.single 2 0 (1 : ℂ)))
  have hKv : ‖K (lp.single 2 0 (1 : ℂ))‖≤schattenNorm p K := by
    have h := K.le_opNorm (lp.single 2 0 (1 : ℂ))
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one] at h
    exact h.trans (opNorm_le_schattenNorm p K hK)
  have hv : ‖v‖≤‖a0‖+schattenNorm p K := by
    calc
      _ ≤ ‖a0 • lp.single 2 0 (1 : ℂ)‖+
          ‖(sequenceBackwardShift 1).adjoint (K (lp.single 2 0 (1 : ℂ)))‖ := norm_add_le _ _
      _ ≤ ‖a0‖+schattenNorm p K := by
        rw [norm_smul,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one]
        linarith [(norm_sequenceBackwardShift_adjoint_apply_le 1 _).trans hKv]
  obtain ⟨hCol,hColN⟩ := sequenceColumn_schatten hp0 0 v
  refine ⟨schatten_add hTail.1 hCol,?_⟩
  have h := schattenNorm_add_le_sharp p hp _ _ hTail.1 hCol
  change schattenNorm p (K ∘L sequenceBackwardShift 1+sequenceColumn 0 v)≤_
  rw [hColN] at h
  linarith [hTail.2]

theorem exists_schattenHankel_of_shifted_sequence (g : BoundaryL2) (K : SequenceOperator)
    {p : ℝ} (hp : 1≤p) (hK : Schatten p K)
    (hEntry : ∀ i j : ℕ,K (lp.single 2 j (1 : ℂ)) i=
      fourierCoeff g ((i+j+1 : ℕ) : ℤ)) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤2*schattenNorm p K+‖fourierCoeff g 0‖ := by
  have hA := hankelRestoreFirstColumn_schatten hp K hK (fourierCoeff g 0)
  obtain ⟨H,hH,hS,hN⟩ := exists_schattenHankel_of_positive_sequence g
    (hankelRestoreFirstColumn K (fourierCoeff g 0)) hA.1
      (hankelRestoreFirstColumn_entry (fun n => fourierCoeff g (n : ℤ)) K hEntry)
  exact ⟨H,hH,hS,hN.trans hA.2⟩

end TTO.Paper.Proved
