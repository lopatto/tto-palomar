/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CompactHankelFoundations
public import TTO.WeightedBlaschkeFoundations

/-! Restoring the first two columns of a trace-class Hankel tail. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance tailHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance tailHankelNormedSpace : NormedSpace ℂ HankelOperator := inferInstance
local instance tailSequenceNormed : NormedAddCommGroup SequenceOperator := inferInstance
local instance tailSequenceNormedSpace : NormedSpace ℂ SequenceOperator := inferInstance

def sequenceTail (k : ℕ) (x : SequenceL2) : SequenceL2 :=
  ⟨fun i => x (i+k),memℓp_gen (((lp.memℓp x).summable (by norm_num : 0<(2 : ℝ≥0∞).toReal)).comp_injective
    (fun i j h => Nat.add_right_cancel h))⟩

@[simp] theorem sequenceTail_apply (k : ℕ) (x : SequenceL2) (i : ℕ) : sequenceTail k x i=x (i+k) := rfl

theorem norm_sequenceTail_le (k : ℕ) (x : SequenceL2) : ‖sequenceTail k x‖≤‖x‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0<(2 : ℝ≥0∞).toReal) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal)]
  exact tsum_comp_le_tsum_of_inj
    ((lp.memℓp x).summable (by norm_num : 0<(2 : ℝ≥0∞).toReal))
    (fun i => Real.rpow_nonneg (norm_nonneg (x i)) _)
    (fun i j h => Nat.add_right_cancel h)

def sequenceBackwardShift (k : ℕ) : SequenceOperator :=
  LinearMap.mkContinuous
    { toFun := sequenceTail k
      map_add' := fun x y => by apply lp.ext; funext i; simp only [sequenceTail_apply,lp.coeFn_add,Pi.add_apply]
      map_smul' := fun c x => by apply lp.ext; funext i; simp only [sequenceTail_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply] }
    1 (fun x => by
      change ‖sequenceTail k x‖≤1*‖x‖
      rw [one_mul]
      exact norm_sequenceTail_le k x)

@[simp] theorem sequenceBackwardShift_apply (k : ℕ) (x : SequenceL2) (i : ℕ) :
    sequenceBackwardShift k x i=x (i+k) := rfl

theorem norm_sequenceBackwardShift_le_one (k : ℕ) : ‖sequenceBackwardShift k‖≤1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem sequenceBackwardShift_single (k j : ℕ) :
    sequenceBackwardShift k (lp.single 2 j 1)= if k ≤ j then lp.single 2 (j-k) 1 else 0 := by
  by_cases h : k ≤ j
  · rw [ite_eq_left h]
    apply lp.ext
    funext i
    simp only [sequenceBackwardShift_apply,lp.single_apply,Pi.single_apply]
    have he : (i+k=j)↔(i=j-k) := by omega
    simp only [he]
  · rw [ite_eq_right h]
    apply lp.ext
    funext i
    simp only [sequenceBackwardShift_apply,lp.single_apply,Pi.single_apply,lp.coeFn_zero,Pi.zero_apply]
    rw [ite_eq_right (by omega)]

theorem sequenceBackwardShift_adjoint_apply (k : ℕ) (x : SequenceL2) (i : ℕ) :
    (sequenceBackwardShift k).adjoint x i= if k ≤ i then x (i-k) else 0 := by
  have he := ContinuousLinearMap.adjoint_inner_right (sequenceBackwardShift k) (lp.single 2 i 1) x
  rw [sequenceBackwardShift_single] at he
  by_cases h : k ≤ i
  · rw [ite_eq_left h] at he ⊢
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using he
  · rw [ite_eq_right h] at he ⊢
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,inner_zero_left] using he


theorem schatten_contracting_composition
    {E F G K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    {p : ℝ} {A : F →L[ℂ] G} (hA : Schatten p A)
    (L : G →L[ℂ] K) (R : E →L[ℂ] F) (hL : ‖L‖≤1) (hR : ‖R‖≤1) :
    Schatten p (L ∘L A ∘L R) ∧ schattenNorm p (L ∘L A ∘L R)≤schattenNorm p A := by
  refine ⟨schatten_comp hA L R,(schattenNorm_comp_le hA L R).trans ?_⟩
  have hn : ‖L‖*‖R‖≤1 := by nlinarith [norm_nonneg L,norm_nonneg R]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (Reduction.schattenNorm_nonneg p A)

theorem schatten_hankelSequenceOperator {p : ℝ} (K : HankelOperator) (hK : Schatten p K) :
    Schatten p (hankelSequenceOperator K) ∧
      schattenNorm p (hankelSequenceOperator K)≤schattenNorm p K :=
  schatten_contracting_composition hK _ _
    negativeBasis.repr.toLinearIsometry.norm_toContinuousLinearMap_le
    hardyBasis.repr.symm.toLinearIsometry.norm_toContinuousLinearMap_le

theorem schatten_hankelFromSequence {p : ℝ} (K : SequenceOperator) (hK : Schatten p K) :
    Schatten p (hankelFromSequence K) ∧ schattenNorm p (hankelFromSequence K)≤schattenNorm p K :=
  schatten_contracting_composition hK _ _
    negativeBasis.repr.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    hardyBasis.repr.toLinearIsometry.norm_toContinuousLinearMap_le

def sequenceColumn (j : ℕ) (v : SequenceL2) : SequenceOperator :=
  InnerProductSpace.rankOne ℂ v (lp.single 2 j 1)

theorem sequenceColumn_apply (j : ℕ) (v x : SequenceL2) :
    sequenceColumn j v x=x j • v := by
  rw [sequenceColumn,InnerProductSpace.rankOne_apply,lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one]

theorem sequenceColumn_traceNorm (j : ℕ) (v : SequenceL2) :
    Schatten 1 (sequenceColumn j v) ∧ schattenNorm 1 (sequenceColumn j v)=‖v‖ := by
  have hRange : (sequenceColumn j v).range≤Submodule.span ℂ ({v} : Set SequenceL2) := by
    rintro _ ⟨x,rfl⟩
    rw [ContinuousLinearMap.coe_coe,sequenceColumn_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hRank : (sequenceColumn j v).rank≤(1 : Cardinal) :=
    (Submodule.rank_mono hRange).trans (by simpa only [Cardinal.mk_singleton] using rank_span_le ({v} : Set SequenceL2))
  obtain ⟨hSp,hNorm⟩ := schatten_one_of_rank_le_one (sequenceColumn j v) hRank
  refine ⟨hSp,hNorm.trans ?_⟩
  rw [sequenceColumn,InnerProductSpace.norm_rankOne,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),
    norm_one,mul_one]


def hankelSequenceColumn (g : BoundaryL2) (j : ℕ) : SequenceL2 :=
  negativeBasis.repr (hankelColumn (star (multiply coordinate g)) j)

theorem hankelSequenceColumn_apply (g : BoundaryL2) (j i : ℕ) :
    hankelSequenceColumn g j i=conj (fourierCoeff g ((i+j : ℕ) : ℤ)) := by
  exact (negativeBasis.repr_apply_apply _ _).trans (hankelColumn_coefficient g i j)

theorem hankelSequence_tail_entry (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) (i j : ℕ) :
    hankelSequenceOperator K (lp.single 2 j 1) i=conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ)) := by
  change negativeBasis.repr (K (hardyBasis.repr.symm (lp.single 2 j 1))) i=_
  rw [hardyBasis.repr_symm_single,HilbertBasis.repr_apply_apply,hK]

theorem hankelSequenceColumn_one (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) :
    hankelSequenceColumn g 1=
      conj (fourierCoeff g 1) • lp.single 2 0 1+
        (sequenceBackwardShift 1).adjoint (hankelSequenceOperator K (lp.single 2 0 1)) := by
  apply lp.ext
  funext i
  simp only [hankelSequenceColumn_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,lp.single_apply,Pi.single_apply,sequenceBackwardShift_adjoint_apply,
    hankelSequence_tail_entry g K hK]
  by_cases h0 : i=0
  · subst i
    norm_num
  · have hi : 1 ≤ i := by omega
    simp only [ite_eq_right h0,ite_eq_left hi,mul_zero,zero_add]
    congr 2
    omega

theorem hankelSequenceColumn_zero (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) :
    hankelSequenceColumn g 0=
      conj (fourierCoeff g 0) • lp.single 2 0 1+
        conj (fourierCoeff g 1) • lp.single 2 1 1+
        (sequenceBackwardShift 2).adjoint (hankelSequenceOperator K (lp.single 2 0 1)) := by
  apply lp.ext
  funext i
  simp only [hankelSequenceColumn_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,lp.single_apply,Pi.single_apply,sequenceBackwardShift_adjoint_apply,
    hankelSequence_tail_entry g K hK]
  by_cases h0 : i=0
  · subst i
    norm_num
  · by_cases h1 : i=1
    · subst i
      norm_num
    · have hi : 2 ≤ i := by omega
      simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_left hi,mul_zero,zero_add,add_zero]
      congr 2
      omega

theorem norm_sequenceBackwardShift_adjoint_apply_le (k : ℕ) (x : SequenceL2) :
    ‖(sequenceBackwardShift k).adjoint x‖≤‖x‖ := by
  have hN : ‖(sequenceBackwardShift k).adjoint‖≤1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact norm_sequenceBackwardShift_le_one k
  exact ((sequenceBackwardShift k).adjoint.le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right hN (norm_nonneg x)).trans_eq (one_mul _))

theorem norm_hankelSequence_tail_column (K : HankelOperator) (hK : Schatten 1 K) :
    ‖hankelSequenceOperator K (lp.single 2 0 1)‖≤schattenNorm 1 K := by
  have hSeq := schatten_hankelSequenceOperator K hK
  have hNorm := (hankelSequenceOperator K).le_opNorm (lp.single 2 0 1)
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one] at hNorm
  exact hNorm.trans ((opNorm_le_schattenNorm 1 (hankelSequenceOperator K) hSeq.1).trans hSeq.2)

theorem hankelSequenceColumn_norm_bounds (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) (hS : Schatten 1 K) :
    ‖hankelSequenceColumn g 0‖≤‖fourierCoeff g 0‖+‖fourierCoeff g 1‖+schattenNorm 1 K ∧
    ‖hankelSequenceColumn g 1‖≤‖fourierCoeff g 1‖+schattenNorm 1 K := by
  have hUnit (c : ℂ) (j : ℕ) : ‖c • (lp.single 2 j 1 : SequenceL2)‖=‖c‖ := by
    rw [norm_smul,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one]
  have hTail := norm_hankelSequence_tail_column K hS
  constructor
  · rw [hankelSequenceColumn_zero g K hK]
    have hAdd := norm_add_le
      (conj (fourierCoeff g 0) • (lp.single 2 0 1 : SequenceL2))
      (conj (fourierCoeff g 1) • (lp.single 2 1 1 : SequenceL2))
    rw [hUnit,hUnit,Complex.norm_conj,Complex.norm_conj] at hAdd
    exact (norm_add_le _ _).trans (add_le_add hAdd
      ((norm_sequenceBackwardShift_adjoint_apply_le 2 _).trans hTail))
  · rw [hankelSequenceColumn_one g K hK]
    have hAdd := norm_add_le
      (conj (fourierCoeff g 1) • (lp.single 2 0 1 : SequenceL2))
      ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator K (lp.single 2 0 1)))
    rw [hUnit,Complex.norm_conj] at hAdd
    exact hAdd.trans (add_le_add le_rfl ((norm_sequenceBackwardShift_adjoint_apply_le 1 _).trans hTail))


/-- Literal completion by the original first two columns and the shifted supplied tail. -/
def hankelTailCompletion (g : BoundaryL2) (K : HankelOperator) : SequenceOperator :=
  sequenceColumn 0 (hankelSequenceColumn g 0)+sequenceColumn 1 (hankelSequenceColumn g 1)+
    hankelSequenceOperator K ∘L sequenceBackwardShift 2

theorem hankelTailCompletion_single (g : BoundaryL2) (K : HankelOperator) (j : ℕ) :
    hankelTailCompletion g K (lp.single 2 j 1)=
      if j=0 then hankelSequenceColumn g 0 else
        if j=1 then hankelSequenceColumn g 1 else hankelSequenceOperator K (lp.single 2 (j-2) 1) := by
  change sequenceColumn 0 (hankelSequenceColumn g 0) (lp.single 2 j 1)+
    sequenceColumn 1 (hankelSequenceColumn g 1) (lp.single 2 j 1)+
      hankelSequenceOperator K (sequenceBackwardShift 2 (lp.single 2 j 1))=_
  rw [sequenceColumn_apply,sequenceColumn_apply,sequenceBackwardShift_single]
  by_cases h0 : j=0
  · subst j
    simp [lp.single_apply]
  · by_cases h1 : j=1
    · subst j
      simp [lp.single_apply]
    · have hj : 2 ≤ j := by omega
      have hn0 : (0 : ℕ)≠j := Ne.symm h0
      have hn1 : (1 : ℕ)≠j := Ne.symm h1
      simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_left hj,lp.single_apply,
        Pi.single_apply,ite_eq_right hn0,ite_eq_right hn1,zero_smul,zero_add]

theorem hankelTailCompletion_represents (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) :
    RepresentsHankel (star (multiply coordinate g)) (hankelFromSequence (hankelTailCompletion g K)) := by
  apply representsHankel_of_columns
  intro j
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  change negativeBasis.repr (negativeBasis.repr.symm (hankelTailCompletion g K
    (hardyBasis.repr (hardyBasis j)))) i=hankelSequenceColumn g j i
  rw [LinearIsometryEquiv.apply_symm_apply,hardyBasis.repr_self,hankelTailCompletion_single]
  by_cases h0 : j=0
  · subst j
    rw [ite_eq_left rfl]
  · rw [ite_eq_right h0]
    by_cases h1 : j=1
    · subst j
      rw [ite_eq_left rfl]
    · rw [ite_eq_right h1,hankelSequence_tail_entry g K hK,hankelSequenceColumn_apply]
      congr 2
      omega

theorem hankelTailCompletion_traceNorm (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) (hS : Schatten 1 K) :
    Schatten 1 (hankelTailCompletion g K) ∧
      schattenNorm 1 (hankelTailCompletion g K)≤
        ‖fourierCoeff g 0‖+2*‖fourierCoeff g 1‖+3*schattenNorm 1 K := by
  obtain ⟨hSeq,hSeqNorm⟩ := schatten_hankelSequenceOperator K hS
  have hTail : Schatten 1 (hankelSequenceOperator K ∘L sequenceBackwardShift 2) ∧
      schattenNorm 1 (hankelSequenceOperator K ∘L sequenceBackwardShift 2)≤schattenNorm 1 K := by
    have h := schatten_contracting_composition hSeq (ContinuousLinearMap.id ℂ SequenceL2)
      (sequenceBackwardShift 2) ContinuousLinearMap.norm_id_le (norm_sequenceBackwardShift_le_one 2)
    simp only [ContinuousLinearMap.id_comp] at h
    exact ⟨h.1,h.2.trans hSeqNorm⟩
  obtain ⟨h0,h0Norm⟩ := sequenceColumn_traceNorm 0 (hankelSequenceColumn g 0)
  obtain ⟨h1,h1Norm⟩ := sequenceColumn_traceNorm 1 (hankelSequenceColumn g 1)
  have h01 := schatten_add h0 h1
  refine ⟨schatten_add h01 hTail.1,?_⟩
  have hAdd := schattenNorm_add_le_sharp 1 le_rfl
    (sequenceColumn 0 (hankelSequenceColumn g 0)+sequenceColumn 1 (hankelSequenceColumn g 1))
    (hankelSequenceOperator K ∘L sequenceBackwardShift 2) h01 hTail.1
  have hAdd01 := schattenNorm_add_le_sharp 1 le_rfl _ _ h0 h1
  rw [h0Norm,h1Norm] at hAdd01
  have hCols := hankelSequenceColumn_norm_bounds g K hK hS
  change schattenNorm 1
    (sequenceColumn 0 (hankelSequenceColumn g 0)+sequenceColumn 1 (hankelSequenceColumn g 1)+
      hankelSequenceOperator K ∘L sequenceBackwardShift 2)≤_
  linarith [hTail.2,hCols.1,hCols.2]

/-- A trace-class tail matrix produces the original represented Hankel operator, with
the two missing Taylor coefficients fully restored in the quantitative bound. -/
theorem traceClassHankel_of_tail (g : BoundaryL2) (K : HankelOperator)
    (hK : ∀ i j,inner ℂ (negativeBasis i) (K (hardyBasis j))=
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ))) (hS : Schatten 1 K) :
    ∃ H : HankelOperator, RepresentsHankel (star (multiply coordinate g)) H ∧ Schatten 1 H ∧
      schattenNorm 1 H≤‖fourierCoeff g 0‖+2*‖fourierCoeff g 1‖+3*schattenNorm 1 K := by
  obtain ⟨hComp,hNorm⟩ := hankelTailCompletion_traceNorm g K hK hS
  obtain ⟨hSp,hGauge⟩ := schatten_hankelFromSequence (hankelTailCompletion g K) hComp
  exact ⟨hankelFromSequence (hankelTailCompletion g K),hankelTailCompletion_represents g K hK,
    hSp,hGauge.trans hNorm⟩

end TTO.Paper.Proved
