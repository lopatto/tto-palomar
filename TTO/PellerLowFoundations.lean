/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BesovTaylorCoefficientFoundations
public import TTO.AnalyticBandBudgetFoundations
public import TTO.HankelFirstColumnFoundations

/-! Both original Besov formulations for the genuine classical Hankel theorem, 0<p≤1. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance lowHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance lowHankelNormedSpace : NormedSpace ℂ HankelOperator := inferInstance
local instance lowSequenceNormed : NormedAddCommGroup SequenceOperator := inferInstance
local instance lowSequenceNormedSpace : NormedSpace ℂ SequenceOperator := inferInstance

theorem exists_hankel_schatten_rpow_le_besov_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,besovEnergy p (analyticValue g)≠∞ →
      ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
        Schatten p H ∧ schattenNorm p H^p≤C*(besovEnergy p (analyticValue g)).toReal := by
  obtain ⟨B,hB,hBudget⟩ := exists_wideHankelBandBudget_of_besov p hp hp1
  let m := besovOrder p
  let D := 125*((m : ℝ)+1)*2^(1-p)
  have hD : 0<D := by dsimp only [D];positivity
  refine ⟨wideHankelBaseBesovConstant m p+D*B,
    add_pos (wideHankelBaseBesovConstant_pos m p) (mul_pos hD hB),?_⟩
  intro g hE
  obtain ⟨H,hH,hS,hN⟩ := exists_schattenHankel_of_wide_band_budget m g p hp hp1
    (B*(besovEnergy p (analyticValue g)).toReal)
    (mul_nonneg hB.le ENNReal.toReal_nonneg) (hBudget g hE)
  refine ⟨H,hH,hS,hN.trans ?_⟩
  calc
    _ ≤ wideHankelBaseBesovConstant m p*(besovEnergy p (analyticValue g)).toReal+
        D*(B*(besovEnergy p (analyticValue g)).toReal) :=
      add_le_add (wideHankelBaseBudget_le_besovEnergy_toReal m g p hp hp1 hE) le_rfl
    _ = _ := by ring

theorem besovEnergy_coordinate_shift (p : ℝ) (hp : 0<p) (g : Hardy) :
    besovEnergy p (analyticValue (multiply coordinate g.val))=
      homogeneousBesovEnergy p (fun z => z*analyticValue g.val z) := by
  unfold besovEnergy homogeneousBesovEnergy
  apply congrArg₂ (fun a b : ℝ≥0∞ => a+b)
  · apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDeriv_coordinate_analyticValue g j 0 (by norm_num [disk])]
    by_cases hj0 : j=0
    · subst j
      simp only [iteratedDeriv_zero,zero_mul,norm_zero,Real.zero_rpow hp.ne',
        ENNReal.ofReal_zero,ite_true]
    · rw [ite_eq_right hj0]
  · apply lintegral_congr_ae
    filter_upwards [ae_mem_diskArea] with z hz
    rw [iteratedDeriv_coordinate_analyticValue g (besovOrder p) z hz]

theorem hankelShiftSequence_schatten_low (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (H : HankelOperator) (hH : Schatten p H) :
    Schatten p (hankelShiftSequence H) ∧
      schattenNorm p (hankelShiftSequence H)^p≤2*schattenNorm p H^p := by
  obtain ⟨hSeq,hSeqN⟩ := schatten_hankelSequenceOperator H hH
  have hTail : Schatten p (hankelSequenceOperator H ∘L sequenceBackwardShift 1) ∧
      schattenNorm p (hankelSequenceOperator H ∘L sequenceBackwardShift 1)≤schattenNorm p H := by
    have h := schatten_contracting_composition hSeq (ContinuousLinearMap.id ℂ SequenceL2)
      (sequenceBackwardShift 1) ContinuousLinearMap.norm_id_le (norm_sequenceBackwardShift_le_one 1)
    simp only [ContinuousLinearMap.id_comp] at h
    exact ⟨h.1,h.2.trans hSeqN⟩
  obtain ⟨hCol,hColN⟩ := sequenceColumn_schatten hp 0
    ((sequenceBackwardShift 1).adjoint (hankelSequenceOperator H (lp.single 2 0 1)))
  have hVec : ‖(sequenceBackwardShift 1).adjoint
      (hankelSequenceOperator H (lp.single 2 0 1))‖≤schattenNorm p H := by
    calc
      _ ≤ ‖hankelSequenceOperator H (lp.single 2 0 1)‖ :=
        norm_sequenceBackwardShift_adjoint_apply_le 1 _
      _ ≤ ‖hankelSequenceOperator H‖ := by
        simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one] using
          (hankelSequenceOperator H).le_opNorm (lp.single 2 0 1)
      _ ≤ schattenNorm p (hankelSequenceOperator H) := opNorm_le_schattenNorm p _ hSeq
      _ ≤ schattenNorm p H := hSeqN
  have hColBound := hColN.le.trans hVec
  refine ⟨schatten_add hTail.1 hCol,?_⟩
  change schattenNorm p (hankelSequenceOperator H ∘L sequenceBackwardShift 1+
    sequenceColumn 0 ((sequenceBackwardShift 1).adjoint
      (hankelSequenceOperator H (lp.single 2 0 1))))^p≤_
  calc
    _ ≤ schattenNorm p (hankelSequenceOperator H ∘L sequenceBackwardShift 1)^p+
        schattenNorm p (sequenceColumn 0 ((sequenceBackwardShift 1).adjoint
          (hankelSequenceOperator H (lp.single 2 0 1))))^p :=
      schattenNorm_add_rpow_le_sharp p hp hp1 _ _ hTail.1 hCol
    _ ≤ schattenNorm p H^p+schattenNorm p H^p := add_le_add
      (Real.rpow_le_rpow (schattenNorm_nonneg p _) hTail.2 hp.le)
      (Real.rpow_le_rpow (schattenNorm_nonneg p _) hColBound hp.le)
    _ = _ := by ring

theorem exists_schattenHankel_of_besov_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,besovEnergy p (analyticValue g)<∞ →
      ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
        Schatten p H ∧ schattenNorm p H≤C*besovNorm p g := by
  obtain ⟨C,hC,hBound⟩ := exists_hankel_schatten_rpow_le_besov_low p hp hp1
  refine ⟨C^(1/p),Real.rpow_pos_of_pos hC _,?_⟩
  intro g hE
  obtain ⟨H,hH,hS,hN⟩ := hBound g hE.ne
  refine ⟨H,hH,hS,?_⟩
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (schattenNorm_nonneg p H) p)
    hN (one_div_pos.mpr hp).le
  rw [← Real.rpow_mul (schattenNorm_nonneg p H),mul_one_div_cancel hp.ne',
    Real.rpow_one,Real.mul_rpow hC.le ENNReal.toReal_nonneg] at h
  exact h

theorem besovNorm_coordinate_shift (p : ℝ) (hp : 0<p) (g : Hardy) :
    besovNorm p (multiply coordinate g.val)=
      homogeneousBesovNorm p (fun z => z*analyticValue g.val z) := by
  unfold besovNorm homogeneousBesovNorm
  rw [besovEnergy_coordinate_shift p hp g]

theorem inBesov_coordinate_shift (p : ℝ) (hp : 0<p) (g : Hardy) :
    InBesov p (multiply coordinate g.val) ↔
      homogeneousBesovEnergy p (fun z => z*analyticValue g.val z)<∞ := by
  rw [InBesov,besovEnergy_coordinate_shift p hp g]
  exact and_iff_right (mode_multiply_hardy g 1)

theorem schattenHankel_coordinate_shift_low (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hS : Schatten p H) :
    ∃ K : HankelOperator,RepresentsHankel (star (multiply coordinate (multiply coordinate g.val))) K ∧
      Schatten p K ∧ schattenNorm p K^p≤2*schattenNorm p H^p := by
  obtain ⟨hSeq,hN⟩ := hankelShiftSequence_schatten_low p hp hp1 H hS
  obtain ⟨hK,hKN⟩ := schatten_hankelFromSequence (hankelShiftSequence H) hSeq
  refine ⟨hankelFromSequence (hankelShiftSequence H),
    representsHankel_fromSequence_coefficients _ _ (hankelShiftSequence_matrix g H hH),hK,?_⟩
  exact (Real.rpow_le_rpow (schattenNorm_nonneg p _) hKN hp.le).trans hN

theorem schattenHankel_coordinate_shift_norm_low (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hS : Schatten p H) :
    ∃ K : HankelOperator,RepresentsHankel (star (multiply coordinate (multiply coordinate g.val))) K ∧
      Schatten p K ∧ schattenNorm p K≤2^(1/p)*schattenNorm p H := by
  obtain ⟨K,hK,hKS,hN⟩ := schattenHankel_coordinate_shift_low p hp hp1 g H hH hS
  refine ⟨K,hK,hKS,?_⟩
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (schattenNorm_nonneg p K) p)
    hN (one_div_pos.mpr hp).le
  rw [← Real.rpow_mul (schattenNorm_nonneg p K),mul_one_div_cancel hp.ne',
    Real.rpow_one,Real.mul_rpow (by norm_num : (0 : ℝ)≤2)
      (Real.rpow_nonneg (schattenNorm_nonneg p H) p),
    ← Real.rpow_mul (schattenNorm_nonneg p H),mul_one_div_cancel hp.ne',Real.rpow_one] at h
  exact h

theorem exists_schattenHankel_of_homogeneousBesov_low
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,g∈hardy →
      homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞ →
      ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
        Schatten p H ∧ schattenNorm p H≤C*homogeneousBesovNorm p (fun z => z*analyticValue g z) := by
  obtain ⟨C,hC,hBound⟩ := exists_schattenHankel_of_besov_low p hp hp1
  refine ⟨C,hC,?_⟩
  intro g hg hE
  let f : Hardy := ⟨g,hg⟩
  have hShiftE : besovEnergy p (analyticValue (multiply coordinate g))<∞ := by
    rw [besovEnergy_coordinate_shift p hp f]
    exact hE
  obtain ⟨K,hK,hKS,hKN⟩ := hBound (multiply coordinate g) hShiftE
  obtain ⟨H,hH,hS,hN⟩ := schattenHankel_coordinate_unshift g K hK hKS
  refine ⟨H,hH,hS,?_⟩
  have hNormEq : besovNorm p (multiply coordinate g)=
      homogeneousBesovNorm p (fun z => z*analyticValue g z) :=
    besovNorm_coordinate_shift p hp f
  rw [← hNormEq]
  exact hN.trans hKN

theorem classicalHankel_schatten_low (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (g : BoundaryL2) (hg : g∈hardy) :
    HasSchattenHankel p (star (multiply coordinate g)) ↔ InBesov p g := by
  constructor
  · rintro ⟨H,hH,hS⟩
    exact inBesov_of_schattenHankel_low g hg H hH p hp hp1 hS
  · intro hB
    obtain ⟨C,hC,hBound⟩ := exists_schattenHankel_of_besov_low p hp hp1
    obtain ⟨H,hH,hS,_⟩ := hBound g hB.2
    exact ⟨H,hH,hS⟩

theorem exists_homogeneousBesovNorm_le_hankel_low
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,g∈hardy → ∀ H : HankelOperator,
      RepresentsHankel (star (multiply coordinate g)) H → Schatten p H →
        homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞ ∧
          homogeneousBesovNorm p (fun z => z*analyticValue g z)≤C*schattenNorm p H := by
  obtain ⟨C,hC,hBound⟩ := exists_besovNorm_le_hankel_low p hp hp1
  refine ⟨C*2^(1/p),mul_pos hC (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) _),?_⟩
  intro g hg H hH hS
  let f : Hardy := ⟨g,hg⟩
  obtain ⟨K,hK,hKS,hKN⟩ := schattenHankel_coordinate_shift_norm_low p hp hp1 f H hH hS
  have hgShift : multiply coordinate g∈hardy := mode_multiply_hardy f 1
  have hB := inBesov_of_schattenHankel_low (multiply coordinate g) hgShift K hK p hp hp1 hKS
  have hEnergyEq : besovEnergy p (analyticValue (multiply coordinate g))=
      homogeneousBesovEnergy p (fun z => z*analyticValue g z) :=
    besovEnergy_coordinate_shift p hp f
  have hNormEq : besovNorm p (multiply coordinate g)=
      homogeneousBesovNorm p (fun z => z*analyticValue g z) :=
    besovNorm_coordinate_shift p hp f
  refine ⟨by rw [← hEnergyEq];exact hB.2,?_⟩
  calc
    _ = besovNorm p (multiply coordinate g) := hNormEq.symm
    _ ≤ C*schattenNorm p K := hBound (multiply coordinate g) hgShift K hK hKS
    _ ≤ C*(2^(1/p)*schattenNorm p H) := mul_le_mul_of_nonneg_left hKN hC.le
    _ = _ := by ring

theorem pellerLow (p : ℝ) (hp : 0<p) (hp1 : p≤1) : PellerObligation p := by
  obtain ⟨L,hL,hLower⟩ := exists_besovNorm_le_hankel_low p hp hp1
  obtain ⟨U,hU,hUpper⟩ := exists_schattenHankel_of_besov_low p hp hp1
  obtain ⟨Lh,hLh,hLowerH⟩ := exists_homogeneousBesovNorm_le_hankel_low p hp hp1
  obtain ⟨Uh,hUh,hUpperH⟩ := exists_schattenHankel_of_homogeneousBesov_low p hp hp1
  constructor
  · intro g hg
    refine ⟨classicalHankel_schatten_low p hp hp1 g hg,?_⟩
    constructor
    · rintro ⟨H,hH,hS⟩
      exact (hLowerH g hg H hH hS).1
    · intro hE
      obtain ⟨H,hH,hS,_⟩ := hUpperH g hg hE
      exact ⟨H,hH,hS⟩
  · refine ⟨L⁻¹,U,Lh⁻¹,Uh,inv_pos.mpr hL,hU,inv_pos.mpr hLh,hUh,?_⟩
    intro g hg H hH hS
    have hB := inBesov_of_schattenHankel_low g hg H hH p hp hp1 hS
    have hLB := hLower g hg H hH hS
    have hLHB := hLowerH g hg H hH hS
    obtain ⟨K,hK,hKS,hKN⟩ := hUpper g hB.2
    have he : H=K := representsHankel_unique _ H K hH hK
    have hUN : schattenNorm p H≤U*besovNorm p g := by rw [he];exact hKN
    obtain ⟨Kh,hKh,hKhS,hKhN⟩ := hUpperH g hg hLHB.1
    have heh : H=Kh := representsHankel_unique _ H Kh hH hKh
    have hUhN : schattenNorm p H≤Uh*homogeneousBesovNorm p
        (fun z => z*analyticValue g z) := by rw [heh];exact hKhN
    refine ⟨?_,hUN,?_,hUhN⟩
    · calc
        _ ≤ L⁻¹*(L*schattenNorm p H) :=
          mul_le_mul_of_nonneg_left hLB (inv_nonneg.mpr hL.le)
        _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hL.ne',one_mul]
    · calc
        _ ≤ Lh⁻¹*(Lh*schattenNorm p H) :=
          mul_le_mul_of_nonneg_left hLHB.2 (inv_nonneg.mpr hLh.le)
        _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hLh.ne',one_mul]

theorem besovClassification_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) : BesovConclusion p :=
  besovClassification p hp (pellerLow p hp hp1)

theorem coanalyticBesov_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) : CoanalyticBesovConclusion p :=
  coanalyticBesov p (besovClassification_low p hp hp1)

end TTO.Paper.Proved
