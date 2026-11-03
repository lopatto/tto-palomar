/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelFirstColumnFoundations

/-! Both frozen Besov formulations for the genuine classical Hankel theorem when p>1. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem norm_fourierCoeff_le_hankel_schatten (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    {p : ℝ} (hS : Schatten p H) (n : ℕ) :
    ‖fourierCoeff g (n : ℤ)‖≤schattenNorm p H := by
  obtain ⟨hSeq,hSeqN⟩ := schatten_hankelSequenceOperator H hS
  have hEntry : hankelSequenceOperator H (lp.single 2 0 (1 : ℂ)) n=
      conj (fourierCoeff g (n : ℤ)) := by
    simpa only [Nat.add_zero] using hankelSequenceOperator_coefficient g H hH n 0
  calc
    _ = ‖hankelSequenceOperator H (lp.single 2 0 (1 : ℂ)) n‖ := by
      rw [hEntry,Complex.norm_conj]
    _ ≤ ‖hankelSequenceOperator H (lp.single 2 0 (1 : ℂ))‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) _ n
    _ ≤ ‖hankelSequenceOperator H‖ := by
      simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one,mul_one] using
        (hankelSequenceOperator H).le_opNorm (lp.single 2 0 (1 : ℂ))
    _ ≤ schattenNorm p (hankelSequenceOperator H) := opNorm_le_schattenNorm p _ hSeq
    _ ≤ schattenNorm p H := hSeqN

theorem hankel_derivative_energy_le (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue g) z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)≤
        ENNReal.ofReal (pellerStrongConstant p*schattenNorm p H^p) := by
  let h := multiply (star coordinate) g
  have hRep : RepresentsHankel (star (multiply coordinate (multiply coordinate h))) H := by
    simpa only [h,multiply_cancel_star coordinate coordinate_unimodular] using hH
  obtain ⟨K,hK,hKS,hKN⟩ := schattenHankel_coordinate_unshift h H hRep hS
  have hE := hankel_coordinate_derivative_energy_le h K hK p hp hKS
  simp only [h,multiply_cancel_star coordinate coordinate_unimodular] at hE
  refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ (pellerStrongConstant_pos p hp).le
  exact Real.rpow_le_rpow (schattenNorm_nonneg p K) hKN (lt_trans zero_lt_one hp).le

theorem hankel_besov_energy_le (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    besovEnergy p (analyticValue g)≤
      ENNReal.ofReal ((1+2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p) := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hC : 0≤2^|p-2| *pellerStrongConstant p :=
    mul_nonneg (by positivity) (pellerStrongConstant_pos p hp).le
  have hD : (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue g) z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)≤
        ENNReal.ofReal ((2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p) := by
    calc
      _ ≤ ENNReal.ofReal (2^|p-2|)*
          ∫⁻ z,ENNReal.ofReal
            (‖deriv (analyticValue g) z‖^p*(1-‖z‖)^(p-2)) ∂diskArea :=
        lintegral_frozenDiskWeight_le (fun z => ‖deriv (analyticValue g) z‖^p)
          (fun z _ => Real.rpow_nonneg (norm_nonneg _) p) (p-2)
      _ ≤ ENNReal.ofReal (2^|p-2|)*
          ENNReal.ofReal (pellerStrongConstant p*schattenNorm p H^p) :=
        mul_le_mul_right (hankel_derivative_energy_le g H hH p hp hS) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0≤(2 : ℝ)^|p-2|)]
        congr 1
        ring
  have h0 : ENNReal.ofReal (‖fourierCoeff g 0‖^p)≤ENNReal.ofReal (schattenNorm p H^p) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _)
      (norm_fourierCoeff_le_hankel_schatten g H hH hS 0) hp0.le)
  rw [besovEnergy_of_one_lt p hp,analyticValue_at_zero]
  calc
    _ ≤ ENNReal.ofReal (schattenNorm p H^p)+
        ENNReal.ofReal ((2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p) :=
      add_le_add h0 hD
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (schattenNorm_nonneg p H) p)
        (mul_nonneg hC (Real.rpow_nonneg (schattenNorm_nonneg p H) p))]
      congr 1
      ring

theorem real_le_energy_root (a p : ℝ) (ha : 0≤a) (hp : 0<p)
    (E : ℝ≥0∞) (hE : E<∞) (h : ENNReal.ofReal (a^p)≤E) :
    a≤E.toReal^(1/p) := by
  have hr := ENNReal.toReal_mono hE.ne h
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg ha p)] at hr
  have hrp := Real.rpow_le_rpow (Real.rpow_nonneg ha p) hr (one_div_pos.mpr hp).le
  simpa only [one_div,Real.rpow_rpow_inv ha hp.ne'] using hrp

theorem hankel_besov_necessity_gt_one (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    besovEnergy p (analyticValue g)<∞ ∧ besovNorm p g≤
      (1+2^|p-2| *pellerStrongConstant p)^(1/p)*schattenNorm p H := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hK : 0≤1+2^|p-2| *pellerStrongConstant p := by
    have h := (pellerStrongConstant_pos p hp).le
    positivity
  have hEnergy := hankel_besov_energy_le g H hH p hp hS
  refine ⟨hEnergy.trans_lt ENNReal.ofReal_lt_top,?_⟩
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEnergy
  rw [ENNReal.toReal_ofReal
    (mul_nonneg hK (Real.rpow_nonneg (schattenNorm_nonneg p H) p))] at hReal
  unfold besovNorm
  calc
    _ ≤ ((1+2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p)^(1/p) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg hReal (one_div_pos.mpr hp0).le
    _ = _ := by
      rw [Real.mul_rpow hK (Real.rpow_nonneg (schattenNorm_nonneg p H) p),
        one_div,Real.rpow_rpow_inv (schattenNorm_nonneg p H) hp0.ne']

theorem besov_first_order_bounds (g : BoundaryL2) (p : ℝ) (hp : 1<p)
    (hB : besovEnergy p (analyticValue g)<∞) :
    (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue g) z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)<∞ ∧
    ‖fourierCoeff g 0‖≤besovNorm p g ∧
    (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue g) z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea).toReal^(1/p)≤
        besovNorm p g := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hD : (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue g) z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)≤
        besovEnergy p (analyticValue g) := by
    rw [besovEnergy_of_one_lt p hp]
    exact le_add_left le_rfl
  have h0 : ENNReal.ofReal (‖fourierCoeff g 0‖^p)≤besovEnergy p (analyticValue g) := by
    rw [besovEnergy_of_one_lt p hp,analyticValue_at_zero]
    exact le_add_right le_rfl
  refine ⟨hD.trans_lt hB,?_,?_⟩
  · exact real_le_energy_root _ p (norm_nonneg _) hp0 _ hB h0
  · exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono hB.ne hD) (one_div_pos.mpr hp0).le

theorem diskTaylorCoeff_analytic_deriv_div (g : BoundaryL2) (n : ℕ) :
    diskTaylorCoeff (deriv (analyticValue g)) n/((n : ℂ)+1)=
      fourierCoeff g ((n+1 : ℕ) : ℤ) := by
  rw [diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue]
  simp only [Nat.cast_add,Nat.cast_one]
  have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show (n : ℝ)+1≠0 by positivity)
  field_simp

theorem exists_schattenHankel_of_besov_gt_one (g : BoundaryL2)
    (p q : ℝ) (hpq : p.HolderConjugate q)
    (hB : besovEnergy p (analyticValue g)<∞) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤
        (2*(pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))+1)*besovNorm p g := by
  let G := deriv (analyticValue g)
  have hG : AnalyticOnNhd ℂ G disk :=
    fun z hz => (analyticOnNhd_analyticValue g z hz).deriv
  have hM := aestronglyMeasurable_analytic_disk G hG
  have hBounds := besov_first_order_bounds g p hpq.lt hB
  have hPhysical : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞ :=
    (lintegral_physicalDiskWeight_le (fun z => ‖G z‖^p)
      (fun z _ => Real.rpow_nonneg (norm_nonneg (G z)) p) (p-2)).trans_lt
        (ENNReal.mul_lt_top (by finiteness) hBounds.1)
  obtain ⟨K,hK,hKN,hEntry⟩ := exists_schatten_sequenceHankel_of_analytic_energy
    G hG p q hpq hPhysical
  have hCoeff (i j : ℕ) : K (lp.single 2 j (1 : ℂ)) i=
      fourierCoeff g ((i+j+1 : ℕ) : ℤ) := by
    simpa only [G,diskTaylorCoeff_analytic_deriv_div] using hEntry i j
  obtain ⟨H,hH,hS,hN⟩ := exists_schattenHankel_of_shifted_sequence g K hpq.lt.le hK hCoeff
  have hLP0 := lpNorm_pellerLift_le_frozen_energy G hM p hpq.pos hBounds.1
  have hLP : lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure≤
      (2^|p-2|)^(1/p)*besovNorm p g :=
    hLP0.trans (mul_le_mul_of_nonneg_left hBounds.2.2 (by positivity))
  have hKB : schattenNorm p K≤
      (pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))*besovNorm p g := by
    simpa only [mul_assoc] using hKN.trans
      (mul_le_mul_of_nonneg_left hLP
        (Real.rpow_nonneg (pellerStrongConstant_pos q hpq.symm.lt).le _))
  refine ⟨H,hH,hS,hN.trans ?_⟩
  calc
    _ ≤ 2*((pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))*besovNorm p g)+
        besovNorm p g := by linarith [hBounds.2.1]
    _ = _ := by ring

theorem schattenHankel_upper_of_besov_gt_one (g : BoundaryL2)
    (p q : ℝ) (hpq : p.HolderConjugate q)
    (hB : besovEnergy p (analyticValue g)<∞)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    Schatten p H ∧ schattenNorm p H≤
      (2*(pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))+1)*besovNorm p g := by
  obtain ⟨K,hK,hS,hN⟩ := exists_schattenHankel_of_besov_gt_one g p q hpq hB
  have he := representsHankel_unique _ H K hH hK
  exact he ▸ ⟨hS,hN⟩

theorem classicalHankel_schatten_gt_one (p : ℝ) (hp : 1<p)
    (g : BoundaryL2) (hg : g∈hardy) :
    HasSchattenHankel p (star (multiply coordinate g)) ↔ InBesov p g := by
  constructor
  · rintro ⟨H,hH,hS⟩
    exact ⟨hg,(hankel_besov_necessity_gt_one g H hH p hp hS).1⟩
  · intro hB
    obtain ⟨H,hH,hS,_⟩ := exists_schattenHankel_of_besov_gt_one
      g p (Real.conjExponent p) (Real.HolderConjugate.conjExponent hp) hB.2
    exact ⟨H,hH,hS⟩

theorem pellerGreaterOne (p : ℝ) (hp : 1<p) : PellerObligation p := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let Uh := pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p)
  let U := 2*Uh+1
  let L := (1+2^|p-2| *pellerStrongConstant p)^(1/p)
  let Lh := (2^|p-2| *pellerStrongConstant p)^(1/p)
  have hScale : 0<2^|p-2| *pellerStrongConstant p :=
    mul_pos (by positivity) (pellerStrongConstant_pos p hp)
  have hL : 0<L := Real.rpow_pos_of_pos (add_pos zero_lt_one hScale) _
  have hLh : 0<Lh := Real.rpow_pos_of_pos hScale _
  have hUh : 0<Uh := mul_pos
    (Real.rpow_pos_of_pos (pellerStrongConstant_pos q hpq.symm.lt) _) (by positivity)
  have hU : 0<U := by change 0<2*Uh+1; linarith
  constructor
  · intro g hg
    exact ⟨classicalHankel_schatten_gt_one p hp g hg,
      classicalHankel_schatten_gt_one_homogeneous p hp g hg⟩
  · refine ⟨L⁻¹,U,Lh⁻¹,Uh,inv_pos.mpr hL,hU,inv_pos.mpr hLh,hUh,?_⟩
    intro g hg H hH hS
    have hB := hankel_besov_necessity_gt_one g H hH p hp hS
    have hHN := hankel_homogeneousBesov_necessity g hg H hH p hp hS
    have hBU := (schattenHankel_upper_of_besov_gt_one g p q hpq hB.1 H hH).2
    have hHU := (schattenHankel_upper_of_homogeneousBesov_gt_one
      g hg p q hpq hHN.1 H hH).2
    refine ⟨?_,hBU,?_,hHU⟩
    · calc
        _ ≤ L⁻¹*(L*schattenNorm p H) :=
          mul_le_mul_of_nonneg_left hB.2 (inv_nonneg.mpr hL.le)
        _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hL.ne',one_mul]
    · calc
        _ ≤ Lh⁻¹*(Lh*schattenNorm p H) :=
          mul_le_mul_of_nonneg_left hHN.2 (inv_nonneg.mpr hLh.le)
        _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hLh.ne',one_mul]

theorem besovClassification_gt_one (p : ℝ) (hp : 1<p) : BesovConclusion p :=
  besovClassification p (lt_trans zero_lt_one hp) (pellerGreaterOne p hp)

theorem coanalyticBesov_gt_one (p : ℝ) (hp : 1<p) : CoanalyticBesovConclusion p :=
  coanalyticBesov p (besovClassification_gt_one p hp)

end TTO.Paper.Proved
