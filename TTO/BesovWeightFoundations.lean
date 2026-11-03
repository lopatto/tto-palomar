/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FiniteHankelRecoveryFoundations

/-! Exact comparisons of physical and frozen Besov weights, preserving infinite energies. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem rpow_le_two_abs_of_one_le_le_two (t a : ℝ) (h1 : 1≤t) (h2 : t≤2) :
    t^a≤2^|a| :=
  (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self a)).trans
    (Real.rpow_le_rpow (by linarith) h2 (abs_nonneg a))

theorem frozenDiskWeight_le_physical (r a : ℝ) (hr0 : 0≤r) (hr1 : r<1) :
    (1-r^2)^a≤2^|a| *(1-r)^a := by
  have h0 : 0≤1-r := by linarith
  have ht : 0≤1+r := by linarith
  have he : 1-r^2=(1-r)*(1+r) := by ring
  rw [he,Real.mul_rpow h0 ht]
  nlinarith [Real.rpow_nonneg h0 a,
    rpow_le_two_abs_of_one_le_le_two (1+r) a (by linarith) (by linarith)]

theorem physicalDiskWeight_le_frozen (r a : ℝ) (hr0 : 0≤r) (hr1 : r<1) :
    (1-r)^a≤2^|a| *(1-r^2)^a := by
  have h0 : 0≤1-r := by linarith
  have ht : 0<1+r := by linarith
  have he : 1-r^2=(1-r)*(1+r) := by ring
  have hi : (1+r)^a*(1+r)^(-a)=1 := by
    rw [← Real.rpow_add ht];simp
  calc
    (1-r)^a=((1-r)^a*(1+r)^a)*(1+r)^(-a) := by rw [mul_assoc,hi,mul_one]
    _ = (1-r^2)^a*(1+r)^(-a) := by rw [he,Real.mul_rpow h0 ht.le]
    _ ≤ (1-r^2)^a*2^|a| := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by nlinarith : 0≤1-r^2) a)
      simpa only [abs_neg] using
        rpow_le_two_abs_of_one_le_le_two (1+r) (-a) (by linarith) (by linarith)
    _ = _ := mul_comm _ _

theorem besovOrder_of_one_lt (p : ℝ) (hp : 1<p) : besovOrder p=1 := by
  have h1 : 1/p<1 := (div_lt_one (by linarith)).mpr hp
  simp only [besovOrder,Nat.floor_eq_zero.mpr h1,zero_add]

theorem homogeneousBesovEnergy_of_one_lt (p : ℝ) (hp : 1<p) (F : ℂ→ℂ) :
    homogeneousBesovEnergy p F =
      ∫⁻ z,ENNReal.ofReal (‖deriv F z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea := by
  simp only [homogeneousBesovEnergy,besovOrder_of_one_lt p hp,Finset.sum_range_one,
    ite_true,zero_add,iteratedDeriv_one,Nat.cast_one,one_mul]

theorem besovEnergy_of_one_lt (p : ℝ) (hp : 1<p) (F : ℂ→ℂ) :
    besovEnergy p F=ENNReal.ofReal (‖F 0‖^p)+
      ∫⁻ z,ENNReal.ofReal (‖deriv F z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea := by
  simp only [besovEnergy,besovOrder_of_one_lt p hp,Finset.sum_range_one,
    iteratedDeriv_zero,iteratedDeriv_one,Nat.cast_one,one_mul]

theorem lintegral_frozenDiskWeight_le (U : ℂ→ℝ)
    (hU : ∀ z∈disk,0≤U z) (a : ℝ) :
    (∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖^2)^a) ∂diskArea)≤
      ENNReal.ofReal (2^|a|)*(∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖)^a) ∂diskArea) := by
  calc
    _ ≤ ∫⁻ z,ENNReal.ofReal ((2^|a|)*(U z*(1-‖z‖)^a)) ∂diskArea := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_diskArea] with z hz
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left
        (frozenDiskWeight_le_physical ‖z‖ a (norm_nonneg z) hz) (hU z hz)]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0≤(2 : ℝ)^|a|)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem lintegral_physicalDiskWeight_le (U : ℂ→ℝ)
    (hU : ∀ z∈disk,0≤U z) (a : ℝ) :
    (∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖)^a) ∂diskArea)≤
      ENNReal.ofReal (2^|a|)*(∫⁻ z,ENNReal.ofReal (U z*(1-‖z‖^2)^a) ∂diskArea) := by
  calc
    _ ≤ ∫⁻ z,ENNReal.ofReal ((2^|a|)*(U z*(1-‖z‖^2)^a)) ∂diskArea := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_diskArea] with z hz
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left
        (physicalDiskWeight_le_frozen ‖z‖ a (norm_nonneg z) hz) (hU z hz)]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0≤(2 : ℝ)^|a|)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem iteratedDeriv_coordinate_analyticValue (f : Hardy) (n : ℕ)
    (z : ℂ) (hz : z∈disk) :
    iteratedDeriv n (analyticValue (multiply coordinate f.val)) z=
      iteratedDeriv n (fun w => w*analyticValue f.val w) z := by
  induction n generalizing z with
  | zero => exact analyticValue_coordinate_multiply f ⟨z,hz⟩
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact ih w hw

theorem lpNorm_pellerLift_eq_energy (G : ℂ→ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) (hp : 0<p) :
    lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure=
      (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea).toReal^(1/p) := by
  have hL := aestronglyMeasurable_pellerLift G hG
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hL]
  simp only [ENNReal.toReal_ofReal hp.le,inv_eq_one_div]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))
    (hL.norm.aemeasurable.pow_const p).aestronglyMeasurable,
    lintegral_pellerLift_rpow G hG p]

theorem lpNorm_pellerLift_le_frozen_energy (G : ℂ→ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) (hp : 0<p)
    (hE : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)<∞) :
    lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure≤
      (2^|p-2|)^(1/p)*
        (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea).toReal^(1/p) := by
  rw [lpNorm_pellerLift_eq_energy G hG p hp]
  have h := lintegral_physicalDiskWeight_le (fun z => ‖G z‖^p)
    (fun z _ => Real.rpow_nonneg (norm_nonneg (G z)) p) (p-2)
  have ht : ENNReal.ofReal (2^|p-2|)*
      (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)≠∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne
  have hr := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hr
  have hrp := Real.rpow_le_rpow ENNReal.toReal_nonneg hr
    (le_of_lt (one_div_pos.mpr hp))
  rwa [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg] at hrp

theorem homogeneousBesovEnergy_coordinate_of_one_lt
    (f : Hardy) (p : ℝ) (hp : 1<p) :
    homogeneousBesovEnergy p (fun z => z*analyticValue f.val z)=
      ∫⁻ z,ENNReal.ofReal
        (‖deriv (analyticValue (multiply coordinate f.val)) z‖^p*
          (1-‖z‖^2)^(p-2)) ∂diskArea := by
  rw [homogeneousBesovEnergy_of_one_lt p hp]
  apply lintegral_diskArea_congr
  intro z hz
  have h := iteratedDeriv_coordinate_analyticValue f 1 z hz
  simp only [iteratedDeriv_one] at h
  rw [h]

theorem exists_schattenHankel_of_homogeneousBesov_gt_one
    (g : BoundaryL2) (hg : g∈hardy) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hE : homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤
        (pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))*
          homogeneousBesovNorm p (fun z => z*analyticValue g z) := by
  let G := deriv (analyticValue (multiply coordinate g))
  have hG : AnalyticOnNhd ℂ G disk :=
    fun z hz => (analyticOnNhd_analyticValue (multiply coordinate g) z hz).deriv
  have hM := aestronglyMeasurable_analytic_disk G hG
  have he : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)=
      homogeneousBesovEnergy p (fun z => z*analyticValue g z) :=
    (homogeneousBesovEnergy_coordinate_of_one_lt ⟨g,hg⟩ p hpq.lt).symm
  have hF : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^(p-2)) ∂diskArea)<∞ := by
    rwa [he]
  have hP : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞ :=
    (lintegral_physicalDiskWeight_le (fun z => ‖G z‖^p)
      (fun z _ => Real.rpow_nonneg (norm_nonneg (G z)) p) (p-2)).trans_lt
        (ENNReal.mul_lt_top (by finiteness) hF)
  obtain ⟨H,hH,hS,hN⟩ := exists_schattenHankel_of_coordinate_derivative_energy g p q hpq hP
  refine ⟨H,hH,hS,hN.trans ?_⟩
  have hLP := lpNorm_pellerLift_le_frozen_energy G hM p hpq.pos hF
  rw [he] at hLP
  change pellerStrongConstant q^(1/q)*lpNorm (pellerLift G) (ENNReal.ofReal p)
    pellerPolarMeasure≤_
  unfold homogeneousBesovNorm
  calc
    _ ≤ pellerStrongConstant q^(1/q)*
        ((2^|p-2|)^(1/p)*
          (homogeneousBesovEnergy p (fun z => z*analyticValue g z)).toReal^(1/p)) :=
      mul_le_mul_of_nonneg_left hLP
        (Real.rpow_nonneg (pellerStrongConstant_pos q hpq.symm.lt).le _)
    _ = _ := (mul_assoc _ _ _).symm

theorem schattenHankel_upper_of_homogeneousBesov_gt_one
    (g : BoundaryL2) (hg : g∈hardy) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hE : homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    Schatten p H ∧ schattenNorm p H≤
      (pellerStrongConstant q^(1/q)*(2^|p-2|)^(1/p))*
        homogeneousBesovNorm p (fun z => z*analyticValue g z) := by
  obtain ⟨K,hK,hS,hN⟩ := exists_schattenHankel_of_homogeneousBesov_gt_one g hg p q hpq hE
  have he := representsHankel_unique _ H K hH hK
  exact he ▸ ⟨hS,hN⟩

theorem besovEnergy_coordinate_shift_of_one_lt (f : Hardy) (p : ℝ) (hp : 1<p) :
    besovEnergy p (analyticValue (multiply coordinate f.val))=
      homogeneousBesovEnergy p (fun z => z*analyticValue f.val z) := by
  have h0 : analyticValue (multiply coordinate f.val) 0=0 := by
    rw [analyticValue_at_zero,fourierCoeff_coordinate_product]
    exact (mem_hardy_iff f.val).mp f.property (-1) (by norm_num)
  rw [besovEnergy_of_one_lt p hp,h0,norm_zero,
    Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hp)),ENNReal.ofReal_zero,zero_add]
  exact (homogeneousBesovEnergy_coordinate_of_one_lt f p hp).symm

end TTO.Paper.Proved
