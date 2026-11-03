/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BesovTwoFoundations
public import TTO.AnalyticRadialParsevalFoundations

/-! Actual normalized disk-area Parseval and the p=2 analytic Dirichlet energy. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Bergman Parseval for an arbitrary analytic function on the open disk, including infinite energy. -/
theorem analytic_disk_area_parseval (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk) :
    (∫⁻ z, ENNReal.ofReal (‖F z‖^2) ∂diskArea) =
      ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2/((n : ℝ)+1)) := by
  rw [lintegral_diskArea_polar _ (measurable_disk_indicator_norm_sq F hF.continuousOn)]
  calc
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r)*
        ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [analytic_radial_circle_parseval F hF r hr.1.le hr.2]
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ∑' n : ℕ,
        ENNReal.ofReal (2*r)*ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n)) := by
      simp only [ENNReal.tsum_mul_left]
    _ = ∑' n : ℕ, ∫⁻ r in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (2*r)*ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n)) := by
      apply lintegral_tsum
      intro n
      exact (by fun_prop : Measurable (fun r : ℝ =>
        ENNReal.ofReal (2*r)*ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n)))).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      calc
        _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2)*
            (ENNReal.ofReal (2*r)*ENNReal.ofReal (r^(2*n))) := by
          apply lintegral_congr_ae
          exact Eventually.of_forall fun r => by
            dsimp only
            rw [ENNReal.ofReal_mul (sq_nonneg _)]
            ring
        _ = ENNReal.ofReal (‖diskTaylorCoeff F n‖^2)*
            (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r)*ENNReal.ofReal (r^(2*n))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = _ := by
          rw [lintegral_radial_monomial,← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 1
          ring

/-- The actual complex derivative area energy of the analytic extension. -/
theorem analyticValue_deriv_disk_area (f : BoundaryL2) :
    (∫⁻ z, ENNReal.ofReal (‖deriv (analyticValue f) z‖^2) ∂diskArea) =
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2) := by
  have hD : AnalyticOnNhd ℂ (deriv (analyticValue f)) disk := by
    intro z hz
    exact (analyticOnNhd_analyticValue f z hz).deriv
  rw [analytic_disk_area_parseval _ hD]
  apply tsum_congr
  intro n
  rw [diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue,norm_mul,Complex.norm_natCast]
  congr 1
  push_cast
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem besovEnergy_two (F : ℂ → ℂ) :
    besovEnergy 2 F=ENNReal.ofReal (‖F 0‖^2)+∫⁻ z, ENNReal.ofReal (‖deriv F z‖^2) ∂diskArea := by
  simp only [besovEnergy,besovOrder_two,Finset.sum_range_one,iteratedDeriv_zero,iteratedDeriv_one,
    Real.rpow_two,Nat.cast_one,one_mul,sub_self,Real.rpow_zero,mul_one]

theorem homogeneousBesovEnergy_two (F : ℂ → ℂ) :
    homogeneousBesovEnergy 2 F=∫⁻ z, ENNReal.ofReal (‖deriv F z‖^2) ∂diskArea := by
  simp only [homogeneousBesovEnergy,besovOrder_two,Finset.sum_range_one,ite_true,zero_add,
    iteratedDeriv_one,Real.rpow_two,Nat.cast_one,one_mul,sub_self,Real.rpow_zero,mul_one]

theorem besovEnergy_two_fourier (f : BoundaryL2) :
    besovEnergy 2 (analyticValue f) = ENNReal.ofReal (‖fourierCoeff f 0‖^2)+
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2) := by
  rw [besovEnergy_two,analyticValue_at_zero,analyticValue_deriv_disk_area]

theorem classicalCoefficientEnergy_split (f : BoundaryL2) :
    classicalCoefficientEnergy f = ENNReal.ofReal (‖fourierCoeff f 0‖^2)+
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+2)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2) := by
  unfold classicalCoefficientEnergy
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero,zero_add,one_mul,Nat.cast_add,Nat.cast_one]
  congr 2
  funext n
  congr 1
  ring

theorem besovEnergy_two_le_classical (f : BoundaryL2) :
    besovEnergy 2 (analyticValue f) ≤ classicalCoefficientEnergy f := by
  rw [besovEnergy_two_fourier,classicalCoefficientEnergy_split]
  refine add_le_add le_rfl ?_
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg ‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖]

theorem classical_le_two_besovEnergy (f : BoundaryL2) :
    classicalCoefficientEnergy f ≤ 2*besovEnergy 2 (analyticValue f) := by
  rw [besovEnergy_two_fourier,classicalCoefficientEnergy_split]
  calc
    _ ≤ 2*ENNReal.ofReal (‖fourierCoeff f 0‖^2)+
        ∑' n : ℕ, 2*ENNReal.ofReal (((n : ℝ)+1)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2) := by
      apply add_le_add
      · calc
          _ = 1*ENNReal.ofReal (‖fourierCoeff f 0‖^2) := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ≥0∞) ≤ 2) zero_le
      · apply ENNReal.tsum_le_tsum
        intro n
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hc : 0 ≤ ‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2 := sq_nonneg _
        have ht := ENNReal.ofReal_le_ofReal (show ((n : ℝ)+2)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2 ≤
          2*(((n : ℝ)+1)*‖fourierCoeff f ((n+1 : ℕ) : ℤ)‖^2) by nlinarith)
        simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat] using ht
    _ = _ := by rw [ENNReal.tsum_mul_left]; ring

theorem lintegral_diskArea_congr (f g : ℂ → ℝ≥0∞) (he : ∀ z ∈ disk, f z=g z) :
    (∫⁻ z, f z ∂diskArea) = ∫⁻ z, g z ∂diskArea := by
  rw [diskArea,lintegral_smul_measure,lintegral_smul_measure]
  congr 1
  exact setLIntegral_congr_fun (isOpen_lt continuous_norm continuous_const).measurableSet he

/-- The shifted homogeneous p=2 energy is exactly the original Hankel coefficient energy. -/
theorem homogeneousBesovEnergy_two_shift (f : BoundaryL2) (hf : f ∈ hardy) :
    homogeneousBesovEnergy 2 (fun z => z*analyticValue f z)=classicalCoefficientEnergy f := by
  have hd : IsOpen disk := isOpen_lt continuous_norm continuous_const
  have hDeriv (z : ℂ) (hz : z ∈ disk) :
      deriv (fun w => w*analyticValue f w) z=deriv (analyticValue (multiply coordinate f)) z := by
    have he : (fun w => w*analyticValue f w) =ᶠ[𝓝 z] analyticValue (multiply coordinate f) := by
      filter_upwards [hd.mem_nhds hz] with w hw
      exact (analyticValue_coordinate_multiply ⟨f,hf⟩ ⟨w,hw⟩).symm
    exact he.deriv_eq
  rw [homogeneousBesovEnergy_two]
  calc
    _ = ∫⁻ z, ENNReal.ofReal (‖deriv (analyticValue (multiply coordinate f)) z‖^2) ∂diskArea :=
      lintegral_diskArea_congr _ _ (fun z hz => by rw [hDeriv z hz])
    _ = _ := by
      rw [analyticValue_deriv_disk_area,classicalCoefficientEnergy]
      apply tsum_congr
      intro n
      have hc : fourierCoeff (multiply coordinate f) ((n+1 : ℕ) : ℤ)=fourierCoeff f (n : ℤ) := by
        change fourierCoeff (multiply (mode 1) f) ((n+1 : ℕ) : ℤ)=_
        rw [fourierCoeff_mode_multiply]
        congr 1
        omega
      rw [hc]

theorem besovNorm_two_eq_sqrt (f : BoundaryL2) :
    besovNorm 2 f=Real.sqrt (besovEnergy 2 (analyticValue f)).toReal := by
  unfold besovNorm
  rw [Real.sqrt_eq_rpow]

theorem homogeneousBesovNorm_two_eq_sqrt (F : ℂ → ℂ) :
    homogeneousBesovNorm 2 F=Real.sqrt (homogeneousBesovEnergy 2 F).toReal := by
  unfold homogeneousBesovNorm
  rw [Real.sqrt_eq_rpow]

/-- The full quantitative classical Hankel/Besov statement at p=2 only. -/
theorem pellerTwo : PellerObligation 2 := by
  constructor
  · intro f hf
    have hBiff : besovEnergy 2 (analyticValue f)<∞ ↔ classicalCoefficientEnergy f<∞ := by
      constructor
      · intro hB
        exact (classical_le_two_besovEnergy f).trans_lt (ENNReal.mul_lt_top (by norm_num) hB)
      · intro hE
        exact (besovEnergy_two_le_classical f).trans_lt hE
    constructor
    · rw [classicalHankel_schatten_two,InBesov]
      exact ⟨fun hE => ⟨hf,hBiff.mpr hE⟩,fun h => hBiff.mp h.2⟩
    · rw [homogeneousBesovEnergy_two_shift f hf]
      exact classicalHankel_schatten_two f
  · refine ⟨1,2,1,1,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    intro f hf H hRep hS
    have hE : classicalCoefficientEnergy f<∞ := (classicalHankel_schatten_two f).mp ⟨H,hRep,hS⟩
    have hB : besovEnergy 2 (analyticValue f)<∞ := (besovEnergy_two_le_classical f).trans_lt hE
    have hN : schattenNorm 2 H^2=(classicalCoefficientEnergy f).toReal := by
      have h := congrArg ENNReal.toReal (classicalHankel_norm_two f H hRep hS)
      simpa only [ENNReal.toReal_ofReal (sq_nonneg (schattenNorm 2 H))] using h
    have hBN : besovNorm 2 f^2=(besovEnergy 2 (analyticValue f)).toReal := by
      rw [besovNorm_two_eq_sqrt,Real.sq_sqrt ENNReal.toReal_nonneg]
    have hN0 : 0 ≤ schattenNorm 2 H := Reduction.schattenNorm_nonneg 2 H
    have hB0 : 0 ≤ besovNorm 2 f := by rw [besovNorm_two_eq_sqrt]; exact Real.sqrt_nonneg _
    have hLowerSq : besovNorm 2 f^2 ≤ schattenNorm 2 H^2 := by
      rw [hBN,hN]
      exact ENNReal.toReal_mono hE.ne (besovEnergy_two_le_classical f)
    have hUpperSq : schattenNorm 2 H^2 ≤ 2*besovNorm 2 f^2 := by
      rw [hN,hBN]
      have h := ENNReal.toReal_mono (ENNReal.mul_lt_top (by norm_num : (2 : ℝ≥0∞)<∞) hB).ne
        (classical_le_two_besovEnergy f)
      simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using h
    have hLower : besovNorm 2 f ≤ schattenNorm 2 H := le_of_sq_le_sq hLowerSq hN0
    have hUpper : schattenNorm 2 H ≤ 2*besovNorm 2 f := by
      apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) hB0)
      nlinarith [sq_nonneg (besovNorm 2 f)]
    have hHom : homogeneousBesovNorm 2 (fun z => z*analyticValue f z)=schattenNorm 2 H := by
      rw [homogeneousBesovNorm_two_eq_sqrt,homogeneousBesovEnergy_two_shift f hf,← hN,
        Real.sqrt_sq hN0]
    exact ⟨by simpa only [one_mul] using hLower,hUpper,by rw [hHom,one_mul],by rw [hHom,one_mul]⟩

/-- The complete Theorem 1 contract specialized to p=2; the all-p theorem is supplied by PellerFoundations. -/
theorem besovClassificationTwo : BesovConclusion 2 := besovClassification 2 (by norm_num) pellerTwo

/-- The corresponding coanalytic specialization at p=2. -/
theorem coanalyticBesovTwo : CoanalyticBesovConclusion 2 := coanalyticBesov 2 besovClassificationTwo

end TTO.Paper.Proved
