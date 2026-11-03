/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBandLocalMeansFoundations
public import TTO.BesovWeightFoundations
public import TTO.PolynomialSchattenSynthesisFoundations

/-! Actual finite-band budgets from literal rotating annuli, retaining infinite energies. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- At most one hundred scheduled rotating annuli contain any fixed point. -/
theorem card_active_rotatingDiskAnnuli_le (J : ℕ) (δ : ℝ) :
    ((Finset.range J).filter (fun j =>
      2/(thinWideScale j : ℝ) ≤ δ ∧ δ ≤ 6/(thinWideScale j : ℝ))).card ≤ 100 := by
  classical
  let s := (Finset.range J).filter (fun j =>
    2/(thinWideScale j : ℝ) ≤ δ ∧ δ ≤ 6/(thinWideScale j : ℝ))
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    have hi : i ∈ s := Finset.min'_mem s hs
    have hiBounds := (Finset.mem_filter.mp hi).2
    have hiN : (0 : ℝ) < (thinWideScale i : ℝ) := by
      exact_mod_cast (by have := thinWideScale_ten_le i; omega : 0 < thinWideScale i)
    have hδ : 0 < δ := lt_of_lt_of_le (div_pos (by norm_num) hiN) hiBounds.1
    have hSub : s ⊆ Finset.Ico i (i+100) := by
      intro j hj
      have hij : i ≤ j := Finset.min'_le s j hj
      have hjBounds := (Finset.mem_filter.mp hj).2
      have hjN : (0 : ℝ) < (thinWideScale j : ℝ) := by
        exact_mod_cast (by have := thinWideScale_ten_le j; omega : 0 < thinWideScale j)
      have hjLt : j < i+100 := by
        by_contra h
        have hGap := thinWideScale_sparse_gap i (j-i) (by omega)
        rw [Nat.add_sub_of_le hij] at hGap
        have hGapR : 10*(thinWideScale i : ℝ) ≤ (thinWideScale j : ℝ) := by exact_mod_cast hGap
        have hLo : 2 ≤ δ*(thinWideScale i : ℝ) := (div_le_iff₀ hiN).mp hiBounds.1
        have hHi : δ*(thinWideScale j : ℝ) ≤ 6 := (le_div_iff₀ hjN).mp hjBounds.2
        have hMul := mul_le_mul_of_nonneg_left hGapR hδ.le
        nlinarith
      exact Finset.mem_Ico.mpr ⟨hij,hjLt⟩
    have hCard := Finset.card_le_card hSub
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hCard
  · have hEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ 100
    simp only [hEmpty, Finset.card_empty]
    omega

theorem rotatingDiskAnnulus_subset_disk (N : ℕ) (hN : 0 < N) :
    rotatingDiskAnnulus N ⊆ disk := by
  intro z hz
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : 0 < 1-‖z‖ := lt_of_lt_of_le (div_pos (by norm_num) hNR) hz.1
  exact (show ‖z‖ < 1 by linarith)

/-- The literal inverse scale is dominated by the physical weight on each active annulus. -/
theorem rotatingDiskAnnulus_scale_weight_le (N : ℕ) (hN : 0 < N)
    (α : ℝ) (hα : α ≤ 0) (z : ℂ) (hz : z ∈ rotatingDiskAnnulus N) :
    (N : ℝ)^(-α) ≤ (6 : ℝ)^(-α)*(1-‖z‖)^α := by
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hzD := rotatingDiskAnnulus_subset_disk N hN hz
  have hδ : 0 < 1-‖z‖ := by change ‖z‖ < 1 at hzD; linarith
  have hScale : (N : ℝ) ≤ 6/(1-‖z‖) := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [(le_div_iff₀ hNR).mp hz.2]
  calc
    _ ≤ (6/(1-‖z‖))^(-α) :=
      Real.rpow_le_rpow hNR.le hScale (by linarith)
    _ = _ := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 6) hδ.le,
        div_eq_mul_inv, ← Real.rpow_neg hδ.le]
      congr 1
      simp only [neg_neg]

/-- The pointwise weighted charge of all scheduled annuli has multiplicity at most 100. -/
theorem sum_rotatingDiskAnnulus_scale_weight_le (J : ℕ) (α : ℝ) (hα : α ≤ 0) (z : ℂ) :
    (∑ j ∈ Finset.range J,(rotatingDiskAnnulus (thinWideScale j)).indicator
      (fun _ => ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))) z) ≤
      100*ENNReal.ofReal ((6 : ℝ)^(-α))*diskBoundaryWeight α z := by
  classical
  let s := (Finset.range J).filter (fun j => z ∈ rotatingDiskAnnulus (thinWideScale j))
  have hCard : s.card ≤ 100 := by
    simpa [s,rotatingDiskAnnulus] using card_active_rotatingDiskAnnuli_le J (1-‖z‖)
  have hEq :
      (∑ j ∈ Finset.range J,(rotatingDiskAnnulus (thinWideScale j)).indicator
        (fun _ => ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))) z) =
      ∑ j ∈ s, ENNReal.ofReal ((thinWideScale j : ℝ)^(-α)) := by
    simp only [s, Finset.sum_filter, Set.indicator_apply]
  rw [hEq]
  by_cases hz : z ∈ disk
  · have hEach (j : ℕ) (hj : j ∈ s) :
        ENNReal.ofReal ((thinWideScale j : ℝ)^(-α)) ≤
          ENNReal.ofReal ((6 : ℝ)^(-α))*diskBoundaryWeight α z := by
      have hjA := (Finset.mem_filter.mp hj).2
      have hjN : 0 < thinWideScale j := by have := thinWideScale_ten_le j; omega
      simpa only [diskBoundaryWeight, ite_eq_left hz, diskBoundaryDistance,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) (-α))] using
        ENNReal.ofReal_le_ofReal (rotatingDiskAnnulus_scale_weight_le _ hjN α hα z hjA)
    calc
      _ ≤ ∑ _j ∈ s, ENNReal.ofReal ((6 : ℝ)^(-α))*diskBoundaryWeight α z :=
        Finset.sum_le_sum hEach
      _ = (s.card : ℝ≥0∞)*(ENNReal.ofReal ((6 : ℝ)^(-α))*diskBoundaryWeight α z) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (100 : ℝ≥0∞)*(ENNReal.ofReal ((6 : ℝ)^(-α))*diskBoundaryWeight α z) :=
        mul_le_mul_left (show (s.card : ℝ≥0∞) ≤ 100 by exact_mod_cast hCard) _
      _ = _ := by ring
  · have hs : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hjN : 0 < thinWideScale j := by have := thinWideScale_ten_le j; omega
      exact hz (rotatingDiskAnnulus_subset_disk _ hjN (Finset.mem_filter.mp hj).2)
    simp only [hs, Finset.sum_empty, zero_le]

/-- Nonnegative Tonelli with a genuine finite-multiplicity charge; U may take the value infinity. -/
theorem sum_lintegral_rotatingDiskAnnulus_weight_le (J : ℕ) (α : ℝ) (hα : α ≤ 0)
    (U : ℂ → ℝ≥0∞) (hU : Measurable U) :
    (∑ j ∈ Finset.range J, ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
      (∫⁻ z in rotatingDiskAnnulus (thinWideScale j),U z ∂volume)) ≤
      100*ENNReal.ofReal ((6 : ℝ)^(-α))*(∫⁻ z,U z*diskBoundaryWeight α z ∂volume) := by
  classical
  let W : ℕ → ℂ → ℝ≥0∞ := fun j z =>
    (rotatingDiskAnnulus (thinWideScale j)).indicator
      (fun _ => ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))) z*U z
  have hW (j : ℕ) : Measurable (W j) :=
    (measurable_const.indicator (measurableSet_rotatingDiskAnnulus _)).mul hU
  have hWi (j : ℕ) :
      ∫⁻ z,W j z ∂volume = ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
        (∫⁻ z in rotatingDiskAnnulus (thinWideScale j),U z ∂volume) := by
    dsimp only [W]
    rw [← lintegral_indicator (measurableSet_rotatingDiskAnnulus _)]
    have hEq : (fun z => (rotatingDiskAnnulus (thinWideScale j)).indicator
        (fun _ => ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))) z*U z) =
        (fun z => ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
          (rotatingDiskAnnulus (thinWideScale j)).indicator U z) := by
      funext z
      by_cases hz : z ∈ rotatingDiskAnnulus (thinWideScale j) <;> simp [hz]
    rw [hEq]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ = ∫⁻ z,∑ j ∈ Finset.range J,W j z ∂volume := by
      rw [lintegral_finsetSum _ (fun j _ => hW j)]
      exact Finset.sum_congr rfl (fun j _ => (hWi j).symm)
    _ ≤ ∫⁻ z,(100*ENNReal.ofReal ((6 : ℝ)^(-α)))*(U z*diskBoundaryWeight α z) ∂volume := by
      apply lintegral_mono
      intro z
      have h := mul_le_mul_left (sum_rotatingDiskAnnulus_scale_weight_le J α hα z) (U z)
      simpa only [Finset.sum_mul, Finset.mul_sum, W, mul_assoc, mul_left_comm, mul_comm] using h
    _ = _ := lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)

theorem analytic_band_inverse_scale_identity (N n : ℕ) (hN : 0<N) (p : ℝ) :
    (N : ℝ)*(N : ℝ)/((N : ℝ)^n)^p=(N : ℝ)^(-((n : ℝ)*p-2)) := by
  have hNr : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  rw [← Real.rpow_natCast_mul hNr.le,← pow_two,← Real.rpow_two,
    ← Real.rpow_sub hNr]
  congr 1
  ring

theorem lintegral_volume_disk_eq_normalized (U : ℂ → ℝ≥0∞) :
    (∫⁻ z in disk,U z ∂volume)=ENNReal.ofReal Real.pi*(∫⁻ z,U z ∂diskArea) := by
  rw [diskArea,lintegral_smul_measure,smul_eq_mul,← mul_assoc,
    ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos))
      ENNReal.ofReal_ne_top,one_mul]

theorem analyticWideBandPolynomial_analyticValue_eq (m N N' : ℕ) (g : BoundaryL2) :
    analyticWideBandPolynomial m N N' (analyticValue g)=
      wideHankelPolynomial m N' g-wideHankelPolynomial m N g := by
  ext k
  rw [analyticWideBandPolynomial_analyticValue_coeff,Polynomial.coeff_sub,
    wideHankelPolynomial_coeff,wideHankelPolynomial_coeff]
  ring

def analyticBandBesovConstant (m n : ℕ) (p : ℝ) : ℝ :=
  analyticBandLocalMeanConstant m p*100*6^(-((n : ℝ)*p-2))*Real.pi*
    2^|((n : ℝ)*p-2)|

theorem analyticBandBesovConstant_pos (m n : ℕ) (hm : 1≤m) (p : ℝ) :
    0<analyticBandBesovConstant m n p := by
  unfold analyticBandBesovConstant
  positivity [analyticBandLocalMeanConstant_pos m hm p]

theorem sum_lintegral_analyticWideBand_le_weighted_area
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk) (m n : ℕ)
    (hm : 1≤m) (hn : 1≤n) (hnm : n≤m) (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hOrder : 1<((m+1 : ℕ) : ℝ)*p) (hα : (n : ℝ)*p≤2) (J : ℕ) :
    (∑ j∈Finset.range J,ENNReal.ofReal (thinWideScale j : ℝ)*
      (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m
        (thinWideScale j) (thinWideScale (j+1)) F).eval (fourier (T:=1) 1 x)‖^p)
        ∂circleMeasure))≤
      ENNReal.ofReal (analyticBandBesovConstant m n p)*
        (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n F z‖^p*
          (1-‖z‖^2)^((n : ℝ)*p-2)) ∂diskArea) := by
  let α := (n : ℝ)*p-2
  let C := analyticBandLocalMeanConstant m p
  have hC : 0<C := analyticBandLocalMeanConstant_pos m hm p
  have hα0 : α≤0 := by dsimp only [α];linarith
  have hG : AnalyticOnNhd ℂ (iteratedDeriv n F) disk := by
    simpa only [iteratedDeriv_eq_iterate] using hF.iterated_deriv n
  have hEach (j : ℕ) :
      ENNReal.ofReal (thinWideScale j : ℝ)*
        (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m
          (thinWideScale j) (thinWideScale (j+1)) F).eval (fourier (T:=1) 1 x)‖^p)
          ∂circleMeasure)≤
      ENNReal.ofReal C*(ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
        (∫⁻ z in rotatingDiskAnnulus (thinWideScale j),
          analyticPowerZero (iteratedDeriv n F) p z ∂volume)) := by
    have hN : 0<thinWideScale j := by have := thinWideScale_ten_le j;omega
    have hNr : (0 : ℝ)<thinWideScale j := Nat.cast_pos.mpr hN
    have h := mul_le_mul_right
      (analyticWideBand_lintegral_le_annulus F hF m (thinWideScale j)
        (thinWideScale (j+1)) n hm (thinWideScale_ten_le j)
        (thinWideScale_monotone (Nat.le_succ j)) (thinWideScale_ratio j)
        hn hnm p hp hp1 hOrder) (ENNReal.ofReal (thinWideScale j : ℝ))
    have hFac : ENNReal.ofReal (thinWideScale j : ℝ)*
        ENNReal.ofReal (C*(thinWideScale j : ℝ)/((thinWideScale j : ℝ)^n)^p)=
        ENNReal.ofReal C*ENNReal.ofReal ((thinWideScale j : ℝ)^(-α)) := by
      rw [← ENNReal.ofReal_mul hNr.le,← ENNReal.ofReal_mul hC.le]
      congr 1
      calc
        _ = C*((thinWideScale j : ℝ)*(thinWideScale j : ℝ)/
          ((thinWideScale j : ℝ)^n)^p) := by ring
        _ = _ := by rw [analytic_band_inverse_scale_identity (thinWideScale j) n hN p]
    dsimp only [C] at hFac
    simpa only [← mul_assoc,hFac] using h
  have hCharge := sum_lintegral_rotatingDiskAnnulus_weight_le J α hα0
    (analyticPowerZero (iteratedDeriv n F) p)
    (measurable_analyticPowerZero (iteratedDeriv n F) hG p hp.le)
  have hPhysical := lintegral_physicalDiskWeight_le
    (fun z => ‖iteratedDeriv n F z‖^p)
    (fun z _ => Real.rpow_nonneg (norm_nonneg _) p) α
  have hConst : ENNReal.ofReal (analyticBandBesovConstant m n p)=
      ENNReal.ofReal C*100*ENNReal.ofReal ((6 : ℝ)^(-α))*
        ENNReal.ofReal Real.pi*ENNReal.ofReal ((2 : ℝ)^|α|) := by
    unfold analyticBandBesovConstant
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    norm_num only [ENNReal.ofReal_ofNat]
    rfl
  calc
    _ ≤ ∑ j∈Finset.range J,ENNReal.ofReal C*
        (ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
          (∫⁻ z in rotatingDiskAnnulus (thinWideScale j),
            analyticPowerZero (iteratedDeriv n F) p z ∂volume)) :=
      Finset.sum_le_sum (fun j _ => hEach j)
    _ = ENNReal.ofReal C*(∑ j∈Finset.range J,
        ENNReal.ofReal ((thinWideScale j : ℝ)^(-α))*
          (∫⁻ z in rotatingDiskAnnulus (thinWideScale j),
            analyticPowerZero (iteratedDeriv n F) p z ∂volume)) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal C*(100*ENNReal.ofReal ((6 : ℝ)^(-α))*
        (∫⁻ z,analyticPowerZero (iteratedDeriv n F) p z*diskBoundaryWeight α z ∂volume)) :=
      mul_le_mul_right hCharge _
    _ = ENNReal.ofReal C*(100*ENNReal.ofReal ((6 : ℝ)^(-α))*
        (ENNReal.ofReal Real.pi*(∫⁻ z,ENNReal.ofReal
          (‖iteratedDeriv n F z‖^p*(1-‖z‖)^α) ∂diskArea))) := by
      rw [lintegral_analyticPowerZero_mul_weight,lintegral_volume_disk_eq_normalized]
    _ ≤ ENNReal.ofReal C*(100*ENNReal.ofReal ((6 : ℝ)^(-α))*
        (ENNReal.ofReal Real.pi*(ENNReal.ofReal ((2 : ℝ)^|α|)*
          (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n F z‖^p*(1-‖z‖^2)^α) ∂diskArea)))) := by
      gcongr
    _ = _ := by rw [hConst];ring

theorem ofReal_wideHankelBandMass_eq_lintegral (m j : ℕ) (g : BoundaryL2)
    (p : ℝ) (hp : 0≤p) :
    ENNReal.ofReal (wideHankelBandMass m j g p)=
      ENNReal.ofReal (thinWideScale j : ℝ)*
        (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m
          (thinWideScale j) (thinWideScale (j+1)) (analyticValue g)).eval
          (fourier (T:=1) 1 x)‖^p) ∂circleMeasure) := by
  have hI : Integrable (fun x : Boundary =>
      ‖(wideHankelPolynomial m (thinWideScale (j+1)) g-
        wideHankelPolynomial m (thinWideScale j) g).eval (fourier (T:=1) 1 x)‖^p) circleMeasure := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply (Real.continuous_rpow_const hp).comp
    fun_prop
  rw [wideHankelBandMass,ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p),
    analyticWideBandPolynomial_analyticValue_eq]

theorem exists_wideHankelBandMass_le_besovEnergy
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,∀ J : ℕ,
      (∑ j∈Finset.range J,ENNReal.ofReal (wideHankelBandMass (besovOrder p) j g p))≤
        ENNReal.ofReal C*besovEnergy p (analyticValue g) := by
  have hm : 1≤besovOrder p := by unfold besovOrder;omega
  have hProd := besovOrder_product_bounds p hp
  have hOrder : 1<((besovOrder p+1 : ℕ) : ℝ)*p := by
    push_cast
    nlinarith [hProd.1]
  have hα : (besovOrder p : ℝ)*p≤2 := by linarith [hProd.2]
  refine ⟨analyticBandBesovConstant (besovOrder p) (besovOrder p) p,
    analyticBandBesovConstant_pos (besovOrder p) (besovOrder p) hm p,?_⟩
  intro g J
  have hArea : (∫⁻ z,ENNReal.ofReal
      (‖iteratedDeriv (besovOrder p) (analyticValue g) z‖^p*
        (1-‖z‖^2)^((besovOrder p : ℝ)*p-2)) ∂diskArea)≤besovEnergy p (analyticValue g) := by
    unfold besovEnergy
    exact le_add_of_nonneg_left bot_le
  calc
    _ = ∑ j∈Finset.range J,ENNReal.ofReal (thinWideScale j : ℝ)*
        (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial (besovOrder p)
          (thinWideScale j) (thinWideScale (j+1)) (analyticValue g)).eval
          (fourier (T:=1) 1 x)‖^p) ∂circleMeasure) :=
      Finset.sum_congr rfl (fun j _ => ofReal_wideHankelBandMass_eq_lintegral
        (besovOrder p) j g p hp.le)
    _ ≤ ENNReal.ofReal (analyticBandBesovConstant (besovOrder p) (besovOrder p) p)*
        (∫⁻ z,ENNReal.ofReal
          (‖iteratedDeriv (besovOrder p) (analyticValue g) z‖^p*
            (1-‖z‖^2)^((besovOrder p : ℝ)*p-2)) ∂diskArea) :=
      sum_lintegral_analyticWideBand_le_weighted_area (analyticValue g)
        (analyticOnNhd_analyticValue g) (besovOrder p) (besovOrder p) hm hm le_rfl
        p hp hp1 hOrder hα J
    _ ≤ _ := mul_le_mul_right hArea _

theorem exists_wideHankelBandBudget_of_besov
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,besovEnergy p (analyticValue g)≠∞ → ∀ J : ℕ,
      (∑ j∈Finset.range J,wideHankelBandMass (besovOrder p) j g p)≤
        C*(besovEnergy p (analyticValue g)).toReal := by
  obtain ⟨C,hC,hBound⟩ := exists_wideHankelBandMass_le_besovEnergy p hp hp1
  refine ⟨C,hC,?_⟩
  intro g hE J
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) (hBound g J)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      wideHankelBandMass_nonneg (besovOrder p) j g p),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ =>
      wideHankelBandMass_nonneg (besovOrder p) j g p)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le] at h
  exact h

end TTO.Paper.Proved
