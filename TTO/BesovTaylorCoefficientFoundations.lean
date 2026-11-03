/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialSchattenSynthesisFoundations
public import TTO.AnalyticAreaSubmeanFoundations

/-! Fixed Taylor coefficients are controlled by the original Besov energy. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem norm_diskTaylorCoeff_le_iteratedDeriv (F : ℂ → ℂ) (k : ℕ) :
    ‖diskTaylorCoeff F k‖≤‖iteratedDeriv k F 0‖ := by
  have hf0 : 0<(k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hf1 : 1≤(k.factorial : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k))
  rw [diskTaylorCoeff,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ hf0).mpr
  nlinarith [norm_nonneg (iteratedDeriv k F 0)]

theorem lintegral_inner_disk_le_frozen_weighted_area (G : ℂ → ℂ) (p α : ℝ) (hα : α≤0) :
    (∫⁻ z in ball (0 : ℂ) (1/2),ENNReal.ofReal (‖G z‖^p))≤
      ENNReal.ofReal Real.pi*
        ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^α) ∂diskArea := by
  have hSub : ball (0 : ℂ) (1/2)⊆disk := by
    intro z hz
    change ‖z‖<1
    have h : ‖z‖<(1/2 : ℝ) := by simpa only [mem_ball,dist_zero_right] using hz
    linarith
  calc
    _ ≤ ∫⁻ z in disk,ENNReal.ofReal (‖G z‖^p) := lintegral_mono_set hSub
    _ ≤ ∫⁻ z in disk,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^α) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (isOpen_lt continuous_norm continuous_const).measurableSet] with z hz
      change ‖z‖<1 at hz
      apply ENNReal.ofReal_le_ofReal
      have hW : 1≤(1-‖z‖^2)^α :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by nlinarith [norm_nonneg z])
          (by nlinarith [sq_nonneg ‖z‖]) hα
      exact le_mul_of_one_le_right (Real.rpow_nonneg (norm_nonneg _) p) hW
    _ = _ := by
      rw [diskArea,lintegral_smul_measure,smul_eq_mul,← mul_assoc,
        ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos))
          ENNReal.ofReal_ne_top,one_mul]

theorem analytic_derivative_at_zero_rpow_le_weighted_area
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (q : ℕ)
    (p : ℝ) (hp : 0<p) (α : ℝ) (hα : α≤0) :
    ENNReal.ofReal (‖iteratedDeriv q G 0‖^p)≤
      ENNReal.ofReal (16*((q.factorial : ℝ)/(1/4 : ℝ)^q)^p)*
        ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^α) ∂diskArea := by
  have hSub : closedBall (0 : ℂ) (1/2)⊆disk := by
    intro z hz
    change ‖z‖<1
    have h : ‖z‖≤(1/2 : ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hz
    linarith
  have hSmall := hG.mono hSub
  have hI := (integrableOn_analytic_norm_rpow_closedBall G 0 (1/2) p hSmall hp.le).mono_set
    ball_subset_closedBall
  have hLocal := analytic_iteratedDeriv_rpow_le_local_area G 0 (1/4) p q (by norm_num)
    (by simpa only [show (2 : ℝ)*(1/4)=1/2 by norm_num] using hSmall) hp
  rw [show (2 : ℝ)*(1/4)=1/2 by norm_num] at hLocal
  have hENN := ENNReal.ofReal_le_ofReal hLocal
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p),
    ENNReal.ofReal_mul (by positivity : 0≤(Real.pi*(1/4 : ℝ)^2)⁻¹),
    ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) p)] at hENN
  have hArea := lintegral_inner_disk_le_frozen_weighted_area G p α hα
  calc
    _ ≤ ENNReal.ofReal (((q.factorial : ℝ)/(1/4 : ℝ)^q)^p)*
        (ENNReal.ofReal (Real.pi*(1/4 : ℝ)^2)⁻¹*
          ∫⁻ z in ball (0 : ℂ) (1/2),ENNReal.ofReal (‖G z‖^p)) := hENN
    _ ≤ ENNReal.ofReal (((q.factorial : ℝ)/(1/4 : ℝ)^q)^p)*
        (ENNReal.ofReal (Real.pi*(1/4 : ℝ)^2)⁻¹*
          (ENNReal.ofReal Real.pi*
            ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖^2)^α) ∂diskArea)) := by gcongr
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by positivity) p) (by positivity))]
      congr 1
      field_simp
      ring_nf!

def besovTaylorCoefficientConstant (p : ℝ) (k : ℕ) : ℝ :=
  1+16*((((k-besovOrder p).factorial : ℝ)/(1/4 : ℝ)^(k-besovOrder p))^p)

theorem besovTaylorCoefficientConstant_one_le (p : ℝ) (k : ℕ) :
    1≤besovTaylorCoefficientConstant p k := by
  dsimp only [besovTaylorCoefficientConstant]
  exact le_add_of_nonneg_right (by positivity)

theorem besovTaylorCoefficientConstant_pos (p : ℝ) (k : ℕ) :
    0<besovTaylorCoefficientConstant p k :=
  zero_lt_one.trans_le (besovTaylorCoefficientConstant_one_le p k)

theorem ofReal_diskTaylorCoeff_rpow_le_besovEnergy (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (p : ℝ) (hp : 0<p) (hp1 : p≤1) (k : ℕ) :
    ENNReal.ofReal (‖diskTaylorCoeff F k‖^p)≤
      ENNReal.ofReal (besovTaylorCoefficientConstant p k)*besovEnergy p F := by
  have hCoef := ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (norm_nonneg _) (norm_diskTaylorCoeff_le_iteratedDeriv F k) hp.le)
  apply hCoef.trans
  let m := besovOrder p
  by_cases hkm : k<m
  · have hTerm : ENNReal.ofReal (‖iteratedDeriv k F 0‖^p)≤besovEnergy p F := by
      have hSum : ENNReal.ofReal (‖iteratedDeriv k F 0‖^p)≤
          ∑ j∈Finset.range (besovOrder p),ENNReal.ofReal (‖iteratedDeriv j F 0‖^p) :=
        Finset.single_le_sum (f:=fun j : ℕ => ENNReal.ofReal (‖iteratedDeriv j F 0‖^p))
          (fun j _ => bot_le) (show k∈Finset.range (besovOrder p) from Finset.mem_range.mpr hkm)
      exact hSum.trans (le_add_of_nonneg_right (show (0 : ℝ≥0∞)≤_ from bot_le))
    have hC : (1 : ℝ≥0∞)≤ENNReal.ofReal (besovTaylorCoefficientConstant p k) := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (besovTaylorCoefficientConstant_one_le p k)
    exact hTerm.trans (by simpa only [one_mul] using mul_le_mul_left hC (besovEnergy p F))
  · have hmk : m≤k := by omega
    let q := k-m
    have hG : AnalyticOnNhd ℂ (iteratedDeriv m F) disk := by
      simpa only [iteratedDeriv_eq_iterate] using hF.iterated_deriv m
    have hα : (m : ℝ)*p-2≤0 := by
      have h := (besovOrder_product_bounds p hp).2
      dsimp only [m]
      linarith
    have hLocal := analytic_derivative_at_zero_rpow_le_weighted_area
      (iteratedDeriv m F) hG q p hp ((m : ℝ)*p-2) hα
    have hDeriv : iteratedDeriv q (iteratedDeriv m F) 0=iteratedDeriv k F 0 := by
      dsimp only [q]
      simp only [iteratedDeriv_eq_iterate]
      rw [← Function.iterate_add_apply,Nat.sub_add_cancel hmk]
    rw [hDeriv] at hLocal
    have hC : ENNReal.ofReal (16*((q.factorial : ℝ)/(1/4 : ℝ)^q)^p)≤
        ENNReal.ofReal (besovTaylorCoefficientConstant p k) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp only [q,m,besovTaylorCoefficientConstant]
      linarith
    have hArea :
        (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv m F z‖^p*(1-‖z‖^2)^((m : ℝ)*p-2)) ∂diskArea)≤
          besovEnergy p F := by
      unfold besovEnergy
      exact le_add_of_nonneg_left bot_le
    exact hLocal.trans ((mul_le_mul_left hC _).trans (mul_le_mul_right hArea _))

theorem ofReal_fourierCoeff_rpow_le_besovEnergy (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (k : ℕ) :
    ENNReal.ofReal (‖fourierCoeff g (k : ℤ)‖^p)≤
      ENNReal.ofReal (besovTaylorCoefficientConstant p k)*besovEnergy p (analyticValue g) := by
  simpa only [diskTaylorCoeff_analyticValue] using
    ofReal_diskTaylorCoeff_rpow_le_besovEnergy (analyticValue g)
      (analyticOnNhd_analyticValue g) p hp hp1 k

theorem fourierCoeff_rpow_le_besovEnergy_toReal (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (k : ℕ)
    (hE : besovEnergy p (analyticValue g)≠∞) :
    ‖fourierCoeff g (k : ℤ)‖^p≤
      besovTaylorCoefficientConstant p k*(besovEnergy p (analyticValue g)).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)
    (ofReal_fourierCoeff_rpow_le_besovEnergy g p hp hp1 k)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) p),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (besovTaylorCoefficientConstant_pos p k).le] at h
  exact h

def wideHankelBaseBesovConstant (m : ℕ) (p : ℝ) : ℝ :=
  1+2^(1-p)*((wideDirichletProductShift m 10+1 : ℕ) : ℝ)*
    ∑ k∈Finset.range (wideDirichletProductShift m 10+1),
      ‖wideDirichletPositiveWeight m 10 k‖^p*besovTaylorCoefficientConstant p k

theorem wideHankelBaseBesovConstant_one_le (m : ℕ) (p : ℝ) :
    1≤wideHankelBaseBesovConstant m p := by
  dsimp only [wideHankelBaseBesovConstant]
  apply le_add_of_nonneg_right
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun k _ => mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) p) (besovTaylorCoefficientConstant_pos p k).le)

theorem wideHankelBaseBesovConstant_pos (m : ℕ) (p : ℝ) :
    0<wideHankelBaseBesovConstant m p :=
  zero_lt_one.trans_le (wideHankelBaseBesovConstant_one_le m p)

theorem wideHankelBaseBudget_le_besovEnergy_toReal (m : ℕ) (g : BoundaryL2)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hE : besovEnergy p (analyticValue g)≠∞) :
    wideHankelBaseBudget m g p≤wideHankelBaseBesovConstant m p*
      (besovEnergy p (analyticValue g)).toReal := by
  have hEach (k : ℕ) :
      ‖wideDirichletPositiveWeight m 10 k*fourierCoeff g (k : ℤ)‖^p≤
        (‖wideDirichletPositiveWeight m 10 k‖^p*besovTaylorCoefficientConstant p k)*
          (besovEnergy p (analyticValue g)).toReal := by
    rw [norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left
      (fourierCoeff_rpow_le_besovEnergy_toReal g p hp hp1 k hE)
      (Real.rpow_nonneg (norm_nonneg _) p)).trans_eq (mul_assoc _ _ _).symm
  calc
    _ ≤ 2^(1-p)*((wideDirichletProductShift m 10+1 : ℕ) : ℝ)*
        ∑ k∈Finset.range (wideDirichletProductShift m 10+1),
          (‖wideDirichletPositiveWeight m 10 k‖^p*besovTaylorCoefficientConstant p k)*
            (besovEnergy p (analyticValue g)).toReal := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hEach k)) (by positivity)
    _ = (wideHankelBaseBesovConstant m p-1)*(besovEnergy p (analyticValue g)).toReal := by
      rw [← Finset.sum_mul]
      unfold wideHankelBaseBesovConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg

end TTO.Paper.Proved
