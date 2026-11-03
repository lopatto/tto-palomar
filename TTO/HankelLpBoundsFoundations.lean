/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelAreaPairingFoundations
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Genuine finite Schatten recovery from the actual weighted analytic area energy. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The explicit constant in the proved dimension-independent strong-p bound. -/
def pellerStrongConstant (p : ℝ) : ℝ := 2621440*p*2^(p-1)/(p-1)

theorem pellerStrongConstant_pos (p : ℝ) (hp : 1<p) : 0<pellerStrongConstant p := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hd : 0<p-1 := sub_pos.mpr hp
  unfold pellerStrongConstant
  positivity

theorem integral_pellerLift_finiteAntiDiagonal_rpow_le (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℝ) (hp : 1<p) :
    (∫ x,‖pellerLift (finiteAntiDiagonalValue N A) x‖^p ∂pellerPolarMeasure)≤
      pellerStrongConstant p*schattenNorm p A^p := by
  have hM := memLp_pellerLift_finiteAntiDiagonal N A p hp
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))
    (hM.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_pellerLift_finiteAntiDiagonal_le N A p hp)
  have hn : 0≤pellerStrongConstant p*schattenNorm p A^p :=
    mul_nonneg (pellerStrongConstant_pos p hp).le
      (Real.rpow_nonneg (schattenNorm_nonneg p A) p)
  change _≤(ENNReal.ofReal (pellerStrongConstant p*schattenNorm p A^p)).toReal at h
  rwa [ENNReal.toReal_ofReal hn] at h

theorem lpNorm_pellerLift_finiteAntiDiagonal_le (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℝ) (hp : 1<p) :
    lpNorm (pellerLift (finiteAntiDiagonalValue N A)) (ENNReal.ofReal p) pellerPolarMeasure≤
      pellerStrongConstant p^(1/p)*schattenNorm p A := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hM := memLp_pellerLift_finiteAntiDiagonal N A p hp
  rw [lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
    ENNReal.ofReal_ne_top hM.aestronglyMeasurable,ENNReal.toReal_ofReal hp0.le]
  calc
    _ ≤ (pellerStrongConstant p*schattenNorm p A^p)^p⁻¹ :=
      Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) p))
        (integral_pellerLift_finiteAntiDiagonal_rpow_le N A p hp) (inv_nonneg.mpr hp0.le)
    _ = _ := by
      rw [Real.mul_rpow (pellerStrongConstant_pos p hp).le
        (Real.rpow_nonneg (schattenNorm_nonneg p A) p),
        Real.rpow_rpow_inv (schattenNorm_nonneg p A) hp0.ne',one_div]

theorem norm_area_pairing_le_peller_lpNorm {p q : ℝ} (hpq : p.HolderConjugate q)
    (G W : ℂ → ℂ) (hG : AEStronglyMeasurable G diskArea)
    (hW : AEStronglyMeasurable W diskArea)
    (hLG : MemLp (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure)
    (hLW : MemLp (pellerLift W) (ENNReal.ofReal q) pellerPolarMeasure) :
    ‖∫ z,G z*conj (W z) ∂diskArea‖≤
      lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure*
        lpNorm (pellerLift W) (ENNReal.ofReal q) pellerPolarMeasure := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.pos))
      ENNReal.ofReal_ne_top hLG.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hpq.symm.pos))
      ENNReal.ofReal_ne_top hLW.aestronglyMeasurable,
    ENNReal.toReal_ofReal hpq.nonneg,ENNReal.toReal_ofReal hpq.symm.nonneg]
  simpa only [one_div] using norm_area_pairing_le_pellerLp hpq G W hG hW hLG hLW

/-- Finite Schatten norm recovery by actual coefficient test operators, without a duality axiom. -/
theorem schattenNorm_le_of_finiteHSPair_bound {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
    (A : H →L[ℂ] H) (p q C : ℝ) (hpq : p.HolderConjugate q) (hC : 0≤C)
    (h : ∀ B : H →L[ℂ] H,‖finiteHSPair b B A‖≤C*schattenNorm q B) :
    schattenNorm p A≤C := by
  apply schattenNorm_le_of_besselPair_bounds A p q C hpq hC
  intro N u v huB hvB _huN _hvN c
  let B := besselCoefficientOperator u v (fun i => conj (c i))
  have he : finiteHSPair b B A=∑ i,c i*inner ℂ (u i) (A (v i)) := by
    simpa only [B,Complex.conj_conj] using
      finiteHSPair_besselCoefficient b u v (fun i => conj (c i)) A
  have hn : schattenNorm q B≤FiniteThorin.vectorNorm q c := by
    simpa only [B,FiniteThorin.vectorNorm,Complex.norm_conj] using
      schattenNorm_besselCoefficient_le u v (fun i => conj (c i)) huB hvB q hpq.symm.pos
  rw [← he]
  exact (h B).trans (mul_le_mul_of_nonneg_left hn hC)

/-- Genuine coefficient-Hankel sufficiency on every finite corner, with a uniform constant. -/
theorem schattenNorm_finiteHankelCoefficientMatrix_le (N : ℕ)
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (p q : ℝ)
    (hpq : p.HolderConjugate q)
    (hE : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞) :
    schattenNorm p (finiteHankelCoefficientMatrix N
      (fun n => diskTaylorCoeff G n/((n : ℂ)+1)))≤
      pellerStrongConstant q^(1/q)*
        lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure := by
  let A := finiteHankelCoefficientMatrix N (fun n => diskTaylorCoeff G n/((n : ℂ)+1))
  have hM := aestronglyMeasurable_analytic_disk G hG
  have hLG := memLp_pellerLift_of_energy G hM p hpq.pos hE
  have hGI := integrable_of_peller_energy G hM p hpq.lt hE
  apply schattenNorm_le_of_finiteHSPair_bound (gramBasis A) A p q _ hpq
    (mul_nonneg (Real.rpow_nonneg (pellerStrongConstant_pos q hpq.symm.lt).le _)
      lpNorm_nonneg)
  intro B
  rw [(finiteHSPair_analytic_area N (gramBasis A) B G hG hGI).2]
  calc
    _ ≤ lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure*
        lpNorm (pellerLift (finiteAntiDiagonalValue N B)) (ENNReal.ofReal q) pellerPolarMeasure :=
      norm_area_pairing_le_peller_lpNorm hpq G (finiteAntiDiagonalValue N B) hM
        (continuous_finiteAntiDiagonalValue N B).aestronglyMeasurable hLG
        (memLp_pellerLift_finiteAntiDiagonal N B q hpq.symm.lt)
    _ ≤ lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure*
        (pellerStrongConstant q^(1/q)*schattenNorm q B) :=
      mul_le_mul_of_nonneg_left (lpNorm_pellerLift_finiteAntiDiagonal_le N B q hpq.symm.lt)
        lpNorm_nonneg
    _ = _ := by ring

end TTO.Paper.Proved
