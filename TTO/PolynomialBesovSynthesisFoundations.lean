/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ShortBandDerivativeFoundations
public import TTO.SparseGridSummationFoundations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Finite polynomial Besov synthesis retains the original energy and its low jets. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem complex_norm_add_rpow_le_low (a b : ℂ) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ‖a+b‖^p≤‖a‖^p+‖b‖^p :=
  (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le a b) hp.le).trans
    (Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hp.le hp1)

theorem polynomialIteratedDerivative_add (P Q : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (P+Q).eval z=iteratedDeriv n P.eval z+iteratedDeriv n Q.eval z := by
  rw [← polynomialIteratedDerivative_eval,← polynomialIteratedDerivative_eval,
    ← polynomialIteratedDerivative_eval]
  change ((Polynomial.derivative^[n]) (P+Q)).eval z=
    ((Polynomial.derivative^[n]) P).eval z+((Polynomial.derivative^[n]) Q).eval z
  have he : (Polynomial.derivative^[n]) (P+Q)=
      (Polynomial.derivative^[n]) P+(Polynomial.derivative^[n]) Q := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',ih,Polynomial.derivative_add]
  rw [he,Polynomial.eval_add]

theorem polynomialIteratedDerivative_const_mul (a : ℂ) (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (Polynomial.C a*P).eval z=a*iteratedDeriv n P.eval z := by
  rw [← polynomialIteratedDerivative_eval,← polynomialIteratedDerivative_eval]
  change ((Polynomial.derivative^[n]) (Polynomial.C a*P)).eval z=
    a*((Polynomial.derivative^[n]) P).eval z
  rw [Polynomial.iterate_derivative_C_mul,Polynomial.eval_mul,Polynomial.eval_C]

theorem polynomialIteratedDerivative_zero (n : ℕ) (z : ℂ) :
    iteratedDeriv n (0 : Polynomial ℂ).eval z=0 := by
  rw [← polynomialIteratedDerivative_eval]
  change ((Polynomial.derivative^[n]) (0 : Polynomial ℂ)).eval z=0
  have he : (Polynomial.derivative^[n]) (0 : Polynomial ℂ)=0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih]; simp
  rw [he,Polynomial.eval_zero]

theorem polynomial_besovEnergy_zero (p : ℝ) (hp : 0<p) :
    besovEnergy p (0 : Polynomial ℂ).eval=0 := by
  simp only [besovEnergy,polynomialIteratedDerivative_zero,norm_zero,
    Real.zero_rpow hp.ne',ENNReal.ofReal_zero,zero_mul,Finset.sum_const_zero,
    lintegral_zero,zero_add]

theorem polynomial_besovEnergy_add_le (P Q : Polynomial ℂ)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    besovEnergy p (P+Q).eval≤besovEnergy p P.eval+besovEnergy p Q.eval := by
  have hPoint (n : ℕ) (z : ℂ) :
      ENNReal.ofReal (‖iteratedDeriv n (P+Q).eval z‖^p)≤
        ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p)+
          ENNReal.ofReal (‖iteratedDeriv n Q.eval z‖^p) := by
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) p)
      (Real.rpow_nonneg (norm_nonneg _) p),polynomialIteratedDerivative_add]
    exact ENNReal.ofReal_le_ofReal (complex_norm_add_rpow_le_low _ _ p hp hp1)
  have hJet :
      (∑ j∈Finset.range (besovOrder p),ENNReal.ofReal (‖iteratedDeriv j (P+Q).eval 0‖^p))≤
        (∑ j∈Finset.range (besovOrder p),ENNReal.ofReal (‖iteratedDeriv j P.eval 0‖^p))+
          (∑ j∈Finset.range (besovOrder p),ENNReal.ofReal (‖iteratedDeriv j Q.eval 0‖^p)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hPoint j 0)
  let W : ℂ → ℝ := fun z => (1-‖z‖^2)^((besovOrder p : ℝ)*p-2)
  have hArea :
      (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) (P+Q).eval z‖^p*W z) ∂diskArea)≤
        (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) P.eval z‖^p*W z) ∂diskArea)+
          (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) Q.eval z‖^p*W z) ∂diskArea) := by
    have hM : Measurable (fun z : ℂ =>
        ENNReal.ofReal (‖iteratedDeriv (besovOrder p) P.eval z‖^p*W z)) := by
      have hD : Continuous (iteratedDeriv (besovOrder p) P.eval) := by
        rw [← polynomialIteratedDerivative_eval]
        fun_prop
      exact ((hD.norm.measurable.pow_const p).mul
        ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const _)).ennreal_ofReal
    calc
      _ ≤ ∫⁻ z,(ENNReal.ofReal (‖iteratedDeriv (besovOrder p) P.eval z‖^p)+
          ENNReal.ofReal (‖iteratedDeriv (besovOrder p) Q.eval z‖^p))*
            ENNReal.ofReal (W z) ∂diskArea := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
        exact mul_le_mul_left (hPoint (besovOrder p) z) _
      _ = ∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) P.eval z‖^p*W z)+
          ENNReal.ofReal (‖iteratedDeriv (besovOrder p) Q.eval z‖^p*W z) ∂diskArea := by
        apply lintegral_congr
        intro z
        simp only [add_mul,
          ENNReal.ofReal_mul (Real.rpow_nonneg
            (norm_nonneg (iteratedDeriv (besovOrder p) P.eval z)) p),
          ENNReal.ofReal_mul (Real.rpow_nonneg
            (norm_nonneg (iteratedDeriv (besovOrder p) Q.eval z)) p)]
      _ = _ := lintegral_add_left' hM.aemeasurable _
  unfold besovEnergy
  exact (add_le_add hJet hArea).trans_eq (by dsimp only [W]; ac_rfl)

theorem polynomial_besovEnergy_sum_le {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    besovEnergy p (∑ i∈s,P i).eval≤∑ i∈s,besovEnergy p (P i).eval := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,polynomial_besovEnergy_zero p hp,le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (polynomial_besovEnergy_add_le _ _ p hp hp1).trans (add_le_add le_rfl ih)

theorem polynomial_besovEnergy_const_mul (a : ℂ) (P : Polynomial ℂ) (p : ℝ) :
    besovEnergy p (Polynomial.C a*P).eval=ENNReal.ofReal (‖a‖^p)*besovEnergy p P.eval := by
  have hNorm (n : ℕ) (z : ℂ) :
      ‖iteratedDeriv n (Polynomial.C a*P).eval z‖^p=
        ‖a‖^p*‖iteratedDeriv n P.eval z‖^p := by
    rw [polynomialIteratedDerivative_const_mul,norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hJet :
      (∑ j∈Finset.range (besovOrder p),ENNReal.ofReal
        (‖iteratedDeriv j (Polynomial.C a*P).eval 0‖^p))=
          ENNReal.ofReal (‖a‖^p)*
            ∑ j∈Finset.range (besovOrder p),ENNReal.ofReal (‖iteratedDeriv j P.eval 0‖^p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hNorm,ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
  have hArea :
      (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) (Polynomial.C a*P).eval z‖^p*
        (1-‖z‖^2)^((besovOrder p : ℝ)*p-2)) ∂diskArea)=
          ENNReal.ofReal (‖a‖^p)*
            ∫⁻ z,ENNReal.ofReal (‖iteratedDeriv (besovOrder p) P.eval z‖^p*
              (1-‖z‖^2)^((besovOrder p : ℝ)*p-2)) ∂diskArea := by
    simp_rw [hNorm,mul_assoc,ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg a) p)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp only [besovEnergy,hJet,hArea,mul_add]

theorem lintegral_boundary_distance_rpow (α : ℝ) (hα : -1<α) :
    (∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal ((1-r)^α))=
      ENNReal.ofReal (1/(α+1)) := by
  have h := lintegral_scaled_boundary_distance (fun u => ENNReal.ofReal (u^α))
    1 zero_lt_one
  simp only [one_mul,inv_one,ENNReal.ofReal_one] at h
  rw [h,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact lintegral_unit_rpow α hα

theorem lintegral_disk_boundary_weight_le (α : ℝ) (hα : -1<α) :
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖)^α) ∂diskArea)≤ENNReal.ofReal (2/(α+1)) := by
  have hPolar :
      (∫⁻ z,ENNReal.ofReal ((1-‖z‖)^α) ∂diskArea)=
        ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (2*r*(1-r)^α) := by
    simpa using polynomialDerivative_weighted_polar (1 : Polynomial ℂ) 0 1 α zero_lt_one
  rw [hPolar]
  calc
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) 1,ENNReal.ofReal (2 : ℝ)*
        ENNReal.ofReal ((1-r)^α) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (by linarith [hr.2] : 2*r≤2)
        (Real.rpow_nonneg (by linarith [hr.2]) α)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_boundary_distance_rpow α hα,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
      congr 1
      ring

theorem polynomial_derivative_weighted_area_ne_top (P : Polynomial ℂ) (n : ℕ)
    (p α : ℝ) (hp : 0<p) (hα : -1<α) (hα0 : α≤0) :
    (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*(1-‖z‖^2)^α) ∂diskArea)≠∞ := by
  have hD : Continuous (iteratedDeriv n P.eval) := by
    rw [← polynomialIteratedDerivative_eval]
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hD.continuousOn
  have hC0 : 0≤C := (norm_nonneg _).trans (hC 0 (by simp))
  have hNorm (z : ℂ) (hz : z∈disk) : ‖iteratedDeriv n P.eval z‖^p≤C^p := by
    change ‖z‖<1 at hz
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    exact hC z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.le)
  have hAE : ∀ᵐ z ∂diskArea,z∈disk := by
    rw [diskArea]
    exact Measure.ae_smul_measure
      (ae_restrict_mem (isOpen_lt continuous_norm continuous_const).measurableSet) _
  have hPhys :
      (∫⁻ z,ENNReal.ofReal (‖iteratedDeriv n P.eval z‖^p*(1-‖z‖)^α) ∂diskArea)≤
        ENNReal.ofReal (C^p)*ENNReal.ofReal (2/(α+1)) := by
    calc
      _ ≤ ∫⁻ z,ENNReal.ofReal (C^p)*ENNReal.ofReal ((1-‖z‖)^α) ∂diskArea := by
        apply lintegral_mono_ae
        filter_upwards [hAE] with z hz
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) p)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hNorm z hz)) _
      _ = ENNReal.ofReal (C^p)*(∫⁻ z,ENNReal.ofReal ((1-‖z‖)^α) ∂diskArea) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := mul_le_mul_right (lintegral_disk_boundary_weight_le α hα) _
  have hCompare := lintegral_frozen_weight_le_physical_of_nonpos
    (fun z => ‖iteratedDeriv n P.eval z‖^p)
    (fun _ _ => Real.rpow_nonneg (norm_nonneg _) p) α hα0
  exact ne_top_of_le_ne_top (by finiteness) (hCompare.trans hPhys)

theorem polynomial_besovEnergy_ne_top (P : Polynomial ℂ) (p : ℝ)
    (hp : 0<p) (hp1 : p≤1) : besovEnergy p P.eval≠∞ := by
  have hnp := besovOrder_product_bounds p hp
  rw [besovEnergy]
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  · exact polynomial_derivative_weighted_area_ne_top P (besovOrder p)
      p ((besovOrder p : ℝ)*p-2) hp (by linarith [hnp.1]) (by linarith [hnp.2])

def polynomialBesovDegreeConstant (D : ℕ) (p : ℝ) : ℝ :=
  1+∑ k∈Finset.range D,(besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval).toReal

theorem polynomialBesovDegreeConstant_pos (D : ℕ) (p : ℝ) :
    0<polynomialBesovDegreeConstant D p := by
  dsimp only [polynomialBesovDegreeConstant]
  positivity

theorem polynomial_besovEnergy_le_of_coeff_bound (D : ℕ) (P : Polynomial ℂ)
    (hD : P.natDegree<D) (B p : ℝ) (hB : 0≤B) (hp : 0<p) (hp1 : p≤1)
    (hCoeff : ∀ k∈Finset.range D,‖P.coeff k‖≤B) :
    besovEnergy p P.eval≤ENNReal.ofReal (polynomialBesovDegreeConstant D p*B^p) := by
  have hE := polynomial_besovEnergy_sum_le (Finset.range D)
    (fun k => Polynomial.C (P.coeff k)*Polynomial.X^k) p hp hp1
  rw [← P.as_sum_range_C_mul_X_pow' hD] at hE
  simp_rw [polynomial_besovEnergy_const_mul] at hE
  have hSum : (∑ k∈Finset.range D,besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval)=
      ENNReal.ofReal (∑ k∈Finset.range D,
        (besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl (fun k _ =>
      (ENNReal.ofReal_toReal (polynomial_besovEnergy_ne_top _ p hp hp1)).symm)
  calc
    _ ≤ ∑ k∈Finset.range D,ENNReal.ofReal (‖P.coeff k‖^p)*
        besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval := hE
    _ ≤ ∑ k∈Finset.range D,ENNReal.ofReal (B^p)*
        besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (norm_nonneg _) (hCoeff k hk) hp.le)) _
    _ = ENNReal.ofReal (B^p)*
        (∑ k∈Finset.range D,besovEnergy p (Polynomial.X^k : Polynomial ℂ).eval) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [hSum,← ENNReal.ofReal_mul (Real.rpow_nonneg hB p)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [polynomialBesovDegreeConstant]
      have hPow : 0≤B^p := Real.rpow_nonneg hB p
      nlinarith

theorem polynomial_coeff_norm_le_hankel_schatten (K : ℕ) (P : Polynomial ℂ)
    (hK : P.natDegree<K) (p : ℝ) (hp : 0<p) (k : ℕ) :
    ‖P.coeff k‖≤schattenNorm p (polynomialHankelRectangleOffset K K 0 P) := by
  by_cases hk : k<K
  · have hK0 : 0<K := by omega
    let i : Fin K := ⟨k,hk⟩
    let j : Fin K := ⟨0,hK0⟩
    let A := polynomialHankelRectangleOffset K K 0 P
    let e : EuclideanSpace ℂ (Fin K) := EuclideanSpace.single j 1
    calc
      _ = ‖A e i‖ := by
        dsimp only [A,e]
        rw [polynomialHankelRectangleOffset_single_apply]
        simp only [i,j,zero_add,add_zero]
      _ ≤ ‖A e‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖A‖*‖e‖ := A.le_opNorm e
      _ = ‖A‖ := by simp [e,EuclideanSpace.single]
      _ ≤ _ := opNorm_le_schattenNorm p A (finiteDim_schatten A p hp)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hK.trans_le (by omega)),norm_zero]
    exact schattenNorm_nonneg p _

theorem wideLowpassPolynomial_natDegree_le (m N : ℕ) (P : Polynomial ℂ) :
    (wideLowpassPolynomial m N P).natDegree≤wideDirichletProductShift m N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [wideLowpassPolynomial_coeff]
  change (wideDirichletProductPolynomial m N).coeff (wideDirichletProductShift m N+k)*
    P.coeff k=0
  rw [wideDirichletProductPolynomial_coeff_zero m N k hk,zero_mul]

def wideLowpassCoefficientConstant (m N : ℕ) : ℝ :=
  1+∑ k∈Finset.range (wideDirichletProductShift m N+1),‖wideDirichletPositiveWeight m N k‖

theorem wideLowpassCoefficientConstant_pos (m N : ℕ) :
    0<wideLowpassCoefficientConstant m N := by
  dsimp only [wideLowpassCoefficientConstant]
  positivity

def wideLowpassBesovConstant (m N : ℕ) (p : ℝ) : ℝ :=
  polynomialBesovDegreeConstant (wideDirichletProductShift m N+1) p*
    wideLowpassCoefficientConstant m N^p

theorem wideLowpassBesovConstant_pos (m N : ℕ) (p : ℝ) :
    0<wideLowpassBesovConstant m N p :=
  mul_pos (polynomialBesovDegreeConstant_pos _ p)
    (Real.rpow_pos_of_pos (wideLowpassCoefficientConstant_pos m N) p)

theorem wideLowpassPolynomial_besovEnergy_le (m N K : ℕ) (P : Polynomial ℂ)
    (hK : P.natDegree<K) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    besovEnergy p (wideLowpassPolynomial m N P).eval≤
      ENNReal.ofReal (wideLowpassBesovConstant m N p*
        schattenNorm p (polynomialHankelRectangleOffset K K 0 P)^p) := by
  let B := wideLowpassCoefficientConstant m N
  let A := polynomialHankelRectangleOffset K K 0 P
  have hB : 0<B := wideLowpassCoefficientConstant_pos m N
  have hCoeff : ∀ k∈Finset.range (wideDirichletProductShift m N+1),
      ‖(wideLowpassPolynomial m N P).coeff k‖≤B*schattenNorm p A := by
    intro k hk
    have hSum : ‖wideDirichletPositiveWeight m N k‖≤
        ∑ j∈Finset.range (wideDirichletProductShift m N+1),
          ‖wideDirichletPositiveWeight m N j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg _) hk
    have hWeight : ‖wideDirichletPositiveWeight m N k‖≤B := by
      dsimp only [B,wideLowpassCoefficientConstant]
      linarith
    rw [wideLowpassPolynomial_coeff,norm_mul]
    exact mul_le_mul hWeight (polynomial_coeff_norm_le_hankel_schatten K P hK p hp k)
      (norm_nonneg _) hB.le
  have hE := polynomial_besovEnergy_le_of_coeff_bound
    (wideDirichletProductShift m N+1) (wideLowpassPolynomial m N P)
    (Nat.lt_succ_of_le (wideLowpassPolynomial_natDegree_le m N P))
    (B*schattenNorm p A) p (mul_nonneg hB.le (schattenNorm_nonneg p A)) hp hp1 hCoeff
  simpa only [Real.mul_rpow hB.le (schattenNorm_nonneg p A),
    B,A,wideLowpassBesovConstant,mul_assoc] using hE

theorem thinWideBand_besovEnergy_le (m N N' : ℕ) (hm : 1≤m) (hN : 10≤N)
    (hNN' : N≤N') (hRatio : 5*N'≤6*N) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hmp : besovOrder p≤m) :
    besovEnergy p (thinWideBandPolynomial m N N' P).eval≤
      ENNReal.ofReal ((20*(m : ℝ)*shortBandBesovConstant p)*(N : ℝ)*
        (∫ τ : Boundary,‖(thinWideBandPolynomial m N N' P).eval
          (fourier (T:=1) 1 τ)‖^p ∂circleMeasure)) := by
  obtain ⟨hFit,hCover,hLower⟩ := thinWideBand_geometry m N N' hm hN hNN' hRatio
  obtain ⟨hUpper,hSep,hStart⟩ := thinWideBand_placement_bounds m N N' hm hN hNN' hRatio
  have hb0 : 4*thinWideBandHalfwidth m N N'≤thinWideBandStart m N := by
    nlinarith [Nat.sub_add_cancel hFit]
  have hb1 : thinWideBandStart m N≤102*thinWideBandHalfwidth m N N' := by nlinarith
  have hmN : m≤m*N := by nlinarith
  have hL : 0<thinWideBandHalfwidth m N N' := by omega
  have hn : besovOrder p≤thinWideBandHalfwidth m N N' := hmp.trans (hmN.trans hLower)
  have hHi : ∀ k : ℕ,thinWideBandStart m N+2*thinWideBandHalfwidth m N N'≤k →
      (thinWideBandPolynomial m N N' P).coeff k=0 := by
    intro k hk
    exact thinWideBandPolynomial_coeff_high m N N' hNN' P k (by omega)
  have hE := offsetShortBand_besovEnergy_le
    (thinWideBandStart m N) (thinWideBandHalfwidth m N N') hb0 hb1 hL
    (thinWideBandPolynomial m N N' P) (thinWideBandPolynomial_coeff_low m N N' hNN' P)
    hHi p hp hp1 hn
  apply hE.trans
  apply ENNReal.ofReal_le_ofReal
  have hLR : (thinWideBandHalfwidth m N N' : ℝ)≤20*(m : ℝ)*(N : ℝ) := by
    exact_mod_cast hUpper
  have hMean : 0≤(∫ τ : Boundary,‖(thinWideBandPolynomial m N N' P).eval
      (fourier (T:=1) 1 τ)‖^p ∂circleMeasure) :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) p)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLR (shortBandBesovConstant_pos p hp).le) hMean
  convert h using 1; ring

theorem polynomial_besovEnergy_le_base_add_bandBudget (m : ℕ) (hm : 1≤m)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hmp : besovOrder p≤m) :
    besovEnergy p P.eval≤besovEnergy p (wideLowpassPolynomial m 10 P).eval+
      ENNReal.ofReal ((20*(m : ℝ)*shortBandBesovConstant p)*polynomialWideBandBudget m P p) := by
  let C : ℝ := 20*(m : ℝ)*shortBandBesovConstant p
  have hC : 0≤C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (shortBandBesovConstant_pos p hp).le
  have hEach (j : ℕ) :
      besovEnergy p (thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval≤
        ENNReal.ofReal (C*scheduledWideBandMass m j P p) := by
    simpa only [C,scheduledWideBandMass,mul_assoc] using
      thinWideBand_besovEnergy_le m _ _ hm (thinWideScale_ten_le j)
        (thinWideScale_monotone (Nat.le_succ j)) (thinWideScale_ratio j) P p hp hp1 hmp
  have hBands :
      (∑ j∈Finset.range P.natDegree,
        besovEnergy p (thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval)≤
          ENNReal.ofReal (C*polynomialWideBandBudget m P p) := by
    calc
      _ ≤ ∑ j∈Finset.range P.natDegree,ENNReal.ofReal (C*scheduledWideBandMass m j P p) :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by
        rw [polynomialWideBandBudget,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg
          (fun j _ => mul_nonneg hC (scheduledWideBandMass_nonneg m j P p))]
  have hA := polynomial_besovEnergy_add_le
    (wideLowpassPolynomial m (thinWideScale 0) P)
    (∑ j∈Finset.range P.natDegree,
      thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P) p hp hp1
  have hS := polynomial_besovEnergy_sum_le (Finset.range P.natDegree)
    (fun j => thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P) p hp hp1
  have h := hA.trans (add_le_add le_rfl (hS.trans hBands))
  rw [thinWideScale_polynomial_resolution m P P.natDegree le_rfl] at h
  simpa only [thinWideScale_zero] using h

theorem exists_polynomial_besov_hankel_bound_of_order (m : ℕ) (hm : 1≤m)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hmp : besovOrder p≤m)
    (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    ∃ M : ℕ,100≤M ∧ ∃ C : ℝ,0<C ∧ ∀ P : Polynomial ℂ,
      besovEnergy p P.eval≤ENNReal.ofReal
        (C*schattenNorm p (residueAmbientHankel m M (P.natDegree+1) P)^p) := by
  obtain ⟨M,hM,C,hC,hBound⟩ := exists_polynomialWideBandBudget_concrete_bound
    m hm p hp hp1 hOrder
  let B : ℝ := 20*(m : ℝ)*shortBandBesovConstant p
  have hBr : 0<B := by
    have hmr : 0<(m : ℝ) := by exact_mod_cast (by omega : 0<m)
    dsimp only [B]
    exact mul_pos (by positivity) (shortBandBesovConstant_pos p hp)
  let C0 := wideLowpassBesovConstant m 10 p
  have hC0 : 0<C0 := wideLowpassBesovConstant_pos m 10 p
  refine ⟨M,hM,C0+B*C,by positivity,?_⟩
  intro P
  let K := 150*m*thinWideScale (M*(P.natDegree+1))
  let A := residueAmbientHankel m M (P.natDegree+1) P
  have hK : P.natDegree<K := by
    have hJ : P.natDegree<M*(P.natDegree+1) := by nlinarith
    have hS : M*(P.natDegree+1)≤thinWideScale (M*(P.natDegree+1)) :=
      (by omega : M*(P.natDegree+1)≤M*(P.natDegree+1)+10).trans (thinWideScale_lower _)
    have hF : thinWideScale (M*(P.natDegree+1))≤150*m*thinWideScale (M*(P.natDegree+1)) := by
      nlinarith
    exact hJ.trans_le (hS.trans hF)
  have hLow : besovEnergy p (wideLowpassPolynomial m 10 P).eval≤
      ENNReal.ofReal (C0*schattenNorm p A^p) :=
    wideLowpassPolynomial_besovEnergy_le m 10 K P hK p hp hp1
  have hHigh : ENNReal.ofReal (B*polynomialWideBandBudget m P p)≤
      ENNReal.ofReal (B*(C*schattenNorm p A^p)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (hBound P) hBr.le
  calc
    _ ≤ ENNReal.ofReal (C0*schattenNorm p A^p)+
        ENNReal.ofReal (B*(C*schattenNorm p A^p)) :=
      (polynomial_besovEnergy_le_base_add_bandBudget m hm P p hp hp1 hmp).trans
        (add_le_add hLow hHigh)
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg hC0.le (Real.rpow_nonneg (schattenNorm_nonneg p A) p))
        (mul_nonneg hBr.le (mul_nonneg hC.le (Real.rpow_nonneg (schattenNorm_nonneg p A) p)))]
      congr 1
      ring

theorem exists_polynomial_besov_hankel_bound (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ M : ℕ,100≤M ∧ ∃ C : ℝ,0<C ∧ ∀ P : Polynomial ℂ,
      besovEnergy p P.eval≤ENNReal.ofReal
        (C*schattenNorm p (residueAmbientHankel (besovOrder p) M (P.natDegree+1) P)^p) := by
  have hm : 1≤besovOrder p := by simp only [besovOrder]; omega
  have hOrder : 1<((besovOrder p+1 : ℕ) : ℝ)*p := by
    have h := (besovOrder_product_bounds p hp).1
    push_cast
    nlinarith
  exact exists_polynomial_besov_hankel_bound_of_order (besovOrder p) hm p hp hp1 le_rfl hOrder

end TTO.Paper.Proved
