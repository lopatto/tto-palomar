/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedBlaschkeFoundations

/-! Trace-class Bochner integration under an integrable scalar gauge bound.
All integrals are in the ordinary operator-norm Banach space; no Schatten carrier is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section DominatedIntegral
variable {α H : Type} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An arbitrary-measure trace-class integral with a genuine integrable gauge bound. -/
theorem traceClass_integral_dominated
    (μ : Measure α) (T : α → H →L[ℂ] H) (hT : StronglyMeasurable T)
    (b : α → ℝ) (hbMeas : Measurable b) (hbInt : Integrable b μ) (hb0 : ∀ x,0≤b x)
    (hSp : ∀ x,Schatten 1 (T x)) (hGauge : ∀ x,schattenNorm 1 (T x)≤b x) :
    Integrable T μ ∧ Schatten 1 (∫ x,T x ∂μ) ∧ schattenNorm 1 (∫ x,T x ∂μ)≤∫ x,b x ∂μ := by
  have hop (x : α) : ‖T x‖≤b x := (opNorm_le_schattenNorm 1 (T x) (hSp x)).trans (hGauge x)
  have hInt : Integrable T μ :=
    hbInt.mono' hT.aestronglyMeasurable (Eventually.of_forall hop)
  refine ⟨hInt,?_⟩
  let C : ℝ := ∫ x,b x ∂μ
  have hC0 : 0≤C := integral_nonneg hb0
  have hz (x : α) (hb : b x=0) : T x=0 := by
    exact norm_eq_zero.mp ((hop x).trans_eq hb |>.antisymm (norm_nonneg _))
  by_cases hC : C=0
  · have hbZero : b=ᵐ[μ](fun _ => 0) := (integral_eq_zero_iff_of_nonneg hb0 hbInt).mp hC
    have hTZero : T=ᵐ[μ](fun _ => 0) := hbZero.mono (fun x hx => hz x hx)
    rw [integral_congr_ae hTZero,integral_zero]
    exact ⟨schatten_zero 1 (by norm_num),by rw [schattenNorm_zero 1 (by norm_num)]; exact hC0⟩
  let k : α → ℝ := fun x => b x/C
  have hkMeas : Measurable k := hbMeas.div_const C
  have hkInt : Integrable k μ := hbInt.div_const C
  have hk0 (x : α) : 0≤k x := div_nonneg (hb0 x) hC0
  have hkOne : ∫ x,k x ∂μ=1 := by
    change (∫ x,b x/C ∂μ)=1
    simp only [div_eq_mul_inv]
    rw [integral_mul_const]
    exact mul_inv_cancel₀ hC
  let ν : Measure α := μ.withDensity (fun x => ENNReal.ofReal (k x))
  have hν : ν Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ←ofReal_integral_eq_lintegral_ofReal hkInt (Eventually.of_forall hk0),hkOne,ENNReal.ofReal_one]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let S : α → H →L[ℂ] H := fun x => (C/b x) • T x
  have hSMeas : StronglyMeasurable S := (measurable_const.div hbMeas).stronglyMeasurable.smul hT
  have hS (x : α) : Schatten 1 (S x) ∧ schattenNorm 1 (S x)≤C := by
    obtain ⟨hSS,hSN⟩ := schatten_nonneg_real_smul (hSp x) (C/b x) (div_nonneg hC0 (hb0 x))
    refine ⟨hSS,hSN.trans ?_⟩
    have he := mul_le_mul_of_nonneg_left (hGauge x) (div_nonneg hC0 (hb0 x))
    apply he.trans
    by_cases hb : b x=0
    · simp only [hb,div_zero,zero_mul]
      exact hC0
    · exact (div_mul_cancel₀ C hb).le
  have hSInt : Integrable S ν := (integrable_const C).mono' hSMeas.aestronglyMeasurable
    (Eventually.of_forall (fun x => (opNorm_le_schattenNorm 1 (S x) (hS x).1).trans (hS x).2))
  have hMeas : Measurable (fun x => ENNReal.ofReal (k x)) := hkMeas.ennreal_ofReal
  have hFin : ∀ᵐ x ∂μ,ENNReal.ofReal (k x)<∞ := Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hIntegral : (∫ x,S x ∂ν)=∫ x,T x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hMeas hFin]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change (ENNReal.ofReal (k x)).toReal • S x=T x
      rw [ENNReal.toReal_ofReal (hk0 x)]
      change k x • ((C/b x) • T x)=T x
      by_cases hb : b x=0
      · rw [hz x hb]
        simp only [smul_zero]
      · rw [smul_smul]
        have he : k x*(C/b x)=1 := by dsimp only [k]; field_simp
        rw [he,one_smul])
  have hBall := schatten_integral_ball ν 1 le_rfl C S (Eventually.of_forall hS) hSInt
  rw [hIntegral] at hBall
  exact hBall

end DominatedIntegral
end TTO.Paper.Proved
