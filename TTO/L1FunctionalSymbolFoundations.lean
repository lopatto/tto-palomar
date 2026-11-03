/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBoundaryFoundations
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! A bounded complex L¹ functional has an actual bounded circle symbol.
Only equality on every L² input is asserted here; no Nehari theorem is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

abbrev BoundaryL1 := Lp ℂ 1 circleMeasure

/-- The inclusion keeps the native AEEqFun unchanged. -/
def nativeL2toL1Linear : BoundaryL2 →ₗ[ℂ] BoundaryL1 where
  toFun f := ⟨f.val,(Lp.antitone (E := ℂ) (μ := circleMeasure)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_nativeL2toL1Linear_le (f : BoundaryL2) :
    ‖nativeL2toL1Linear f‖ ≤ ‖f‖ := by
  change (eLpNorm f 1 circleMeasure).toReal ≤ (eLpNorm f 2 circleMeasure).toReal
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

def nativeL2toL1 : BoundaryL2 →L[ℂ] BoundaryL1 :=
  nativeL2toL1Linear.mkContinuous 1 (fun f => by simpa only [one_mul] using norm_nativeL2toL1Linear_le f)

theorem nativeL2toL1_coeFn (f : BoundaryL2) :
    (nativeL2toL1 f : Boundary → ℂ) = f := rfl

theorem norm_nativeL2toL1_le_one : ‖nativeL2toL1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖nativeL2toL1Linear f‖ ≤ 1*‖f‖
  simpa only [one_mul] using norm_nativeL2toL1Linear_le f

/-- Indicator tests bound an L² Riesz vector in the actual a.e. sense. -/
theorem l2_ae_bound_of_l1_pair_bound (h : BoundaryL2) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f : BoundaryL2, ‖inner ℂ h f‖ ≤ C*‖nativeL2toL1 f‖) :
    ∀ᵐ t ∂circleMeasure, ‖h t‖ ≤ C := by
  have hI2 : Integrable (fun t => ‖h t‖^2) circleMeasure :=
    (Lp.memLp h).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hI1 : Integrable (fun t => ‖h t‖) circleMeasure :=
    ((Lp.memLp h).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable (by norm_num) |>.norm
  have hSets (s : Set Boundary) (hs : MeasurableSet s) :
      (∫ t in s, ‖h t‖^2 ∂circleMeasure) ≤ C*∫ t in s, ‖h t‖ ∂circleMeasure := by
    let f : BoundaryL2 := ((Lp.memLp h).indicator hs.nullMeasurableSet).toLp (s.indicator h)
    have hf : f =ᵐ[circleMeasure] s.indicator h := MemLp.coeFn_toLp _
    have hi : inner ℂ h f = (((∫ t in s, ‖h t‖^2 ∂circleMeasure) : ℝ) : ℂ) := by
      rw [L2.inner_def,← integral_complex_ofReal,← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      by_cases hts : t ∈ s
      · rw [ht,indicator_of_mem hts,indicator_of_mem hts]
        simp only [RCLike.inner_apply,← Complex.conj_mul',Complex.ofReal_pow]
        exact mul_comm _ _
      · rw [ht,indicator_of_notMem hts,indicator_of_notMem hts]
        simp only [RCLike.inner_apply,zero_mul]
    have hn : ‖nativeL2toL1 f‖ = ∫ t in s, ‖h t‖ ∂circleMeasure := by
      rw [L1.norm_eq_integral_norm]
      change (∫ t, ‖f t‖ ∂circleMeasure) = _
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      by_cases hts : t ∈ s
      · rw [ht,indicator_of_mem hts,indicator_of_mem hts]
      · rw [ht,indicator_of_notMem hts,indicator_of_notMem hts,norm_zero]
    have hb := hBound f
    rw [hi,hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun t => sq_nonneg ‖h t‖))] at hb
    exact hb
  have hAE : (fun t => ‖h t‖^2) ≤ᵐ[circleMeasure] (fun t => C*‖h t‖) := by
    apply ae_le_of_forall_setIntegral_le hI2 (hI1.const_mul C)
    intro s hs _hsm
    rw [integral_const_mul]
    exact hSets s hs
  filter_upwards [hAE] with t ht
  have hn : 0 ≤ ‖h t‖ := norm_nonneg _
  nlinarith

/-- Finite-Haar L¹ dual representation on all actual L² inputs, with the sharp bound. -/
theorem exists_bounded_symbol_of_l1_functional (L : BoundaryL1 →L[ℂ] ℂ) :
    ∃ σ : BoundaryLInf, ‖σ‖ ≤ ‖L‖ ∧ ∀ f : BoundaryL2,
      L (nativeL2toL1 f) = ∫ t, f t*σ t ∂circleMeasure := by
  let F : BoundaryL2 →L[ℂ] ℂ := L.comp nativeL2toL1
  let h : BoundaryL2 := (InnerProductSpace.toDual ℂ BoundaryL2).symm F
  have hRep (f : BoundaryL2) : inner ℂ h f = L (nativeL2toL1 f) :=
    InnerProductSpace.toDual_symm_apply
  have hBound (f : BoundaryL2) : ‖inner ℂ h f‖ ≤ ‖L‖*‖nativeL2toL1 f‖ := by
    rw [hRep]
    exact L.le_opNorm _
  have hAE := l2_ae_bound_of_l1_pair_bound h ‖L‖ (norm_nonneg L) hBound
  have hInf : MemLp h ∞ circleMeasure :=
    memLp_top_of_bound (Lp.aestronglyMeasurable h) ‖L‖ hAE
  let a : BoundaryLInf := hInf.toLp h
  let σ : BoundaryLInf := star a
  have ha : a =ᵐ[circleMeasure] h := hInf.coeFn_toLp
  have hσ : σ =ᵐ[circleMeasure] fun t => conj (h t) := by
    filter_upwards [Lp.coeFn_star a,ha] with t hs ht
    change (star a) t=conj (h t)
    rw [hs]
    change conj (a t)=conj (h t)
    rw [ht]
  refine ⟨σ,?_,?_⟩
  · have hSs : ∀ᵐ t ∂circleMeasure, ‖σ t‖ ≤ ‖L‖ := by
      filter_upwards [hσ,hAE] with t ht hb
      rw [ht,Complex.norm_conj]
      exact hb
    have hN := Lp.norm_le_of_ae_bound (f := σ) (norm_nonneg L) hSs
    simpa only [ENNReal.toReal_top,inv_zero,Real.rpow_zero,one_mul] using hN
  · intro f
    rw [← hRep,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hσ] with t ht
    simp only [ht,RCLike.inner_apply]

end TTO.Paper.Proved
