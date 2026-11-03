/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcBMOEstimatesFoundations
public import TTO.CauchyDerivativeFoundations

/-! Actual measurable circle charts and L² localization on literal real arcs. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The standard real representative in the specified unit window. -/
def arcWindowRep (a : ℝ) (ζ : Boundary) : ℝ :=
  (AddCircle.measurableEquivIoc 1 a ζ : ℝ)

theorem measurable_arcWindowRep (a : ℝ) : Measurable (arcWindowRep a) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 a).measurable

theorem arcWindowRep_coe (a t : ℝ) (ht : t∈Ioc a (a+1)) :
    arcWindowRep a (t : Boundary)=t := by
  change ((AddCircle.equivIoc 1 a (t : Boundary)) : ℝ)=t
  rw [AddCircle.equivIoc_coe_eq ht]

/-- A genuine measurable circular arc in the fixed real window. -/
def arcWindowSet (a b c : ℝ) : Set Boundary := arcWindowRep a ⁻¹' Ioc b c

theorem measurableSet_arcWindowSet (a b c : ℝ) : MeasurableSet (arcWindowSet a b c) :=
  (measurable_arcWindowRep a) measurableSet_Ioc

theorem memLp_arcWindow_indicator (a b c : ℝ) (f : BoundaryL2) :
    MemLp ((arcWindowSet a b c).indicator f) 2 circleMeasure :=
  MemLp.indicator (measurableSet_arcWindowSet a b c).nullMeasurableSet (Lp.memLp f)

/-- Native L² localization, using the actual measurable indicator. -/
def arcWindowL2 (a b c : ℝ) (f : BoundaryL2) : BoundaryL2 :=
  (memLp_arcWindow_indicator a b c f).toLp ((arcWindowSet a b c).indicator f)

theorem arcWindowL2_ae (a b c : ℝ) (f : BoundaryL2) :
    (fun ζ => arcWindowL2 a b c f ζ)=ᵐ[circleMeasure] (arcWindowSet a b c).indicator f :=
  (memLp_arcWindow_indicator a b c f).coeFn_toLp


/-- The native localized L² norm is exactly the original real-arc square integral. -/
theorem norm_arcWindowL2_sq (a b c : ℝ) (hab : a≤b) (hc : c≤a+1) (f : BoundaryL2) :
    ‖arcWindowL2 a b c f‖^2=∫ t in Ioc b c,‖f (t : Boundary)‖^2 := by
  classical
  let S := arcWindowSet a b c
  have hAE : (fun ζ => ‖arcWindowL2 a b c f ζ‖^2)=ᵐ[circleMeasure]
      S.indicator (fun ζ => ‖f ζ‖^2) := by
    filter_upwards [arcWindowL2_ae a b c f] with ζ hζ
    rw [hζ]
    by_cases hS : ζ∈S
    · simp only [S,indicator_of_mem hS]
    · simp only [S,indicator_of_notMem hS,norm_zero,zero_pow (by decide : 2≠0)]
  have hBase : ‖arcWindowL2 a b c f‖^2=
      ∫ ζ : Boundary,S.indicator (fun ζ => ‖f ζ‖^2) ζ ∂circleMeasure :=
    (boundaryL2_integral_norm_sq _).symm.trans (integral_congr_ae hAE)
  have hμ := congrArg (fun μ : Measure Boundary =>
    ∫ ζ : Boundary,S.indicator (fun ζ => ‖f ζ‖^2) ζ ∂μ) circleMeasure_eq_volume
  have hPre := AddCircle.integral_preimage 1 a
    (S.indicator (fun ζ : Boundary => ‖f ζ‖^2))
  have hRep (t : ℝ) (ht : t∈Ioc a (a+1)) :
      S.indicator (fun ζ => ‖f ζ‖^2) (t : Boundary)=
        (Ioc b c).indicator (fun t : ℝ => ‖f (t : Boundary)‖^2) t := by
    have hMem : (t : Boundary)∈S ↔ t∈Ioc b c := by
      change arcWindowRep a (t : Boundary)∈Ioc b c ↔ t∈Ioc b c
      rw [arcWindowRep_coe a t ht]
    by_cases hbc : t∈Ioc b c
    · rw [indicator_of_mem (hMem.mpr hbc),indicator_of_mem hbc]
    · rw [indicator_of_notMem (fun h => hbc (hMem.mp h)),indicator_of_notMem hbc]
  have hReal : (∫ t in Ioc a (a+1),S.indicator (fun ζ => ‖f ζ‖^2) (t : Boundary))=
      ∫ t in Ioc a (a+1),(Ioc b c).indicator (fun t : ℝ => ‖f (t : Boundary)‖^2) t :=
    setIntegral_congr_fun measurableSet_Ioc hRep
  have hSub : Ioc b c ⊆ Ioc a (a+1) := fun t ht =>
    ⟨hab.trans_lt ht.1,ht.2.trans hc⟩
  rw [hBase,hμ,← hPre,hReal,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr hSub]


/-- The whole-disk weighted kernel energy depends only on oscillation, including B=0. -/
theorem cauchyWeightedHardyKernel_energy_le_oscillation (f : BoundaryL2)
    (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B) :
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2) ∂diskArea)≤
      ENNReal.ofReal (768*B^2) := by
  have hEq : (fun z => ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2))=ᵐ[diskArea]
      fun z => ENNReal.ofReal ((1-‖z‖^2)*
        ‖cauchyWeightedHardyKernel (f-constL2 (fourierCoeff f 0)) z‖^2) := by
    filter_upwards [ae_mem_diskArea] with z hz
    rw [cauchyWeightedHardyKernel_sub_const f (fourierCoeff f 0) ⟨z,hz⟩]
  calc
    _ = ∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*
        ‖cauchyWeightedHardyKernel (f-constL2 (fourierCoeff f 0)) z‖^2) ∂diskArea :=
      lintegral_congr_ae hEq
    _ ≤ ENNReal.ofReal (2*‖f-constL2 (fourierCoeff f 0)‖^2) :=
      cauchyWeightedHardyKernel_weighted_energy_le _
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := norm_sub_constant_sq_le_of_meanOscillation_bound f B hB hMO
      linarith)

end TTO.Paper.Proved
