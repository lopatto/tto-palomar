/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcLocalizationFoundations

/-! Actual circle-chart integrals and localized L² pairings.
All representative changes are justified almost everywhere, without pointwise Lp identities. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Actual indicator transport through the standard unit-window circle chart.
The ordinary integral identity also retains the nonintegrable zero convention. -/
theorem integral_arcWindow_indicator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : ℝ) (hab : a≤b) (hc : c≤a+1) (F : Boundary → E) :
    (∫ ζ,(arcWindowSet a b c).indicator F ζ ∂circleMeasure)=
      ∫ t in Ioc b c,F (t : Boundary) := by
  classical
  let S := arcWindowSet a b c
  have hRep (t : ℝ) (ht : t∈Ioc a (a+1)) :
      S.indicator F (t : Boundary)=(Ioc b c).indicator (fun t : ℝ => F (t : Boundary)) t := by
    have hMem : (t : Boundary)∈S ↔ t∈Ioc b c := by
      change arcWindowRep a (t : Boundary)∈Ioc b c ↔ t∈Ioc b c
      rw [arcWindowRep_coe a t ht]
    by_cases hbc : t∈Ioc b c
    · rw [indicator_of_mem (hMem.mpr hbc),indicator_of_mem hbc]
    · rw [indicator_of_notMem (fun h => hbc (hMem.mp h)),indicator_of_notMem hbc]
  have hSub : Ioc b c ⊆ Ioc a (a+1) := fun t ht =>
    ⟨hab.trans_lt ht.1,ht.2.trans hc⟩
  change (∫ ζ,S.indicator F ζ ∂circleMeasure)=_
  calc
    _ = ∫ ζ : Boundary,S.indicator F ζ := by rw [circleMeasure_eq_volume]
    _ = ∫ t in Ioc a (a+1),S.indicator F (t : Boundary) :=
      (AddCircle.integral_preimage 1 a (S.indicator F)).symm
    _ = ∫ t in Ioc a (a+1),(Ioc b c).indicator (fun t : ℝ => F (t : Boundary)) t :=
      setIntegral_congr_fun measurableSet_Ioc hRep
    _ = _ := by rw [setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr hSub]

/-- The native localized L² class paired with an arbitrary boundary kernel. -/
theorem integral_arcWindowL2_mul (a b c : ℝ) (hab : a≤b) (hc : c≤a+1)
    (f : BoundaryL2) (k : Boundary → ℂ) :
    (∫ ζ,arcWindowL2 a b c f ζ*k ζ ∂circleMeasure)=
      ∫ t in Ioc b c,f (t : Boundary)*k (t : Boundary) := by
  classical
  have hEq : (fun ζ => arcWindowL2 a b c f ζ*k ζ)=ᵐ[circleMeasure]
      (arcWindowSet a b c).indicator (fun ζ => f ζ*k ζ) := by
    filter_upwards [arcWindowL2_ae a b c f] with ζ hζ
    rw [hζ]
    by_cases hS : ζ∈arcWindowSet a b c
    · rw [indicator_of_mem hS,indicator_of_mem hS]
    · rw [indicator_of_notMem hS,indicator_of_notMem hS,zero_mul]
  exact (integral_congr_ae hEq).trans (integral_arcWindow_indicator a b c hab hc _)

/-- Subtraction of a constant is identified only almost everywhere on the real arc. -/
theorem norm_arcWindowL2_sub_const_sq (a b c : ℝ) (hab : a≤b) (hc : c≤a+1)
    (f : BoundaryL2) (v : ℂ) :
    ‖arcWindowL2 a b c (f-constL2 v)‖^2=∫ t in Ioc b c,‖f (t : Boundary)-v‖^2 := by
  rw [norm_arcWindowL2_sq a b c hab hc]
  have hAE : (fun ζ => (f-constL2 v) ζ)=ᵐ[circleMeasure] fun ζ => f ζ-v := by
    filter_upwards [Lp.coeFn_sub f (constL2 v),
      (memLp_const v (μ:=circleMeasure) (p:=2)).coeFn_toLp] with ζ hs hv
    change (f-constL2 v) ζ=f ζ-(constL2 v) ζ at hs
    change (constL2 v) ζ=v at hv
    rw [hs,hv]
  have hLen : c-b≤1 := by linarith
  apply integral_congr_ae
  filter_upwards [circle_ae_lift_Ioc hAE b c hLen] with t ht
  rw [ht]

/-- Homogeneous local BMO² control, including B=0 and arbitrary real window positions. -/
theorem norm_arcWindowL2_sub_arcMean_sq_le (a b c : ℝ) (hab : a≤b) (hc : c≤a+1)
    (hbc : b<c) (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ x y : ℝ,x<y → y-x≤1 → meanOscillation f x y≤B) :
    ‖arcWindowL2 a b c (f-constL2 (arcMean f b c))‖^2≤384*B^2*(c-b) := by
  rw [norm_arcWindowL2_sub_const_sq a b c hab hc]
  exact arc_square_oscillation_le_of_meanOscillation_bound f B hB hMO b c hbc (by linarith)

/-- Literal localized weighted Cauchy integral, with ordinary circle integrability retained. -/
theorem cauchyWeightedHardyKernel_arcWindow_integral (a b c : ℝ) (hab : a≤b) (hc : c≤a+1)
    (f : BoundaryL2) (w : Disk) :
    Integrable (fun ζ => arcWindowL2 a b c f ζ*cauchyWeightedBoundaryKernel w ζ) circleMeasure ∧
    cauchyWeightedHardyKernel (arcWindowL2 a b c f) w.val=
      ∫ t in Ioc b c,f (t : Boundary)*cauchyWeightedBoundaryKernel w (t : Boundary) := by
  have h := cauchyWeightedHardyKernel_integral (arcWindowL2 a b c f) w
  exact ⟨h.1,h.2.trans (integral_arcWindowL2_mul a b c hab hc f _)⟩

/-- The literal real-arc Cauchy integrand is ordinarily integrable for every L² datum. -/
theorem integrableOn_cauchyWeightedBoundaryKernel (f : BoundaryL2) (w : Disk)
    (b c : ℝ) (hLen : c-b≤1) :
    IntegrableOn (fun t : ℝ => f (t : Boundary)*cauchyWeightedBoundaryKernel w (t : Boundary))
      (Ioc b c) := by
  have hp : MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ioc b (b+1))) circleMeasure := by
    rw [circleMeasure_eq_volume]
    exact AddCircle.measurePreserving_mk 1 b
  have hI := hp.integrable_comp_of_integrable (cauchyWeightedHardyKernel_integral f w).1
  have hJ : IntegrableOn
      (fun t : ℝ => f (t : Boundary)*cauchyWeightedBoundaryKernel w (t : Boundary))
        (Ioc b (b+1)) := hI
  exact hJ.mono_set (fun t ht => ⟨ht.1,ht.2.trans (by linarith)⟩)

end TTO.Paper.Proved
