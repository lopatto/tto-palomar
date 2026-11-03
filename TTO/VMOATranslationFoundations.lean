/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcL2OscillationFoundations
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-! Uniform literal arc-oscillation continuity of translations of VMOA data. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Translation of the actual Haar L² class by the real circle parameter s. -/
def circleTranslate (s : ℝ) (f : BoundaryL2) : BoundaryL2 :=
  DomAddAct.mk (s : Boundary) +ᵥ f

theorem circleTranslate_ae (s : ℝ) (f : BoundaryL2) :
    circleTranslate s f =ᵐ[circleMeasure] fun t => f (t+(s : Boundary)) := by
  filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (s : Boundary)) f] with t ht
  simpa only [circleTranslate,Equiv.symm_apply_apply,vadd_eq_add,add_comm] using ht

@[simp] theorem circleTranslate_zero (f : BoundaryL2) : circleTranslate 0 f=f := by
  simp [circleTranslate]

theorem norm_circleTranslate (s : ℝ) (f : BoundaryL2) : ‖circleTranslate s f‖=‖f‖ :=
  DomAddAct.norm_vadd_Lp _ _

theorem continuous_circleTranslate (f : BoundaryL2) :
    Continuous (fun s : ℝ => circleTranslate s f) := by
  have : Fact ((2 : ℝ≥0∞)≠∞) := ⟨by simp⟩
  have hc : Continuous (fun s : ℝ => (DomAddAct.mk (s : Boundary) : DomAddAct Boundary)) :=
    DomAddAct.continuous_mk.comp (by fun_prop)
  exact hc.vadd continuous_const

/-- Literal real-Ioc change of variables, including arcs crossing the circle origin. -/
theorem setIntegral_circle_lift_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Boundary → E) (a b s : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, F ((t+s : ℝ) : Boundary))=
      ∫ t : ℝ in Ioc (a+s) (b+s), F (t : Boundary) := by
  rw [← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le (by linarith : a+s≤b+s)]
  exact intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t : Boundary)) s

theorem arcMean_circleTranslate (f : BoundaryL2) (s a b : ℝ)
    (hab : a < b) (hLen : b-a≤1) :
    arcMean (circleTranslate s f) a b=arcMean f (a+s) (b+s) := by
  have he := circle_ae_lift_Ioc (circleTranslate_ae s f) a b hLen
  unfold arcMean
  rw [integral_congr_ae he]
  have hAdd : (fun t : ℝ => f ((t : Boundary)+(s : Boundary)))=
      fun t : ℝ => f ((t+s : ℝ) : Boundary) := by funext t; rw [AddCircle.coe_add]
  rw [hAdd,setIntegral_circle_lift_add f a b s hab.le]
  congr 1
  push_cast
  ring

theorem meanOscillation_circleTranslate (f : BoundaryL2) (s a b : ℝ)
    (hab : a < b) (hLen : b-a≤1) :
    meanOscillation (circleTranslate s f) a b=meanOscillation f (a+s) (b+s) := by
  have he := circle_ae_lift_Ioc (circleTranslate_ae s f) a b hLen
  unfold meanOscillation
  have hAE : (fun t : ℝ => ‖circleTranslate s f (t : Boundary)-
      arcMean (circleTranslate s f) a b‖)=ᵐ[volume.restrict (Ioc a b)]
      fun t : ℝ => ‖f ((t+s : ℝ) : Boundary)-arcMean f (a+s) (b+s)‖ := by
    filter_upwards [he] with t ht
    rw [ht,arcMean_circleTranslate f s a b hab hLen,AddCircle.coe_add]
  rw [integral_congr_ae hAE,setIntegral_circle_lift_add
    (fun t : Boundary => ‖f t-arcMean f (a+s) (b+s)‖) a b s hab.le]
  congr 1
  ring



/-- Literal VMO alone gives uniform small oscillation of actual translation differences.
No Hardy-invariance premise or replacement definition of VMO is used. -/
theorem uniform_meanOscillation_translation_of_vmo (f : BoundaryL2)
    (hVMO : ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧
      ∀ a b : ℝ, a<b → b-a≤min δ 1 → meanOscillation f a b<ε) :
    ∀ ε : ℝ, 0<ε → ∃ η : ℝ, 0<η ∧ ∀ s : ℝ, ‖s‖<η →
      ∀ a b : ℝ, a<b → b-a≤1 → meanOscillation (f-circleTranslate s f) a b<ε := by
  intro ε hε
  obtain ⟨δ,hδ,hSmall⟩ := hVMO (ε/4) (by linarith)
  let d := min δ 1
  have hd : 0<d := lt_min hδ zero_lt_one
  have hsqrt : 0<Real.sqrt d := Real.sqrt_pos.mpr hd
  have hc : Continuous (fun s : ℝ => ‖f-circleTranslate s f‖) :=
    (continuous_const.sub (continuous_circleTranslate f)).norm
  have hT : Tendsto (fun s : ℝ => ‖f-circleTranslate s f‖) (𝓝 0) (𝓝 0) := by
    simpa only [circleTranslate_zero,sub_self,norm_zero] using hc.continuousAt.tendsto (x := 0)
  have hNear := hT.eventually (gt_mem_nhds (by positivity : 0<ε*Real.sqrt d/4))
  obtain ⟨η,hη,hNear⟩ := Metric.eventually_nhds_iff.mp hNear
  refine ⟨η,hη,?_⟩
  intro s hs a b hab hLen
  have hNorm : ‖f-circleTranslate s f‖<ε*Real.sqrt d/4 := by
    exact hNear (by simpa only [dist_zero_right] using hs)
  by_cases hShort : b-a≤d
  · have hF := hSmall a b hab hShort
    have hG : meanOscillation (circleTranslate s f) a b<ε/4 := by
      rw [meanOscillation_circleTranslate f s a b hab hLen]
      apply hSmall (a+s) (b+s) (by linarith)
      change b+s-(a+s)≤d
      linarith
    have hNeg : meanOscillation (-circleTranslate s f) a b=
        meanOscillation (circleTranslate s f) a b := by
      simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using
        meanOscillation_smul (-1 : ℂ) (circleTranslate s f) a b hLen
    have hSum := meanOscillation_add_le f (-circleTranslate s f) a b hab hLen
    rw [hNeg] at hSum
    have hSum' : meanOscillation (f-circleTranslate s f) a b≤
        meanOscillation f a b+meanOscillation (circleTranslate s f) a b := by
      simpa only [sub_eq_add_neg] using hSum
    linarith
  · have hLong : d<b-a := lt_of_not_ge hShort
    have hSqrt : Real.sqrt d≤Real.sqrt (b-a) := Real.sqrt_le_sqrt hLong.le
    have hSqrtPos : 0<Real.sqrt (b-a) := hsqrt.trans_le hSqrt
    have hBound := meanOscillation_le_l2 (f-circleTranslate s f) a b hab hLen
    apply hBound.trans_lt
    apply (div_lt_iff₀ hSqrtPos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hSqrt hε.le]

theorem uniform_meanOscillation_translation (f : BoundaryL2) (hf : InVMOA f) :
    ∀ ε : ℝ, 0<ε → ∃ η : ℝ, 0<η ∧ ∀ s : ℝ, ‖s‖<η →
      ∀ a b : ℝ, a<b → b-a≤1 → meanOscillation (f-circleTranslate s f) a b<ε :=
  uniform_meanOscillation_translation_of_vmo f hf.2

end TTO.Paper.Proved
