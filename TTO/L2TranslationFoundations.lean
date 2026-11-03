/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HalfLinePWFoundations
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-! Actual L² translations and L¹-kernel Bochner convolution.
These constructions do not identify any source distribution with a convenient substitute. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

abbrev LineL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Right translation of the actual whole-line L² equivalence class. -/
def lineTranslate (s : ℝ) (f : LineL2) : LineL2 := DomAddAct.mk (-s) +ᵥ f

theorem lineTranslate_ae (s : ℝ) (f : LineL2) :
    lineTranslate s f =ᵐ[volume] fun t => f (t - s) := by
  filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-s)) f] with t ht
  simpa only [lineTranslate,Equiv.symm_apply_apply,vadd_eq_add,add_comm,sub_eq_add_neg] using ht

theorem norm_lineTranslate (s : ℝ) (f : LineL2) : ‖lineTranslate s f‖ = ‖f‖ :=
  DomAddAct.norm_vadd_Lp _ _

theorem continuous_lineTranslate (f : LineL2) : Continuous (fun s : ℝ => lineTranslate s f) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have hc : Continuous (fun s : ℝ => (DomAddAct.mk (-s) : DomAddAct ℝ)) :=
    DomAddAct.continuous_mk.comp continuous_neg
  exact hc.vadd continuous_const

/-- A scalar L¹ kernel gives a genuinely integrable L²-valued translation average. -/
theorem integrable_lineBochnerKernel (k : ℝ → ℂ) (hk : Integrable k) (f : LineL2) :
    Integrable (fun s : ℝ => k s • lineTranslate s f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.aestronglyMeasurable.smul (continuous_lineTranslate f).aestronglyMeasurable)
  exact Eventually.of_forall fun s => by
    change ‖k s • lineTranslate s f‖ ≤ ‖k s‖ * ‖f‖
    rw [norm_smul,norm_lineTranslate]

/-- L¹*L² convolution defined by its native Bochner integral in actual L². -/
def lineBochnerConvolution (k : ℝ → ℂ) (f : LineL2) : LineL2 :=
  ∫ s : ℝ, k s • lineTranslate s f

theorem norm_lineBochnerConvolution_le (k : ℝ → ℂ) (_hk : Integrable k) (f : LineL2) :
    ‖lineBochnerConvolution k f‖ ≤ (∫ s : ℝ, ‖k s‖) * ‖f‖ := by
  calc
    _ ≤ ∫ s : ℝ, ‖k s • lineTranslate s f‖ := norm_integral_le_integral_norm _
    _ = ∫ s : ℝ, ‖k s‖ * ‖f‖ := by simp only [norm_smul,norm_lineTranslate]
    _ = _ := integral_mul_const ‖f‖ _

/-- Every native L² continuous linear functional evaluates the actual convolution integral. -/
theorem lineBochnerConvolution_clm (k : ℝ → ℂ) (hk : Integrable k) (f : LineL2)
    (L : LineL2 →L[ℂ] ℂ) :
    L (lineBochnerConvolution k f) = ∫ s : ℝ, k s * L (lineTranslate s f) := by
  rw [lineBochnerConvolution,← L.integral_comp_comm (integrable_lineBochnerKernel k hk f)]
  simp only [map_smul,smul_eq_mul]

theorem inner_lineBochnerConvolution (k : ℝ → ℂ) (hk : Integrable k) (f b : LineL2) :
    inner ℂ b (lineBochnerConvolution k f) =
      ∫ s : ℝ, k s * inner ℂ b (lineTranslate s f) :=
  lineBochnerConvolution_clm k hk f (innerSL ℂ b)

/-- Native restriction of a whole-line L² vector to the positive half-line. -/
def restrictToHalfLine (f : LineL2) : HalfLineL2 :=
  ((Lp.memLp f).restrict (Ioi (0 : ℝ))).toLp f

theorem restrictToHalfLine_ae (f : LineL2) :
    restrictToHalfLine f =ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
  ((Lp.memLp f).restrict (Ioi (0 : ℝ))).coeFn_toLp

theorem norm_restrictToHalfLine_le (f : LineL2) : ‖restrictToHalfLine f‖ ≤ ‖f‖ := by
  rw [restrictToHalfLine,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne
    (eLpNorm_mono_measure f Measure.restrict_le_self)

theorem restrictToHalfLine_add (f g : LineL2) :
    restrictToHalfLine (f + g) = restrictToHalfLine f + restrictToHalfLine g := by
  apply Lp.ext
  filter_upwards [restrictToHalfLine_ae (f + g),restrictToHalfLine_ae f,restrictToHalfLine_ae g,
    ae_restrict_of_ae (Lp.coeFn_add f g),Lp.coeFn_add (restrictToHalfLine f) (restrictToHalfLine g)]
    with t hfg hf hg hadd hsum
  rw [hfg,hadd,hsum,Pi.add_apply,Pi.add_apply,hf,hg]

theorem restrictToHalfLine_smul (c : ℂ) (f : LineL2) :
    restrictToHalfLine (c • f) = c • restrictToHalfLine f := by
  apply Lp.ext
  filter_upwards [restrictToHalfLine_ae (c • f),restrictToHalfLine_ae f,
    ae_restrict_of_ae (Lp.coeFn_smul c f),Lp.coeFn_smul c (restrictToHalfLine f)]
    with t hcf hf hsm hsm'
  rw [hcf,hsm,hsm',Pi.smul_apply,Pi.smul_apply,hf]

/-- The actual restriction contraction, with an explicit transparent linear map. -/
def restrictHalfLineL : LineL2 →L[ℂ] HalfLineL2 :=
  ({ toFun := restrictToHalfLine
     map_add' := restrictToHalfLine_add
     map_smul' := restrictToHalfLine_smul } : LineL2 →ₗ[ℂ] HalfLineL2).mkContinuous 1
    (fun f => by simpa only [one_mul] using! norm_restrictToHalfLine_le f)

@[simp] theorem restrictHalfLineL_apply (f : LineL2) : restrictHalfLineL f = restrictToHalfLine f := rfl

/-- Actual zero extension, using an indicator rather than an assumption on arbitrary Lp representatives. -/
def zeroExtendHalfLine (f : HalfLineL2) : LineL2 :=
  ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr (Lp.memLp f)).toLp
    ((Ioi (0 : ℝ)).indicator f)

theorem zeroExtendHalfLine_ae (f : HalfLineL2) :
    zeroExtendHalfLine f =ᵐ[volume] (Ioi (0 : ℝ)).indicator f :=
  ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr (Lp.memLp f)).coeFn_toLp

theorem norm_zeroExtendHalfLine (f : HalfLineL2) : ‖zeroExtendHalfLine f‖ = ‖f‖ := by
  rw [zeroExtendHalfLine,Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict
    measurableSet_Ioi.nullMeasurableSet,Lp.norm_def]

theorem restrict_zeroExtendHalfLine (f : HalfLineL2) :
    restrictToHalfLine (zeroExtendHalfLine f) = f := by
  apply Lp.ext
  filter_upwards [restrictToHalfLine_ae (zeroExtendHalfLine f),
    ae_restrict_of_ae (zeroExtendHalfLine_ae f),ae_restrict_mem measurableSet_Ioi] with t hr he ht
  rw [hr,he,indicator_of_mem ht]

/-- Zero extension and native restriction have the actual L² adjoint pairing. -/
theorem inner_zeroExtend_restrict (g : HalfLineL2) (f : LineL2) :
    inner ℂ (zeroExtendHalfLine g) f = inner ℂ g (restrictToHalfLine f) := by
  rw [L2.inner_def,L2.inner_def]
  have he : (∫ t : ℝ, inner ℂ ((zeroExtendHalfLine g) t) (f t)) =
      ∫ t : ℝ, (Ioi (0 : ℝ)).indicator (fun t => inner ℂ (g t) (f t)) t := by
    apply integral_congr_ae
    filter_upwards [zeroExtendHalfLine_ae g] with t ht
    rw [ht]
    by_cases hti : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hti,indicator_of_mem hti]
    · rw [indicator_of_notMem hti,indicator_of_notMem hti,inner_zero_left]
  rw [he,integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [restrictToHalfLine_ae f] with t ht
  rw [ht]

/-- Literal Laplace translation after actual zero extension and restriction. -/
theorem halfLine_translate_laplace (s : ℝ) (hs : 0 ≤ s) (g : HalfLineL2) (w : ℂ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) *
        (restrictToHalfLine (lineTranslate s (zeroExtendHalfLine g))) t) =
      Complex.exp ((s : ℂ) * w * Complex.I) *
        ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * g t := by
  have hmp : MeasurePreserving (fun t : ℝ => t - s) volume volume := by
    simpa only [vadd_eq_add,sub_eq_add_neg,add_comm] using
      (measurePreserving_vadd (-s) (volume : Measure ℝ))
  have hExt := hmp.quasiMeasurePreserving.ae (zeroExtendHalfLine_ae g)
  have hR := (ae_restrict_iff' measurableSet_Ioi).mp
    (restrictToHalfLine_ae (lineTranslate s (zeroExtendHalfLine g)))
  have heq :
      (fun t : ℝ => (Ioi (0 : ℝ)).indicator
        (fun t => Complex.exp ((t : ℂ) * w * Complex.I) *
          (restrictToHalfLine (lineTranslate s (zeroExtendHalfLine g))) t) t) =ᵐ[volume]
      (fun t : ℝ => Complex.exp ((s : ℂ) * w * Complex.I) *
        ((Ioi (0 : ℝ)).indicator
          (fun y => Complex.exp ((y : ℂ) * w * Complex.I) * g y)) (t - s)) := by
    filter_upwards [hExt,hR,lineTranslate_ae s (zeroExtendHalfLine g)] with t he hr htr
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht,hr ht,htr,he]
      by_cases hts : t - s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hts,indicator_of_mem hts,← mul_assoc,← Complex.exp_add]
        congr 2
        push_cast
        ring
      · rw [indicator_of_notMem hts,indicator_of_notMem hts,mul_zero,mul_zero]
    · have hts : t - s ∉ Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi,not_lt] at ht ⊢
        linarith
      rw [indicator_of_notMem ht,indicator_of_notMem hts,mul_zero]
  calc
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator
        (fun t => Complex.exp ((t : ℂ) * w * Complex.I) *
          (restrictToHalfLine (lineTranslate s (zeroExtendHalfLine g))) t) t :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ t : ℝ, Complex.exp ((s : ℂ) * w * Complex.I) *
        ((Ioi (0 : ℝ)).indicator
          (fun y => Complex.exp ((y : ℂ) * w * Complex.I) * g y)) (t - s) :=
      integral_congr_ae heq
    _ = Complex.exp ((s : ℂ) * w * Complex.I) *
        ∫ t : ℝ, ((Ioi (0 : ℝ)).indicator
          (fun y => Complex.exp ((y : ℂ) * w * Complex.I) * g y)) (t - s) :=
      integral_const_mul _ _
    _ = _ := by rw [integral_sub_right_eq_self,integral_indicator measurableSet_Ioi]

/-- The actual shifted half-line vector has the expected analytic multiplication factor. -/
theorem analyticValue_halfLine_translate (s : ℝ) (hs : 0 ≤ s) (g : HalfLineL2)
    (w : ℂ) (hw : 0 < w.im) :
    analyticValue (halfLinePWEquiv (restrictToHalfLine (lineTranslate s (zeroExtendHalfLine g)))).val
      (upperCayley w) =
      Complex.exp ((s : ℂ) * w * Complex.I) *
        analyticValue (halfLinePWEquiv g).val (upperCayley w) := by
  rw [analyticValue_halfLinePWEquiv _ w hw,halfLine_translate_laplace s hs g w,
    analyticValue_halfLinePWEquiv g w hw]
  ring

/-- A genuine L² convolution vector on the half-line, obtained by actual restriction. -/
def causalBochnerConvolution (k : ℝ → ℂ) (g : HalfLineL2) : HalfLineL2 :=
  restrictToHalfLine (lineBochnerConvolution k (zeroExtendHalfLine g))

theorem analyticValue_causalBochnerConvolution (k : ℝ → ℂ) (hk : Integrable k)
    (hk0 : ∀ s : ℝ, s ≤ 0 → k s = 0) (g : HalfLineL2) (w : ℂ) (hw : 0 < w.im) :
    analyticValue (halfLinePWEquiv (causalBochnerConvolution k g)).val (upperCayley w) =
      analyticValue (halfLinePWEquiv g).val (upperCayley w) *
        ∫ s in Ioi (0 : ℝ), Complex.exp ((s : ℂ) * w * Complex.I) * k s := by
  let L : LineL2 →L[ℂ] ℂ := (innerSL ℂ (halfLineEvalKernel w hw)).comp restrictHalfLineL
  have hL (f : LineL2) : L f =
      analyticValue (halfLinePWEquiv (restrictToHalfLine f)).val (upperCayley w) := by
    change inner ℂ (halfLineEvalKernel w hw) (restrictToHalfLine f) = _
    rw [inner_halfLineEvalKernel,analyticValue_halfLinePWEquiv _ w hw]
  calc
    _ = L (lineBochnerConvolution k (zeroExtendHalfLine g)) :=
      (hL _).symm
    _ = ∫ s : ℝ, k s * L (lineTranslate s (zeroExtendHalfLine g)) :=
      lineBochnerConvolution_clm k hk _ L
    _ = ∫ s in Ioi (0 : ℝ), k s *
        (Complex.exp ((s : ℂ) * w * Complex.I) *
          analyticValue (halfLinePWEquiv g).val (upperCayley w)) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        by_cases hs : s ∈ Ioi (0 : ℝ)
        · simp only [indicator_of_mem hs]
          rw [hL,analyticValue_halfLine_translate s hs.le g w hw]
        · simp only [indicator_of_notMem hs,hk0 s (le_of_not_gt hs),zero_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by ring

/-- Actual bounded-core multiplication has the product of the original Hardy analytic values. -/
theorem analyticValue_coreMultiply (φ f : Hardy) (hf : IsBounded f.val)
    {z : ℂ} (hz : z ∈ disk) :
    analyticValue (coreMultiply φ.val ⟨f.val,hf⟩) z =
      analyticValue φ.val z * analyticValue f.val z := by
  let b : BoundaryLInf := hf.toLp f.val
  have he : toL2 b = f.val := Lp.ext ((toL2_ae b).trans hf.coeFn_toLp)
  have hb : toL2 b ∈ hardy := he.symm ▸ f.property
  change analyticValue (multiply b φ.val) z = _
  rw [analyticValue_multiply b hb φ ⟨z,hz⟩]
  change analyticValue (toL2 b) z * analyticValue φ.val z = _
  rw [he,mul_comm]

theorem IntervalSmoothCompact.eq_zero_of_not_mem {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) {s : ℝ} (hs : s ∉ Ioo (0 : ℝ) ℓ) : a s = 0 := by
  by_contra hn
  exact hs (ha.2.2 (subset_tsupport a hn))

/-- The exact derivative-corrected compact test kernel in the causal Fourier calculation. -/
def pwTestDerivative (a : ℝ → ℂ) (s : ℝ) : ℂ := deriv a s + a s

theorem pwTestDerivative_zero_of_not_mem {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) {s : ℝ} (hs : s ∉ Ioo (0 : ℝ) ℓ) :
    pwTestDerivative a s = 0 := by
  rw [pwTestDerivative,deriv_of_notMem_tsupport (fun h => hs (ha.2.2 h)),
    ha.eq_zero_of_not_mem hs,add_zero]

theorem integrable_pwTestDerivative {ℓ : ℝ} {a : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) :
    Integrable (pwTestDerivative a) := by
  exact ((ha.1.continuous_deriv (by simp)).add ha.1.continuous).integrable_of_hasCompactSupport
    (ha.2.1.deriv.add ha.2.1)

theorem integral_pwTestDerivative_Ioi {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (w : ℂ) :
    (∫ s in Ioi (0 : ℝ), Complex.exp ((s : ℂ) * w * Complex.I) * pwTestDerivative a s) =
      ∫ s in Ioo (0 : ℝ) ℓ, Complex.exp ((s : ℂ) * w * Complex.I) * pwTestDerivative a s := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    by_cases hs : s ∈ Ioo (0 : ℝ) ℓ
    · have hs0 : s ∈ Ioi (0 : ℝ) := hs.1
      rw [indicator_of_mem hs0,indicator_of_mem hs]
    · by_cases hp : s ∈ Ioi (0 : ℝ)
      · simp only [indicator_of_mem hp,indicator_of_notMem hs,pwTestDerivative_zero_of_not_mem ha hs,mul_zero]
      · rw [indicator_of_notMem hp,indicator_of_notMem hs]

/-- Direct causal Hardy product identity. It is derived from the actual PW maps,
native translation and Bochner integration, without asserting a boundary-distribution identification. -/
theorem coreMultiply_pwTest_eq_halfLineConvolution (ℓ : ℝ) (hℓ : 0 < ℓ)
    (u : BoundaryLInf) (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u)
    (hU : PaleyWienerUnitary u ℓ U) (φ : Hardy) (a : ℝ → ℂ)
    (ha : IntervalSmoothCompact ℓ a) :
    coreMultiply φ.val
        ⟨(U (smoothIntervalL2 ℓ a ha)).val,bounded_paleyWiener_smoothCompact ℓ hℓ u U hU a ha⟩ =
      (halfLinePWEquiv
        ((Complex.I / (Real.sqrt 2 : ℂ)) •
          causalBochnerConvolution (pwTestDerivative a) (halfLinePWEquiv.symm φ))).val := by
  let b : Hardy := ⟨(U (smoothIntervalL2 ℓ a ha)).val,(U (smoothIntervalL2 ℓ a ha)).property.1⟩
  have hb : IsBounded b.val := bounded_paleyWiener_smoothCompact ℓ hℓ u U hU a ha
  let g : HalfLineL2 := halfLinePWEquiv.symm φ
  let c : ℂ := Complex.I / (Real.sqrt 2 : ℂ)
  let h : HalfLineL2 := c • causalBochnerConvolution (pwTestDerivative a) g
  have hh : coreMultiply φ.val ⟨b.val,hb⟩ ∈ hardy := coreMultiply_mem_hardy φ b hb
  have he : (⟨coreMultiply φ.val ⟨b.val,hb⟩,hh⟩ : Hardy) = halfLinePWEquiv h := by
    apply hardy_analyticValue_injective
    intro z hz
    obtain ⟨w,hwz⟩ := upperCayleyDisk_surjective ⟨z,hz⟩
    have hwz' : upperCayley w.val = z := congrArg Subtype.val hwz
    change analyticValue (coreMultiply φ.val ⟨b.val,hb⟩) z = analyticValue (halfLinePWEquiv h).val z
    rw [← hwz']
    have h0 : a 0 = 0 := ha.eq_zero_of_not_mem (by simp)
    have hEnd : a ℓ = 0 := ha.eq_zero_of_not_mem (by simp)
    have hbval : analyticValue b.val (upperCayley w.val) =
        c * ∫ t in Ioo (0 : ℝ) ℓ,
          Complex.exp ((t : ℂ) * w.val * Complex.I) * pwTestDerivative a t :=
      paleyWiener_eval_C1 ℓ hℓ u U hU a (deriv a) ha.1.continuous.continuousOn
        (ha.1.continuous_deriv (by simp)).continuousOn
        (fun t _ => ((ha.1.differentiable (by simp)) t).hasDerivAt) h0 hEnd _
        (smoothIntervalL2_ae ℓ a ha) w.val w.property
    have hsm : analyticValue (halfLinePWEquiv h).val (upperCayley w.val) =
        c * analyticValue (halfLinePWEquiv (causalBochnerConvolution (pwTestDerivative a) g)).val
          (upperCayley w.val) := by
      dsimp only [h]
      rw [map_smul]
      change analyticValue (c • (halfLinePWEquiv (causalBochnerConvolution (pwTestDerivative a) g)).val)
        (upperCayley w.val) = _
      exact analyticValue_smul c _ (upperCayley_mem_disk w.val w.property)
    have hk0 : ∀ s : ℝ, s ≤ 0 → pwTestDerivative a s = 0 := by
      intro s hs
      exact pwTestDerivative_zero_of_not_mem ha (fun ht => (not_lt_of_ge hs) ht.1)
    rw [analyticValue_coreMultiply φ b hb (upperCayley_mem_disk w.val w.property),
      hbval,hsm,analyticValue_causalBochnerConvolution (pwTestDerivative a)
        (integrable_pwTestDerivative ha) hk0 g w.val w.property,
      integral_pwTestDerivative_Ioi ha]
    have hg : halfLinePWEquiv g = φ := halfLinePWEquiv.apply_symm_apply φ
    rw [hg]
    ring
  exact congrArg Subtype.val he

/-- A literal compact smooth test, now as a native half-line L² class. -/
def smoothHalfLineL2 {ℓ : ℝ} (a : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) : HalfLineL2 :=
  (show MemLp a 2 (volume.restrict (Ioi (0 : ℝ))) from
    ha.1.continuous.memLp_of_hasCompactSupport ha.2.1).toLp a

theorem smoothHalfLineL2_ae {ℓ : ℝ} (a : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) :
    smoothHalfLineL2 a ha =ᵐ[volume.restrict (Ioi (0 : ℝ))] a :=
  (show MemLp a 2 (volume.restrict (Ioi (0 : ℝ))) from
    ha.1.continuous.memLp_of_hasCompactSupport ha.2.1).coeFn_toLp

theorem integral_pwTest_Ioi {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (w : ℂ) :
    (∫ s in Ioi (0 : ℝ), Complex.exp ((s : ℂ) * w * Complex.I) * a s) =
      ∫ s in Ioo (0 : ℝ) ℓ, Complex.exp ((s : ℂ) * w * Complex.I) * a s := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    by_cases hs : s ∈ Ioo (0 : ℝ) ℓ
    · have hs0 : s ∈ Ioi (0 : ℝ) := hs.1
      rw [indicator_of_mem hs0,indicator_of_mem hs]
    · by_cases hp : s ∈ Ioi (0 : ℝ)
      · simp only [indicator_of_mem hp,indicator_of_notMem hs,ha.eq_zero_of_not_mem hs,mul_zero]
      · rw [indicator_of_notMem hp,indicator_of_notMem hs]

/-- The finite-interval and half-line constructions agree on each actual compact test;
they are not identified by replacing either unitary's definition. -/
theorem halfLinePWEquiv_smooth_test (ℓ : ℝ) (_hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (a : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) :
    (halfLinePWEquiv (smoothHalfLineL2 a ha)).val = (U (smoothIntervalL2 ℓ a ha)).val := by
  have he : halfLinePWEquiv (smoothHalfLineL2 a ha) =
      (⟨(U (smoothIntervalL2 ℓ a ha)).val,(U (smoothIntervalL2 ℓ a ha)).property.1⟩ : Hardy) := by
    apply hardy_analyticValue_injective
    intro z hz
    obtain ⟨w,hwz⟩ := upperCayleyDisk_surjective ⟨z,hz⟩
    have hwz' : upperCayley w.val = z := congrArg Subtype.val hwz
    change analyticValue (halfLinePWEquiv (smoothHalfLineL2 a ha)).val z =
      analyticValue (U (smoothIntervalL2 ℓ a ha)).val z
    rw [← hwz',analyticValue_halfLinePWEquiv _ w.val w.property,
      paleyWienerUnitary_eval ℓ u U hU _ w.val w.property,inner_intervalEvalKernel]
    have hi : (∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w.val * Complex.I) *
        (smoothHalfLineL2 a ha) t) =
        ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w.val * Complex.I) * a t := by
      apply integral_congr_ae
      filter_upwards [smoothHalfLineL2_ae a ha] with t ht
      rw [ht]
    have hf : (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w.val * Complex.I) *
        (smoothIntervalL2 ℓ a ha) t) =
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w.val * Complex.I) * a t := by
      apply integral_congr_ae
      filter_upwards [smoothIntervalL2_ae ℓ a ha] with t ht
      rw [ht]
    rw [hi,hf,integral_pwTest_Ioi ha]
  exact congrArg Subtype.val he

/-- An exact direct PW core-form formula, with a genuine L² translation pairing.
The subsequent correlation/Fubini reformulation is a separate obligation. -/
theorem coreForm_pwTests_bochner (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
    (hb : IntervalSmoothCompact ℓ b) :
    coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ s : ℝ, pwTestDerivative a s *
          inner ℂ (zeroExtendHalfLine (smoothHalfLineL2 b hb))
            (lineTranslate s (zeroExtendHalfLine (halfLinePWEquiv.symm φ))) := by
  rw [coreForm_eq_inner_left _ _ _ (bounded_paleyWiener_smoothCompact ℓ hℓ u U hU a ha)]
  change inner ℂ (U (smoothIntervalL2 ℓ b hb)).val
    (coreMultiply φ.val
      ⟨(U (smoothIntervalL2 ℓ a ha)).val,bounded_paleyWiener_smoothCompact ℓ hℓ u U hU a ha⟩) = _
  rw [coreMultiply_pwTest_eq_halfLineConvolution ℓ hℓ u U hU φ a ha,
    ← halfLinePWEquiv_smooth_test ℓ hℓ u U hU b hb]
  change inner ℂ (halfLinePWEquiv (smoothHalfLineL2 b hb))
    (halfLinePWEquiv ((Complex.I / (Real.sqrt 2 : ℂ)) •
      causalBochnerConvolution (pwTestDerivative a) (halfLinePWEquiv.symm φ))) = _
  rw [halfLinePWEquiv.inner_map_map,inner_smul_right]
  congr 1
  rw [causalBochnerConvolution,← inner_zeroExtend_restrict,
    inner_lineBochnerConvolution (pwTestDerivative a) (integrable_pwTestDerivative ha)]

/-- Cauchy--Schwarz for the actual absolute product of two whole-line L² representatives. -/
theorem lineL2_normPairIntegral_le (f g : LineL2) :
    (∫ t : ℝ, ‖f t‖ * ‖g t‖) ≤ ‖f‖ * ‖g‖ := by
  let F : Lp ℝ 2 (volume : Measure ℝ) := (Lp.memLp f).norm.toLp (fun t => ‖f t‖)
  let G : Lp ℝ 2 (volume : Measure ℝ) := (Lp.memLp g).norm.toLp (fun t => ‖g t‖)
  have hFn : ‖F‖ = ‖f‖ := by
    dsimp only [F]
    rw [Lp.norm_toLp,eLpNorm_norm f (Lp.aestronglyMeasurable f)]
    rfl
  have hGn : ‖G‖ = ‖g‖ := by
    dsimp only [G]
    rw [Lp.norm_toLp,eLpNorm_norm g (Lp.aestronglyMeasurable g)]
    rfl
  have hFa : F =ᵐ[volume] fun t => ‖f t‖ := (Lp.memLp f).norm.coeFn_toLp
  have hGa : G =ᵐ[volume] fun t => ‖g t‖ := (Lp.memLp g).norm.coeFn_toLp
  have he : inner ℝ F G = ∫ t : ℝ, ‖f t‖ * ‖g t‖ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hFa,hGa] with t hf hg
    simp only [hf,hg,RCLike.inner_apply,starRingEnd_apply,star_trivial,mul_comm]
  rw [← he,← hFn,← hGn]
  exact real_inner_le_norm F G

theorem inner_lineTranslate_integral (s : ℝ) (f b : LineL2) :
    inner ℂ b (lineTranslate s f) = ∫ t : ℝ, f t * conj (b (t + s)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ t : ℝ, conj (b t) * f (t - s) := by
      apply integral_congr_ae
      filter_upwards [lineTranslate_ae s f] with t ht
      rw [ht,RCLike.inner_apply]
      ring
    _ = ∫ t : ℝ, (fun r : ℝ => f r * conj (b (r + s))) (t - s) := by
      congr 1
      funext t
      simp only [sub_add_cancel,mul_comm]
    _ = _ := by
      simpa only using! (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
        (fun r : ℝ => f r * conj (b (r + s))) s)

/-- Absolute Fubini integrability of the actual L¹-kernel/L²/L² pairing integrand. -/
theorem integrable_lineBochner_pairing (k : ℝ → ℂ) (hk : Integrable k) (f b : LineL2) :
    Integrable (fun p : ℝ × ℝ => k p.1 * (f p.2 * conj (b (p.2 + p.1)))) (volume.prod volume) := by
  have hba : AEStronglyMeasurable (fun p : ℝ × ℝ => b (p.2 + p.1)) (volume.prod volume) :=
    (Lp.aestronglyMeasurable b).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add_swap (volume : Measure ℝ) volume)
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => k p.1 * (f p.2 * conj (b (p.2 + p.1)))) (volume.prod volume) :=
    hk.aestronglyMeasurable.comp_fst.mul ((Lp.aestronglyMeasurable f).comp_snd.mul hba.star)
  have hint (s : ℝ) : Integrable (fun t : ℝ => k s * (f t * conj (b (t + s)))) := by
    apply ((L2.integrable_inner (lineTranslate (-s) b) f).const_mul (k s)).congr
    filter_upwards [lineTranslate_ae (-s) b] with t ht
    simp only [RCLike.inner_apply,ht,sub_neg_eq_add]
  have hbound (s : ℝ) : (∫ t : ℝ, ‖k s * (f t * conj (b (t + s)))‖) ≤
      ‖k s‖ * (‖f‖ * ‖b‖) := by
    calc
      _ = ‖k s‖ * ∫ t : ℝ, ‖f t‖ * ‖(lineTranslate (-s) b) t‖ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [lineTranslate_ae (-s) b] with t ht
        simp only [ht,sub_neg_eq_add,norm_mul,Complex.norm_conj]
      _ ≤ ‖k s‖ * (‖f‖ * ‖lineTranslate (-s) b‖) :=
        mul_le_mul_of_nonneg_left (lineL2_normPairIntegral_le f (lineTranslate (-s) b)) (norm_nonneg _)
      _ = _ := by rw [norm_lineTranslate]
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall hint,?_⟩
  apply (hk.norm.mul_const (‖f‖ * ‖b‖)).mono' hm.norm.integral_prod_right'
  exact Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hbound s

/-- A checked Fubini formula for the actual Bochner convolution pairing. -/
theorem inner_lineBochnerConvolution_fubini (k : ℝ → ℂ) (hk : Integrable k) (f b : LineL2) :
    inner ℂ b (lineBochnerConvolution k f) =
      ∫ t : ℝ, f t * ∫ s : ℝ, k s * conj (b (t + s)) := by
  rw [inner_lineBochnerConvolution k hk f b]
  calc
    _ = ∫ s : ℝ, ∫ t : ℝ, k s * (f t * conj (b (t + s))) := by
      simp only [inner_lineTranslate_integral,integral_const_mul]
    _ = ∫ t : ℝ, ∫ s : ℝ, k s * (f t * conj (b (t + s))) :=
      integral_integral_swap (integrable_lineBochner_pairing k hk f b)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change (∫ s : ℝ, k s * (f t * conj (b (t + s)))) =
          f t * ∫ s : ℝ, k s * conj (b (t + s))
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by ring

/-- A compact interval test has its literal original function as its whole-line zero extension. -/
theorem zeroExtend_smoothHalfLineL2_ae {ℓ : ℝ} (b : ℝ → ℂ) (hb : IntervalSmoothCompact ℓ b) :
    zeroExtendHalfLine (smoothHalfLineL2 b hb) =ᵐ[volume] b := by
  filter_upwards [zeroExtendHalfLine_ae (smoothHalfLineL2 b hb),
    (ae_restrict_iff' measurableSet_Ioi).mp (smoothHalfLineL2_ae b hb)] with t he hb'
  rw [he]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht,hb' ht]
  · rw [indicator_of_notMem ht,hb.eq_zero_of_not_mem (fun h => ht h.1)]

/-- The direct original core form has a literal scalar integral, with checked absolute Fubini. -/
theorem coreForm_pwTests_scalar (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
    (hb : IntervalSmoothCompact ℓ b) :
    coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t in Ioi (0 : ℝ), (halfLinePWEquiv.symm φ) t *
          ∫ s : ℝ, pwTestDerivative a s * conj (b (s + t)) := by
  rw [coreForm_pwTests_bochner ℓ hℓ u U hU φ a b ha hb]
  congr 1
  rw [← inner_lineBochnerConvolution (pwTestDerivative a) (integrable_pwTestDerivative ha),
    inner_lineBochnerConvolution_fubini (pwTestDerivative a) (integrable_pwTestDerivative ha)]
  have hInner (t : ℝ) :
      (∫ s : ℝ, pwTestDerivative a s * conj ((zeroExtendHalfLine (smoothHalfLineL2 b hb)) (t + s))) =
        ∫ s : ℝ, pwTestDerivative a s * conj (b (s + t)) := by
    have hPull := (measurePreserving_vadd t (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (zeroExtend_smoothHalfLineL2_ae b hb)
    apply integral_congr_ae
    filter_upwards [hPull] with s hs
    have hs' : (zeroExtendHalfLine (smoothHalfLineL2 b hb)) (t + s) = b (t + s) := by
      simpa only [vadd_eq_add] using hs
    rw [hs',add_comm t s]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [zeroExtendHalfLine_ae (halfLinePWEquiv.symm φ)] with t ht
  rw [ht,hInner t]
  by_cases hti : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hti,indicator_of_mem hti]
  · rw [indicator_of_notMem hti,indicator_of_notMem hti,zero_mul]

/-- The manuscript's literal compact-test correlation a⋆b. -/
def pwCorrelation (a b : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ, a s * conj (b (s + t))

theorem pwCorrelation_eq_convolution (a b : ℝ → ℂ) :
    pwCorrelation a b =
      convolution (fun s : ℝ => a (-s)) (fun s : ℝ => conj (b s))
        (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext t
  rw [convolution_def]
  change (∫ s : ℝ, a s * conj (b (s + t))) = ∫ s : ℝ, a (-s) * conj (b (t - s))
  symm
  calc
    _ = ∫ s : ℝ, (fun r : ℝ => a r * conj (b (r + t))) (-s) := by
      congr 1
      funext s
      rw [sub_eq_add_neg,add_comm t (-s)]
    _ = _ := by
      simpa only using! (integral_neg_eq_self (fun r : ℝ => a r * conj (b (r + t)))
        (volume : Measure ℝ))

/-- Differentiating the reflected left factor gives precisely the source correlation sign. -/
theorem hasDerivAt_pwCorrelation_left {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) (t : ℝ) :
    HasDerivAt (pwCorrelation a b) (-(∫ s : ℝ, deriv a s * conj (b (s + t)))) t := by
  have hcf : HasCompactSupport (fun s : ℝ => a (-s)) :=
    ha.2.1.comp_homeomorph (Homeomorph.neg ℝ)
  have hca : ContDiff ℝ 1 (fun s : ℝ => a (-s)) :=
    (ha.1.of_le (by simp)).comp contDiff_neg
  have hcb : Continuous (fun s : ℝ => conj (b s)) := hb.1.continuous.star
  have hdref : deriv (fun s : ℝ => a (-s)) = fun s : ℝ => -(deriv a (-s)) := by
    funext s
    have hd := (((ha.1.differentiable (by simp)) (-s)).hasDerivAt).scomp s (hasDerivAt_neg s)
    simpa only [Function.comp_def,neg_smul,one_smul] using! hd.deriv
  have hd := hcf.hasDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (μ := (volume : Measure ℝ)) hca hcb.locallyIntegrable t
  have hv : convolution (deriv (fun s : ℝ => a (-s))) (fun s : ℝ => conj (b s))
      (ContinuousLinearMap.mul ℝ ℂ) volume t =
      -(∫ s : ℝ, deriv a s * conj (b (s + t))) := by
    rw [hdref,convolution_def]
    change (∫ s : ℝ, -(deriv a (-s)) * conj (b (t - s))) = _
    simp_rw [neg_mul,integral_neg]
    congr 1
    have he := congrFun (pwCorrelation_eq_convolution (deriv a) b) t
    exact he.symm
  rw [← pwCorrelation_eq_convolution a b,hv] at hd
  exact hd

theorem deriv_pwCorrelation_left {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) (t : ℝ) :
    deriv (pwCorrelation a b) t = -(∫ s : ℝ, deriv a s * conj (b (s + t))) :=
  (hasDerivAt_pwCorrelation_left ha hb t).deriv

theorem integral_pwTestDerivative_correlation {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) (t : ℝ) :
    (∫ s : ℝ, pwTestDerivative a s * conj (b (s + t))) =
      -deriv (pwCorrelation a b) t + pwCorrelation a b t := by
  have hbc : Continuous (fun s : ℝ => conj (b (s + t))) :=
    (hb.1.continuous.comp (continuous_id.add_const t)).star
  have hi' : Integrable (fun s : ℝ => deriv a s * conj (b (s + t))) :=
    ((ha.1.continuous_deriv (by simp)).mul hbc).integrable_of_hasCompactSupport ha.2.1.deriv.mul_right
  have hi : Integrable (fun s : ℝ => a s * conj (b (s + t))) :=
    (ha.1.continuous.mul hbc).integrable_of_hasCompactSupport ha.2.1.mul_right
  simp_rw [pwTestDerivative,add_mul]
  rw [integral_add hi' hi,deriv_pwCorrelation_left ha hb t,pwCorrelation,neg_neg]

/-- The original compact-test form is the causal derivative action on the literal source correlation.
No assertion equating a convenient distribution definition with a Cayley boundary distribution is made. -/
theorem coreForm_pwTests_correlation (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
    (hb : IntervalSmoothCompact ℓ b) :
    coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t in Ioi (0 : ℝ), (halfLinePWEquiv.symm φ) t *
          (-deriv (pwCorrelation a b) t + pwCorrelation a b t) := by
  rw [coreForm_pwTests_scalar ℓ hℓ u U hU φ a b ha hb]
  simp_rw [integral_pwTestDerivative_correlation ha hb]

end TTO.Paper.Proved
