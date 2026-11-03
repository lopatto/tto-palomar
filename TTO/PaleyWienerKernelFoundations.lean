/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Portions of the interval Parseval uniqueness argument: Copyright (c) 2026 The Tau Ceti contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticLiftFoundations
public import TTO.SingleAtomConstruction
public import TTO.VolterraFoundations
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Literal interval evaluation kernels for the manuscript's normalized Cayley/Fourier--Laplace map. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The vector representing the exact normalized disk evaluation prescribed by PaleyWienerUnitary. -/
def intervalEvalFunction (w : ℂ) (t : ℝ) : ℂ :=
  (conj w - Complex.I) / (Real.sqrt 2 : ℂ) * Complex.exp (-(t : ℂ) * conj w * Complex.I)

theorem memLp_intervalEvalFunction (ℓ : ℝ) (w : ℂ) (hw : 0 < w.im) :
    MemLp (intervalEvalFunction w) 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  apply MemLp.of_bound (by unfold intervalEvalFunction; fun_prop)
    ‖(conj w - Complex.I) / (Real.sqrt 2 : ℂ)‖
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [intervalEvalFunction, norm_mul, Complex.norm_exp]
  have he : (-(t : ℂ) * conj w * Complex.I).re = -t * w.im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, neg_zero, zero_mul, mul_zero, sub_zero, zero_sub, mul_one]
    ring
  rw [he]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (by nlinarith [ht.1])

def intervalEvalKernel (ℓ : ℝ) (w : ℂ) (hw : 0 < w.im) : IntervalL2 ℓ :=
  (memLp_intervalEvalFunction ℓ w hw).toLp (intervalEvalFunction w)

theorem intervalEvalKernel_ae (ℓ : ℝ) (w : ℂ) (hw : 0 < w.im) :
    intervalEvalKernel ℓ w hw =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] intervalEvalFunction w :=
  (memLp_intervalEvalFunction ℓ w hw).coeFn_toLp

/-- The coefficient is exactly (w+i)/sqrt(2); this fixes the normalization before constructing a unitary. -/
theorem inner_intervalEvalKernel (ℓ : ℝ) (w : ℂ) (hw : 0 < w.im) (f : IntervalL2 ℓ) :
    inner ℂ (intervalEvalKernel ℓ w hw) f =
      (w + Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [intervalEvalKernel_ae ℓ w hw] with t ht
  rw [ht]
  have hc : conj ((conj w - Complex.I) / (Real.sqrt 2 : ℂ)) =
      (w + Complex.I) / (Real.sqrt 2 : ℂ) := by simp
  have he : conj (Complex.exp (-(t : ℂ) * conj w * Complex.I)) =
      Complex.exp ((t : ℂ) * w * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [RCLike.inner_apply]
  dsimp only [intervalEvalFunction]
  rw [map_mul, hc, he]
  ring

/-- The exact Gram formula for the literal normalized interval evaluation vectors. -/
theorem inner_intervalEvalKernel_gram (ℓ : ℝ) (hℓ : 0 < ℓ)
    (w v : ℂ) (hw : 0 < w.im) (hv : 0 < v.im) :
    inner ℂ (intervalEvalKernel ℓ w hw) (intervalEvalKernel ℓ v hv) =
      ((w + Complex.I) * (conj v - Complex.I) / 2) *
        ((Complex.exp ((ℓ : ℂ) * (w - conj v) * Complex.I) - 1) /
          ((w - conj v) * Complex.I)) := by
  let c : ℂ := (w - conj v) * Complex.I
  have hd : w - conj v ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hc : c ≠ 0 := mul_ne_zero hd Complex.I_ne_zero
  have hInt : (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp (c * (t : ℂ))) =
      (Complex.exp ((ℓ : ℂ) * (w - conj v) * Complex.I) - 1) / c := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ.le,
      integral_exp_mul_complex hc]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    congr 2
    dsimp [c]
    ring_nf
  rw [inner_intervalEvalKernel]
  have heq : (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) *
      (intervalEvalKernel ℓ v hv) t) =
      (conj v - Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp (c * (t : ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [intervalEvalKernel_ae ℓ v hv] with t ht
    rw [ht, intervalEvalFunction, mul_left_comm, ← Complex.exp_add]
    congr 2
    dsimp [c]
    ring
  rw [heq, hInt, ← mul_assoc, div_mul_div_comm]
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs]

/-- The exact Cayley map used by the PaleyWienerUnitary contract. -/
def upperCayley (w : ℂ) : ℂ := (w - Complex.I) / (w + Complex.I)

theorem upperCayley_den_ne_zero (w : ℂ) (hw : 0 < w.im) : w + Complex.I ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem upperCayley_mem_disk (w : ℂ) (hw : 0 < w.im) : upperCayley w ∈ disk := by
  have hden := upperCayley_den_ne_zero w hw
  change ‖(w - Complex.I) / (w + Complex.I)‖ < 1
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
  nlinarith

def upperCayleyDisk (w : ℂ) (hw : 0 < w.im) : Disk := ⟨upperCayley w, upperCayley_mem_disk w hw⟩

theorem one_sub_upperCayley (w : ℂ) (hw : 0 < w.im) :
    1 - upperCayley w = 2 * Complex.I / (w + Complex.I) := by
  unfold upperCayley
  field_simp [upperCayley_den_ne_zero w hw]
  ring

theorem one_add_upperCayley (w : ℂ) (hw : 0 < w.im) :
    1 + upperCayley w = 2 * w / (w + Complex.I) := by
  unfold upperCayley
  field_simp [upperCayley_den_ne_zero w hw]
  ring

/-- The mass and phase are exact: the point mass ℓ at 1 becomes exp(iℓw). -/
theorem atomDiskFunction_upperCayley (ℓ : ℝ) (w : ℂ) (hw : 0 < w.im) :
    atomDiskFunction ℓ 0 (upperCayley w) = Complex.exp ((ℓ : ℂ) * w * Complex.I) := by
  unfold atomDiskFunction
  rw [fourier_eval_zero, one_add_upperCayley w hw, one_sub_upperCayley w hw]
  congr 1
  field_simp [upperCayley_den_ne_zero w hw]
  ring_nf
  simp [Complex.I_sq]

/-- The Cayley denominator carries the precise scalar needed by the interval Gram formula. -/
theorem upperCayley_kernel_factor (w v : ℂ) (hw : 0 < w.im) (hv : 0 < v.im) :
    ((w + Complex.I) * (conj v - Complex.I) / 2) *
        (1 - conj (upperCayley v) * upperCayley w) = -((w - conj v) * Complex.I) := by
  have hvden : conj v - Complex.I ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.conj_im, Complex.I_im, Complex.zero_im] at him
    linarith
  have hconj : conj (upperCayley v) = (conj v + Complex.I) / (conj v - Complex.I) := by
    simp [upperCayley, sub_eq_add_neg]
  rw [hconj]
  unfold upperCayley
  field_simp [upperCayley_den_ne_zero w hw, hvden]
  ring_nf

/-- The literal interval kernels and the actual native model kernels have exactly the same Gram matrix. -/
theorem intervalEvalKernel_model_gram (ℓ : ℝ) (hℓ : 0 < ℓ)
    (u : BoundaryLInf) (hu : IsInner u)
    (hval : ∀ z ∈ disk, innerValue u z = atomDiskFunction ℓ 0 z)
    (w v : ℂ) (hw : 0 < w.im) (hv : 0 < v.im) :
    inner ℂ (intervalEvalKernel ℓ w hw) (intervalEvalKernel ℓ v hv) =
      inner ℂ (modelReproducingKernel u hu (upperCayleyDisk w hw))
        (modelReproducingKernel u hu (upperCayleyDisk v hv)) := by
  have hd : w - conj v ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hc : (w - conj v) * Complex.I ≠ 0 := mul_ne_zero hd Complex.I_ne_zero
  have hfac := upperCayley_kernel_factor w v hw hv
  have hden : 1 - conj (upperCayley v) * upperCayley w ≠ 0 := by
    intro he
    rw [he, mul_zero] at hfac
    exact hc (neg_eq_zero.mp hfac.symm)
  rw [inner_intervalEvalKernel_gram ℓ hℓ w v hw hv, inner_modelReproducingKernel]
  change _ = analyticValue (modelReproducingKernel u hu (upperCayleyDisk v hv)).val (upperCayley w)
  rw [analyticValue_modelReproducingKernel _ _ _ (upperCayley_mem_disk w hw)]
  unfold kernelValue
  change _ = (1 - conj (innerValue u (upperCayley v)) * innerValue u (upperCayley w)) /
    (1 - conj (upperCayley v) * upperCayley w)
  rw [hval _ (upperCayley_mem_disk v hv), hval _ (upperCayley_mem_disk w hw),
    atomDiskFunction_upperCayley ℓ v hv, atomDiskFunction_upperCayley ℓ w hw]
  have he : conj (Complex.exp ((ℓ : ℂ) * v * Complex.I)) *
      Complex.exp ((ℓ : ℂ) * w * Complex.I) =
      Complex.exp ((ℓ : ℂ) * (w - conj v) * Complex.I) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [he]
  apply (eq_div_iff hden).mpr
  calc
    _ = (((w + Complex.I) * (conj v - Complex.I) / 2) *
        (1 - conj (upperCayley v) * upperCayley w)) *
        (Complex.exp ((ℓ : ℂ) * (w - conj v) * Complex.I) - 1) /
          ((w - conj v) * Complex.I) := by ring
    _ = _ := by rw [hfac]; field_simp [hc]; ring

/-- The literal phase-one boundary symbol with the specified point mass, before proving innerness. -/
def normalizedAtomBoundary (ℓ : ℝ) : BoundaryLInf :=
  (memLp_top_of_bound (show AEStronglyMeasurable (atomBoundaryFunction ℓ 0) circleMeasure by
      apply Measurable.aestronglyMeasurable
      unfold atomBoundaryFunction atomDiskFunction
      fun_prop) 1 (Eventually.of_forall fun t => (norm_atomBoundaryFunction ℓ 0 t).le)).toLp
    (atomBoundaryFunction ℓ 0)

theorem normalizedAtomBoundary_ae (ℓ : ℝ) :
    normalizedAtomBoundary ℓ =ᵐ[circleMeasure] atomBoundaryFunction ℓ 0 :=
  MemLp.coeFn_toLp _

/-- The constructed boundary symbol has the exact mass ℓ and phase one, not merely an unspecified SingleAtom witness. -/
theorem normalizedAtomBoundary_inner_value (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsInner (normalizedAtomBoundary ℓ) ∧ Nonconstant (normalizedAtomBoundary ℓ) ∧
      ∀ z ∈ disk, innerValue (normalizedAtomBoundary ℓ) z = atomDiskFunction ℓ 0 z := by
  let F := atomDiskFunction ℓ 0
  have hF := analyticOnNhd_atomDiskFunction ℓ 0
  have hM : ∀ z ∈ disk, ‖F z‖ ≤ 1 := fun _ hz => norm_atomDiskFunction_le_one ℓ hℓ.le 0 hz
  let x := boundedAnalyticHardy F hF 1 hM
  have hlim : ∀ᵐ t ∂circleMeasure, Tendsto
      (fun r : ℝ => F ((r : ℂ) * fourier (T := 1) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (atomBoundaryFunction ℓ 0 t)) := by
    have hn : ∀ᵐ t ∂circleMeasure, t ≠ (0 : Boundary) := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (0 : Boundary) : circleMeasure {0} = 0)
    exact hn.mono fun t ht => tendsto_atomDiskFunction_radial ℓ 0 t ht
  have hxb := boundedAnalyticHardy_ae_of_radialLimit F hF 1 hM (atomBoundaryFunction ℓ 0) hlim
  have he : toL2 (normalizedAtomBoundary ℓ) = x.val := by
    apply Lp.ext
    filter_upwards [toL2_ae (normalizedAtomBoundary ℓ), normalizedAtomBoundary_ae ℓ, hxb]
      with t htu hut hxt
    rw [htu, hut, hxt]
  have hu : IsInner (normalizedAtomBoundary ℓ) := by
    refine ⟨he ▸ x.property, ?_⟩
    filter_upwards [normalizedAtomBoundary_ae ℓ] with t ht
    rw [ht]
    exact norm_atomBoundaryFunction ℓ 0 t
  have hv : ∀ z ∈ disk, innerValue (normalizedAtomBoundary ℓ) z = F z := by
    intro z hz
    change analyticValue (toL2 (normalizedAtomBoundary ℓ)) z = F z
    rw [he]
    exact analyticValue_boundedAnalyticHardy F hF 1 hM hz
  refine ⟨hu, ?_, hv⟩
  have hstrict : ‖innerValue (normalizedAtomBoundary ℓ) 0‖ < 1 := by
    rw [hv 0 (by norm_num [disk])]
    change ‖atomDiskFunction ℓ 0 0‖ < 1
    rw [norm_atomDiskFunction]
    simp only [atomicPoissonKernel, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      fourier_apply, Circle.norm_coe, one_pow, div_one, mul_one]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hℓ)
  rintro ⟨c, hc⟩
  have hunit := hu.2
  rw [hc] at hunit
  have hcae : constLInf c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  obtain ⟨t, ht, hct⟩ := (hunit.and hcae).exists
  have hnc : ‖c‖ = 1 := by rw [hct] at ht; exact ht
  have hcval : innerValue (normalizedAtomBoundary ℓ) 0 = c := by
    rw [hc]
    change analyticValue (toL2 (constLInf c)) 0 = c
    rw [toL2_constLInf, analyticValue_at_zero, fourierCoeff_constL2]
    simp
  rw [hcval, hnc] at hstrict
  exact (lt_irrefl 1) hstrict

/-- Interval Parseval uniqueness, adapted from TauCeti/Fourier/SineSeries.lean,
Apache-2.0 revision d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad, using native Mathlib declarations. -/
theorem interval_ae_zero_of_fourierCoeffOn_zero (ℓ : ℝ) (hℓ : 0 < ℓ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ℓ)))
    (h : ∀ n : ℤ, fourierCoeffOn hℓ f n = 0) :
    f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] 0 := by
  have hf' : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rwa [← restrict_Ioo_eq_restrict_Ioc]
  have hsum := hasSum_sq_fourierCoeffOn hℓ hf'
  simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsum
  have h0 := hasSum_zero.unique hsum
  rw [eq_comm, smul_eq_mul, mul_eq_zero, intervalIntegral.integral_of_le hℓ.le] at h0
  have hint : ∫ t in Ioc (0 : ℝ) ℓ, ‖f t‖ ^ 2 = 0 :=
    h0.resolve_left (inv_ne_zero (sub_pos.mpr hℓ).ne')
  have hz : f =ᵐ[volume.restrict (Ioc (0 : ℝ) ℓ)] 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun t => by positivity)
      (hf'.integrable_norm_pow' (p := 2))).1 hint] with t ht
    simpa using ht
  simpa only [← restrict_Ioo_eq_restrict_Ioc] using hz

/-- The literal upper-half-plane evaluation kernels are total on the finite interval.
A horizontal frequency grid at imaginary height one reduces this to native interval Parseval. -/
theorem intervalEvalKernels_dense (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Dense (Submodule.span ℂ (Set.range (fun w : {w : ℂ // 0 < w.im} =>
      intervalEvalKernel ℓ w.val w.property)) : Set (IntervalL2 ℓ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  let g : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ) * f t
  have hgm : AEStronglyMeasurable g (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    (show Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) by fun_prop).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  have hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) := by
    apply (Lp.memLp f).of_le hgm
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1.le))
  have hcoeff : ∀ n : ℤ, fourierCoeffOn hℓ g n = 0 := by
    intro n
    let w : ℂ := ((-2 * Real.pi * (n : ℝ) / ℓ : ℝ) : ℂ) + Complex.I
    have hw : 0 < w.im := by simp [w]
    have hmem : intervalEvalKernel ℓ w hw ∈ Submodule.span ℂ
        (Set.range (fun a : {a : ℂ // 0 < a.im} => intervalEvalKernel ℓ a.val a.property)) :=
      Submodule.subset_span ⟨(⟨w, hw⟩ : {w : ℂ // 0 < w.im}), rfl⟩
    have hpair : inner ℂ (intervalEvalKernel ℓ w hw) f = 0 :=
      (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.le_topologicalClosure _ hmem)
    rw [inner_intervalEvalKernel] at hpair
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hc : (w + Complex.I) / (Real.sqrt 2 : ℂ) ≠ 0 :=
      div_ne_zero (upperCayley_den_ne_zero w hw) hs
    have hInt : (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t) = 0 :=
      (mul_eq_zero.mp hpair).resolve_left hc
    have hexp (t : ℝ) : fourier (T := ℓ - 0) (-n) (t : AddCircle (ℓ - 0)) * (Real.exp (-t) : ℂ) =
        Complex.exp ((t : ℂ) * w * Complex.I) := by
      rw [fourier_coe_apply, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [w]
      push_cast
      ring_nf
      simp [Complex.I_sq, sub_eq_add_neg]
    rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le hℓ.le,
      integral_Ioc_eq_integral_Ioo]
    have heq : (∫ t in Ioo (0 : ℝ) ℓ, fourier (T := ℓ - 0) (-n) (t : AddCircle (ℓ - 0)) • g t) =
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only [g]
        rw [smul_eq_mul, ← mul_assoc, hexp]
    rw [heq, hInt, smul_zero]
  have hz := interval_ae_zero_of_fourierCoeffOn_zero ℓ hℓ hg hcoeff
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ))] with t ht hzero
  rw [hzero]
  change f t = 0
  have he : (Real.exp (-t) : ℂ) * f t = 0 := ht
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast Real.exp_ne_zero (-t))

/-- Every open-disk point is the Cayley image of a genuine upper-half-plane pole. -/
theorem upperCayleyDisk_surjective : Function.Surjective
    (fun w : {w : ℂ // 0 < w.im} => upperCayleyDisk w.val w.property) := by
  intro z
  have hz : ‖z.val‖ < 1 := z.property
  have hzne : (1 : ℂ) - z.val ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one] at hn
    linarith
  let w : ℂ := Complex.I * ((1 + z.val) / (1 - z.val))
  have hw : 0 < w.im := by
    have him : w.im = ((1 + z.val) / (1 - z.val)).re := by
      dsimp [w]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [him, herglotz_re z.val 1 (by norm_num)]
    apply div_pos _ (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    nlinarith [norm_nonneg z.val]
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  change upperCayley w = z.val
  apply (div_eq_iff (upperCayley_den_ne_zero w hw)).mpr
  dsimp [w]
  field_simp [hzne]
  ring

theorem modelCayleyKernels_dense (u : BoundaryLInf) (hu : IsInner u) :
    Dense (Submodule.span ℂ (Set.range (fun w : {w : ℂ // 0 < w.im} =>
      modelReproducingKernel u hu (upperCayleyDisk w.val w.property))) : Set (Model u)) := by
  have hrange : Set.range (fun w : {w : ℂ // 0 < w.im} =>
      modelReproducingKernel u hu (upperCayleyDisk w.val w.property)) =
      Set.range (modelReproducingKernel u hu) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      exact ⟨upperCayleyDisk w.val w.property, rfl⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := upperCayleyDisk_surjective z
      exact ⟨w, congrArg (modelReproducingKernel u hu) hw⟩
  rw [hrange]
  exact modelReproducingKernels_dense u hu

section DenseGramUnitary
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
private theorem clm_eq_id_of_dense_generators (p : I → E)
    (hd : Dense (Submodule.span ℂ (Set.range p) : Set E)) (T : E →L[ℂ] E)
    (hp : ∀ i, T (p i) = p i) : ∀ x, T x = x := by
  have hs : ∀ x ∈ Submodule.span ℂ (Set.range p), T x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hp i
    | zero => exact map_zero T
    | add x y hx hy hx' hy' => rw [map_add, hx', hy']
    | smul c x hx hx' => rw [map_smul, hx']
  have he : (fun x => T x) = (fun x => x) :=
    Continuous.ext_on hd T.continuous continuous_id hs
  exact fun x => congrFun he x

/-- The already-proved equal-Gram contractions give an actual unitary when both families are total. -/
theorem exists_unitary_of_equal_gram_dense (p : I → E) (q : I → F)
    (hGram : ∀ i j, inner ℂ (p i) (p j) = inner ℂ (q i) (q j))
    (hdp : Dense (Submodule.span ℂ (Set.range p) : Set E))
    (hdq : Dense (Submodule.span ℂ (Set.range q) : Set F)) :
    ∃ U : E ≃ₗᵢ[ℂ] F, ∀ i, U (p i) = q i := by
  obtain ⟨T, hT, hTp⟩ := exists_contraction_of_equal_gram p q hGram
  obtain ⟨S, hS, hSq⟩ := exists_contraction_of_equal_gram q p (fun i j => (hGram i j).symm)
  have hST : ∀ x, S (T x) = x := clm_eq_id_of_dense_generators p hdp (S.comp T) (by
    intro i
    change S (T (p i)) = p i
    rw [hTp, hSq])
  have hTS : ∀ y, T (S y) = y := clm_eq_id_of_dense_generators q hdq (T.comp S) (by
    intro i
    change T (S (q i)) = q i
    rw [hSq, hTp])
  have hTnorm (x : E) : ‖T x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg x)
      _ = _ := one_mul _
  have hSnorm (y : F) : ‖S y‖ ≤ ‖y‖ := by
    calc
      _ ≤ ‖S‖ * ‖y‖ := S.le_opNorm y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg y)
      _ = _ := one_mul _
  let L : E →ₗᵢ[ℂ] F :=
    { toLinearMap := T.toLinearMap
      norm_map' := fun x => le_antisymm (hTnorm x) (by
        calc
          ‖x‖ = ‖S (T x)‖ := by rw [hST]
          _ ≤ ‖T x‖ := hSnorm (T x)) }
  let U := LinearIsometryEquiv.ofSurjective L (fun y => ⟨S y, hTS y⟩)
  exact ⟨U, fun i => hTp i⟩

end DenseGramUnitary

/-- The exact Paley--Wiener formula follows from the two literal dense Gram families. -/
theorem exists_paleyWienerUnitary (ℓ : ℝ) (hℓ : 0 < ℓ)
    (u : BoundaryLInf) (hu : IsInner u)
    (hval : ∀ z ∈ disk, innerValue u z = atomDiskFunction ℓ 0 z) :
    ∃ U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u, PaleyWienerUnitary u ℓ U := by
  obtain ⟨U, hU⟩ := exists_unitary_of_equal_gram_dense
    (fun w : {w : ℂ // 0 < w.im} => intervalEvalKernel ℓ w.val w.property)
    (fun w : {w : ℂ // 0 < w.im} => modelReproducingKernel u hu (upperCayleyDisk w.val w.property))
    (fun w v => intervalEvalKernel_model_gram ℓ hℓ u hu hval w.val v.val w.property v.property)
    (intervalEvalKernels_dense ℓ hℓ) (modelCayleyKernels_dense u hu)
  refine ⟨U, ?_⟩
  intro f w hw
  have heval : analyticValue (U f).val (upperCayley w) =
      (w + Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
    change analyticValue (U f).val (upperCayleyDisk w hw).val = _
    rw [← inner_modelReproducingKernel u hu (upperCayleyDisk w hw) (U f)]
    have hm := hU (⟨w, hw⟩ : {w : ℂ // 0 < w.im})
    change U (intervalEvalKernel ℓ w hw) = modelReproducingKernel u hu (upperCayleyDisk w hw) at hm
    rw [← hm, U.inner_map_map, inner_intervalEvalKernel]
  change analyticValue (U f).val (upperCayley w) /
      ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) = _
  rw [heval]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hroot : (Real.sqrt (2 * Real.pi) : ℂ) =
      (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul]
  rw [hroot]
  field_simp [h2, hpi, upperCayley_den_ne_zero w hw]

/-- The completely constructed phase-one symbol has the manuscript's exact one-atom disk formula. -/
theorem normalizedAtomBoundary_value (ℓ : ℝ) (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ disk) :
    innerValue (normalizedAtomBoundary ℓ) z =
      Complex.exp (-(ℓ : ℂ) * (1 + z) / (1 - z)) := by
  simpa only [atomDiskFunction, fourier_eval_zero] using
    (normalizedAtomBoundary_inner_value ℓ hℓ).2.2 z hz

/-- An actual native Paley--Wiener unitary for every positive interval length, with no added hypothesis. -/
theorem exists_normalizedPaleyWienerUnitary (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model (normalizedAtomBoundary ℓ),
      PaleyWienerUnitary (normalizedAtomBoundary ℓ) ℓ U :=
  exists_paleyWienerUnitary ℓ hℓ (normalizedAtomBoundary ℓ)
    (normalizedAtomBoundary_inner_value ℓ hℓ).1 (normalizedAtomBoundary_inner_value ℓ hℓ).2.2

/-- The unnormalized finite Fourier--Laplace integral of the constant one function. -/
theorem integral_upper_exponential (ℓ : ℝ) (hℓ : 0 < ℓ) (w : ℂ) (hw : 0 < w.im) :
    (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I)) =
      (Complex.exp ((ℓ : ℂ) * w * Complex.I) - 1) / (w * Complex.I) := by
  have hw0 : w ≠ 0 := by intro he; simp only [he, Complex.zero_im, lt_self_iff_false] at hw
  have hc : w * Complex.I ≠ 0 := mul_ne_zero hw0 Complex.I_ne_zero
  have heq : (fun t : ℝ => Complex.exp ((t : ℂ) * w * Complex.I)) =
      (fun t : ℝ => Complex.exp ((w * Complex.I) * (t : ℂ))) := by
    funext t
    congr 1
    ring
  rw [heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ.le,
    integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  congr 2
  ring_nf

theorem norm_upper_exponential_le_one (t : ℝ) (ht : 0 ≤ t) (w : ℂ) (hw : 0 < w.im) :
    ‖Complex.exp ((t : ℂ) * w * Complex.I)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : ((t : ℂ) * w * Complex.I).re = -t * w.im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, zero_sub, mul_one]
    ring
  rw [he]
  nlinarith

/-- The literal analytic symbol in the manuscript's Volterra example. -/
def volterraDiskSymbol (ℓ : ℝ) (z : ℂ) : ℂ :=
  (1 - z) * (1 - atomDiskFunction ℓ 0 z) / (1 + z)

/-- Its normalized Cayley value has exactly the required Fourier--Laplace integral, with no extra scalar. -/
theorem volterraDiskSymbol_upperCayley (ℓ : ℝ) (hℓ : 0 < ℓ) (w : ℂ) (hw : 0 < w.im) :
    volterraDiskSymbol ℓ (upperCayley w) =
      ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) := by
  have hw0 : w ≠ 0 := by intro he; simp only [he, Complex.zero_im, lt_self_iff_false] at hw
  rw [volterraDiskSymbol, one_sub_upperCayley w hw, atomDiskFunction_upperCayley ℓ w hw,
    one_add_upperCayley w hw, integral_upper_exponential ℓ hℓ w hw]
  field_simp [upperCayley_den_ne_zero w hw, hw0]
  ring_nf
  simp [Complex.I_sq]

theorem analyticOnNhd_volterraDiskSymbol (ℓ : ℝ) : AnalyticOnNhd ℂ (volterraDiskSymbol ℓ) disk := by
  intro z hz
  have hden : (1 : ℂ) + z ≠ 0 := by
    intro he
    have hn := congrArg norm (add_eq_zero_iff_eq_neg.mp he)
    simp only [norm_one, norm_neg] at hn
    have hz' : ‖z‖ < 1 := hz
    linarith
  exact (((analyticAt_const.sub analyticAt_id).mul
    (analyticAt_const.sub (analyticOnNhd_atomDiskFunction ℓ 0 z hz))).div
    (analyticAt_const.add analyticAt_id) hden)

theorem norm_volterraDiskSymbol_le (ℓ : ℝ) (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ disk) :
    ‖volterraDiskSymbol ℓ z‖ ≤ ℓ := by
  obtain ⟨w, hw⟩ := upperCayleyDisk_surjective (⟨z, hz⟩ : Disk)
  have he : upperCayley w.val = z := congrArg Subtype.val hw
  rw [← he, volterraDiskSymbol_upperCayley ℓ hℓ w.val w.property]
  have hb : ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioo (0 : ℝ) ℓ)),
      ‖Complex.exp ((t : ℂ) * w.val * Complex.I)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_upper_exponential_le_one t ht.1.le w.val w.property
  simpa [measureReal_def, hℓ.le] using norm_integral_le_of_norm_le_const hb

/-- The actual native Hardy symbol with the manuscript's Volterra analytic values. -/
def normalizedVolterraSymbol (ℓ : ℝ) (hℓ : 0 < ℓ) : Hardy :=
  boundedAnalyticHardy (volterraDiskSymbol ℓ) (analyticOnNhd_volterraDiskSymbol ℓ) ℓ
    (fun _ hz => norm_volterraDiskSymbol_le ℓ hℓ hz)

theorem normalizedVolterraSymbol_value (ℓ : ℝ) (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ disk) :
    analyticValue (normalizedVolterraSymbol ℓ hℓ).val z =
      (1 - z) * (1 - innerValue (normalizedAtomBoundary ℓ) z) / (1 + z) := by
  rw [normalizedAtomBoundary_value ℓ hℓ hz]
  change analyticValue (boundedAnalyticHardy _ _ _ _).val z = _
  rw [analyticValue_boundedAnalyticHardy _ _ _ _ hz]
  simp only [volterraDiskSymbol, atomDiskFunction, fourier_eval_zero]

theorem normalizedVolterraSymbol_bound (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∀ᵐ t ∂circleMeasure, ‖(normalizedVolterraSymbol ℓ hℓ).val t‖ ≤ ℓ :=
  boundedAnalyticHardy_ae_bound _ _ _ _

/-- The literal evaluation vector has its explicit primitive on every ordered finite interval. -/
theorem integral_intervalEvalFunction (a b : ℝ) (hab : a ≤ b) (w : ℂ) (hw : 0 < w.im) :
    (∫ t in Ioo a b, intervalEvalFunction w t) =
      (conj w - Complex.I) / (Real.sqrt 2 : ℂ) *
        ((Complex.exp (-(b : ℂ) * conj w * Complex.I) -
          Complex.exp (-(a : ℂ) * conj w * Complex.I)) / (-conj w * Complex.I)) := by
  have hw0 : w ≠ 0 := by intro he; simp only [he, Complex.zero_im, lt_self_iff_false] at hw
  have hconj : conj w ≠ 0 := by
    rw [← norm_pos_iff, Complex.norm_conj]
    exact norm_pos_iff.mpr hw0
  have hc : -conj w * Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hconj) Complex.I_ne_zero
  have heq : intervalEvalFunction w = (fun t : ℝ =>
      (conj w - Complex.I) / (Real.sqrt 2 : ℂ) * Complex.exp ((-conj w * Complex.I) * (t : ℂ))) := by
    funext t
    unfold intervalEvalFunction
    congr 2
    ring
  rw [heq, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, integral_exp_mul_complex hc]
  have hb : (-conj w * Complex.I) * (b : ℂ) = -(b : ℂ) * conj w * Complex.I := by ring
  have ha : (-conj w * Complex.I) * (a : ℂ) = -(a : ℂ) * conj w * Complex.I := by ring
  rw [hb, ha]

/-- Primitive identity on the genuine L² evaluation vectors. The two operator hypotheses are
complete literal Volterra/adjoint integral meanings, to be discharged by the actual operator. -/
theorem volterra_intervalEvalKernel_identity (ℓ : ℝ) (hℓ : 0 < ℓ)
    (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hV : RepresentsVolterra ℓ V)
    (hVad : ∀ f : IntervalL2 ℓ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)),
      (V.adjoint f) t = ∫ s in Ioo t ℓ, f s)
    (w : ℂ) (hw : 0 < w.im) :
    conj (volterraDiskSymbol ℓ (upperCayley w)) • intervalEvalKernel ℓ w hw =
      V.adjoint (intervalEvalKernel ℓ w hw) +
        conj (Complex.exp ((ℓ : ℂ) * w * Complex.I)) • V (intervalEvalKernel ℓ w hw) := by
  let k := intervalEvalKernel ℓ w hw
  have hconjE : conj (Complex.exp ((ℓ : ℂ) * w * Complex.I)) =
      Complex.exp (-(ℓ : ℂ) * conj w * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hphi : conj (volterraDiskSymbol ℓ (upperCayley w)) =
      (Complex.exp (-(ℓ : ℂ) * conj w * Complex.I) - 1) / (-conj w * Complex.I) := by
    rw [volterraDiskSymbol_upperCayley ℓ hℓ w hw, integral_upper_exponential ℓ hℓ w hw]
    simp [hconjE]
  apply Lp.ext
  filter_upwards [hV k, hVad k, intervalEvalKernel_ae ℓ w hw,
    Lp.coeFn_smul (conj (volterraDiskSymbol ℓ (upperCayley w))) k,
    Lp.coeFn_add (V.adjoint k) (conj (Complex.exp ((ℓ : ℂ) * w * Complex.I)) • V k),
    Lp.coeFn_smul (conj (Complex.exp ((ℓ : ℂ) * w * Complex.I))) (V k),
    ae_restrict_mem measurableSet_Ioo] with t hvt hvadt hkt hsm hadd hsmV ht
  have hlow : (V k) t = ∫ s in Ioo (0 : ℝ) t, intervalEvalFunction w s := by
    rw [hvt]
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2.le) (intervalEvalKernel_ae ℓ w hw)
  have hhigh : (V.adjoint k) t = ∫ s in Ioo t ℓ, intervalEvalFunction w s := by
    rw [hvadt]
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ht.1.le le_rfl) (intervalEvalKernel_ae ℓ w hw)
  change (conj (volterraDiskSymbol ℓ (upperCayley w)) • k) t =
    (V.adjoint k + conj (Complex.exp ((ℓ : ℂ) * w * Complex.I)) • V k) t
  rw [hsm, hadd]
  simp only [Pi.add_apply]
  rw [hsmV]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hlow, hhigh]
  change conj (volterraDiskSymbol ℓ (upperCayley w)) * k t =
    (∫ s in Ioo t ℓ, intervalEvalFunction w s) +
      conj (Complex.exp ((ℓ : ℂ) * w * Complex.I)) *
        (∫ s in Ioo (0 : ℝ) t, intervalEvalFunction w s)
  rw [hphi, hconjE, hkt, intervalEvalFunction,
    integral_intervalEvalFunction t ℓ ht.2.le w hw,
    integral_intervalEvalFunction 0 t ht.1.le w hw]
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero]
  ring

/-- The PW formula is equivalently reproduction by the literal interval evaluation kernel. -/
theorem paleyWienerUnitary_eval (ℓ : ℝ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f : IntervalL2 ℓ) (w : ℂ) (hw : 0 < w.im) :
    analyticValue (U f).val (upperCayley w) = inner ℂ (intervalEvalKernel ℓ w hw) f := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hroot : (Real.sqrt (2 * Real.pi) : ℂ) =
      (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul]
  have hv := (div_eq_iff (mul_ne_zero hpi (upperCayley_den_ne_zero w hw))).mp (hU f w hw)
  rw [inner_intervalEvalKernel]
  change analyticValue (U f).val ((w - Complex.I) / (w + Complex.I)) = _
  rw [hv, hroot]
  field_simp [h2, hpi]
  rw [mul_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    have he : (t : ℂ) * w * Complex.I = w * Complex.I * (t : ℂ) := by ring
    rw [he]

/-- Pairing the primitive identity gives the needed Laplace product identity without another Fubini argument. -/
theorem volterra_intervalEvalKernel_pair (ℓ : ℝ) (hℓ : 0 < ℓ)
    (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hV : RepresentsVolterra ℓ V)
    (hVad : ∀ f : IntervalL2 ℓ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)),
      (V.adjoint f) t = ∫ s in Ioo t ℓ, f s)
    (f : IntervalL2 ℓ) (w : ℂ) (hw : 0 < w.im) :
    volterraDiskSymbol ℓ (upperCayley w) * inner ℂ (intervalEvalKernel ℓ w hw) f =
      inner ℂ (intervalEvalKernel ℓ w hw) (V f) +
        Complex.exp ((ℓ : ℂ) * w * Complex.I) * inner ℂ (intervalEvalKernel ℓ w hw) (V.adjoint f) := by
  have he := congrArg (fun k : IntervalL2 ℓ => inner ℂ k f)
    (volterra_intervalEvalKernel_identity ℓ hℓ V hV hVad w hw)
  simpa only [inner_smul_left, inner_add_left, Complex.conj_conj,
    V.adjoint_inner_left f (intervalEvalKernel ℓ w hw),
    ← V.adjoint_inner_right (intervalEvalKernel ℓ w hw) f] using he

/-- The concrete L∞ representative of the constructed Hardy Volterra symbol. -/
def normalizedVolterraBoundary (ℓ : ℝ) (hℓ : 0 < ℓ) : BoundaryLInf :=
  (memLp_top_of_bound (Lp.aestronglyMeasurable (normalizedVolterraSymbol ℓ hℓ).val)
    ℓ (normalizedVolterraSymbol_bound ℓ hℓ)).toLp (normalizedVolterraSymbol ℓ hℓ).val

theorem normalizedVolterraBoundary_toL2 (ℓ : ℝ) (hℓ : 0 < ℓ) :
    toL2 (normalizedVolterraBoundary ℓ hℓ) = (normalizedVolterraSymbol ℓ hℓ).val :=
  Lp.ext ((toL2_ae _).trans (MemLp.coeFn_toLp _))

theorem normalizedVolterraBoundary_value (ℓ : ℝ) (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ disk) :
    innerValue (normalizedVolterraBoundary ℓ hℓ) z = volterraDiskSymbol ℓ z := by
  change analyticValue (toL2 (normalizedVolterraBoundary ℓ hℓ)) z = _
  rw [normalizedVolterraBoundary_toL2]
  exact analyticValue_boundedAnalyticHardy _ _ _ _ hz

/-- The actual product decomposition has an explicit uH² error, so model compression removes it. -/
theorem normalizedVolterra_PW_product (ℓ : ℝ) (hℓ : 0 < ℓ)
    (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hV : RepresentsVolterra ℓ V)
    (hVad : ∀ f : IntervalL2 ℓ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)),
      (V.adjoint f) t = ∫ s in Ioo t ℓ, f s)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model (normalizedAtomBoundary ℓ))
    (hU : PaleyWienerUnitary (normalizedAtomBoundary ℓ) ℓ U) (f : IntervalL2 ℓ) :
    multiply (normalizedVolterraBoundary ℓ hℓ) (U f).val =
      (U (V f)).val + multiply (normalizedAtomBoundary ℓ) (U (V.adjoint f)).val := by
  let u := normalizedAtomBoundary ℓ
  let b := normalizedVolterraBoundary ℓ hℓ
  have hu : IsInner u := (normalizedAtomBoundary_inner_value ℓ hℓ).1
  have hb : toL2 b ∈ hardy := normalizedVolterraBoundary_toL2 ℓ hℓ ▸ (normalizedVolterraSymbol ℓ hℓ).property
  have hUf : (U f).val ∈ hardy := (U f).property.1
  have hUVf : (U (V f)).val ∈ hardy := (U (V f)).property.1
  have hUVadf : (U (V.adjoint f)).val ∈ hardy := (U (V.adjoint f)).property.1
  have he : (⟨multiply b (U f).val, multiply_mem_hardy b hb _ hUf⟩ : Hardy) =
      ⟨(U (V f)).val + multiply u (U (V.adjoint f)).val,
        hardy.add_mem hUVf (multiply_mem_hardy u hu.1 _ hUVadf)⟩ := by
    apply hardy_analyticValue_injective
    intro z hz
    change analyticValue (multiply b (U f).val) z =
      analyticValue ((U (V f)).val + multiply u (U (V.adjoint f)).val) z
    obtain ⟨w, hw⟩ := upperCayleyDisk_surjective (⟨z, hz⟩ : Disk)
    have hzw : upperCayley w.val = z := congrArg Subtype.val hw
    rw [← hzw]
    change analyticValue (multiply b (U f).val) (upperCayleyDisk w.val w.property).val =
      analyticValue ((U (V f)).val + multiply u (U (V.adjoint f)).val) (upperCayleyDisk w.val w.property).val
    rw [analyticValue_multiply b hb ⟨(U f).val, hUf⟩ (upperCayleyDisk w.val w.property),
      analyticValue_add _ _ (z := (upperCayleyDisk w.val w.property).val)
        (upperCayleyDisk w.val w.property).property,
      analyticValue_multiply u hu.1 ⟨(U (V.adjoint f)).val, hUVadf⟩
        (upperCayleyDisk w.val w.property)]
    change innerValue b (upperCayley w.val) * analyticValue (U f).val (upperCayley w.val) =
      analyticValue (U (V f)).val (upperCayley w.val) +
        innerValue u (upperCayley w.val) * analyticValue (U (V.adjoint f)).val (upperCayley w.val)
    dsimp only [u, b]
    rw [normalizedVolterraBoundary_value ℓ hℓ (upperCayley_mem_disk w.val w.property),
      (normalizedAtomBoundary_inner_value ℓ hℓ).2.2 _ (upperCayley_mem_disk w.val w.property),
      atomDiskFunction_upperCayley ℓ w.val w.property,
      paleyWienerUnitary_eval ℓ u U hU f w.val w.property,
      paleyWienerUnitary_eval ℓ u U hU (V f) w.val w.property,
      paleyWienerUnitary_eval ℓ u U hU (V.adjoint f) w.val w.property]
    exact volterra_intervalEvalKernel_pair ℓ hℓ V hV hVad f w.val w.property
  exact congrArg Subtype.val he

/-- The concrete analytic compressed multiplication operator for the actual bounded symbol. -/
def normalizedVolterraAnalyticOperator (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Model (normalizedAtomBoundary ℓ) →L[ℂ] Model (normalizedAtomBoundary ℓ) :=
  boundedSymbolOperator (normalizedAtomBoundary ℓ) (normalizedVolterraBoundary ℓ hℓ)

theorem normalizedVolterraAnalyticOperator_represents (ℓ : ℝ) (hℓ : 0 < ℓ) :
    RepresentsTTO (normalizedAtomBoundary ℓ) (normalizedVolterraSymbol ℓ hℓ).val
      (normalizedVolterraAnalyticOperator ℓ hℓ) := by
  have h := boundedSymbolOperator_represents (normalizedAtomBoundary ℓ) (normalizedVolterraBoundary ℓ hℓ)
  rwa [normalizedVolterraBoundary_toL2] at h

/-- The actual normalized PW map intertwines the analytic TTO with any operator having the literal Volterra formulas. -/
theorem normalizedVolterraAnalyticOperator_intertwines (ℓ : ℝ) (hℓ : 0 < ℓ)
    (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hV : RepresentsVolterra ℓ V)
    (hVad : ∀ f : IntervalL2 ℓ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)),
      (V.adjoint f) t = ∫ s in Ioo t ℓ, f s)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model (normalizedAtomBoundary ℓ))
    (hU : PaleyWienerUnitary (normalizedAtomBoundary ℓ) ℓ U) (f : IntervalL2 ℓ) :
    normalizedVolterraAnalyticOperator ℓ hℓ (U f) = U (V f) := by
  change (model (normalizedAtomBoundary ℓ)).orthogonalProjectionOnto
    (multiply (normalizedVolterraBoundary ℓ hℓ) (U f).val) = U (V f)
  rw [normalizedVolterra_PW_product ℓ hℓ V hV hVad U hU f, map_add,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    modelProjection_multiply_hardy_zero (normalizedAtomBoundary ℓ)
      ⟨(U (V.adjoint f)).val, (U (V.adjoint f)).property.1⟩, add_zero]

/-- The complete concrete PW/Volterra model uses the actual integral operator and its actual adjoint.
No compactness, approximation-number or Schatten conclusion is inserted into these model data. -/
def normalizedVolterraModelData (ℓ : ℝ) (hℓ : 0 < ℓ) : VolterraModelData ℓ := by
  let U := Classical.choose (exists_normalizedPaleyWienerUnitary ℓ hℓ)
  have hU : PaleyWienerUnitary (normalizedAtomBoundary ℓ) ℓ U :=
    Classical.choose_spec (exists_normalizedPaleyWienerUnitary ℓ hℓ)
  exact
    { u := normalizedAtomBoundary ℓ
      inner := (normalizedAtomBoundary_inner_value ℓ hℓ).1
      nonconstant := (normalizedAtomBoundary_inner_value ℓ hℓ).2.1
      u_value := fun _ hz => normalizedAtomBoundary_value ℓ hℓ hz
      symbol := normalizedVolterraSymbol ℓ hℓ
      symbol_value := fun _ hz => normalizedVolterraSymbol_value ℓ hℓ hz
      bound := normalizedVolterraSymbol_bound ℓ hℓ
      piModel := U
      piModel_formula := hU
      V := volterraOperator ℓ
      volterra := volterraOperator_represents ℓ
      analyticOperator := normalizedVolterraAnalyticOperator ℓ hℓ
      represents := normalizedVolterraAnalyticOperator_represents ℓ hℓ
      intertwines := fun f => normalizedVolterraAnalyticOperator_intertwines ℓ hℓ
        (volterraOperator ℓ) (volterraOperator_represents ℓ) (adjoint_volterraOperator_ae ℓ) U hU f
      rank_one := volterraOperator_rank_one ℓ hℓ
      rank_one_formula := volterraOperator_add_adjoint_ae ℓ }

theorem exists_volterraModelData (ℓ : ℝ) (hℓ : 0 < ℓ) : Nonempty (VolterraModelData ℓ) :=
  ⟨normalizedVolterraModelData ℓ hℓ⟩

end TTO.Paper.Proved
