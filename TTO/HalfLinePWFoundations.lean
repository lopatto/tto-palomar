/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PWBoundedCoreFoundations
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Native Fourier uniqueness and the actual half-line Hardy/PW correspondence.
No Hardy positive-frequency or Fourier-support theorem is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset FourierTransform
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology ContDiff SchwartzMap
namespace TTO.Paper.Proved
open Reduction

/-- Native distribution Fourier inversion supplies classical L¹ Fourier uniqueness. -/
theorem integrable_ae_zero_of_fourier_zero {h : ℝ → ℂ}
    (hh : Integrable h) (hF : ∀ x : ℝ, 𝓕 h x = 0) : h =ᵐ[volume] 0 := by
  have hm : MemLp h 1 := memLp_one_iff_integrable.mpr hh
  let a : Lp ℂ 1 (volume : Measure ℝ) := hm.toLp h
  have ha : a =ᵐ[volume] h := hm.coeFn_toLp
  have hDF : 𝓕 (Lp.toTemperedDistribution a) = (0 : 𝓢'(ℝ,ℂ)) := by
    ext φ
    rw [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply]
    change (∫ t : ℝ, (𝓕 φ) t • a t) = 0
    have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) Real.continuous_fourierChar continuous_inner φ.integrable hh
    have hswap : (∫ t : ℝ, (𝓕 φ) t • h t) = ∫ t : ℝ, φ t • (𝓕 h) t := by
      simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,VectorFourier.fourierIntegral,
        LinearMap.flip_apply,innerₗ_apply_apply,real_inner_comm] using! hi
    have hae : (∫ t : ℝ, (𝓕 φ) t • a t) = ∫ t : ℝ, (𝓕 φ) t • h t := by
      apply integral_congr_ae
      filter_upwards [ha] with t ht
      rw [ht]
    rw [hae,hswap]
    simp only [hF,smul_zero,integral_zero]
  have hD : Lp.toTemperedDistribution a = (0 : 𝓢'(ℝ,ℂ)) := by
    apply (fourierEquiv ℂ 𝓢'(ℝ,ℂ)).injective
    simpa only [fourierEquiv_apply,FourierTransform.fourier_zero] using hDF
  have hker : a ∈ (Lp.toTemperedDistributionCLM ℂ volume 1).ker := hD
  rw [Lp.ker_toTemperedDistributionCLM_eq_bot] at hker
  have ha0 : a = 0 := hker
  exact ha.symm.trans (ha0 ▸ Lp.coeFn_zero ℂ 1 volume)

/-- The actual positive half-line L² space, with no boundary/Fourier condition in its definition. -/
abbrev HalfLineL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

theorem norm_intervalEvalFunction_sq (w : ℂ) (t : ℝ) :
    ‖intervalEvalFunction w t‖ ^ 2 =
      ‖(conj w - Complex.I) / (Real.sqrt 2 : ℂ)‖ ^ 2 * Real.exp ((-2 * w.im) * t) := by
  have he : (-(t : ℂ) * conj w * Complex.I).re = -t * w.im := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
      Complex.I_re,Complex.I_im,neg_zero,zero_mul,mul_zero,sub_zero,zero_sub,mul_one]
    ring
  rw [intervalEvalFunction,norm_mul,mul_pow,Complex.norm_exp,he,← Real.exp_nat_mul]
  congr 2
  ring

theorem memLp_halfLineEvalFunction (w : ℂ) (hw : 0 < w.im) :
    MemLp (intervalEvalFunction w) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold intervalEvalFunction; fun_prop)).mpr
  simp_rw [norm_intervalEvalFunction_sq]
  exact (integrableOn_exp_mul_Ioi (by nlinarith : -2 * w.im < 0) 0).const_mul _

def halfLineEvalKernel (w : ℂ) (hw : 0 < w.im) : HalfLineL2 :=
  (memLp_halfLineEvalFunction w hw).toLp (intervalEvalFunction w)

theorem halfLineEvalKernel_ae (w : ℂ) (hw : 0 < w.im) :
    halfLineEvalKernel w hw =ᵐ[volume.restrict (Ioi (0 : ℝ))] intervalEvalFunction w :=
  (memLp_halfLineEvalFunction w hw).coeFn_toLp

theorem inner_halfLineEvalKernel (w : ℂ) (hw : 0 < w.im) (f : HalfLineL2) :
    inner ℂ (halfLineEvalKernel w hw) f =
      (w + Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
  rw [L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [halfLineEvalKernel_ae w hw] with t ht
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
  rw [map_mul,hc,he]
  ring

/-- The half-line kernel Gram is exactly the full Hardy Szegő-kernel Gram. -/
theorem halfLineEvalKernel_hardy_gram (w v : ℂ) (hw : 0 < w.im) (hv : 0 < v.im) :
    inner ℂ (halfLineEvalKernel w hw) (halfLineEvalKernel v hv) =
      inner ℂ (szegoKernel (upperCayleyDisk w hw)) (szegoKernel (upperCayleyDisk v hv)) := by
  let c : ℂ := (w - conj v) * Complex.I
  have hcRe : c.re < 0 := by
    dsimp only [c]
    simp only [Complex.mul_re,Complex.sub_im,Complex.conj_im,Complex.I_re,
      Complex.I_im,mul_zero,mul_one,zero_sub]
    linarith
  have hc : c ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at hcRe
  have hint : (∫ t in Ioi (0 : ℝ), Complex.exp (c * (t : ℂ))) = -1 / c := by
    simpa only [Complex.ofReal_zero,mul_zero,Complex.exp_zero] using
      integral_exp_mul_complex_Ioi hcRe 0
  have hprod : (∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) *
      (halfLineEvalKernel v hv) t) =
      (conj v - Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (c * (t : ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [halfLineEvalKernel_ae v hv] with t ht
    rw [ht,intervalEvalFunction,mul_left_comm,← Complex.exp_add]
    congr 2
    dsimp only [c]
    ring
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [inner_halfLineEvalKernel,hprod,hint,← mul_assoc,div_mul_div_comm,hs,
    inner_szegoKernel,analyticValue_szegoKernel _ (upperCayleyDisk w hw).property]
  have hf := upperCayley_kernel_factor w v hw hv
  have hd : 1 - conj (upperCayley v) * upperCayley w ≠ 0 := by
    intro he
    rw [he,mul_zero] at hf
    exact hc (neg_eq_zero.mp hf.symm)
  rw [← one_div]
  change ((w + Complex.I) * (conj v - Complex.I) / 2) * (-1 / c) =
    1 / (1 - conj (upperCayley v) * upperCayley w)
  apply (eq_div_iff hd).mpr
  calc
    _ = (((w + Complex.I) * (conj v - Complex.I) / 2) *
        (1 - conj (upperCayley v) * upperCayley w)) * (-1 / c) := by ring
    _ = 1 := by
      rw [hf]
      dsimp only [c] at hc ⊢
      field_simp [hc]
      exact div_self (left_ne_zero_of_mul hc)

theorem memLp_halfLine_damping :
    MemLp (fun t : ℝ => (Real.exp (-t) : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have he : (fun t : ℝ => ‖(Real.exp (-t) : ℂ)‖ ^ 2) =
      fun t : ℝ => Real.exp ((-2 : ℝ) * t) := by
    funext t
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0

/-- All actual half-line Laplace evaluations determine the native L² vector. -/
theorem halfLine_eq_zero_of_eval_pairs (f : HalfLineL2)
    (hf : ∀ (w : ℂ) (hw : 0 < w.im), inner ℂ (halfLineEvalKernel w hw) f = 0) : f = 0 := by
  let h : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (fun t => (Real.exp (-t) : ℂ) * f t)
  have hi : Integrable (fun t : ℝ => (Real.exp (-t) : ℂ) * f t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_one_iff_integrable.mp (memLp_halfLine_damping.mul (Lp.memLp f))
  have hh : Integrable h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have hF : ∀ x : ℝ, 𝓕 h x = 0 := by
    intro x
    let w : ℂ := ((-2 * Real.pi * x : ℝ) : ℂ) + Complex.I
    have hw : 0 < w.im := by simp [w]
    have hp := hf w hw
    rw [inner_halfLineEvalKernel] at hp
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hc : (w + Complex.I) / (Real.sqrt 2 : ℂ) ≠ 0 :=
      div_ne_zero (upperCayley_den_ne_zero w hw) hs
    have hInt : (∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * f t) = 0 :=
      (mul_eq_zero.mp hp).resolve_left hc
    rw [Real.fourier_real_eq_integral_exp_smul]
    have he : (fun t : ℝ => Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) • h t) =
        (Ioi (0 : ℝ)).indicator
          (fun t : ℝ => Complex.exp ((t : ℂ) * w * Complex.I) * f t) := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp only [h,indicator_of_mem ht,smul_eq_mul]
        rw [← mul_assoc,Complex.ofReal_exp,← Complex.exp_add]
        congr 2
        dsimp only [w]
        push_cast
        ring_nf
        simp [Complex.I_sq,sub_eq_add_neg]
      · simp only [h,indicator_of_notMem ht,smul_zero]
    rw [he,integral_indicator measurableSet_Ioi]
    exact hInt
  have hz := integrable_ae_zero_of_fourier_zero hh hF
  apply Lp.ext
  filter_upwards [ae_restrict_of_ae hz,ae_restrict_mem measurableSet_Ioi,
    Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with t ht hti h0
  rw [h0]
  have hc : (Real.exp (-t) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos (-t)).ne'
  change f t = 0
  dsimp only [h] at ht
  rw [indicator_of_mem hti] at ht
  exact (mul_eq_zero.mp ht).resolve_left hc

theorem halfLineEvalKernels_dense :
    Dense (Submodule.span ℂ (Set.range (fun w : {w : ℂ // 0 < w.im} =>
      halfLineEvalKernel w.val w.property)) : Set HalfLineL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply halfLine_eq_zero_of_eval_pairs
  intro w hw
  exact (Submodule.mem_orthogonal _ _).mp hf _
    (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨w,hw⟩,rfl⟩))

theorem hardyCayleyKernels_dense :
    Dense (Submodule.span ℂ (Set.range (fun w : {w : ℂ // 0 < w.im} =>
      szegoKernel (upperCayleyDisk w.val w.property))) : Set Hardy) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply hardy_analyticValue_injective f 0
  intro z hz
  obtain ⟨w,he⟩ := upperCayleyDisk_surjective ⟨z,hz⟩
  have hp : inner ℂ (szegoKernel (upperCayleyDisk w.val w.property)) f = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w,rfl⟩))
  rw [inner_szegoKernel] at hp
  have he' : (upperCayleyDisk w.val w.property).val = z := congrArg Subtype.val he
  change analyticValue f.val z = analyticValue (0 : BoundaryL2) z
  rw [analyticValue_zero]
  simpa only [he'] using hp

/-- Actual kernel-Gram construction of the half-line Hardy unitary. -/
theorem exists_halfLinePW_equiv :
    ∃ U : HalfLineL2 ≃ₗᵢ[ℂ] Hardy,
      ∀ w : {w : ℂ // 0 < w.im},
        U (halfLineEvalKernel w.val w.property) = szegoKernel (upperCayleyDisk w.val w.property) :=
  exists_unitary_of_equal_gram_dense
    (fun w : {w : ℂ // 0 < w.im} => halfLineEvalKernel w.val w.property)
    (fun w : {w : ℂ // 0 < w.im} => szegoKernel (upperCayleyDisk w.val w.property))
    (fun w v => halfLineEvalKernel_hardy_gram w.val v.val w.property v.property)
    halfLineEvalKernels_dense hardyCayleyKernels_dense

/-- The actual isometric isomorphism uses only the native half-line L² and native boundary Hardy space. -/
def halfLinePWEquiv : HalfLineL2 ≃ₗᵢ[ℂ] Hardy := Classical.choose exists_halfLinePW_equiv

theorem halfLinePWEquiv_kernel (w : ℂ) (hw : 0 < w.im) :
    halfLinePWEquiv (halfLineEvalKernel w hw) = szegoKernel (upperCayleyDisk w hw) :=
  Classical.choose_spec exists_halfLinePW_equiv ⟨w,hw⟩

/-- Literal point evaluations of this actual unitary, before any distribution is introduced. -/
theorem analyticValue_halfLinePWEquiv (f : HalfLineL2) (w : ℂ) (hw : 0 < w.im) :
    analyticValue (halfLinePWEquiv f).val (upperCayley w) =
      (w + Complex.I) / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
  calc
    _ = inner ℂ (szegoKernel (upperCayleyDisk w hw)) (halfLinePWEquiv f) :=
      (inner_szegoKernel _ _).symm
    _ = inner ℂ (halfLinePWEquiv (halfLineEvalKernel w hw)) (halfLinePWEquiv f) := by
      rw [halfLinePWEquiv_kernel]
    _ = inner ℂ (halfLineEvalKernel w hw) f := halfLinePWEquiv.inner_map_map _ _
    _ = _ := inner_halfLineEvalKernel w hw f

/-- Exact sqrt(pi)/sqrt(2*pi) normalization for the actual half-line map. -/
theorem halfLinePWEquiv_formula (f : HalfLineL2) (w : ℂ) (hw : 0 < w.im) :
    analyticValue (halfLinePWEquiv f).val ((w - Complex.I) / (w + Complex.I)) /
        ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
  rw [show (w - Complex.I) / (w + Complex.I) = upperCayley w from rfl,
    analyticValue_halfLinePWEquiv f w hw]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsp : (Real.sqrt (2 * Real.pi) : ℂ) =
      (Real.sqrt 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    exact_mod_cast Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi
  rw [hsp]
  field_simp [upperCayley_den_ne_zero w hw,h2,hp]

/-- Every original H² symbol has the actual half-line L² Fourier--Laplace representative. -/
theorem hardy_halfLine_representation (φ : Hardy) :
    ∃ g : HalfLineL2, ∀ (w : ℂ), 0 < w.im →
      analyticValue φ.val ((w - Complex.I) / (w + Complex.I)) /
          ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) =
        (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * g t := by
  refine ⟨halfLinePWEquiv.symm φ,?_⟩
  intro w hw
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    halfLinePWEquiv_formula (halfLinePWEquiv.symm φ) w hw

end TTO.Paper.Proved
