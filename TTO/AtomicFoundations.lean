/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.FiniteBlaschkeFoundations
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Literal Poisson averages and normalized-kernel identities for the atomic boundary argument. -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

def szegoInf (w : Disk) : BoundaryLInf := (bounded_szegoKernel w).toLp (szegoKernel w).val

theorem toL2_szegoInf (w : Disk) : toL2 (szegoInf w) = (szegoKernel w).val :=
  Lp.ext ((toL2_ae _).trans (bounded_szegoKernel w).coeFn_toLp)

/-- Bounded linear Poisson averaging, whose literal integral is established below. -/
def poissonAverage (w : Disk) : BoundaryL2 →L[ℂ] ℂ :=
  (((1-‖w.val‖^2 : ℝ) : ℂ)) • (innerSL ℂ (szegoKernel w).val).comp (multiply (szegoInf w))

theorem poissonAverage_core (w : Disk) (f : BoundaryL2) :
    poissonAverage w f = (((1-‖w.val‖^2 : ℝ) : ℂ))*
      coreForm f (szegoKernel w).val (szegoKernel w).val := by
  rw [coreForm_eq_inner_left _ _ _ (bounded_szegoKernel w)]
  rfl

theorem norm_kernelDenominator (w : Disk) (t : Boundary) :
    ‖1-conj w.val*fourier (T := 1) 1 t‖ = ‖fourier (T := 1) 1 t-w.val‖ := by
  let e := fourier (T := 1) 1 t
  have he : ‖e‖ = 1 := by simp only [e,fourier_apply,Circle.norm_coe]
  have hec : conj e*e = 1 := by simp only [Complex.conj_mul',he,Complex.ofReal_one,one_pow]
  have hid : 1-conj w.val*e = conj (e-w.val)*e := by rw [map_sub,sub_mul,hec]
  change ‖1-conj w.val*e‖ = ‖e-w.val‖
  rw [hid,norm_mul,Complex.norm_conj,he,mul_one]

theorem szego_weight_ae (w : Disk) :
    (fun t => (szegoKernel w).val t*conj ((szegoKernel w).val t)) =ᵐ[circleMeasure]
      fun t => (((‖fourier (T := 1) 1 t-w.val‖^2)⁻¹ : ℝ) : ℂ) := by
  filter_upwards [szegoKernel_ae w] with t ht
  rw [Complex.mul_conj',ht,norm_inv,norm_kernelDenominator,← Complex.ofReal_pow,inv_pow]

theorem poissonAverage_integral (w : Disk) (f : BoundaryL2) :
    poissonAverage w f = ∫ t, f t*
      (((1-‖w.val‖^2)/‖fourier (T := 1) 1 t-w.val‖^2 : ℝ) : ℂ) ∂circleMeasure := by
  rw [poissonAverage_core]
  unfold coreForm
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [szego_weight_ae w] with t ht
  change (((1-‖w.val‖^2 : ℝ) : ℂ))*(f t*(szegoKernel w).val t*conj ((szegoKernel w).val t)) = _
  rw [mul_assoc (f t),ht,Complex.ofReal_div,div_eq_mul_inv,Complex.ofReal_inv]
  ring

/-- Poisson reproduction for arbitrary native H² data, without boundedness of f. -/
theorem poissonAverage_hardy (w : Disk) (f : Hardy) : poissonAverage w f.val = analyticValue f.val w.val := by
  have hs : toL2 (szegoInf w) ∈ hardy := by rw [toL2_szegoInf]; exact (szegoKernel w).property
  let g : Hardy := ⟨multiply (szegoInf w) f.val,multiply_mem_hardy (szegoInf w) hs f.val f.property⟩
  have he : inner ℂ (szegoKernel w).val g.val = analyticValue g.val w.val := inner_szegoKernel w g
  change (((1-‖w.val‖^2 : ℝ) : ℂ))*inner ℂ (szegoKernel w).val g.val = _
  rw [he,analyticValue_multiply (szegoInf w) hs f w]
  change (((1-‖w.val‖^2 : ℝ) : ℂ))*(analyticValue (toL2 (szegoInf w)) w.val*analyticValue f.val w.val) = _
  rw [toL2_szegoInf,analyticValue_szegoKernel w w.property]
  have hpos : 0 < 1-‖w.val‖^2 := by have hw : ‖w.val‖ < 1 := w.property; nlinarith [norm_nonneg w.val]
  have hd : (1-‖w.val‖^2 : ℝ) ≠ 0 := ne_of_gt hpos
  simp only [Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub]
  field_simp [Complex.ofReal_ne_zero.mpr hd]
  rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hd)]

/-- The paper's literal Poisson error is precisely this bounded L² average. -/
theorem poissonError_eq_average (u : BoundaryLInf) (φ : BoundaryL2) (w : Disk) :
    poissonError u φ w.val = poissonAverage w (multiply (star u) φ) := by
  rw [poissonAverage_integral]
  apply integral_congr_ae
  filter_upwards [multiply_ae (star u) φ,Lp.coeFn_star u] with t hm hs
  change (star u) t = conj (u t) at hs
  rw [hm,hs]


def poissonNumerator (u : BoundaryLInf) (φ : BoundaryL2) (w : Disk) : BoundaryL2 :=
  (((1+‖innerValue u w.val‖^2 : ℝ) : ℂ)) • φ-
    conj (innerValue u w.val) • multiply u φ-innerValue u w.val • multiply (star u) φ

theorem poissonNumerator_ae (u : BoundaryLInf) (hu : IsInner u) (φ : BoundaryL2) (w : Disk) :
    poissonNumerator u φ w =ᵐ[circleMeasure] fun t =>
      φ t*(1-conj (innerValue u w.val)*u t)*conj (1-conj (innerValue u w.val)*u t) := by
  let v := innerValue u w.val
  let c : ℂ := ((1+‖v‖^2 : ℝ) : ℂ)
  filter_upwards [Lp.coeFn_sub (c • φ-conj v • multiply u φ) (v • multiply (star u) φ),
    Lp.coeFn_sub (c • φ) (conj v • multiply u φ),Lp.coeFn_smul c φ,
    Lp.coeFn_smul (conj v) (multiply u φ),Lp.coeFn_smul v (multiply (star u) φ),
    multiply_ae u φ,multiply_ae (star u) φ,Lp.coeFn_star u,hu.2] with t h1 h2 h3 h4 h5 h6 h7 h8 h9
  change ((c • φ-conj v • multiply u φ)-v • multiply (star u) φ) t = _
  simp only [Pi.sub_apply,Pi.smul_apply] at h1 h2 h3 h4 h5
  rw [h1,h2,h3,h4,h5]
  change c*φ t-conj v*(multiply u φ) t-v*(multiply (star u) φ) t = _
  change (star u) t = conj (u t) at h8
  rw [h6,h7,h8,map_sub,map_mul,map_one,Complex.conj_conj]
  have huu : u t*conj (u t) = 1 := by simp only [Complex.mul_conj',h9,Complex.ofReal_one,one_pow]
  have hvv : ((‖v‖^2 : ℝ) : ℂ) = v*conj v := by rw [Complex.mul_conj',Complex.ofReal_pow]
  dsimp only [c]
  rw [Complex.ofReal_add,Complex.ofReal_one,hvv]
  change (1+v*conj v)*φ t-conj v*(u t*φ t)-v*(conj (u t)*φ t) =
    φ t*(1-conj v*u t)*(1-v*conj (u t))
  linear_combination -(φ t*v*conj v)*huu

theorem poissonAverage_modelKernel (u : BoundaryLInf) (hu : IsInner u) (φ : BoundaryL2) (w : Disk) :
    poissonAverage w (poissonNumerator u φ w) = (((1-‖w.val‖^2 : ℝ) : ℂ))*
      coreForm φ (modelReproducingKernel u hu w).val (modelReproducingKernel u hu w).val := by
  rw [poissonAverage_core]
  congr 1
  unfold coreForm
  apply integral_congr_ae
  filter_upwards [poissonNumerator_ae u hu φ w,modelReproducingKernel_ae u hu w,szegoKernel_ae w] with t hn hk hs
  rw [hn,hk,hs]
  simp only [kernelBoundary,div_eq_mul_inv,map_mul]
  ring

/-- Exact raw-kernel Berezin/Poisson identity for arbitrary H² symbols. -/
theorem modelKernel_poisson_identity (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy) (w : Disk) :
    (((1-‖w.val‖^2 : ℝ) : ℂ))*
      coreForm φ.val (modelReproducingKernel u hu w).val (modelReproducingKernel u hu w).val =
      analyticValue φ.val w.val-innerValue u w.val*poissonError u φ.val w.val := by
  rw [← poissonAverage_modelKernel u hu φ.val w]
  unfold poissonNumerator
  rw [map_sub,map_sub,map_smul,map_smul,map_smul,poissonAverage_hardy w φ,
    poissonAverage_hardy w ⟨multiply u φ.val,multiply_mem_hardy u hu.1 φ.val φ.property⟩,
    analyticValue_multiply u hu.1 φ w,← poissonError_eq_average]
  simp only [smul_eq_mul,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_pow,← Complex.conj_mul']
  ring


/-- The exact normalized-kernel identity used by the source's atomic boundary argument. -/
theorem normalized_modelKernel_poisson_identity (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (φ : Hardy) (X : Model u →L[ℂ] Model u)
    (hX : RepresentsTTO u φ.val X) (w : Disk) :
    analyticValue φ.val w.val = (((1-‖innerValue u w.val‖^2 : ℝ) : ℂ))*
      inner ℂ (NormedSpace.normalize (modelReproducingKernel u hu w))
        (X (NormedSpace.normalize (modelReproducingKernel u hu w)))+
      innerValue u w.val*poissonError u φ.val w.val := by
  let K := modelReproducingKernel u hu w
  let d := ‖K‖
  have hd : d ≠ 0 := norm_ne_zero_iff.mpr (modelReproducingKernel_ne_zero u hu hn w)
  have he : NormedSpace.normalize K = (((d⁻¹ : ℝ) : ℂ)) • K := by
    rw [NormedSpace.normalize]
    exact (Complex.coe_smul ..).symm
  have hbeta : inner ℂ (NormedSpace.normalize K) (X (NormedSpace.normalize K)) =
      (((d⁻¹ : ℝ) : ℂ))^2*coreForm φ.val K.val K.val := by
    rw [he,map_smul]
    rw [inner_smul_left (𝕜 := ℂ) (E := Model u) K ((((d⁻¹ : ℝ) : ℂ)) • X K) (((d⁻¹ : ℝ) : ℂ)),
      inner_smul_right (𝕜 := ℂ) (E := Model u),
      hX K K (bounded_modelReproducingKernel u hu w) (bounded_modelReproducingKernel u hu w),Complex.conj_ofReal]
    ring
  have hnK : d^2 = (1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2) := norm_modelReproducingKernel_sq u hu w
  have hpos : 0 < 1-‖w.val‖^2 := by have hw : ‖w.val‖ < 1 := w.property; nlinarith [norm_nonneg w.val]
  have hde : d^2*(1-‖w.val‖^2) = 1-‖innerValue u w.val‖^2 := (eq_div_iff (ne_of_gt hpos)).mp hnK
  have hr : (1-‖innerValue u w.val‖^2)*(d⁻¹)^2 = 1-‖w.val‖^2 := by
    rw [inv_pow,← div_eq_mul_inv]
    apply (div_eq_iff (pow_ne_zero 2 hd)).mpr
    nlinarith [hde]
  have hrc : (((1-‖innerValue u w.val‖^2 : ℝ) : ℂ))*(((d⁻¹ : ℝ) : ℂ))^2 =
      (((1-‖w.val‖^2 : ℝ) : ℂ)) := by exact_mod_cast hr
  have hp := modelKernel_poisson_identity u hu φ w
  rw [hbeta,← mul_assoc,hrc]
  change analyticValue φ.val w.val = (((1-‖w.val‖^2 : ℝ) : ℂ))*coreForm φ.val K.val K.val+
    innerValue u w.val*poissonError u φ.val w.val
  linear_combination -hp

/-- The corresponding identity uses the manuscript's literal Berezin function. -/
theorem berezin_poisson_identity (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (φ : Hardy) (X : Model u →L[ℂ] Model u) (hX : RepresentsTTO u φ.val X) (z : ℂ) (hz : z ∈ disk) :
    analyticValue φ.val z = (((1-‖innerValue u z‖^2 : ℝ) : ℂ))*
      berezin (fun w => NormedSpace.normalize (modelReproducingKernel u hu w)) X z+
      innerValue u z*poissonError u φ.val z := by
  unfold berezin
  rw [dite_eq_left hz]
  exact normalized_modelKernel_poisson_identity u hu hn φ X hX ⟨z,hz⟩


/-- Elementary disk geometry for the contractive finite/infinite Blaschke factor. -/
theorem norm_blaschkeFactor_le_one (a w : Disk) : ‖blaschkeFactor a w.val‖ ≤ 1 := by
  have ha : ‖a.val‖ < 1 := a.property
  have hw : ‖w.val‖ < 1 := w.property
  have hid : ‖1-conj a.val*w.val‖^2-‖a.val-w.val‖^2 =
      (1-‖a.val‖^2)*(1-‖w.val‖^2) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
    ring
  have hnonneg : 0 ≤ (1-‖a.val‖^2)*(1-‖w.val‖^2) :=
    mul_nonneg (by nlinarith [norm_nonneg a.val]) (by nlinarith [norm_nonneg w.val])
  have hle : ‖a.val-w.val‖ ≤ ‖1-conj a.val*w.val‖ := by
    nlinarith [norm_nonneg (a.val-w.val),norm_nonneg (1-conj a.val*w.val)]
  have hd : 1-conj a.val*w.val ≠ 0 := by
    intro he
    have hnorm := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one,norm_mul,Complex.norm_conj] at hnorm
    have hpr := mul_le_mul_of_nonneg_left hw.le (norm_nonneg a.val)
    nlinarith
  by_cases hz : a.val = 0
  · simpa only [blaschkeFactor,hz,ite_true] using hw.le
  · rw [blaschkeFactor,ite_eq_right hz,norm_div,norm_mul,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg a.val),div_self (norm_ne_zero_iff.mpr hz),one_mul]
    exact (div_le_one (norm_pos_iff.mpr hd)).mpr hle

theorem norm_tprod_le_one {I : Type*} (f : I → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) : ‖∏' i, f i‖ ≤ 1 := by
  classical
  by_cases hm : Multipliable f
  · have hp : ∀ s : Finset I, ‖∏ i ∈ s, f i‖ ≤ 1 := by
      intro s
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hf i)
    exact le_of_tendsto hm.hasProd.norm (Eventually.of_forall hp)
  · rw [tprod_eq_one_of_not_multipliable hm,norm_one]

def atomicPoissonKernel (z : ℂ) (t : Boundary) : ℝ :=
  (1-‖z‖^2)/‖fourier (T := 1) 1 t-z‖^2

theorem herglotz_re (z e : ℂ) (he : ‖e‖ = 1) :
    ((e+z)/(e-z)).re = (1-‖z‖^2)/‖e-z‖^2 := by
  rw [Complex.div_re,Complex.normSq_eq_norm_sq,← add_div,Complex.add_re,Complex.sub_re,
    Complex.add_im,Complex.sub_im]
  have hn : e.re*e.re+e.im*e.im = 1 := by
    simpa only [Complex.sq_norm,Complex.normSq_apply,he,one_pow] using (Complex.sq_norm e).symm
  have hz : z.re*z.re+z.im*z.im = ‖z‖^2 := by simp only [Complex.sq_norm,Complex.normSq_apply]
  congr 1
  nlinarith

theorem herglotz_integrable (μ : Measure Boundary) [IsFiniteMeasure μ] (z : Disk) :
    Integrable (fun t => (fourier (T := 1) 1 t+z.val)/(fourier (T := 1) 1 t-z.val)) μ := by
  have hne (t : Boundary) : fourier (T := 1) 1 t-z.val ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    have hz : ‖z.val‖ < 1 := z.property
    simp only [fourier_apply,Circle.norm_coe] at hn
    linarith
  have hc : Continuous (fun t => (fourier (T := 1) 1 t+z.val)/(fourier (T := 1) 1 t-z.val)) :=
    ((fourier (T := 1) 1).continuous.add continuous_const).div
      ((fourier (T := 1) 1).continuous.sub continuous_const) hne
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem singularInner_atom_bound (μ : Measure Boundary) [IsFiniteMeasure μ] (ζ : Boundary) (z : Disk) :
    ‖singularInnerValue μ 1 z.val‖ ≤ Real.exp (-μ.real {ζ}*atomicPoissonKernel z.val ζ) := by
  have hi := herglotz_integrable μ z
  have hp : Integrable (atomicPoissonKernel z.val) μ := by
    have he : (fun t => ((fourier (T := 1) 1 t+z.val)/(fourier (T := 1) 1 t-z.val)).re) = atomicPoissonKernel z.val := by
      funext t
      exact herglotz_re z.val _ (by simp only [fourier_apply,Circle.norm_coe])
    exact he ▸ hi.re
  have hnonneg : ∀ t, 0 ≤ atomicPoissonKernel z.val t := by
    intro t
    apply div_nonneg _ (sq_nonneg _)
    have hz : ‖z.val‖ < 1 := z.property
    nlinarith [norm_nonneg z.val]
  have hbound := setIntegral_le_integral (s := {ζ}) hp (Eventually.of_forall hnonneg)
  rw [integral_singleton,smul_eq_mul] at hbound
  unfold singularInnerValue
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_one,neg_one_mul,Complex.neg_re]
  apply Real.exp_le_exp.mpr
  have hr : (∫ t, (fourier (T := 1) 1 t+z.val)/(fourier (T := 1) 1 t-z.val) ∂μ).re =
      ∫ t, atomicPoissonKernel z.val t ∂μ := by
    change RCLike.re (∫ t, (fourier (T := 1) 1 t+z.val)/(fourier (T := 1) 1 t-z.val) ∂μ) = _
    rw [← integral_re hi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => herglotz_re z.val _ (by simp only [fourier_apply,Circle.norm_coe]))
  rw [hr]
  linarith

theorem canonicalMeasure_atom_bound (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasCanonicalMeasure u μ) (ζ : Boundary) (z : Disk) :
    ‖innerValue u z.val‖ ≤ Real.exp (-μ.real {ζ}*atomicPoissonKernel z.val ζ) := by
  let : IsFiniteMeasure μ := ⟨hμ.1.1⟩
  obtain ⟨a,_ha,α,hα,hval⟩ := hμ.2
  rw [hval z.val z.property,norm_mul,norm_mul,hα,one_mul]
  apply (mul_le_mul_of_nonneg_right (norm_tprod_le_one _ (fun i => ?_)) (norm_nonneg _)).trans
    (by simpa only [one_mul] using singularInner_atom_bound μ ζ z)
  cases h : a i with
  | none => simp only [Option.elim_none,norm_one,le_refl]
  | some w => simpa only [h,Option.elim_some] using norm_blaschkeFactor_le_one w z


theorem stolz_delta_tendsto (ζ : Boundary) (M : ℝ) :
    Tendsto (fun z : ℂ => 1-‖z‖) (StolzFilter ζ M) (𝓝[>] (0 : ℝ)) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (StolzFilter ζ M) (𝓝 1) := by
    have h := (continuous_norm.tendsto (fourier (T := 1) 1 ζ)).mono_left
      (show StolzFilter ζ M ≤ 𝓝 (fourier (T := 1) 1 ζ) from nhdsWithin_le_nhds)
    simpa only [fourier_apply,Circle.norm_coe] using h
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [sub_self] using (tendsto_const_nhds.sub hn :
      Tendsto (fun z : ℂ => (1 : ℝ)-‖z‖) (StolzFilter ζ M) (𝓝 (1-1)))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_pos.mpr hz.1

theorem stolz_poisson_lower (ζ : Boundary) (M : ℝ) (hM : 0 < M) (z : Disk)
    (hz : ‖z.val-fourier (T := 1) 1 ζ‖ ≤ M*(1-‖z.val‖)) :
    1/(M^2*(1-‖z.val‖)) ≤ atomicPoissonKernel z.val ζ := by
  let δ := 1-‖z.val‖
  let d := ‖fourier (T := 1) 1 ζ-z.val‖
  have hδ : 0 < δ := sub_pos.mpr z.property
  have hdl : δ ≤ d := by
    simpa only [δ,d,fourier_apply,Circle.norm_coe] using
      norm_sub_norm_le (fourier (T := 1) 1 ζ) z.val
  have hd : 0 < d := lt_of_lt_of_le hδ hdl
  have hdu : d ≤ M*δ := by simpa only [d,δ,norm_sub_rev] using hz
  have hds : d^2 ≤ M^2*δ^2 := by
    have h := pow_le_pow_left₀ (le_of_lt hd) hdu 2
    simpa only [mul_pow] using h
  have hnum : δ ≤ 1-‖z.val‖^2 := by
    have hr : ‖z.val‖ < 1 := z.property
    dsimp only [δ]
    nlinarith [norm_nonneg z.val]
  change 1/(M^2*δ) ≤ (1-‖z.val‖^2)/d^2
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hM) hδ) (sq_pos_of_pos hd)).mpr
  simp only [one_mul]
  calc
    d^2 ≤ M^2*δ^2 := hds
    _ = δ*(M^2*δ) := by ring
    _ ≤ (1-‖z.val‖^2)*(M^2*δ) := mul_le_mul_of_nonneg_right hnum (by positivity)

/-- A canonical atom kills every fixed inverse power of the radial boundary distance. -/
theorem canonical_atom_flatness (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasCanonicalMeasure u μ) (ζ : Boundary) (hζ : 0 < μ {ζ})
    (M : ℝ) (hM : 1 < M) (k : ℕ) :
    Tendsto (fun z : ℂ => ‖innerValue u z‖*((1-‖z‖)⁻¹)^k) (StolzFilter ζ M) (𝓝 0) := by
  have hμfinite : μ {ζ} < ∞ := lt_of_le_of_lt (measure_mono (subset_univ _)) hμ.1.1
  have hm : 0 < μ.real {ζ} := ENNReal.toReal_pos hζ.ne' hμfinite.ne
  have hMp : 0 < M := lt_trans zero_lt_one hM
  let c := μ.real {ζ}/M^2
  have hc : 0 < c := div_pos hm (sq_pos_of_pos hMp)
  have hi := (stolz_delta_tendsto ζ M).inv_tendsto_nhdsGT_zero
  have hlim : Tendsto (fun z : ℂ => ((1-‖z‖)⁻¹)^k*Real.exp (-c*((1-‖z‖)⁻¹)))
      (StolzFilter ζ M) (𝓝 0) := by
    simpa only [Real.rpow_natCast,Function.comp_def,Pi.inv_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp hi
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hδ : 0 < 1-‖z‖ := sub_pos.mpr hz.1
    positivity
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hδ : 0 < 1-‖z‖ := sub_pos.mpr hz.1
    have hb := canonicalMeasure_atom_bound u μ hμ ζ ⟨z,hz.1⟩
    have hp := stolz_poisson_lower ζ M hMp ⟨z,hz.1⟩ hz.2
    have hpc := mul_le_mul_of_nonneg_left hp hm.le
    have he : c*((1-‖z‖)⁻¹) = μ.real {ζ}*(1/(M^2*(1-‖z‖))) := by
      dsimp only [c]
      field_simp
    have hbound : ‖innerValue u z‖ ≤ Real.exp (-c*((1-‖z‖)⁻¹)) :=
      hb.trans (Real.exp_le_exp.mpr (by nlinarith [hpc]))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ ((1-‖z‖)⁻¹)^k)

theorem canonical_atom_tendsto_zero (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasCanonicalMeasure u μ) (ζ : Boundary) (hζ : 0 < μ {ζ}) (M : ℝ) (hM : 1 < M) :
    Tendsto (innerValue u) (StolzFilter ζ M) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [pow_zero,mul_one] using canonical_atom_flatness u μ hμ ζ hζ M hM 0


/-- A coarse polynomial bound suffices because canonical atomic decay is exponential. -/
theorem poissonError_bound (u : BoundaryLInf) (hu : IsInner u) (φ : BoundaryL2) (z : Disk) :
    ‖poissonError u φ z.val‖ ≤ (∫ t, ‖φ t‖ ∂circleMeasure)*((1-‖z.val‖)⁻¹)^2 := by
  let δ := 1-‖z.val‖
  have hδ : 0 < δ := sub_pos.mpr z.property
  have hden (t : Boundary) : δ ≤ ‖fourier (T := 1) 1 t-z.val‖ := by
    simpa only [δ,fourier_apply,Circle.norm_coe] using norm_sub_norm_le (fourier (T := 1) 1 t) z.val
  have hweight (t : Boundary) : 0 ≤ atomicPoissonKernel z.val t ∧ atomicPoissonKernel z.val t ≤ (δ⁻¹)^2 := by
    have hd := lt_of_lt_of_le hδ (hden t)
    have hn : 0 ≤ 1-‖z.val‖^2 := by have hz : ‖z.val‖ < 1 := z.property; nlinarith [norm_nonneg z.val]
    refine ⟨div_nonneg hn (sq_nonneg _),?_⟩
    change (1-‖z.val‖^2)/‖fourier (T := 1) 1 t-z.val‖^2 ≤ (δ⁻¹)^2
    rw [inv_pow,← one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hδ)).mpr
    have hs := pow_le_pow_left₀ hδ.le (hden t) 2
    nlinarith [sq_nonneg ‖z.val‖]
  let F := fun t : Boundary => conj (u t)*φ t*((atomicPoissonKernel z.val t : ℝ) : ℂ)
  have hct : Continuous (fun t : Boundary => ((atomicPoissonKernel z.val t : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply continuous_const.div
      ((((fourier (T := 1) 1).continuous.sub continuous_const).norm).pow 2)
    intro t
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hδ (hden t)))
  have hmeas : AEStronglyMeasurable F circleMeasure :=
    ((Lp.aestronglyMeasurable u).star.mul (Lp.aestronglyMeasurable φ)).mul hct.aestronglyMeasurable
  have hφ : Integrable (fun t => φ t) circleMeasure := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp φ)
  have hdom : Integrable (fun t => (δ⁻¹)^2*‖φ t‖) circleMeasure := hφ.norm.const_mul _
  have hb : ∀ᵐ t ∂circleMeasure, ‖F t‖ ≤ (δ⁻¹)^2*‖φ t‖ := by
    filter_upwards [hu.2] with t ht
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_conj,ht,one_mul,Complex.norm_real,
      Real.norm_of_nonneg (hweight t).1]
    exact (mul_le_mul_of_nonneg_left (hweight t).2 (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hF : Integrable F circleMeasure := hdom.mono' hmeas hb
  change ‖∫ t, F t ∂circleMeasure‖ ≤ _
  calc
    _ ≤ ∫ t, ‖F t‖ ∂circleMeasure := norm_integral_le_integral_norm F
    _ ≤ ∫ t, (δ⁻¹)^2*‖φ t‖ ∂circleMeasure := integral_mono_ae hF.norm hdom hb
    _ = (δ⁻¹)^2*(∫ t, ‖φ t‖ ∂circleMeasure) := integral_const_mul _ _
    _ = _ := mul_comm _ _

/-- The full source-specific atomic decay input, including its literal Poisson error. -/
theorem atomicDecay : AtomicDecayObligation := by
  intro u hu _ μ hμ ζ hζ φ M hM
  refine ⟨canonical_atom_tendsto_zero u μ hμ ζ hζ M hM,?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hflat := canonical_atom_flatness u μ hμ ζ hζ M hM 2
  have hlim := hflat.mul_const (∫ t, ‖φ.val t‖ ∂circleMeasure)
  simp only [zero_mul] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [norm_mul]
  have hb := mul_le_mul_of_nonneg_left (poissonError_bound u hu φ.val ⟨z,hz.1⟩) (norm_nonneg (innerValue u z))
  convert hb using 1; ring


/-- Finite-rank maps send bounded weakly null families to norm-null families. -/
theorem finiteRank_tendsto_zero_of_inner {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L : Filter I) (f : I → H)
    (hf : ∀ v : H, Tendsto (fun i => inner ℂ v (f i)) L (𝓝 0))
    (R : H →L[ℂ] H) (hR : FiniteRank R) : Tendsto (fun i => R (f i)) L (𝓝 0) := by
  classical
  obtain ⟨n,hn⟩ := hR
  let : FiniteDimensional ℂ R.range := Module.rank_lt_aleph0_iff.mp
    (hn.trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
  let b := stdOrthonormalBasis ℂ R.range
  have hcoeff (j : Fin (Module.finrank ℂ R.range)) :
      Tendsto (fun i => inner ℂ (b j).val (R (f i))) L (𝓝 0) := by
    convert hf (R.adjoint (b j).val) using 1
    funext i
    exact (R.adjoint_inner_left (f i) (b j).val).symm
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => (hcoeff j).smul_const (b j).val)
  simp only [zero_smul,Finset.sum_const_zero] at hsum
  convert hsum using 1
  funext i
  have he := congrArg (fun v : R.range => v.val) (b.sum_repr' (R.rangeRestrict (f i)))
  simp only [Submodule.coe_sum,Submodule.coe_smul] at he
  change (∑ j, inner ℂ (b j).val (R (f i)) • (b j).val) = R (f i) at he
  exact he.symm

/-- Compact maps send unit-bounded weakly null families to norm-null families. -/
theorem compact_tendsto_zero_of_inner {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L : Filter I) (f : I → H)
    (hb : ∀ i, ‖f i‖ ≤ 1) (hf : ∀ v : H, Tendsto (fun i => inner ℂ v (f i)) L (𝓝 0))
    (A : H →L[ℂ] H) (hA : IsCompactOperator A) : Tendsto (fun i => A (f i)) L (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR,he⟩ := compact_finiteRank_approx A hA (ε/2) (by positivity)
  have hr := finiteRank_tendsto_zero_of_inner L f hf R hR
  filter_upwards [Metric.tendsto_nhds.mp hr (ε/2) (by positivity)] with i hi
  rw [dist_zero_right] at hi ⊢
  calc
    ‖A (f i)‖ ≤ ‖(A-R) (f i)‖+‖R (f i)‖ := by
      simpa only [sub_apply,sub_add_cancel] using norm_add_le ((A-R) (f i)) (R (f i))
    _ ≤ ‖A-R‖*‖f i‖+‖R (f i)‖ := by have hh := (A-R).le_opNorm (f i); linarith
    _ ≤ ε/2+‖R (f i)‖ := by
      have hb' : ‖A-R‖*‖f i‖ ≤ ε/2 :=
        (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)).trans (by simpa only [mul_one] using he)
      linarith
    _ < ε := by linarith


/-- Uniformly unit-bounded families may be tested on a dense linear family. -/
theorem tendsto_inner_of_dense_tests {H I W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (L : Filter I) (f : I → H) (hb : ∀ i, ‖f i‖ ≤ 1)
    (k : W → H) (hd : Dense (Submodule.span ℂ (Set.range k) : Set H))
    (hk : ∀ w, Tendsto (fun i => inner ℂ (k w) (f i)) L (𝓝 0)) :
    ∀ v : H, Tendsto (fun i => inner ℂ v (f i)) L (𝓝 0) := by
  have hspan : ∀ v ∈ Submodule.span ℂ (Set.range k), Tendsto (fun i => inner ℂ v (f i)) L (𝓝 0) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨w,rfl⟩ := hv; exact hk w
    | zero => simpa only [inner_zero_left] using (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℂ)) L (𝓝 0))
    | add v w _ _ hv hw => simpa only [inner_add_left,add_zero] using hv.add hw
    | smul c v _ hv => simpa only [inner_smul_left,mul_zero] using hv.const_mul (conj c)
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha,hda⟩ := Metric.mem_closure_iff.mp (hd v) (ε/2) (by positivity)
  have hva : ‖v-a‖ < ε/2 := by simpa only [dist_eq_norm] using hda
  have hlim := hspan a ha
  filter_upwards [Metric.tendsto_nhds.mp hlim (ε/2) (by positivity)] with i hi
  rw [dist_zero_right] at hi ⊢
  have he : inner ℂ v (f i) = inner ℂ (v-a) (f i)+inner ℂ a (f i) := by
    rw [← inner_add_left,sub_add_cancel]
  rw [he]
  have hn := norm_inner_le_norm (𝕜 := ℂ) (v-a) (f i)
  have hp := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg (v-a))
  have hs := norm_add_le (inner ℂ (v-a) (f i)) (inner ℂ a (f i))
  nlinarith


/-- Zero extension outside the disk is used only to state ordinary filter limits. -/
def unitModelKernelAt (u : BoundaryLInf) (hu : IsInner u) (z : ℂ) : Model u := by
  classical
  exact if hz : z ∈ disk then NormedSpace.normalize (modelReproducingKernel u hu ⟨z,hz⟩) else 0

theorem unitModelKernelAt_norm_le (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (z : ℂ) :
    ‖unitModelKernelAt u hu z‖ ≤ 1 := by
  unfold unitModelKernelAt
  split_ifs with hz
  · rw [norm_normalize_modelReproducingKernel u hu hn]
  · simp only [norm_zero,zero_le_one]

theorem inverse_modelKernel_norm (u : BoundaryLInf) (hu : IsInner u) (z : Disk) :
    ‖modelReproducingKernel u hu z‖⁻¹ =
      Real.sqrt ((1-‖z.val‖^2)/(1-‖innerValue u z.val‖^2)) := by
  rw [norm_modelReproducingKernel,← Real.sqrt_inv,inv_div]

theorem unitModelKernelAt_pair (u : BoundaryLInf) (hu : IsInner u) (w z : Disk) :
    inner ℂ (modelReproducingKernel u hu w) (unitModelKernelAt u hu z.val) =
      ((Real.sqrt ((1-‖z.val‖^2)/(1-‖innerValue u z.val‖^2)) : ℝ) : ℂ)*
        conj (kernelValue u w.val z.val) := by
  unfold unitModelKernelAt
  rw [dite_eq_left z.property]
  have he : NormedSpace.normalize (modelReproducingKernel u hu z) =
      (((‖modelReproducingKernel u hu z‖⁻¹ : ℝ) : ℂ)) • modelReproducingKernel u hu z := by
    rw [NormedSpace.normalize]
    exact (Complex.coe_smul ..).symm
  rw [he,inner_smul_right (𝕜 := ℂ) (E := Model u),inverse_modelKernel_norm]
  congr 1
  rw [← inner_conj_symm (𝕜 := ℂ),inner_modelReproducingKernel,
    analyticValue_modelReproducingKernel u hu w z.property]

/-- Fixed model-kernel tests vanish along every angle when u tends to zero. -/
theorem unitModelKernelAt_test_tendsto (u : BoundaryLInf) (hu : IsInner u)
    (ζ : Boundary) (M : ℝ) (hzero : Tendsto (innerValue u) (StolzFilter ζ M) (𝓝 0)) (w : Disk) :
    Tendsto (fun z => inner ℂ (modelReproducingKernel u hu w) (unitModelKernelAt u hu z))
      (StolzFilter ζ M) (𝓝 0) := by
  let L := StolzFilter ζ M
  let e := fourier (T := 1) 1 ζ
  have hz : Tendsto (fun z : ℂ => z) L (𝓝 e) := nhdsWithin_le_nhds
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) L (𝓝 1) := by
    simpa only [e,fourier_apply,Circle.norm_coe] using hz.norm
  have hnum : Tendsto (fun z : ℂ => 1-‖z‖^2) L (𝓝 0) := by
    simpa only [one_pow,sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hnorm.pow 2)
  have hden : Tendsto (fun z : ℂ => 1-‖innerValue u z‖^2) L (𝓝 1) := by
    simpa only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using
      tendsto_const_nhds.sub (hzero.norm.pow 2)
  have ha : Tendsto (fun z : ℂ => Real.sqrt ((1-‖z‖^2)/(1-‖innerValue u z‖^2))) L (𝓝 0) := by
    simpa only [zero_div,Real.sqrt_zero,Pi.div_apply] using (hnum.div hden one_ne_zero).sqrt
  have hkv : Tendsto (fun z => kernelValue u w.val z) L (𝓝 (1/(1-conj w.val*e))) := by
    unfold kernelValue
    have h := ((tendsto_const_nhds (x := (1 : ℂ))).sub
      (hzero.const_mul (conj (innerValue u w.val)))).div
      ((tendsto_const_nhds (x := (1 : ℂ))).sub (hz.const_mul (conj w.val)))
      (kernelDenominator_ne_zero w ζ)
    simp only [mul_zero,sub_zero] at h
    convert h using 1
  have hca := (Complex.continuous_ofReal.tendsto 0).comp ha
  have ht : Tendsto (fun z : ℂ => (((Real.sqrt ((1-‖z‖^2)/(1-‖innerValue u z‖^2)) : ℝ) : ℂ))*
      conj (kernelValue u w.val z)) L (𝓝 0) := by
    have h := hca.mul hkv.star
    simp only [Complex.ofReal_zero,zero_mul] at h
    convert h using 1
    funext z
    rfl
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (unitModelKernelAt_pair u hu w ⟨z,hz.1⟩).symm

/-- All actual Hilbert tests vanish; kernel totality and unit boundedness supply the extension. -/
theorem unitModelKernelAt_weak_tendsto (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (ζ : Boundary) (M : ℝ) (hzero : Tendsto (innerValue u) (StolzFilter ζ M) (𝓝 0)) :
    ∀ v : Model u, Tendsto (fun z => inner ℂ v (unitModelKernelAt u hu z)) (StolzFilter ζ M) (𝓝 0) :=
  tendsto_inner_of_dense_tests _ _ (unitModelKernelAt_norm_le u hu hn) (modelReproducingKernel u hu)
    (modelReproducingKernels_dense u hu) (unitModelKernelAt_test_tendsto u hu ζ M hzero)


/-- Literal compact Berezin limit along any fixed Stolz region where u tends to zero. -/
theorem compact_berezin_tendsto (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (ζ : Boundary) (M : ℝ) (hzero : Tendsto (innerValue u) (StolzFilter ζ M) (𝓝 0))
    (X : Model u →L[ℂ] Model u) (c : ℂ)
    (hX : IsCompactOperator (X-c • ContinuousLinearMap.id ℂ (Model u))) :
    Tendsto (berezin (fun w => NormedSpace.normalize (modelReproducingKernel u hu w)) X)
      (StolzFilter ζ M) (𝓝 c) := by
  let L := StolzFilter ζ M
  let f := unitModelKernelAt u hu
  let A := X-c • ContinuousLinearMap.id ℂ (Model u)
  have hb : ∀ z, ‖f z‖ ≤ 1 := unitModelKernelAt_norm_le u hu hn
  have hw : ∀ v : Model u, Tendsto (fun z => inner ℂ v (f z)) L (𝓝 0) :=
    unitModelKernelAt_weak_tendsto u hu hn ζ M hzero
  have ht := compact_tendsto_zero_of_inner L f hb hw A hX
  have hs : Tendsto (fun z => inner ℂ (f z) (A (f z))) L (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have htn := ht.norm
    simp only [norm_zero] at htn
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun z => ?_) htn
    calc
      ‖inner ℂ (f z) (A (f z))‖ ≤ ‖f z‖*‖A (f z)‖ := norm_inner_le_norm _ _
      _ ≤ 1*‖A (f z)‖ := mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)
      _ = _ := one_mul _
  have hsc : Tendsto (fun z => inner ℂ (f z) (A (f z))+c) L (𝓝 c) := by
    simpa only [zero_add] using hs.add_const c
  apply hsc.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hf : f z = NormedSpace.normalize (modelReproducingKernel u hu ⟨z,hz.1⟩) := by
    change unitModelKernelAt u hu z = _
    unfold unitModelKernelAt
    rw [dite_eq_left hz.1]
  have hnorm : ‖f z‖ = 1 := by rw [hf]; exact norm_normalize_modelReproducingKernel u hu hn ⟨z,hz.1⟩
  unfold berezin
  rw [dite_eq_left hz.1]
  change inner ℂ (f z) (A (f z))+c =
    inner ℂ (NormedSpace.normalize (modelReproducingKernel u hu ⟨z,hz.1⟩))
      (X (NormedSpace.normalize (modelReproducingKernel u hu ⟨z,hz.1⟩)))
  rw [← hf]
  change inner ℂ (f z) ((X-c • ContinuousLinearMap.id ℂ (Model u)) (f z))+c = inner ℂ (f z) (X (f z))
  rw [sub_apply,smul_apply,ContinuousLinearMap.id_apply,inner_sub_right,
    inner_smul_right (𝕜 := ℂ) (E := Model u),inner_self_eq_norm_sq_to_K,hnorm]
  norm_num

/-- Both clauses of the actual canonical-atom Berezin input are proved. -/
theorem atomicBerezin : AtomicBerezinObligation := by
  intro u hu hn μ hμ ζ hζ
  refine ⟨fun w => NormedSpace.normalize (modelReproducingKernel u hu w),?_,?_,?_⟩
  · intro w
    exact normalizedModelKernel_normalize u hu w
  · intro X c hX M hM
    exact compact_berezin_tendsto u hu hn ζ M (canonical_atom_tendsto_zero u μ hμ ζ hζ M hM) X c hX
  · intro φ X hX z hz
    exact berezin_poisson_identity u hu hn φ X hX z hz

/-- Full manuscript Lemma 6, for arbitrary inner u with a positive canonical-measure atom. -/
theorem compactScalarAngularLimitTheorem : AtomicBoundaryConclusion :=
  Reduction.compactScalarAngularLimit atomicBerezin atomicDecay

end TTO.Paper.Proved
