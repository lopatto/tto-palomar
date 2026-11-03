/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedBlaschkeFoundations

/-! Literal normalized Szegő rank-one kernels for a trace-class synthesis probe.
No Peller sufficiency, converse or all-p classification is asserted here. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

def szegoConjugatePoint (w : Disk) : Disk :=
  ⟨conj w.val,by
    change ‖conj w.val‖ < 1
    simpa only [Complex.norm_conj] using! (show ‖w.val‖ < 1 from w.property)⟩

/-- Output k_conj(w), input evaluation at w. Both conjugations matter. -/
def normalizedSzegoRankOne (w : Disk) : Hardy →L[ℂ] Hardy :=
  InnerProductSpace.rankOne ℂ
    (((1-‖w.val‖^2 : ℝ) : ℂ) • szegoKernel (szegoConjugatePoint w)) (szegoKernel w)

theorem normalizedSzegoRankOne_matrix (w : Disk) (i j : ℕ) :
    inner ℂ (hardyBasis i) (normalizedSzegoRankOne w (hardyBasis j)) =
      ((1-‖w.val‖^2 : ℝ) : ℂ) * w.val^(i+j) := by
  have hIn : inner ℂ (szegoKernel w) (hardyBasis j) = w.val^j := by
    rw [inner_szegoKernel,hardyBasis_apply]
    exact analyticValue_fourierBasis j w.val
  have hOut : inner ℂ (hardyBasis i) (szegoKernel (szegoConjugatePoint w)) = w.val^i := by
    rw [← inner_conj_symm,inner_szegoKernel,hardyBasis_apply]
    change conj (analyticValue (fourierBasis (T := 1) (i : ℤ)) (conj w.val)) = w.val^i
    rw [analyticValue_fourierBasis i (conj w.val),map_pow,Complex.conj_conj]
  rw [normalizedSzegoRankOne,InnerProductSpace.rankOne_apply,
    inner_smul_right (𝕜 := ℂ) (E := Hardy),inner_smul_right (𝕜 := ℂ) (E := Hardy),hIn,hOut,pow_add]
  ring

theorem normalizedSzegoRankOne_rank_le_one (w : Disk) :
    (normalizedSzegoRankOne w).rank ≤ (1 : Cardinal) := by
  let V : Submodule ℂ Hardy := Submodule.span ℂ ({szegoKernel (szegoConjugatePoint w)} : Set Hardy)
  have hRange : (normalizedSzegoRankOne w).range ≤ V := by
    rintro y ⟨x,rfl⟩
    change (inner ℂ (szegoKernel w) x) •
      (((1-‖w.val‖^2 : ℝ) : ℂ) • szegoKernel (szegoConjugatePoint w)) ∈ V
    rw [smul_smul]
    exact V.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  have hVrank : Module.rank ℂ V ≤ (1 : Cardinal) := by
    simpa only [V,Cardinal.mk_singleton] using
      rank_span_le ({szegoKernel (szegoConjugatePoint w)} : Set Hardy)
  exact (Submodule.rank_mono hRange).trans hVrank

theorem norm_normalizedSzegoRankOne (w : Disk) : ‖normalizedSzegoRankOne w‖ = 1 := by
  have hw0 : ‖w.val‖ < 1 := w.property
  have hw : 0 < 1-‖w.val‖^2 := by nlinarith [hw0,norm_nonneg w.val]
  have hconj : ‖szegoKernel (szegoConjugatePoint w)‖ = ‖szegoKernel w‖ := by
    simp only [norm_szegoKernel,szegoConjugatePoint,Complex.norm_conj]
  rw [normalizedSzegoRankOne,InnerProductSpace.norm_rankOne,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg hw.le,hconj,mul_assoc,← pow_two,norm_szegoKernel_sq]
  exact mul_inv_cancel₀ hw.ne'

theorem normalizedSzegoRankOne_schatten_one (w : Disk) :
    Schatten 1 (normalizedSzegoRankOne w) ∧ schattenNorm 1 (normalizedSzegoRankOne w) = 1 := by
  obtain ⟨hs,hn⟩ := schatten_one_of_rank_le_one (normalizedSzegoRankOne w)
    (normalizedSzegoRankOne_rank_le_one w)
  exact ⟨hs,hn.trans (norm_normalizedSzegoRankOne w)⟩

theorem normalizedSzegoRankOne_eq_smul (w : Disk) :
    normalizedSzegoRankOne w = ((1-‖w.val‖^2 : ℝ) : ℂ) •
      (InnerProductSpace.rankOne ℂ (szegoKernel (szegoConjugatePoint w)) (szegoKernel w)) := by
  apply ContinuousLinearMap.ext
  intro f
  change (inner ℂ (szegoKernel w) f) •
    (((1-‖w.val‖^2 : ℝ) : ℂ) • szegoKernel (szegoConjugatePoint w)) =
      ((1-‖w.val‖^2 : ℝ) : ℂ) • ((inner ℂ (szegoKernel w) f) • szegoKernel (szegoConjugatePoint w))
  exact smul_comm _ _ _

/-- The literal Szegő kernel varies in the native Hardy norm, not only weakly. -/
theorem continuous_szegoKernel : Continuous (szegoKernel : Disk → Hardy) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hNC : Continuous (fun z : Disk => (1-‖z.val‖^2)⁻¹) := by
    apply (continuous_const.sub (continuous_subtype_val.norm.pow 2)).inv₀
    intro z
    have hz : ‖z.val‖ < 1 := z.property
    change 1-‖z.val‖^2 ≠ 0
    exact ne_of_gt (by nlinarith [norm_nonneg z.val])
  have hKC : Continuous (fun z : Disk => (1-conj w.val*z.val)⁻¹) := by
    apply (continuous_const.sub (continuous_const.mul continuous_subtype_val)).inv₀
    intro z
    have hw : ‖w.val‖ < 1 := w.property
    have hz : ‖z.val‖ < 1 := z.property
    have hp : ‖conj w.val*z.val‖ < 1 := by
      rw [norm_mul,Complex.norm_conj]
      nlinarith [norm_nonneg w.val,norm_nonneg z.val]
    intro he
    change 1-conj w.val*z.val=0 at he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one] at hn
    linarith
  let G : Disk → ℝ := fun z =>
    (1-‖z.val‖^2)⁻¹ - 2*((1-conj w.val*z.val)⁻¹).re + ‖szegoKernel w‖^2
  have hGC : Continuous G :=
    (hNC.sub (continuous_const.mul (Complex.continuous_re.comp hKC))).add continuous_const
  have hEq (z : Disk) : ‖szegoKernel z-szegoKernel w‖^2 = G z := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_szegoKernel_sq,inner_szegoKernel,
      analyticValue_szegoKernel w z.property]
    rfl
  have hG0 : G w=0 := by
    rw [← hEq w,sub_self,norm_zero,zero_pow (by decide)]
  have hSq : Tendsto (fun z : Disk => ‖szegoKernel z-szegoKernel w‖^2) (𝓝 w) (𝓝 0) := by
    simpa only [hEq,hG0] using hGC.tendsto w
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hSq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using! hroot

theorem continuous_szegoConjugatePoint : Continuous szegoConjugatePoint := by
  apply Continuous.subtype_mk
  exact Complex.continuous_conj.comp continuous_subtype_val

theorem continuous_normalizedSzegoRankOne : Continuous normalizedSzegoRankOne := by
  have hOut : Continuous (fun w : Disk =>
      ((1-‖w.val‖^2 : ℝ) : ℂ) • szegoKernel (szegoConjugatePoint w)) :=
    (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_subtype_val.norm.pow 2))).smul
      (continuous_szegoKernel.comp continuous_szegoConjugatePoint)
  have hL : Continuous (fun w : Disk => ContinuousLinearMap.toSpanSingleton ℂ
      (((1-‖w.val‖^2 : ℝ) : ℂ) • szegoKernel (szegoConjugatePoint w))) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ Hardy).continuous.comp hOut
  have hR : Continuous (fun w : Disk => innerSL ℂ (szegoKernel w)) :=
    (innerSL ℂ).continuous.comp continuous_szegoKernel
  simpa only [normalizedSzegoRankOne,InnerProductSpace.rankOne_def'] using! hL.clm_comp hR

theorem stronglyMeasurable_normalizedSzegoRankOne : StronglyMeasurable normalizedSzegoRankOne := by
  let : TopologicalSpace.PseudoMetrizableSpace (Hardy →L[ℂ] Hardy) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (Hardy →L[ℂ] Hardy) inferInstance
  exact continuous_normalizedSzegoRankOne.stronglyMeasurable

/-- Literal zero extension; no boundary continuity is asserted. -/
def weightedSzegoRankOneZero (F : ℂ → ℂ) : ℂ → (Hardy →L[ℂ] Hardy) :=
  Function.extend (Subtype.val : Disk → ℂ)
    (fun w => F w.val • normalizedSzegoRankOne w) (fun _ => 0)

theorem weightedSzegoRankOneZero_on (F : ℂ → ℂ) (w : Disk) :
    weightedSzegoRankOneZero F w.val = F w.val • normalizedSzegoRankOne w := by
  exact Subtype.val_injective.extend_apply _ _ w

theorem weightedSzegoRankOneZero_off (F : ℂ → ℂ) (z : ℂ) (hz : z ∉ disk) :
    weightedSzegoRankOneZero F z = 0 := by
  apply Function.extend_apply'
  rintro ⟨w,he⟩
  exact hz (he ▸ w.property)

theorem stronglyMeasurable_weightedSzegoRankOneZero (F : ℂ → ℂ)
    (hF : ContinuousOn F disk) : StronglyMeasurable (weightedSzegoRankOneZero F) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Hardy →L[ℂ] Hardy) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (Hardy →L[ℂ] Hardy) inferInstance
  have h : Continuous (fun w : Disk => F w.val • normalizedSzegoRankOne w) :=
    hF.domRestrict.smul continuous_normalizedSzegoRankOne
  exact (MeasurableEmbedding.subtype_coe
    (isOpen_lt continuous_norm continuous_const).measurableSet).stronglyMeasurable_extend
      h.stronglyMeasurable stronglyMeasurable_const

theorem weightedSzegoRankOneZero_schatten_one (F : ℂ → ℂ) (z : ℂ) :
    Schatten 1 (weightedSzegoRankOneZero F z) ∧
      schattenNorm 1 (weightedSzegoRankOneZero F z) ≤ ‖F z‖ := by
  by_cases hz : z ∈ disk
  · rw [weightedSzegoRankOneZero_on F ⟨z,hz⟩]
    obtain ⟨hS,hN⟩ := normalizedSzegoRankOne_schatten_one ⟨z,hz⟩
    exact ⟨schatten_smul hS (F z),by
      simpa only [hN,mul_one] using schattenNorm_smul_le hS (F z)⟩
  · rw [weightedSzegoRankOneZero_off F z hz]
    exact ⟨schatten_zero 1 (by norm_num),by
      rw [schattenNorm_zero 1 (by norm_num)]
      exact norm_nonneg _⟩

end TTO.Paper.Proved
