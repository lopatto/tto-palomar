/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.L2TranslationFoundations
public import TTO.SchattenAveragingFoundations

/-! Literal interval indicators, truncated translations and ordinary compact-operator averaging. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Literal multiplication of an interval L² vector by a measurable indicator. -/
def intervalMaskVector (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (f : IntervalL2 ℓ) :
    IntervalL2 ℓ :=
  (MemLp.indicator hs.nullMeasurableSet (Lp.memLp f)).toLp (s.indicator f)

theorem intervalMaskVector_ae (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (f : IntervalL2 ℓ) :
    intervalMaskVector ℓ s hs f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] s.indicator f :=
  MemLp.coeFn_toLp _

theorem norm_intervalMaskVector_le (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (f : IntervalL2 ℓ) : ‖intervalMaskVector ℓ s hs f‖ ≤ ‖f‖ := by
  rw [intervalMaskVector,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne (eLpNorm_indicator_le f hs.nullMeasurableSet)

theorem intervalMaskVector_add (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (f g : IntervalL2 ℓ) :
    intervalMaskVector ℓ s hs (f+g)=intervalMaskVector ℓ s hs f+intervalMaskVector ℓ s hs g := by
  apply Lp.ext
  filter_upwards [intervalMaskVector_ae ℓ s hs (f+g),intervalMaskVector_ae ℓ s hs f,
    intervalMaskVector_ae ℓ s hs g,Lp.coeFn_add f g,
    Lp.coeFn_add (intervalMaskVector ℓ s hs f) (intervalMaskVector ℓ s hs g)]
    with t hfg hf hg hadd hsum
  rw [hfg,hsum]
  by_cases ht : t∈s
  · simp only [indicator_of_mem ht,Pi.add_apply] at *
    rw [hadd,hf,hg]
  · simp only [indicator_of_notMem ht,Pi.add_apply] at *
    rw [hf,hg,add_zero]

theorem intervalMaskVector_smul (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (c : ℂ) (f : IntervalL2 ℓ) :
    intervalMaskVector ℓ s hs (c • f)=c • intervalMaskVector ℓ s hs f := by
  apply Lp.ext
  filter_upwards [intervalMaskVector_ae ℓ s hs (c • f),intervalMaskVector_ae ℓ s hs f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (intervalMaskVector ℓ s hs f)]
    with t hcf hf hsm hsm'
  rw [hcf,hsm']
  by_cases ht : t∈s
  · simp only [indicator_of_mem ht,Pi.smul_apply] at *
    rw [hsm,hf]
  · simp only [indicator_of_notMem ht,Pi.smul_apply] at *
    rw [hf,smul_zero]

/-- Actual indicator projection on the fixed interval space. -/
def intervalMask (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  ({ toFun := intervalMaskVector ℓ s hs
     map_add' := intervalMaskVector_add ℓ s hs
     map_smul' := intervalMaskVector_smul ℓ s hs } :
      IntervalL2 ℓ →ₗ[ℂ] IntervalL2 ℓ).mkContinuous 1
        (fun f => by simpa only [one_mul] using! norm_intervalMaskVector_le ℓ s hs f)

theorem intervalMask_ae (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (f : IntervalL2 ℓ) :
    intervalMask ℓ s hs f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] s.indicator f :=
  intervalMaskVector_ae ℓ s hs f

theorem norm_intervalMask_le_one (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ‖intervalMask ℓ s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using! norm_intervalMaskVector_le ℓ s hs f

theorem adjoint_intervalMask (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (intervalMask ℓ s hs).adjoint=intervalMask ℓ s hs := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalMask_ae ℓ s hs f,intervalMask_ae ℓ s hs g] with t hf hg
  rw [hf,hg]
  by_cases ht : t∈s
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht,inner_zero_left,inner_zero_right]

theorem intervalMask_comp (ℓ : ℝ) (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    intervalMask ℓ s hs ∘L intervalMask ℓ t ht=intervalMask ℓ (s∩t) (hs.inter ht) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMask_ae ℓ s hs (intervalMask ℓ t ht f),
    intervalMask_ae ℓ t ht f,intervalMask_ae ℓ (s∩t) (hs.inter ht) f] with x hst htf hboth
  change intervalMask ℓ s hs (intervalMask ℓ t ht f) x=_
  rw [hst,hboth]
  by_cases hxs : x∈s <;> by_cases hxt : x∈t <;> simp [hxs,hxt,htf]

theorem intervalMask_idempotent (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    intervalMask ℓ s hs ∘L intervalMask ℓ s hs=intervalMask ℓ s hs := by
  simpa only [inter_self] using intervalMask_comp ℓ s s hs hs

theorem intervalMask_empty (ℓ : ℝ) : intervalMask ℓ ∅ MeasurableSet.empty=0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMask_ae ℓ ∅ MeasurableSet.empty f,
    Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ))] with t hm h0
  simp only [indicator_empty',Pi.zero_apply] at hm h0
  exact hm.trans h0.symm

theorem intervalMask_comp_of_disjoint (ℓ : ℝ) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdis : Disjoint s t) :
    intervalMask ℓ s hs ∘L intervalMask ℓ t ht=0 := by
  rw [intervalMask_comp]
  simpa only [Set.disjoint_iff_inter_eq_empty.mp hdis] using intervalMask_empty ℓ

/-- A literal finite measurable partition modulo null sets gives an exact operator partition. -/
theorem intervalMask_sum_of_partition {ι : Type*} [Fintype ι] (ℓ : ℝ) (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hPart : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) ℓ), ∃! i, t∈s i) :
    (∑ i, intervalMask ℓ (s i) (hs i))=ContinuousLinearMap.id ℂ (IntervalL2 ℓ) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [_root_.sum_apply,ContinuousLinearMap.id_apply]
  apply Lp.ext
  have hAll : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) ℓ),
      ∀ i, intervalMask ℓ (s i) (hs i) f t=(s i).indicator f t :=
    Filter.eventually_all.mpr (fun i => intervalMask_ae ℓ (s i) (hs i) f)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => intervalMask ℓ (s i) (hs i) f),
    hAll,hPart] with t hSum hMask hPart
  rw [hSum]
  obtain ⟨i,hi,hUnique⟩ := hPart
  rw [Finset.sum_eq_single i]
  · rw [hMask i,indicator_of_mem hi]
  · intro j hj hji
    rw [hMask j,indicator_of_notMem (fun hjs => hji (hUnique j hjs))]
  · simp

/-- Native interval restriction of the actual whole-line L² vector. -/
def restrictIntervalVector (ℓ : ℝ) (f : LineL2) : IntervalL2 ℓ :=
  ((Lp.memLp f).restrict (Ioo (0 : ℝ) ℓ)).toLp f

theorem restrictIntervalVector_ae (ℓ : ℝ) (f : LineL2) :
    restrictIntervalVector ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f := MemLp.coeFn_toLp _

theorem norm_restrictIntervalVector_le (ℓ : ℝ) (f : LineL2) :
    ‖restrictIntervalVector ℓ f‖ ≤ ‖f‖ := by
  rw [restrictIntervalVector,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).ne
    (eLpNorm_mono_measure f Measure.restrict_le_self)

theorem restrictIntervalVector_add (ℓ : ℝ) (f g : LineL2) :
    restrictIntervalVector ℓ (f+g)=restrictIntervalVector ℓ f+restrictIntervalVector ℓ g := by
  apply Lp.ext
  filter_upwards [restrictIntervalVector_ae ℓ (f+g),restrictIntervalVector_ae ℓ f,
    restrictIntervalVector_ae ℓ g,ae_restrict_of_ae (Lp.coeFn_add f g),
    Lp.coeFn_add (restrictIntervalVector ℓ f) (restrictIntervalVector ℓ g)]
    with t hfg hf hg hadd hsum
  rw [hfg,hadd,hsum,Pi.add_apply,Pi.add_apply,hf,hg]

theorem restrictIntervalVector_smul (ℓ : ℝ) (c : ℂ) (f : LineL2) :
    restrictIntervalVector ℓ (c • f)=c • restrictIntervalVector ℓ f := by
  apply Lp.ext
  filter_upwards [restrictIntervalVector_ae ℓ (c • f),restrictIntervalVector_ae ℓ f,
    ae_restrict_of_ae (Lp.coeFn_smul c f),Lp.coeFn_smul c (restrictIntervalVector ℓ f)]
    with t hcf hf hsm hsm'
  rw [hcf,hsm,hsm',Pi.smul_apply,Pi.smul_apply,hf]

def restrictIntervalL (ℓ : ℝ) : LineL2 →L[ℂ] IntervalL2 ℓ :=
  ({ toFun := restrictIntervalVector ℓ
     map_add' := restrictIntervalVector_add ℓ
     map_smul' := restrictIntervalVector_smul ℓ } :
      LineL2 →ₗ[ℂ] IntervalL2 ℓ).mkContinuous 1
        (fun f => by simpa only [one_mul] using! norm_restrictIntervalVector_le ℓ f)

theorem restrictIntervalL_ae (ℓ : ℝ) (f : LineL2) :
    restrictIntervalL ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f :=
  restrictIntervalVector_ae ℓ f

theorem norm_restrictIntervalL_le_one (ℓ : ℝ) : ‖restrictIntervalL ℓ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using! norm_restrictIntervalVector_le ℓ f

/-- Actual zero extension of interval L² classes; arbitrary representatives are never used outside. -/
def zeroExtendIntervalVector (ℓ : ℝ) (f : IntervalL2 ℓ) : LineL2 :=
  ((memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr (Lp.memLp f)).toLp
    ((Ioo (0 : ℝ) ℓ).indicator f)

theorem zeroExtendIntervalVector_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    zeroExtendIntervalVector ℓ f =ᵐ[volume] (Ioo (0 : ℝ) ℓ).indicator f :=
  MemLp.coeFn_toLp _

theorem norm_zeroExtendIntervalVector (ℓ : ℝ) (f : IntervalL2 ℓ) :
    ‖zeroExtendIntervalVector ℓ f‖=‖f‖ := by
  rw [zeroExtendIntervalVector,Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo.nullMeasurableSet,Lp.norm_def]

theorem zeroExtendIntervalVector_add (ℓ : ℝ) (f g : IntervalL2 ℓ) :
    zeroExtendIntervalVector ℓ (f+g)=zeroExtendIntervalVector ℓ f+zeroExtendIntervalVector ℓ g := by
  apply Lp.ext
  have hfg := (ae_restrict_iff' measurableSet_Ioo).mp (Lp.coeFn_add f g)
  filter_upwards [zeroExtendIntervalVector_ae ℓ (f+g),zeroExtendIntervalVector_ae ℓ f,
    zeroExtendIntervalVector_ae ℓ g,Lp.coeFn_add (zeroExtendIntervalVector ℓ f) (zeroExtendIntervalVector ℓ g),
    hfg] with t hsum hf hg hadd hfg'
  rw [hsum,hadd,Pi.add_apply,hf,hg]
  by_cases ht : t∈Ioo (0 : ℝ) ℓ
  · simp only [indicator_of_mem ht]
    exact hfg' ht
  · simp only [indicator_of_notMem ht,zero_add]

theorem zeroExtendIntervalVector_smul (ℓ : ℝ) (c : ℂ) (f : IntervalL2 ℓ) :
    zeroExtendIntervalVector ℓ (c • f)=c • zeroExtendIntervalVector ℓ f := by
  apply Lp.ext
  have hcf := (ae_restrict_iff' measurableSet_Ioo).mp (Lp.coeFn_smul c f)
  filter_upwards [zeroExtendIntervalVector_ae ℓ (c • f),zeroExtendIntervalVector_ae ℓ f,
    Lp.coeFn_smul c (zeroExtendIntervalVector ℓ f),hcf] with t hsum hf hsm hcf'
  rw [hsum,hsm,Pi.smul_apply,hf]
  by_cases ht : t∈Ioo (0 : ℝ) ℓ
  · simp only [indicator_of_mem ht]
    exact hcf' ht
  · simp only [indicator_of_notMem ht,smul_zero]

def zeroExtendIntervalIsometry (ℓ : ℝ) : IntervalL2 ℓ →ₗᵢ[ℂ] LineL2 where
  toLinearMap :=
    { toFun := zeroExtendIntervalVector ℓ
      map_add' := zeroExtendIntervalVector_add ℓ
      map_smul' := zeroExtendIntervalVector_smul ℓ }
  norm_map' := norm_zeroExtendIntervalVector ℓ

theorem zeroExtendIntervalIsometry_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    zeroExtendIntervalIsometry ℓ f =ᵐ[volume] (Ioo (0 : ℝ) ℓ).indicator f :=
  zeroExtendIntervalVector_ae ℓ f

theorem inner_zeroExtendInterval_restrict (ℓ : ℝ) (g : IntervalL2 ℓ) (f : LineL2) :
    inner ℂ (zeroExtendIntervalIsometry ℓ g) f=inner ℂ g (restrictIntervalL ℓ f) := by
  rw [L2.inner_def,L2.inner_def]
  have he : (∫ t : ℝ, inner ℂ (zeroExtendIntervalIsometry ℓ g t) (f t)) =
      ∫ t : ℝ, (Ioo (0 : ℝ) ℓ).indicator (fun t => inner ℂ (g t) (f t)) t := by
    apply integral_congr_ae
    filter_upwards [zeroExtendIntervalIsometry_ae ℓ g] with t ht
    rw [ht]
    by_cases hti : t∈Ioo (0 : ℝ) ℓ
    · rw [indicator_of_mem hti,indicator_of_mem hti]
    · rw [indicator_of_notMem hti,indicator_of_notMem hti,inner_zero_left]
  rw [he,integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [restrictIntervalL_ae ℓ f] with t ht
  rw [ht]

theorem adjoint_zeroExtendIntervalIsometry (ℓ : ℝ) :
    (zeroExtendIntervalIsometry ℓ).toContinuousLinearMap.adjoint=restrictIntervalL ℓ := by
  have h : (zeroExtendIntervalIsometry ℓ).toContinuousLinearMap=(restrictIntervalL ℓ).adjoint :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_zeroExtendInterval_restrict ℓ)
  rw [h,ContinuousLinearMap.adjoint_adjoint]

theorem measurePreserving_sub_const_line (r : ℝ) :
    MeasurePreserving (fun t : ℝ => t-r) volume volume := by
  simpa only [vadd_eq_add,sub_eq_add_neg,add_comm] using
    (measurePreserving_vadd (-r) (volume : Measure ℝ))

/-- Whole-line translation as its actual native linear isometry. -/
def lineTranslateIsometry (r : ℝ) : LineL2 →ₗᵢ[ℂ] LineL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => t-r) (measurePreserving_sub_const_line r)

theorem lineTranslateIsometry_eq (r : ℝ) (f : LineL2) :
    lineTranslateIsometry r f=lineTranslate r f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_const_line r),
    lineTranslate_ae r f] with t h₁ h₂
  exact h₁.trans h₂.symm

/-- The manuscript's truncated interval translation, defined for every real shift. -/
def intervalTranslate (ℓ r : ℝ) : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  restrictIntervalL ℓ ∘L (lineTranslateIsometry r).toContinuousLinearMap ∘L
    (zeroExtendIntervalIsometry ℓ).toContinuousLinearMap

theorem intervalTranslate_ae (ℓ r : ℝ) (f : IntervalL2 ℓ) :
    intervalTranslate ℓ r f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      fun t => (Ioo (0 : ℝ) ℓ).indicator f (t-r) := by
  have hExt := (measurePreserving_sub_const_line r).quasiMeasurePreserving.ae
    (zeroExtendIntervalIsometry_ae ℓ f)
  have hTr := lineTranslate_ae r (zeroExtendIntervalIsometry ℓ f)
  filter_upwards [restrictIntervalL_ae ℓ
      (lineTranslateIsometry r (zeroExtendIntervalIsometry ℓ f)),
    ae_restrict_of_ae hExt,ae_restrict_of_ae hTr] with t hRes hExt hTr
  change restrictIntervalL ℓ (lineTranslateIsometry r (zeroExtendIntervalIsometry ℓ f)) t=_
  rw [hRes,lineTranslateIsometry_eq]
  exact hTr.trans hExt

theorem norm_intervalTranslate_le_one (ℓ r : ℝ) : ‖intervalTranslate ℓ r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖restrictIntervalVector ℓ (lineTranslateIsometry r (zeroExtendIntervalIsometry ℓ f))‖ ≤ _
  calc
    _ ≤ ‖lineTranslateIsometry r (zeroExtendIntervalIsometry ℓ f)‖ :=
      norm_restrictIntervalVector_le ℓ _
    _ = ‖f‖ := by rw [(lineTranslateIsometry r).norm_map,(zeroExtendIntervalIsometry ℓ).norm_map]
    _ = _ := (one_mul ‖f‖).symm

theorem continuous_intervalTranslate (ℓ : ℝ) (f : IntervalL2 ℓ) :
    Continuous (fun r : ℝ => intervalTranslate ℓ r f) := by
  have h : Continuous (fun r : ℝ => restrictIntervalL ℓ (lineTranslate r (zeroExtendIntervalIsometry ℓ f))) :=
    (restrictIntervalL ℓ).continuous.comp (continuous_lineTranslate _)
  simpa only [intervalTranslate,ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    lineTranslateIsometry_eq] using h

end TTO.Paper.Proved
