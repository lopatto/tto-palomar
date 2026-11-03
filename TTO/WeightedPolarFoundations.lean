/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolarCarlesonFoundations
public import TTO.ArcLocalizationFoundations
public import TTO.HardyWeightedEmbeddingReductionFoundations

/-! Actual weighted polar measures and their application to the Hardy embedding.
Uniform kernel box bounds remain an explicit internal proof obligation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Normalized disk area in a real angular window; the radial measure already contains 2r. -/
def realPolarBase : Measure (ℝ × ℝ) :=
  diskRadialMeasure.prod (volume.restrict (Ico (0 : ℝ) 1))

theorem realPolar_angle_measurePreserving :
    MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ico (0 : ℝ) 1)) circleMeasure := by
  rw [restrict_Ico_eq_restrict_Ioc,circleMeasure_eq_volume]
  simpa only [zero_add] using AddCircle.measurePreserving_mk 1 0

/-- Exact normalized area transport: no angular or area normalization factor is omitted. -/
theorem realPolar_measurePreserving :
    MeasurePreserving polarMap realPolarBase diskArea := by
  have hprod := (MeasurePreserving.id diskRadialMeasure).prod realPolar_angle_measurePreserving
  have hdisk : MeasurePreserving diskPolar (diskRadialMeasure.prod circleMeasure) diskArea :=
    ⟨continuous_diskPolar.measurable,diskArea_eq_map_diskPolar.symm⟩
  exact hdisk.comp hprod

theorem realPolarBase_support : PolarSupport realPolarBase := by
  have hr := (Measure.quasiMeasurePreserving_fst
    (μ:=diskRadialMeasure) (ν:=volume.restrict (Ico (0 : ℝ) 1))).ae ae_mem_diskRadialMeasure
  have hθ := (Measure.quasiMeasurePreserving_snd
    (μ:=diskRadialMeasure) (ν:=volume.restrict (Ico (0 : ℝ) 1))).ae
      (ae_restrict_mem measurableSet_Ico)
  filter_upwards [hr,hθ] with p hp hθp
  exact ⟨hp.1.le,hp.2,hθp.1,hθp.2⟩

theorem norm_polarMap_sq (p : ℝ × ℝ) : ‖polarMap p‖^2=p.1^2 := by
  simp only [polarMap,norm_mul,Complex.norm_real,
    show ‖fourier (T:=1) 1 (p.2 : Boundary)‖=1 by simp,mul_one,Real.norm_eq_abs,sq_abs]

/-- Honest zero extension of the actual analytic weighted Cauchy kernel. -/
def diskCauchyKernel (f : BoundaryL2) : ℂ → ℂ :=
  Function.extend (Subtype.val : Disk → ℂ) (fun w => cauchyWeightedHardyKernel f w.val)
    (fun _ => 0)

theorem diskCauchyKernel_on (f : BoundaryL2) (w : Disk) :
    diskCauchyKernel f w.val=cauchyWeightedHardyKernel f w.val :=
  Subtype.val_injective.extend_apply _ _ w

theorem measurable_diskCauchyKernel (f : BoundaryL2) : Measurable (diskCauchyKernel f) := by
  apply StronglyMeasurable.measurable
  apply (MeasurableEmbedding.subtype_coe
    (isOpen_lt continuous_norm continuous_const).measurableSet).stronglyMeasurable_extend
  · apply Continuous.stronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro w
    have he : cauchyWeightedHardyKernel f =
        hardyWeightedPairingKernel (hardy.orthogonalProjectionOnto f) :=
      funext (cauchyWeightedHardyKernel_eq_projection f)
    rw [he]
    exact (analyticOnNhd_hardyWeightedPairingKernel
      (hardy.orthogonalProjectionOnto f) w.val w.property).continuousAt.comp
        continuous_subtype_val.continuousAt
  · exact stronglyMeasurable_const

/-- The genuine density in the real polar variables. -/
def polarKernelDensity (f : BoundaryL2) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1-p.1^2)*‖diskCauchyKernel f (polarMap p)‖^2)

theorem measurable_polarKernelDensity (f : BoundaryL2) : Measurable (polarKernelDensity f) := by
  exact ((measurable_const.sub (measurable_fst.pow_const 2)).mul
    (((measurable_diskCauchyKernel f).comp continuous_polarMap.measurable).norm.pow_const 2)).ennreal_ofReal

/-- The actual measure whose dyadic boxes are the remaining local analytic estimate. -/
def weightedPolarMeasure (f : BoundaryL2) : Measure (ℝ × ℝ) :=
  realPolarBase.withDensity (polarKernelDensity f)

theorem weightedPolarMeasure_support (f : BoundaryL2) :
    PolarSupport (weightedPolarMeasure f) :=
  (withDensity_absolutelyContinuous _ _).ae_le realPolarBase_support


/-- The literal weighted measure transports exactly to weighted normalized disk area.
Only the test function is assumed globally measurable; the analytic kernel is zero-extended. -/
theorem lintegral_weightedPolarMeasure (f : BoundaryL2) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,F (polarMap p) ∂weightedPolarMeasure f)=
      ∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2)*F z ∂diskArea := by
  let D : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((1-‖z‖^2)*‖diskCauchyKernel f z‖^2)
  have hD : Measurable D :=
    ((measurable_const.sub (measurable_id.norm.pow_const 2)).mul
      ((measurable_diskCauchyKernel f).norm.pow_const 2)).ennreal_ofReal
  have he (p : ℝ × ℝ) : polarKernelDensity f p=D (polarMap p) := by
    simp only [polarKernelDensity,D,norm_polarMap_sq]
  rw [weightedPolarMeasure]
  calc
    _ = ∫⁻ p,polarKernelDensity f p*F (polarMap p) ∂realPolarBase := by
      simpa only [Function.comp_def,Pi.mul_apply] using
        lintegral_withDensity_eq_lintegral_mul realPolarBase (measurable_polarKernelDensity f)
          (hF.comp continuous_polarMap.measurable)
    _ = ∫⁻ p,(D*F) (polarMap p) ∂realPolarBase := by
      apply lintegral_congr
      intro p
      rw [he p]
      rfl
    _ = ∫⁻ z,(D*F) z ∂diskArea :=
      realPolar_measurePreserving.lintegral_comp (hD.mul hF)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_diskArea] with z hz
      change D z*F z=_
      dsimp only [D]
      rw [diskCauchyKernel_on f ⟨z,hz⟩]

theorem weightedPolarMeasure_univ (f : BoundaryL2) :
    weightedPolarMeasure f univ=
      ∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2) ∂diskArea := by
  simpa only [lintegral_one,mul_one] using
    lintegral_weightedPolarMeasure f (fun _ => 1) measurable_const

instance weightedPolarMeasure_isFiniteMeasure (f : BoundaryL2) :
    IsFiniteMeasure (weightedPolarMeasure f) := by
  constructor
  rw [weightedPolarMeasure_univ]
  exact (cauchyWeightedHardyKernel_weighted_energy_le f).trans_lt ENNReal.ofReal_lt_top

/-- The whole-mass oscillation estimate is a proved preliminary fact, not a box hypothesis. -/
theorem weightedPolarMeasure_univ_le_oscillation (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B) :
    weightedPolarMeasure f univ≤ENNReal.ofReal (768*B^2) := by
  rw [weightedPolarMeasure_univ]
  exact cauchyWeightedHardyKernel_energy_le_oscillation f B hB hMO

/-- The exact weighted Hardy integral in the frozen embedding is the actual polar-measure
Hardy integral. No boundedness of the Hardy vector is assumed. -/
theorem weightedPolarMeasure_hardy_integral (f : BoundaryL2) (q : Hardy) :
    (∫⁻ p,ENNReal.ofReal (‖analyticValue q.val (polarMap p)‖^2) ∂weightedPolarMeasure f)=
      ∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2*
        ‖analyticValue q.val z‖^2) ∂diskArea := by
  have hp : (fun p => ENNReal.ofReal (‖analyticValue q.val (polarMap p)‖^2))=ᵐ[weightedPolarMeasure f]
      fun p => ENNReal.ofReal (‖diskHardyValue q (polarMap p)‖^2) := by
    filter_upwards [weightedPolarMeasure_support f] with p hp
    rw [← polarHardyValue_eq hp.1 hp.2.1]
    rfl
  rw [lintegral_congr_ae hp,
    lintegral_weightedPolarMeasure f (fun z => ENNReal.ofReal (‖diskHardyValue q z‖^2))
      ((measurable_diskHardyValue q).norm.pow_const 2).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_diskArea] with z hz
  rw [diskHardyValue_on q ⟨z,hz⟩]
  have hw : 0≤1-‖z‖^2 := by
    have hz1 : ‖z‖<1 := hz
    nlinarith [norm_nonneg z]
  exact (ENNReal.ofReal_mul (mul_nonneg hw (sq_nonneg _))).symm

/-- Concrete kernel box control gives the actual weighted Hardy embedding.
The ordinary measure hypothesis is a genuine intermediate estimate, independent of q. -/
theorem hardyWeightedEmbedding_of_polar_box (g : Hardy) (A : ℝ) (hA : 0≤A)
    (hBox : PolarBoxBound (weightedPolarMeasure g.val) A) :
    HardyWeightedEmbedding g (Real.sqrt (1310720*A)) := by
  intro q
  have hk : hardyWeightedPairingKernel g=cauchyWeightedHardyKernel g.val := rfl
  rw [hk,← weightedPolarMeasure_hardy_integral g.val q]
  have h := polar_carleson_embedding_analyticValue hA
    (weightedPolarMeasure_support g.val) hBox q
  have hs : (Real.sqrt (1310720*A))^2=1310720*A := Real.sq_sqrt (by positivity)
  simpa only [hs,mul_assoc,polarMap] using h

/-- A uniform literal box estimate, when proved, discharges the complete frozen weighted
oscillation embedding. This is internal logical glue, not an unconditional Hartman theorem. -/
theorem hardyWeightedOscillationEmbedding_of_polar_boxes (D : ℝ) (hD : 0<D)
    (hBox : ∀ (f : BoundaryL2) (B : ℝ),0≤B →
      (∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B) →
        PolarBoxBound (weightedPolarMeasure f) (D*B^2)) :
    HardyWeightedOscillationEmbedding := by
  refine ⟨Real.sqrt (1310720*D),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro g B hB hMO
  have h := hardyWeightedEmbedding_of_polar_box g (D*B^2)
    (by positivity) (hBox g.val B hB hMO)
  have he : Real.sqrt (1310720*(D*B^2))=Real.sqrt (1310720*D)*B := by
    rw [show 1310720*(D*B^2)=(1310720*D)*B^2 by ring,
      Real.sqrt_mul (by positivity),Real.sqrt_sq hB]
  rw [he] at h
  exact h


/-- On the actual polar support, the zero-extended density is the literal source kernel. -/
theorem polarKernelDensity_ae (f : BoundaryL2) :
    polarKernelDensity f =ᵐ[realPolarBase]
      fun p => ENNReal.ofReal ((1-p.1^2)*‖cauchyWeightedHardyKernel f (polarMap p)‖^2) := by
  filter_upwards [realPolarBase_support] with p hp
  have h : polarMap p∈disk := by
    change ‖polarMap p‖<1
    simp only [polarMap,norm_mul,Complex.norm_real,Real.norm_of_nonneg hp.1,
      show ‖fourier (T:=1) 1 (p.2 : Boundary)‖=1 by simp,mul_one]
    exact hp.2.1
  rw [polarKernelDensity,diskCauchyKernel_on f ⟨polarMap p,h⟩]

/-- Exact box/set mass in the original real polar coordinates. -/
theorem weightedPolarMeasure_apply (f : BoundaryL2) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    weightedPolarMeasure f S=
      ∫⁻ p in S,ENNReal.ofReal ((1-p.1^2)*‖cauchyWeightedHardyKernel f (polarMap p)‖^2)
        ∂realPolarBase := by
  rw [weightedPolarMeasure,withDensity_apply _ hS]
  exact lintegral_congr_ae (ae_restrict_of_ae (polarKernelDensity_ae f))

end TTO.Paper.Proved
