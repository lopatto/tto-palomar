/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CompactHankelFoundations
public import TTO.AtomicFoundations
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-! Actual Poisson probability measures and native Hardy radial Bochner averages. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The actual real radial point at the previously fixed approximation radius. -/
def radialPoissonPoint (n : ℕ) : Disk := ⟨(hankelRadius n : ℂ),by
  simpa only [disk,Set.mem_ofPred_eq,Complex.norm_real,
    Real.norm_of_nonneg (hankelRadius_mem n).1.le] using (hankelRadius_mem n).2⟩

theorem radialPoisson_nonneg (n : ℕ) (s : Boundary) :
    0≤atomicPoissonKernel (hankelRadius n : ℂ) s := by
  apply div_nonneg _ (sq_nonneg _)
  have h := (radialPoissonPoint n).property
  change ‖(hankelRadius n : ℂ)‖<1 at h
  nlinarith [norm_nonneg (hankelRadius n : ℂ)]

theorem continuous_radialPoisson (n : ℕ) :
    Continuous (atomicPoissonKernel (hankelRadius n : ℂ)) := by
  apply continuous_const.div (((fourier (T := 1) 1).continuous.sub continuous_const).norm.pow 2)
  intro s
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (circlePoint_sub_disk_ne_zero s (radialPoissonPoint n)))

theorem integrable_radialPoisson (n : ℕ) :
    Integrable (atomicPoissonKernel (hankelRadius n : ℂ)) circleMeasure :=
  (continuous_radialPoisson n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem radialPoisson_character_moment (n k : ℕ) :
    (∫ s, fourier (T := 1) (k : ℤ) s*
      ((atomicPoissonKernel (hankelRadius n : ℂ) s : ℝ) : ℂ) ∂circleMeasure)=
        (hankelRadius n : ℂ)^k := by
  have h := poissonAverage_hardy (radialPoissonPoint n)
    (⟨fourierBasis (T := 1) (k : ℤ),fourierBasis_mem_hardy k⟩ : Hardy)
  rw [poissonAverage_integral,analyticValue_fourierBasis] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [fourierBasis_ae (k : ℤ)] with s hs
  rw [hs]
  rfl

theorem radialPoisson_integral_one (n : ℕ) :
    (∫ s,atomicPoissonKernel (hankelRadius n : ℂ) s ∂circleMeasure)=1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [Nat.cast_zero,fourier_zero,ContinuousMap.one_apply,one_mul,pow_zero,Complex.ofReal_one] using
    radialPoisson_character_moment n 0

def radialPoissonMeasure (n : ℕ) : Measure Boundary :=
  circleMeasure.withDensity (fun s => ENNReal.ofReal (atomicPoissonKernel (hankelRadius n : ℂ) s))

instance radialPoissonMeasure_probability (n : ℕ) : IsProbabilityMeasure (radialPoissonMeasure n) := by
  constructor
  rw [radialPoissonMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_radialPoisson n)
      (Eventually.of_forall (radialPoisson_nonneg n)),radialPoisson_integral_one,ENNReal.ofReal_one]

theorem boundaryTranslate_eq_domAddAct (s : Boundary) (f : BoundaryL2) :
    boundaryTranslate s f=DomAddAct.mk s +ᵥ f := by
  apply Lp.ext
  filter_upwards [boundaryTranslate_ae s f,DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk s) f] with t ht hd
  rw [ht,hd]
  simp only [Equiv.symm_apply_apply,vadd_eq_add,add_comm]

theorem continuous_boundaryTranslate (f : BoundaryL2) :
    Continuous (fun s : Boundary => boundaryTranslate s f) := by
  have : Fact ((2 : ℝ≥0∞)≠∞) := ⟨by simp⟩
  simp_rw [boundaryTranslate_eq_domAddAct]
  exact DomAddAct.continuous_mk.vadd continuous_const

theorem integrable_radialPoisson_boundaryTranslate (n : ℕ) (f : BoundaryL2) :
    Integrable (fun s => boundaryTranslate s f) (radialPoissonMeasure n) :=
  (continuous_boundaryTranslate f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)



theorem radialPoissonMeasure_character_moment (n k : ℕ) :
    (∫ s,fourier (T := 1) (k : ℤ) s ∂radialPoissonMeasure n)=(hankelRadius n : ℂ)^k := by
  rw [radialPoissonMeasure,integral_withDensity_eq_integral_toReal_smul
    (continuous_radialPoisson n).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hReal (s : Boundary) := ENNReal.toReal_ofReal (radialPoisson_nonneg n s)
  simp_rw [hReal]
  convert radialPoisson_character_moment n k using 1
  congr 1
  funext s
  change ((atomicPoissonKernel (hankelRadius n : ℂ) s : ℝ) : ℂ)*fourier (T := 1) (k : ℤ) s=_
  ring

def radialPoissonAverage (n : ℕ) (f : BoundaryL2) : BoundaryL2 :=
  ∫ s,boundaryTranslate s f ∂radialPoissonMeasure n

theorem fourierCoeff_radialPoisson_average (n : ℕ) (f : BoundaryL2) (k : ℤ) :
    fourierCoeff (radialPoissonAverage n f) k=
      (∫ s,fourier (T := 1) k s ∂radialPoissonMeasure n)*fourierCoeff f k := by
  have hI := integrable_radialPoisson_boundaryTranslate n f
  have h := (innerSL ℂ (fourierBasis (T := 1) k)).integral_comp_comm hI
  have hMap : fourierCoeff (radialPoissonAverage n f) k=
      ∫ s,fourierCoeff (boundaryTranslate s f) k ∂radialPoissonMeasure n := by
    simpa only [radialPoissonAverage,← fourierBasis_repr,HilbertBasis.repr_apply_apply,innerSL_apply_apply] using h.symm
  rw [hMap]
  simp_rw [fourierCoeff_translate]
  rw [integral_mul_const]

theorem radialPoisson_average_eq_hardyRadialBoundary (n : ℕ) (g : Hardy) :
    radialPoissonAverage n g.val=
      (hardyRadialBoundary g (hankelRadius n)).val := by
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext k
  rw [fourierBasis_repr,fourierBasis_repr,fourierCoeff_radialPoisson_average]
  by_cases hk : 0≤k
  · obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [radialPoissonMeasure_character_moment]
    have h := hardyBasis_repr_hardyRadialBoundary g (hankelRadius n)
      (hankelRadius_mem n).1.le (hankelRadius_mem n).2 j
    simpa only [hardyBasis_repr_eq_fourierCoeff,hardyRadialCoeff] using h.symm
  · rw [(mem_hardy_iff g.val).mp g.property k (lt_of_not_ge hk),mul_zero,
      (mem_hardy_iff (hardyRadialBoundary g (hankelRadius n)).val).mp
        (hardyRadialBoundary g (hankelRadius n)).property k (lt_of_not_ge hk)]

end TTO.Paper.Proved
