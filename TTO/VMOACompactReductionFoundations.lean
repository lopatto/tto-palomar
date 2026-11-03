/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.VMOARadialApproximationFoundations
public import TTO.HankelVMOAFoundations
public import TTO.HankelSymbolDualityFoundations
public import TTO.CompactHankelSymbolFoundations

/-! A parameterized compactness reduction from an explicit quantitative analytic estimate.
`FiniteHardyL1OscillationEstimate` is an explicit intermediate estimate, proved in
PolarBoxEstimatesFoundations. This module records the reduction using that estimate. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance vmoaReductionHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance vmoaReductionHankelSpace : NormedSpace ℂ HankelOperator := inferInstance

/-- Universal quantitative Hardy L¹ pairing estimate.
The constant coefficient is explicit; oscillation alone cannot detect constants. -/
def FiniteHardyL1OscillationEstimate : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ g : Hardy, ∀ B : ℝ, 0≤B →
    (∀ a b : ℝ, a<b → b-a≤1 → meanOscillation g.val a b≤B) →
    ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g.val (∑ n∈range N,c n • hardyBasis n).val‖ ≤
        C*(‖fourierCoeff g.val 0‖+B)*
          ‖nativeL2toL1 (∑ n∈range N,c n • hardyBasis n).val‖

theorem boundedHankelOperator_norm_le_symbol (a : BoundaryLInf) :
    ‖boundedHankelOperator a‖≤‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro f
  exact (hardy.orthogonal.norm_orthogonalProjectionOnto_apply_le (multiply a f.val)).trans
    (norm_multiply_le a f.val)

/-- The explicit finite pairing bound constructs an actual represented bounded operator. -/
theorem exists_hankel_of_finite_hardy_l1_bound (g : BoundaryL2) (M : ℝ) (hM : 0≤M)
    (hFinite : ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g (∑ n∈range N,c n • hardyBasis n).val‖ ≤
        M*‖nativeL2toL1 (∑ n∈range N,c n • hardyBasis n).val‖) :
    ∃ H : HankelOperator, RepresentsHankel (star (multiply coordinate g)) H ∧ ‖H‖≤M := by
  obtain ⟨a,ha,hSame⟩ := exists_sameHankel_bounded_symbol_of_finite_hardy_l1_bound g M hM hFinite
  refine ⟨boundedHankelOperator a,?_,(boundedHankelOperator_norm_le_symbol a).trans ha⟩
  intro f v hf hv
  exact (boundedHankelOperator_represents a f v hf hv).trans (hSame f v hf hv).symm

theorem hankel_norm_le_of_finite_hardy_l1_bound (g : BoundaryL2) (M : ℝ) (hM : 0≤M)
    (hFinite : ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g (∑ n∈range N,c n • hardyBasis n).val‖ ≤
        M*‖nativeL2toL1 (∑ n∈range N,c n • hardyBasis n).val‖)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    ‖H‖≤M := by
  obtain ⟨K,hK,hNorm⟩ := exists_hankel_of_finite_hardy_l1_bound g M hM hFinite
  rw [representsHankel_unique _ H K hH hK]
  exact hNorm

/-- The actual radial residual has zero constant coefficient, without normalizing g. -/
theorem fourierCoeff_hardyRadialResidual_zero (g : Hardy) (n : ℕ) :
    fourierCoeff (g.val-(hardyRadialBoundary g (hankelRadius n)).val) 0=0 := by
  rw [fourierCoeff_sub_L2]
  have h := fourierCoeff_hardyRadialBoundary g (hankelRadius n)
    (hankelRadius_mem n).1.le (hankelRadius_mem n).2 0
  simpa only [Nat.cast_zero,pow_zero,one_mul] using sub_eq_zero.mpr h.symm



/-- The explicit universal pairing estimate implies compactness.
The estimate is supplied by PolarBoxEstimatesFoundations. -/
theorem compactHankel_of_inVMOA_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate) (g : Hardy) (hg : InVMOA g.val)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g.val)) H) :
    IsCompactOperator H := by
  obtain ⟨C,hC,hPair⟩ := hEstimate
  apply (compact_iff_tendsto_hankelRadialOperator H).mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hSmall : 0<ε/(2*C) := by positivity
  obtain ⟨N,hN⟩ := eventually_atTop.1
    (uniform_hardyRadial_meanOscillation g hg (ε/(2*C)) hSmall)
  refine ⟨N,?_⟩
  intro n hn
  let d : Hardy := g-hardyRadialBoundary g (hankelRadius n)
  have hZero : fourierCoeff d.val 0=0 := fourierCoeff_hardyRadialResidual_zero g n
  have hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation d.val a b≤ε/(2*C) :=
    fun a b hab hLen => (hN n hn a b hab hLen).le
  have hFinite := hPair d (ε/(2*C)) hSmall.le hMO
  have hNorm := hankel_norm_le_of_finite_hardy_l1_bound d.val
    (C*(‖fourierCoeff d.val 0‖+ε/(2*C))) (by positivity) hFinite
    (H-hankelRadialOperator H n) (hankelRadialResidual_represents g H hH n)
  rw [hZero,norm_zero,zero_add] at hNorm
  have hCalc : C*(ε/(2*C))=ε/2 := by field_simp
  rw [hCalc] at hNorm
  rw [dist_zero_right,norm_norm,norm_sub_rev]
  exact hNorm.trans_lt (by linarith)

/-- Actual bounded-operator existence is also derived, not added as a VMOA hypothesis. -/
theorem hasCompactHankel_of_inVMOA_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate) (g : BoundaryL2) (hg : InVMOA g) :
    HasCompactHankel (star (multiply coordinate g)) := by
  obtain ⟨C,hC,hPair⟩ := hEstimate
  obtain ⟨B,hB,hMO⟩ := exists_uniform_meanOscillation_bound g hg
  let G : Hardy := ⟨g,hg.1⟩
  obtain ⟨H,hH,hNorm⟩ := exists_hankel_of_finite_hardy_l1_bound g
    (C*(‖fourierCoeff g 0‖+B)) (by positivity) (hPair G B hB.le hMO)
  exact ⟨H,hH,compactHankel_of_inVMOA_of_finiteHardyL1OscillationEstimate
    ⟨C,hC,hPair⟩ G hg H hH⟩

theorem hartmanObligation_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate) : HartmanObligation := by
  intro g hg
  refine ⟨⟨fun h => hasCompactHankel_inVMOA g hg h,
    fun h => hasCompactHankel_of_inVMOA_of_finiteHardyL1OscillationEstimate hEstimate g h⟩,
    compactHankel_iff_continuous_lift _⟩

/-- Analytic TTO sufficiency from the explicit pairing estimate. -/
theorem compactTTO_of_inVMOA_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (φ : Model u)
    (hVMO : InVMOA (conjugation u φ.val)) : HasCompactTTO u φ.val := by
  obtain ⟨H,hH,hC⟩ := hasCompactHankel_of_inVMOA_of_finiteHardyL1OscillationEstimate
    hEstimate (conjugation u φ.val) hVMO
  obtain ⟨A,hA,hComp,hApprox⟩ := (exactHankel u hu hn φ).2.2 H hH
  exact ⟨A,hA,hComp.mpr hC⟩

theorem compactCoanalyticTTO_of_inVMOA_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (φ : Model u)
    (hVMO : InVMOA (conjugation u φ.val)) : HasCompactTTO u (star φ.val) := by
  obtain ⟨A,hA,hC⟩ := compactTTO_of_inVMOA_of_finiteHardyL1OscillationEstimate
    hEstimate u hu hn φ hVMO
  exact ⟨A.adjoint,coreLaws.adjoint u _ A hA,(adjointLaws.compact A).mpr hC⟩

/-- Principal compactness conclusion from the explicit pairing estimate. -/
theorem compactClassification_of_finiteHardyL1OscillationEstimate
    (hEstimate : FiniteHardyL1OscillationEstimate) : CompactConclusion :=
  compactClassification (hartmanObligation_of_finiteHardyL1OscillationEstimate hEstimate)

end TTO.Paper.Proved
