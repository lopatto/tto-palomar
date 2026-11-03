/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelBMOFoundations
public import TTO.HankelArcGeometryFoundations
public import TTO.CompactHankelFoundations
public import TTO.ArcMeanFoundations
public import TTO.ContinuousHankelFoundations

/-! Native Hankel norm controls literal real-arc oscillation; compactness gives VMOA.
The converse VMOA-to-compact theorem remains separate. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem hankel_meanOscillation_le (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H)
    (a b : ℝ) (hab : a<b) (hLen : b-a≤1) :
    meanOscillation g.val a b≤2*(Real.pi+1)*‖H‖ := by
  let w := arcDiskPoint a b hab hLen
  have hE := hankel_centered_poisson_energy g H hH w
  have hM := meanOscillation_le_poisson_energy g.val a b hab hLen
    (analyticValue g.val w.val) hE.1
  have hS : Real.sqrt (∫ t,‖g.val t-analyticValue g.val w.val‖^2*
      atomicPoissonKernel w.val t ∂circleMeasure)≤‖H‖ := by
    exact (Real.sqrt_le_sqrt hE.2).trans_eq (Real.sqrt_sq (norm_nonneg H))
  exact hM.trans (mul_le_mul_of_nonneg_left hS (by positivity))

theorem hardyRadialBoundary_inVMOA (g : Hardy) (n : ℕ) :
    InVMOA (hardyRadialBoundary g (hankelRadius n)).val := by
  rw [← hankelRadialContinuous_toL2 g n]
  apply continuous_toLp_inVMOA
  rw [hankelRadialContinuous_toL2]
  exact (hardyRadialBoundary g (hankelRadius n)).property


theorem hankelRadialResidual_represents (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (n : ℕ) :
    RepresentsHankel (star (multiply coordinate (g.val-(hardyRadialBoundary g (hankelRadius n)).val)))
      (H-hankelRadialOperator H n) := by
  intro f v hf hv
  rw [sub_apply,inner_sub_right,hH f v hf hv,
    hankelRadialOperator_represents g H hH n f v hf hv]
  rw [map_sub,boundary_star_sub,coreForm_sub _ _ _ _ hf]


theorem compactHankel_inVMOA (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hC : IsCompactOperator H) :
    InVMOA g.val := by
  let G : ℕ → BoundaryL2 := fun n => (hardyRadialBoundary g (hankelRadius n)).val
  apply inVMOA_of_uniform_meanOscillation_approximation g.val g.property G
    (fun n => hardyRadialBoundary_inVMOA g n)
  intro ε hε
  have hConst : 0<2*(Real.pi+1) := by positivity
  have ht := tendsto_norm_hankelRadialOperator_sub H hC
  have he : ∀ᶠ n in atTop,‖hankelRadialOperator H n-H‖<ε/(2*(Real.pi+1)) :=
    ht.eventually (gt_mem_nhds (div_pos hε hConst))
  obtain ⟨n,hn⟩ := he.exists
  rw [norm_sub_rev (hankelRadialOperator H n) H] at hn
  refine ⟨n,?_⟩
  intro a b hab hLen
  let d : Hardy := ⟨g.val-G n,hardy.sub_mem g.property (hardyRadialBoundary g (hankelRadius n)).property⟩
  have hd : RepresentsHankel (star (multiply coordinate d.val)) (H-hankelRadialOperator H n) :=
    hankelRadialResidual_represents g H hH n
  calc
    _ ≤ 2*(Real.pi+1)*‖H-hankelRadialOperator H n‖ := hankel_meanOscillation_le d _ hd a b hab hLen
    _ < 2*(Real.pi+1)*(ε/(2*(Real.pi+1))) := mul_lt_mul_of_pos_left hn hConst
    _ = ε := mul_div_cancel₀ _ hConst.ne'

theorem hasCompactHankel_inVMOA (g : BoundaryL2) (hg : g∈hardy)
    (hC : HasCompactHankel (star (multiply coordinate g))) : InVMOA g := by
  obtain ⟨H,hH,hCompact⟩ := hC
  exact compactHankel_inVMOA ⟨g,hg⟩ H hH hCompact

/-- The VMOA necessity clause of manuscript Theorem 2, with all source hypotheses. -/
theorem compactTTO_inVMOA (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (φ : Model u) (hC : HasCompactTTO u φ.val) : InVMOA (conjugation u φ.val) := by
  obtain ⟨A,hA,hCompact⟩ := hC
  obtain ⟨H,hH,hComp,_⟩ := (exactHankel u hu hn φ).2.1 A hA
  exact compactHankel_inVMOA ⟨conjugation u φ.val,(exactHankel u hu hn φ).1⟩ H hH (hComp.mp hCompact)

theorem compactCoanalyticTTO_inVMOA (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (φ : Model u) (hC : HasCompactTTO u (star φ.val)) : InVMOA (conjugation u φ.val) := by
  obtain ⟨A,hA,hCompact⟩ := hC
  apply compactTTO_inVMOA u hu hn φ
  exact ⟨A.adjoint,by simpa using coreLaws.adjoint u _ A hA,(adjointLaws.compact A).mpr hCompact⟩

theorem continuous_hankel_lift_inVMOA (g : BoundaryL2) (hg : g∈hardy)
    (a : C(Boundary,ℂ)) (hSame : SameHankel (star (multiply coordinate g))
      (ContinuousMap.toLp 2 circleMeasure ℂ a)) : InVMOA g :=
  hasCompactHankel_inVMOA g hg (continuousHankel_lift_implies_compact _ ⟨a,hSame⟩)


end TTO.Paper.Proved
