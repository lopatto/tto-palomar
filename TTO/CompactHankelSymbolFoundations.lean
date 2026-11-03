/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelPolynomialBoundFoundations
public import TTO.ContinuousHankelFoundations
public import TTO.BanachCorrectionFoundations
public import TTO.PoissonHankelSmoothingFoundations

/-! Actual compact Hankel residuals and continuous-symbol lifting.
The literal mean-oscillation VMOA criterion remains separate. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance compactSymbolHankelNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance compactSymbolHankelSpace : NormedSpace ℂ HankelOperator := inferInstance

theorem representsHankel_sub (σ τ : BoundaryL2) (H K : HankelOperator)
    (hH : RepresentsHankel σ H) (hK : RepresentsHankel τ K) :
    RepresentsHankel (σ-τ) (H-K) := by
  intro f v hf hv
  rw [sub_apply,inner_sub_right,hH f v hf hv,hK f v hf hv,
    coreForm_sub σ τ f.val v.val hf]

/-- Every continuous-symbol residual has a genuine bounded symbol with controlled norm. -/
theorem compact_hankel_residual_bounded_symbol (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (hC : IsCompactOperator H) (a : C(Boundary,ℂ)) :
    ∃ b : BoundaryLInf,‖b‖≤‖H-continuousHankelSymbolMap a‖ ∧
      RepresentsHankel (toL2 b) (H-continuousHankelSymbolMap a) ∧
      IsCompactOperator (H-continuousHankelSymbolMap a) := by
  have hR := representsHankel_sub σ (ContinuousMap.toLp 2 circleMeasure ℂ a)
    H (continuousHankelSymbolMap a) hH (continuousHankelSymbolMap_represents a)
  obtain ⟨b,hb,hSame⟩ := nehari_bounded_symbol_for_symbol _ _ hR
  refine ⟨b,hb,?_,hC.sub (compact_continuousHankelSymbolMap a)⟩
  intro f v hf hv
  exact (hR f v hf hv).trans (hSame f v hf hv)


/-- A compact represented Hankel has controlled corrections at every continuous-symbol residual. -/
theorem compact_hankel_controlled_correction (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (hC : IsCompactOperator H) (x : C(Boundary,ℂ)) :
    ∃ d : C(Boundary,ℂ), ‖d‖≤‖H-continuousHankelSymbolMap x‖ ∧
      ‖H-continuousHankelSymbolMap x-continuousHankelSymbolMap d‖≤
        (1/2 : ℝ)*‖H-continuousHankelSymbolMap x‖ := by
  by_cases hz : H-continuousHankelSymbolMap x=0
  · refine ⟨0,by simp,?_⟩
    simp only [map_zero,sub_zero,hz,norm_zero,mul_zero,le_refl]
  obtain ⟨b,hb,hbR,hRc⟩ := compact_hankel_residual_bounded_symbol σ H hH hC x
  have hpos : 0<‖H-continuousHankelSymbolMap x‖/2 := by
    exact div_pos (norm_pos_iff.mpr hz) (by norm_num)
  obtain ⟨d,hd,_,he⟩ := exists_contracting_continuous_hankel_approximation_lt
    b (H-continuousHankelSymbolMap x) hbR hRc
    (‖H-continuousHankelSymbolMap x‖/2) hpos
  refine ⟨d,hd.trans hb,?_⟩
  rw [norm_sub_rev] at he
  exact he.le.trans_eq (by ring)


/-- Exact continuous lift with a uniform operator-norm bound; no VMOA identification is used. -/
theorem compactHankel_exists_continuous_lift (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (hC : IsCompactOperator H) :
    ∃ a : C(Boundary,ℂ), ‖a‖≤2*‖H‖ ∧
      SameHankel σ (ContinuousMap.toLp 2 circleMeasure ℂ a) := by
  obtain ⟨a,ha,hna⟩ := exists_exact_lift_of_controlled_residual
    continuousHankelSymbolMap H 1 (by norm_num) (fun x => by
      simpa only [one_mul] using compact_hankel_controlled_correction σ H hH hC x)
  refine ⟨a,by simpa only [mul_one] using hna,?_⟩
  have hA := continuousHankelSymbolMap_represents a
  rw [ha] at hA
  intro f v hf hv
  exact (hH f v hf hv).symm.trans (hA f v hf hv)

theorem compactHankel_iff_continuous_lift (σ : BoundaryL2) :
    HasCompactHankel σ ↔ ∃ a : C(Boundary,ℂ),
      SameHankel σ (ContinuousMap.toLp 2 circleMeasure ℂ a) := by
  constructor
  · rintro ⟨H,hH,hC⟩
    obtain ⟨a,_,ha⟩ := compactHankel_exists_continuous_lift σ H hH hC
    exact ⟨a,ha⟩
  · exact continuousHankel_lift_implies_compact σ

/-- The continuous classical-Hankel representative clause of manuscript Theorem 2. -/
theorem compactTTO_iff_continuous_hankel (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (φ : Model u) :
    HasCompactTTO u φ.val ↔ ∃ a : C(Boundary,ℂ),
      SameHankel (hankelSymbol u φ.val) (ContinuousMap.toLp 2 circleMeasure ℂ a) := by
  have he : HasCompactTTO u φ.val ↔ HasCompactHankel (hankelSymbol u φ.val) := by
    constructor
    · rintro ⟨A,ha,hc⟩
      obtain ⟨H,hh,hcomp,_⟩ := (exactHankel u hu hn φ).2.1 A ha
      exact ⟨H,hh,hcomp.mp hc⟩
    · rintro ⟨H,hh,hc⟩
      obtain ⟨A,ha,hcomp,_⟩ := (exactHankel u hu hn φ).2.2 H hh
      exact ⟨A,ha,hcomp.mpr hc⟩
  exact he.trans (compactHankel_iff_continuous_lift _)

/-- The same continuous classical-Hankel criterion for the coanalytic symbol. -/
theorem compactCoanalyticTTO_iff_continuous_hankel (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (φ : Model u) :
    HasCompactTTO u (star φ.val) ↔ ∃ a : C(Boundary,ℂ),
      SameHankel (hankelSymbol u φ.val) (ContinuousMap.toLp 2 circleMeasure ℂ a) := by
  have he : HasCompactTTO u (star φ.val) ↔ HasCompactTTO u φ.val := by
    constructor
    · rintro ⟨A,hA,hC⟩
      exact ⟨A.adjoint,by simpa using coreLaws.adjoint u _ A hA,(adjointLaws.compact A).mpr hC⟩
    · rintro ⟨A,hA,hC⟩
      exact ⟨A.adjoint,coreLaws.adjoint u _ A hA,(adjointLaws.compact A).mpr hC⟩
  exact he.trans (compactTTO_iff_continuous_hankel u hu hn φ)

end TTO.Paper.Proved
