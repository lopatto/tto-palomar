/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalRegularizationFoundations
public import TTO.IntervalSmoothTranslationFoundations
public import TTO.AtomicCoronaFoundations
public import TTO.VolterraSpectrumFoundations

/-! The actual one-atom regularization, with every intermediate Fourier, kernel and ideal input proved. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Source equations (4)--(7), with the original exact triangular constant and a scalar sequence.
The same actual PW coordinates are used for the average, kernel and asymptotic identities. -/
theorem atomicRegularization : AtomicRegularizationObligation := by
  intro p hp τ hτPos hτ u hu hn ζ hζ φ ψ A hRep hSp
  obtain ⟨ℓ,hℓ,U,H,hDense,hBound,hAnalytic,hCoanalytic⟩ := exists_singleAtomPWBothForms u hu ζ hζ
  apply atomicRegularization_data_of_average_pairing p τ hp hτPos hτ u hu hn ℓ hℓ U H
    hDense hBound φ ψ A hSp (hAnalytic φ)
  intro n a b ha hb
  let ε := atomicRegularizationStep ℓ n
  have hε : 0 < ε := atomicRegularizationStep_pos ℓ hℓ n
  have hL : ℓ-ε ≤ ℓ := by linarith
  change inner ℂ (smoothIntervalL2 (ℓ-ε) b hb)
    ((intervalInclusion (ℓ-ε) ℓ).adjoint
      (intervalTranslatedAverage ℓ ε (scaledAtomicMollifier ε) (unitaryConjugate U.symm A)
        (intervalInclusion (ℓ-ε) ℓ (smoothIntervalL2 (ℓ-ε) a ha)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    intervalInclusion_smooth (ℓ-ε) ℓ hL a ha,intervalInclusion_smooth (ℓ-ε) ℓ hL b hb]
  exact intervalTranslatedAverage_kernel_pair hε u U H hBound hAnalytic hCoanalytic
    p hp.le φ ψ A hRep hSp a b ha hb

/-- Full Lemma 8, with no open regularization, triangular or literature input. -/
theorem oneAtomSplittingTheorem : OneAtomConclusion :=
  oneAtomSplitting_of_triangular_regularization triangularBound atomicRegularization

/-- The local one-atom input to the finite-family and endpoint reductions is now proved. -/
theorem oneAtomLocal : OneAtomObligation := oneAtomExtraction oneAtomSplittingTheorem

/-- Full Theorem 6, including the fixed-family uniform bound and every scalar splitting criterion. -/
theorem finiteAtomClassificationTheorem : FiniteAtomConclusion :=
  finiteAtomClassification_of_oneAtom oneAtomLocal

/-- Full Remark 6, retaining the endpoint range and exact same-p obstruction. -/
theorem endpointObstructionTheorem : EndpointConclusion := endpointObstruction_of_oneAtom oneAtomLocal

/-- Full Remark 8 for every p>0, with the source membership hypothesis retained. -/
theorem atomicBoundednessTheorem : AtomicBoundednessConclusion :=
  Reduction.atomicBoundedness finiteAtomClassificationTheorem schattenMonotonicity

end TTO.Paper.Proved
