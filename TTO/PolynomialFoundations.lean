/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IndexedDiagonalFoundations
public import TTO.MultiplierCompactFoundations
public import TTO.TrigonometricFoundations
public import TTO.PolynomialMeaningFoundations

/-! Multiplier laws and reductions for polynomial models. -/
@[expose] public section
noncomputable section
namespace TTO.Paper.Proved
open Reduction

/-- All six fields of the actual polynomial multiplier package, now without proof parameters. -/
theorem multiplicationLaws : MultiplicationLaws where
  diagonal_compact := fun _ w D hd => indexedDiagonal_compact_iff w D hd
  diagonal_schatten := fun _ w D hd p hp => indexedDiagonal_schatten_iff w D hd p hp
  nonatomic_compact := nonatomic_multiplier_compact_iff
  fiber_compact := fiber_multiplier_compact_iff
  multiplier_zero := fiberMultiplier_zero
  atomic_ae := atomicMeasure_ae_zero_iff

/-- Polynomial classification from pure-model representations and a positive atomic witness. -/
theorem polynomialClassification_of_spectral_models (hP : PolynomialModels)
    (hQ : AtomicQuadraticWitness) : PolynomialConclusion :=
  polynomialClassification_of_models hP multiplicationLaws trigonometricUniqueness hQ

end TTO.Paper.Proved
