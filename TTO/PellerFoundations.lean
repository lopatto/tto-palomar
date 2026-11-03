/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PellerLowFoundations
public import TTO.PellerGreaterOneFoundations

/-! Complete classical Hankel classification and both manuscript Besov conclusions for every p>0.

Classical reference: V. V. Peller, *Besov spaces in operator theory*,
https://arxiv.org/abs/2402.09853v1, Theorems 4.1 and 4.2.
The needed results are proved here, rather than assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem peller (p : ℝ) (hp : 0<p) : PellerObligation p := by
  by_cases hp1 : p≤1
  · exact pellerLow p hp hp1
  · exact pellerGreaterOne p (lt_of_not_ge hp1)

theorem besovClassificationTheorem (p : ℝ) (hp : 0<p) : BesovConclusion p :=
  besovClassification p hp (peller p hp)

theorem coanalyticBesovTheorem (p : ℝ) (hp : 0<p) : CoanalyticBesovConclusion p :=
  coanalyticBesov p (besovClassificationTheorem p hp)

end TTO.Paper.Proved
