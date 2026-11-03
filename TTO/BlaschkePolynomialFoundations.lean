/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations
public import TTO.PolynomialFoundations

/-! The full Blaschke clause of Theorem 7, retaining countable multiplicities and p≥2. -/
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace TTO.Paper.Proved
open Reduction

theorem blaschkePolynomialClassification :
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ι : Type, ∀ a : ι → Disk,
    Countable ι → HasBlaschkeZeros u a → ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔
        Tendsto (fun i => polynomialValue q (a i).val) cofinite (𝓝 0)) ∧
      ∀ p : ℝ, 2 ≤ p → (HasSchattenTTO p u (polynomialSymbol q) ↔
        summableValues p (fun i => polynomialValue q (a i).val)) := by
  intro u hu hn ι a hι ha q
  let hC : CoreLaws := coreLaws
  let hI : IdealLaws := idealLaws
  let hU : UnitaryIdealLaws := unitaryIdealLaws
  let hM : MultiplicationLaws := multiplicationLaws
  obtain ⟨A,he,U,D,hd,K,hk,hA⟩ := polynomialBlaschkeModel u hu hn ι a hι ha q
  have hc : HasCompactTTO u (polynomialSymbol q) ↔ IsCompactOperator A := by
    constructor
    · rintro ⟨B,hb,hc⟩
      exact (hC.unique u hu hn _ B A hb he) ▸ hc
    · exact fun hc => ⟨A,he,hc⟩
  constructor
  · apply hc.trans
    rw [hA]
    exact (compact_perturb_iff hI _ _ hk.2.1).trans
      ((hU.compact U D).trans (hM.diagonal_compact ι _ D hd))
  · intro p hp
    have hkp := hU.inclusion K p hp hk
    have hpos : 0 < p := lt_of_lt_of_le (by norm_num) hp
    have hs : HasSchattenTTO p u (polynomialSymbol q) ↔ Schatten p A := by
      constructor
      · rintro ⟨B,hb,hs⟩
        exact (hC.unique u hu hn _ B A hb he) ▸ hs
      · exact fun hs => ⟨A,he,hs⟩
    apply hs.trans
    rw [hA]
    exact (schatten_perturb_iff hI p _ _ hkp).trans
      ((hU.schatten U D p).trans (hM.diagonal_schatten ι _ D hd p hpos))

end TTO.Paper.Proved
