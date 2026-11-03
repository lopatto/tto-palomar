/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations

/-! Literal boundary meaning of the polynomial symbols. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The Holder-recursive power is the ordinary pointwise power almost everywhere. -/
theorem powerInf_ae (a : BoundaryLInf) (n : ℕ) :
    powerInf a n =ᵐ[circleMeasure] fun t => (a t)^n := by
  induction n with
  | zero => exact (memLp_const (1 : ℂ)).coeFn_toLp
  | succ n ih =>
    filter_upwards [multiplyInf_ae a (powerInf a n),ih] with t hp hn
    change multiplyInf a (powerInf a n) t = (a t)^(n+1)
    rw [hp,hn,pow_succ']

/-- A finite sum of the actual L∞ polynomial monomials has its literal boundary formula. -/
theorem polynomialSymbol_ae (q : BiPolynomial) :
    polynomialSymbol q =ᵐ[circleMeasure] fun t =>
      polynomialValue q (fourier (T := 1) 1 t) := by
  classical
  let v (jk : ℕ × ℕ) : BoundaryLInf :=
    multiplyInf (powerInf coordinate jk.1) (powerInf (star coordinate) jk.2)
  have hm (jk : ℕ × ℕ) : v jk =ᵐ[circleMeasure] fun t =>
      (fourier (T := 1) 1 t)^jk.1 * conj (fourier (T := 1) 1 t)^jk.2 := by
    filter_upwards [multiplyInf_ae (powerInf coordinate jk.1) (powerInf (star coordinate) jk.2),
      powerInf_ae coordinate jk.1,powerInf_ae (star coordinate) jk.2,
      Lp.coeFn_star coordinate,coordinate_ae] with t hp h1 h2 hs hc
    change multiplyInf (powerInf coordinate jk.1) (powerInf (star coordinate) jk.2) t = _
    change (star coordinate) t = conj (coordinate t) at hs
    rw [hp,h1,h2,hs,hc]
  have hs := Lp.coeFn_finsetSum q.support (fun jk => q jk • v jk)
  have ht : (q.sum (fun jk c => c • v jk) : BoundaryLInf) =ᵐ[circleMeasure]
      fun t => ∑ jk ∈ q.support, q jk *
        ((fourier (T := 1) 1 t)^jk.1 * conj (fourier (T := 1) 1 t)^jk.2) := by
    unfold Finsupp.sum
    filter_upwards [hs,ae_all_iff.2 (fun jk => Lp.coeFn_smul (q jk) (v jk)),
      ae_all_iff.2 hm] with t hsum hsm hmon
    rw [hsum,Finset.sum_apply]
    apply sum_congr rfl
    intro jk _
    rw [hsm jk]
    change q jk * v jk t = _
    rw [hmon jk]
  exact (toL2_ae _).trans (ht.trans (Filter.Eventually.of_forall (fun t => by
    unfold polynomialValue Finsupp.sum
    apply sum_congr rfl
    intro jk _
    ring)))

/-- The actual polynomial-symbol meaning obligation, with no extra hypotheses. -/
theorem polynomialSymbolMeaning : PolynomialSymbolMeaning := polynomialSymbol_ae

/-- T7 retains its full conclusion while supplying the actual polynomial-symbol meaning. -/
theorem polynomialClassification_of_models (hP : PolynomialModels) (hM : MultiplicationLaws)
    (hT : TrigonometricUniqueness) (hQ : AtomicQuadraticWitness) : PolynomialConclusion :=
  polynomialClassification hP hM hT polynomialSymbolMeaning hQ

end TTO.Paper.Proved
