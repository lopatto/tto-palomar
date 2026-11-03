/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicPolynomialFoundations
public import TTO.PolynomialBoundaryFoundations
public import TTO.SingleAtomConstruction
public import TTO.MultiplicationFoundations

/-! The complete atomic clause and actual nonzero example of Theorem 7. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- A pure singular representation is a canonical representation with every Blaschke slot empty. -/
theorem hasCanonicalMeasure_of_singular (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasSingularRepresentation u μ) : HasCanonicalMeasure u μ := by
  obtain ⟨hf, α, hα, hv⟩ := hμ
  refine ⟨hf, fun _ => none, ?_, α, hα, ?_⟩
  · simp only [Option.elim_none, summable_zero]
  · intro z hz
    simpa only [Option.elim_none, tprod_one, mul_one] using hv z hz

/-- Compact polynomial operators vanish at each positive canonical atom, with no pure-type
or atomic-support hypothesis on the remainder of the measure. -/
theorem compactPolynomial_positive_atom_zero (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (μ : Measure Boundary) (hμ : HasCanonicalMeasure u μ)
    (q : BiPolynomial) (hA : HasCompactTTO u (polynomialSymbol q))
    (ζ : Boundary) (hζ : 0 < μ {ζ}) :
    polynomialValue q (fourier (T := 1) 1 ζ) = 0 := by
  classical
  let L := StolzFilter ζ 2
  let : NeBot L := stolz_neBot ζ 2 (by norm_num)
  let w (z : ℂ) : Disk := if hz : z ∈ disk then ⟨z, hz⟩ else origin
  have heq : (fun z => (w z).val) =ᶠ[L] fun z => z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [w, dite_eq_left hz.1]
  have hw : Tendsto (fun z => (w z).val) L (𝓝 (fourier (T := 1) 1 ζ)) :=
    by
      have hid : Tendsto (fun z : ℂ => z) L (𝓝 (fourier (T := 1) 1 ζ)) := nhdsWithin_le_nhds
      exact hid.congr' heq.symm
  have hzero : Tendsto (fun z => innerValue u (w z).val) L (𝓝 0) := by
    have ht := canonical_atom_tendsto_zero u μ hμ ζ hζ 2 (by norm_num)
    apply ht.congr'
    exact heq.mono fun z hz => congrArg (innerValue u) hz.symm
  exact compactPolynomial_boundary_value_zero L u hu hn q hA w ζ hw hzero

/-- The full atomic singular clause of Theorem 7, including the Hilbert–Schmidt improvement. -/
theorem atomicPolynomialClassification :
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
    HasSingularRepresentation u μ → AtomicMeasure μ → ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔ ∀ ζ : Boundary, 0 < μ {ζ} →
        polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
      (HasCompactTTO u (polynomialSymbol q) → HasSchattenTTO 2 u (polynomialSymbol q)) := by
  intro u hu hn μ hμ ha q
  have hnecessity : HasCompactTTO u (polynomialSymbol q) →
      ∀ ζ : Boundary, 0 < μ {ζ} → polynomialValue q (fourier (T := 1) 1 ζ) = 0 :=
    fun hc ζ hζ => compactPolynomial_positive_atom_zero u hu hn μ
      (hasCanonicalMeasure_of_singular u μ hμ) q hc ζ hζ
  have hsufficiency (hv : ∀ ζ : Boundary, 0 < μ {ζ} →
      polynomialValue q (fourier (T := 1) 1 ζ) = 0) : HasSchattenTTO 2 u (polynomialSymbol q) :=
    singularPolynomial_hasSchatten_two u hu μ hμ q
      ((atomicMeasure_ae_zero_iff μ ha _).mpr hv)
  refine ⟨⟨hnecessity, ?_⟩, fun hc => hsufficiency (hnecessity hc)⟩
  intro hv
  obtain ⟨A, hA, hs⟩ := hsufficiency hv
  exact ⟨A, hA, hs.2.1⟩

/-- The actual compact nonzero quadratic example, with its native Schatten proof. -/
theorem atomicPolynomial_nonzero_example :
    ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ SingleAtom u 0 ∧ ∃ q : BiPolynomial,
      (∀ z : ℂ, polynomialValue q z = 2 - z - conj z) ∧ ∃ A : Model u →L[ℂ] Model u,
        RepresentsTTO u (polynomialSymbol q) A ∧ Schatten 2 A ∧ A ≠ 0 := by
  obtain ⟨u, hu, hn, hs, μ, hμ, ha, q, hq, hv, A, hA, f, hf⟩ := atomicQuadraticWitness
  refine ⟨u, hu, hn, hs, q, hq, A, hA, ?_, ?_⟩
  · have hbound := singularPolynomial_schatten_two u hu μ hμ q
      ((atomicMeasure_ae_zero_iff μ ha _).mpr hv)
    have heq : A = boundedSymbolOperator u (biPolynomialBoundary q) :=
      coreLaws.unique u hu hn _ A _ hA (boundedSymbolOperator_represents u (biPolynomialBoundary q))
    rw [heq]
    exact hbound
  · intro hzero
    simp only [hzero, zero_apply, inner_zero_right, Complex.zero_re, lt_self_iff_false] at hf

end TTO.Paper.Proved
