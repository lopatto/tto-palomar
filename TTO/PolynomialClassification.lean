/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicPolynomialClassification
public import TTO.BlaschkePolynomialFoundations
public import TTO.SingularBoundaryFoundations

/-! The complete parameter-free polynomial classification of Theorem 7. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Direct singular-polynomial compactness criterion. The sufficiency even gives S₂;
the necessity uses actual μ-a.e. radial zero sequences and normalized model kernels. -/
theorem singularPolynomial_compact_iff_ae_zero (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ)
    (q : BiPolynomial) :
    HasCompactTTO u (polynomialSymbol q) ↔
      ∀ᵐ ζ ∂μ, polynomialValue q (fourier (T := 1) 1 ζ) = 0 := by
  constructor
  · intro hc
    filter_upwards [singular_radial_zero_sequence u μ hμ] with ζ hζ
    obtain ⟨r, hr, ht, hzero⟩ := hζ
    let w (n : ℕ) : Disk := singularRadialPoint ζ (r n) (hr n).1 (hr n).2
    have hw : Tendsto (fun n => (w n).val) atTop (𝓝 (fourier (T := 1) 1 ζ)) := by
      have hcast := (Complex.continuous_ofReal.tendsto 1).comp ht
      have hm := hcast.mul_const (fourier (T := 1) 1 ζ)
      simp only [Complex.ofReal_one, one_mul] at hm
      convert hm using 1
      funext n
      rfl
    exact compactPolynomial_boundary_value_zero atTop u hu hn q hc w ζ hw hzero
  · intro hq
    obtain ⟨A, hA, hs⟩ := singularPolynomial_hasSchatten_two u hu μ hμ q hq
    exact ⟨A, hA, hs.2.1⟩

/-- A circle-zero polynomial symbol represents only the zero operator on a nonconstant model. -/
theorem polynomial_circle_zero_operator (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (q : BiPolynomial)
    (hq : ∀ ζ : Boundary, polynomialValue q (fourier (T := 1) 1 ζ) = 0)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u (polynomialSymbol q) A) : A = 0 := by
  have hz : polynomialSymbol q =ᵐ[circleMeasure] fun _ => (0 : ℂ) := by
    filter_upwards [polynomialSymbol_ae q] with t ht
    rw [ht, hq t]
  have he : polynomialSymbol q = 0 := Lp.ext (hz.trans (Lp.coeFn_zero ℂ 2 circleMeasure).symm)
  exact coreLaws.unique u hu hn _ A 0 hA (by rw [he]; exact represents_zero u)

/-- The full nonatomic singular clause of Theorem 7, including its zero-operator conclusion. -/
theorem continuousSingularPolynomialClassification :
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
    HasSingularRepresentation u μ → NonatomicMeasure μ → ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔ ∀ ζ : Boundary,
        polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
      (HasCompactTTO u (polynomialSymbol q) → ∀ A : Model u →L[ℂ] Model u,
        RepresentsTTO u (polynomialSymbol q) A → A = 0) := by
  intro u hu hn μ hμ ha q
  have hc := (singularPolynomial_compact_iff_ae_zero u hu hn μ hμ q).trans
    (trigonometricUniqueness u hu hn μ hμ ha q)
  exact ⟨hc, fun hcompact A hA => polynomial_circle_zero_operator u hu hn q (hc.mp hcompact) A hA⟩

/-- Theorem 7 in its full frozen scope: all pure types, countable zero multiplicities, p≥2
in the Blaschke Schatten clause, and the actual nonzero atomic S₂ example. -/
theorem polynomialClassificationTheorem : PolynomialConclusion := by
  refine ⟨blaschkePolynomialClassification, ?_, atomicPolynomialClassification,
    atomicPolynomial_nonzero_example⟩
  intro u hu hn μ hμ ha q
  have hc := continuousSingularPolynomialClassification u hu hn μ hμ ha q
  exact ⟨hc.1, fun hz A hA => hc.2 (hc.1.mpr hz) A hA⟩

end TTO.Paper.Proved
