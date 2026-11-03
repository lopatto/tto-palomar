/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Solution

/-! Independent reviewed contracts for the advertised statements and essential definitions.
This module is outside Solution's import closure. Changes to these contracts require
mathematical review against the local manuscript. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.StatementChecks
open Reduction

/-- Independently written expected mathematical statement. -/
def ExpectedT1 (p : ℝ) : Prop :=
  ∃ c C ch Ch : ℝ, 0 < c ∧ 0 < C ∧ 0 < ch ∧ 0 < Ch ∧
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasSchattenTTO p u φ.val ↔ InBesov p (conjugation u φ.val)) ∧
    (HasSchattenTTO p u φ.val ↔ homogeneousBesovEnergy p
      (fun z => z * analyticValue (conjugation u φ.val) z) < ∞) ∧
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A → Schatten p A →
      c * besovNorm p (conjugation u φ.val) ≤ schattenNorm p A ∧
      schattenNorm p A ≤ C * besovNorm p (conjugation u φ.val) ∧
      ch * homogeneousBesovNorm p (fun z => z * analyticValue (conjugation u φ.val) z)
        ≤ schattenNorm p A ∧
      schattenNorm p A ≤ Ch * homogeneousBesovNorm p
        (fun z => z * analyticValue (conjugation u φ.val) z)

theorem t1_view (p : ℝ) (h : BesovConclusion p) : ExpectedT1 p := by
  obtain ⟨hc, c, C, ch, Ch, hpos, hC, hch, hCh, hb⟩ := h
  exact ⟨c, C, ch, Ch, hpos, hC, hch, hCh, fun u hu hn φ =>
    ⟨(hc u hu hn φ).1, (hc u hu hn φ).2, hb u hu hn φ⟩⟩

/-- Independently written expected mathematical statement. -/
def ExpectedT2 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasCompactTTO u φ.val ↔ InVMOA (conjugation u φ.val)) ∧
    (InVMOA (conjugation u φ.val) ↔ ∃ g : C(Boundary, ℂ),
      SameHankel (hankelSymbol u φ.val) (ContinuousMap.toLp 2 circleMeasure ℂ g))

/-- Independently written expected mathematical statement. -/
def ExpectedT3 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
  Function.Injective a → HasBlaschkeZeros u a → Interpolating a →
  ∃ R : lp (fun _ : ℕ => ℂ) 2 ≃L[ℂ] Model u, RieszSynthesis u a R ∧
  ∀ φ : Hardy,
    (HasBoundedTTO u φ.val ↔ ∃ M : ℝ, ∀ n, ‖analyticValue φ.val (a n).val‖ ≤ M) ∧
    (HasCompactTTO u φ.val ↔ Tendsto (fun n => analyticValue φ.val (a n).val) atTop (𝓝 0)) ∧
    ∀ p : ℝ, 0 < p →
      (HasSchattenTTO p u φ.val ↔ summableValues p (fun n => analyticValue φ.val (a n).val)) ∧
      ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A → Schatten p A →
        let κ := ‖R.toContinuousLinearMap‖ * ‖R.symm.toContinuousLinearMap‖
        κ⁻¹ * valueNorm p (fun n => analyticValue φ.val (a n).val) ≤ schattenNorm p A ∧
        schattenNorm p A ≤ κ * valueNorm p (fun n => analyticValue φ.val (a n).val)

/-- Independently written expected mathematical statement. -/
def ExpectedT4 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
  Function.Injective a → HasBlaschkeZeros u a →
    (∀ A : Model u →L[ℂ] Model u, HasBoundedAnalyticSplit u A ↔ HasBoundedSymbolSplit u A) ∧
    ∀ φ ψ : BoundaryLInf, toL2 φ ∈ hardy → toL2 ψ ∈ hardy →
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A →
      (∀ p : ℝ, 0 < p → PerturbedKernelBasis u a {Γ | Schatten p Γ} →
        (Schatten p A ↔ summableValues p (fun n => innerValue φ (a n).val + conj (innerValue ψ (a n).val)))) ∧
      (PerturbedKernelBasis u a {Γ | IsCompactOperator Γ} →
        (IsCompactOperator A ↔ Tendsto (fun n => innerValue φ (a n).val +
          conj (innerValue ψ (a n).val)) atTop (𝓝 0)))

/-- Independently written expected mathematical statement. -/
def ExpectedT5 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasSingularRepresentation u μ → ∀ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I →
  ∀ r : ℝ, 0 < r → r < 1 → ∀ φ ψ : Hardy, HasAnalyticGap μ r φ.val →
    InTTOIdeal u I (splitSymbol φ.val ψ.val) → InTTOIdeal u I φ.val ∧ InTTOIdeal u I (star ψ.val)

/-- Independently written expected mathematical statement. -/
def ExpectedRemainders {m : ℕ} (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2)
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) : Prop :=
  ∃ X Y : Model u →L[ℂ] Model u, RepresentsTTO u φ X ∧ RepresentsTTO u (star ψ) Y ∧
    Schatten p (X - ∑ j, c j • E j) ∧ Schatten p (Y + ∑ j, c j • E j)

theorem remainders_meaning {m : ℕ} (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2)
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) :
    Remainders p u φ ψ E c ↔ ExpectedRemainders p u φ ψ E c := by
  constructor
  · rintro ⟨⟨X, hX, hs⟩, Y, hY, ht⟩
    exact ⟨X, Y, hX, hY, hs, ht⟩
  · rintro ⟨X, Y, hX, hY, hs, ht⟩
    exact ⟨⟨X, hX, hs⟩, Y, hY, ht⟩

/-- Independently written expected mathematical statement. -/
def ExpectedT6Analytic {m : ℕ} (p : ℝ) (u : Fin m → BoundaryLInf)
    (ζ : Fin m → Boundary) (C : ℝ) : Prop :=
  ∀ a, Bezout u a → ∀ E, RepresentsIdempotents u a E → ∀ φ ψ : Hardy,
    (HasSchattenTTO p (finiteProduct u) (splitSymbol φ.val ψ.val) ↔
      ∃! c : Fin m → ℂ, ExpectedRemainders p (finiteProduct u) φ.val ψ.val E c) ∧
    ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
      (∀ c, ExpectedRemainders p (finiteProduct u) φ.val ψ.val E c ↔
        ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _)) ∧
      (∀ c, ExpectedRemainders p (finiteProduct u) φ.val ψ.val E c →
        (∀ j, AngularLimit (analyticValue φ.val) (ζ j) (c j) ∧
          AngularLimit (analyticValue ψ.val) (ζ j) (-conj (c j))) ∧
        ∀ X Y : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
          RepresentsTTO (finiteProduct u) φ.val X → RepresentsTTO (finiteProduct u) (star ψ.val) Y →
          Schatten p (X - ∑ j, c j • E j) → Schatten p (Y + ∑ j, c j • E j) →
          schattenNorm p (X - ∑ j, c j • E j) + schattenNorm p (Y + ∑ j, c j • E j) ≤ C * schattenNorm p A) ∧
      (HasSchattenSplit p (finiteProduct u) A ↔ ∃ c : ℂ, ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c) ∧
      (∀ c : ℂ, (AnalyticRemainder p (finiteProduct u) φ.val (c • ContinuousLinearMap.id ℂ _) ∧
        CoanalyticRemainder p (finiteProduct u) ψ.val (c • ContinuousLinearMap.id ℂ _)) ↔
        ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c) ∧
      ((HasSchattenTTO p (finiteProduct u) φ.val ∧ HasSchattenTTO p (finiteProduct u) (star ψ.val)) ↔
        ∀ j, AngularLimit (analyticValue φ.val) (ζ j) 0)

/-- Independently written expected mathematical statement. -/
def ExpectedT6 : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf, ∀ ζ : Fin m → Boundary,
  Function.Injective ζ → (∀ j, IsInner (u j) ∧ Nonconstant (u j) ∧ SingleAtom (u j) (ζ j)) →
    IsInner (finiteProduct u) ∧ Nonconstant (finiteProduct u) ∧ (∃ a, Bezout u a) ∧
    (∀ a, Bezout u a → ∃ E, RepresentsIdempotents u a E ∧ ComplementaryIdempotents E ∧
      IdempotentRanges u E ∧ ∀ a' E', Bezout u a' → RepresentsIdempotents u a' E' → E' = E) ∧
    ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ExpectedT6Analytic p u ζ C

theorem t6_view (h : FiniteAtomConclusion) : ExpectedT6 := by
  intro m hm u ζ hz hu
  obtain ⟨hi, hn, hb, hE, hp⟩ := h m hm u ζ hz hu
  refine ⟨hi, hn, hb, hE, ?_⟩
  intro p hp'
  obtain ⟨C, hC, hd⟩ := hp p hp'
  refine ⟨C, hC, ?_⟩
  intro a ha E he φ ψ
  have hs := hd a ha E he φ ψ
  simp only [remainders_meaning, correction] at hs
  refine ⟨?_, hs.2.2⟩
  constructor
  · intro hh
    obtain ⟨c, hc⟩ := hs.1.mp hh
    exact ⟨c, hc, fun d hd' => hs.2.1 d c hd' hc⟩
  · rintro ⟨c, hc, _⟩
    exact hs.1.mpr ⟨c, hc⟩

/-- Independently written expected mathematical statement. -/
def ExpectedT7Blaschke : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ι : Type, ∀ a : ι → Disk,
  Countable ι → HasBlaschkeZeros u a → ∀ q : BiPolynomial,
    (HasCompactTTO u (polynomialSymbol q) ↔ Tendsto (fun i => polynomialValue q (a i).val) cofinite (𝓝 0)) ∧
    ∀ p : ℝ, 2 ≤ p → (HasSchattenTTO p u (polynomialSymbol q) ↔ summableValues p (fun i => polynomialValue q (a i).val))

/-- Independently written expected mathematical statement. -/
def ExpectedT7ContinuousSingular : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasSingularRepresentation u μ → NonatomicMeasure μ → ∀ q : BiPolynomial,
    (HasCompactTTO u (polynomialSymbol q) ↔ ∀ ζ : Boundary, polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
    (HasCompactTTO u (polynomialSymbol q) → ∀ A : Model u →L[ℂ] Model u,
      RepresentsTTO u (polynomialSymbol q) A → A = 0)

/-- Independently written expected mathematical statement. -/
def ExpectedT7Atomic : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasSingularRepresentation u μ → AtomicMeasure μ → ∀ q : BiPolynomial,
    (HasCompactTTO u (polynomialSymbol q) ↔ ∀ ζ : Boundary, 0 < μ {ζ} →
      polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
    (HasCompactTTO u (polynomialSymbol q) → HasSchattenTTO 2 u (polynomialSymbol q))

/-- Independently written expected mathematical statement. -/
def ExpectedT7NonzeroExample : Prop :=
  ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ SingleAtom u 0 ∧ ∃ q : BiPolynomial,
    (∀ z : ℂ, polynomialValue q z = 2 - z - conj z) ∧ ∃ A : Model u →L[ℂ] Model u,
      RepresentsTTO u (polynomialSymbol q) A ∧ Schatten 2 A ∧ A ≠ 0

theorem t7_view (h : PolynomialConclusion) : ExpectedT7Blaschke ∧
    ExpectedT7ContinuousSingular ∧ ExpectedT7Atomic ∧ ExpectedT7NonzeroExample := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro u hu hn μ hμ hc q
  have ht := h.2.1 u hu hn μ hμ hc q
  exact ⟨ht.1, fun hk => ht.2 (ht.1.mp hk)⟩

/-- Independently written expected mathematical statement. -/
def ExpectedEnergyGeometry (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D S : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  (∀ η G, (η, G) ∈ Q.graph ↔ ∀ z ∈ disk, ∀ w ∈ disk,
    analyticValue₂ G.val z w = FKernel u η.val z w) ∧
  (∀ η : Ambient u, η ∈ Q.domain ↔ energy u η.val < ∞) ∧
  Q.IsClosed ∧ Dense (Q.domain : Set (Ambient u)) ∧
  (∀ x y : Ambient u, (x, y) ∈ D.graph ↔ ∃ v : TensorModel u,
    (x, v) ∈ Q.graph ∧ (v, y) ∈ Q.adjoint.graph) ∧
  (IsSelfAdjoint D ∧ ∀ x : D.domain,
    (inner ℂ x.val (D x)).im = 0 ∧ 0 ≤ (inner ℂ x.val (D x)).re) ∧
  ((IsSelfAdjoint S ∧ ∀ x : S.domain,
    (inner ℂ x.val (S x)).im = 0 ∧ 0 ≤ (inner ℂ x.val (S x)).re) ∧
    ∀ x y : Ambient u, (x, y) ∈ D.graph ↔ ∃ v : Ambient u,
      (x, v) ∈ S.graph ∧ (v, y) ∈ S.graph) ∧
  S.domain = Q.domain ∧
  (∀ η : S.domain, ENNReal.ofReal (‖S η‖ ^ 2) = energy u η.val.val) ∧
  (∀ η χ : Ambient u, (η, χ) ∈ D.graph ↔ η ∈ Q.domain ∧
    ∀ γ : Q.domain, inner ℂ γ.val χ = energyPairing u η.val γ.val.val) ∧
  (∀ η γ : Q.domain, energyPairing u η.val.val γ.val.val = inner ℂ (Q γ) (Q η))

/-- Independently written expected mathematical statement. -/
def ExpectedT8Functions (u : BoundaryLInf) : Prop :=
  (∀ η : Ambient u,
    η.val = eta₁ u η.val + multiply u (eta₂ u η.val) ∧
    (∀ z ∈ disk, ∀ w ∈ disk, FKernel u η.val z w = dividedDifference u η.val z w) ∧
    (HasBidiskRepresentative u η.val ↔ energy u η.val < ∞) ∧
    (HasSchattenTHO 2 u (star η.val) ↔ HasBidiskRepresentative u η.val ∧ energy u η.val < ∞) ∧
    (energy u η.val < ∞ → ∃ G : TensorModel u, QGraph u η G) ∧
    (∀ G : TensorModel u, QGraph u η G → ENNReal.ofReal (‖G‖ ^ 2) = energy u η.val) ∧
    ∀ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u (star η.val) B → Schatten 2 B →
      ENNReal.ofReal (schattenNorm 2 B ^ 2) = energy u η.val) ∧
  (∀ φ ψ : Model u, analyticValue ψ.val 0 = 0 → ∃ η : Ambient u,
    η.val = conjugation u φ.val + multiply u (multiply (star coordinate) ψ.val) ∧
    energyH u η.val = multiply coordinate (conjugation u φ.val) ∧ energyG u η.val = ψ.val ∧
    (HasSchattenTTO 2 u (splitSymbol φ.val ψ.val) ↔ energy u η.val < ∞) ∧
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten 2 A →
      ENNReal.ofReal (schattenNorm 2 A ^ 2) = energy u η.val)

theorem t8_functions (u : BoundaryLInf) (h : EnergyIdentities u) : ExpectedT8Functions u := by
  refine ⟨?_, h.2⟩
  intro η
  have ht := h.1 η
  refine ⟨ht.1, ht.2.1, ht.2.2.1.symm.trans ht.2.2.2.1, ?_, ht.2.2.2.2⟩
  exact ⟨fun hs => ⟨ht.2.2.1.mp hs, ht.2.2.2.1.mp hs⟩, fun hs => ht.2.2.1.mpr hs.1⟩

/-- Independently written expected mathematical statement. -/
def ExpectedT8 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ExpectedT8Functions u ∧
    ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u, ∃ D S : Ambient u →ₗ.[ℂ] Ambient u,
      ExpectedEnergyGeometry u Q D S

theorem t8_view (h : HilbertSchmidtConclusion) : ExpectedT8 := by
  intro u hu hn
  obtain ⟨he, Q, D, S, hg⟩ := h u hu hn
  exact ⟨t8_functions u he, Q, D, S, hg⟩

/-- Independently written expected mathematical statement. -/
def ExpectedDifferential (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  (∀ η : Ambient u, ∀ z ∈ disk,
    FKernel u η.val z z = deriv (fun w => w * analyticValue η.val w) z -
      2 * innerValue u z * deriv (fun w => w * analyticValue (eta₂ u η.val) w) z ∧
    FKernel u η.val z z = deriv (analyticValue (energyH u η.val)) z +
      deriv (innerValue u) z * analyticValue (energyG u η.val) z -
      innerValue u z * deriv (analyticValue (energyG u η.val)) z) ∧
  (∀ w ∈ disk, ∃ κ χ : Ambient u,
    (∀ z ∈ disk, analyticValue κ.val z = kernelValue (multiplyInf u u) w z) ∧
    (∀ z ∈ disk, analyticValue χ.val z = kernelValue u w z ^ 2) ∧ (κ, χ) ∈ D.graph) ∧
  (∀ η : D.domain,
    (∀ z ∈ disk, analyticValue (D η).val z = FKernel u η.val.val z z) ∧
    inner ℂ η.val (D η) = ((energy u η.val.val).toReal : ℂ)) ∧
  (∀ η : Ambient u, η ∈ D.domain ↔ η ∈ Q.domain ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ γ : Q.domain, ‖energyPairing u η.val γ.val.val‖ ≤ C * ‖γ.val‖)

/-- Independently written expected mathematical statement. -/
def ExpectedT9 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u, ∃ D S : Ambient u →ₗ.[ℂ] Ambient u,
      ExpectedEnergyGeometry u Q D S ∧ ExpectedDifferential u Q D

/-- Independently written expected mathematical statement. -/
def ExpectedCorollary1 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasSingularRepresentation u μ → ∀ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I →
  ∀ r : ℝ, 0 < r → r < 1 → ∀ φ ψ : Model u, analyticValue ψ.val 0 = 0 →
    (InTTOIdeal u I (powerProjection μ r φ.val) ↔
      InTTOIdeal u I (powerProjection μ r (splitSymbol φ.val ψ.val))) ∧
    ((InTTOIdeal u I (splitSymbol φ.val ψ.val) ∧ InTTOIdeal u I (powerProjection μ r φ.val)) →
      InTTOIdeal u I φ.val ∧ InTTOIdeal u I (star ψ.val))

/-- Independently written expected mathematical statement. -/
def ExpectedR10Quotient (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D : Ambient u →ₗ.[ℂ] Ambient u) (d : DiagonalKernelData u Q) : Prop :=
  (∀ G : TensorModel u, G ∈ diagonalNull d ↔ ∀ w : Disk, analyticValue₂ G.val w.val w.val = 0) ∧
  (diagonalNull d).orthogonal = (Submodule.span ℂ (Set.range d.tensorKernel)).topologicalClosure ∧
  (∀ G : TensorModel u, ∀ w : Disk, analyticValue₂ (diagonalProjection d G).val.val w.val w.val = analyticValue₂ G.val w.val w.val) ∧
  (∀ h : ↥(diagonalNull d).orthogonal, diagonalProjection d h.val = h) ∧
  (∀ G T : TensorModel u, (∀ w : Disk, analyticValue₂ T.val w.val w.val = analyticValue₂ G.val w.val w.val) →
    ‖diagonalProjection d G‖ ≤ ‖T‖) ∧
  (∀ w : Disk, ∃ k : ↥(diagonalNull d).orthogonal, k.val = d.tensorKernel w ∧
    (∀ z : Disk, analyticValue₂ k.val.val z.val z.val = kernelValue u w.val z.val ^ 2) ∧
    ∀ h : ↥(diagonalNull d).orthogonal, analyticValue₂ h.val.val w.val w.val = inner ℂ k h) ∧
  (∀ η : Q.domain,
    (∀ w : Disk, analyticValue₂ (diagonalProjection d (Q η)).val.val w.val w.val = FKernel u η.val.val w.val w.val) ∧
    ∀ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u (star η.val.val) B → Schatten 2 B →
      ‖diagonalProjection d (Q η)‖ ≤ schattenNorm 2 B ∧
      (‖diagonalProjection d (Q η)‖ = schattenNorm 2 B ↔ Q η ∈ (diagonalNull d).orthogonal)) ∧
  (KernelGraphCore d → (∀ η : Q.domain, ‖diagonalProjection d (Q η)‖ = ‖Q η‖) ∧
    ∀ η : Ambient u, η ∈ D.domain ↔ η ∈ Q.domain ∧ ∃ χ : Ambient u,
      ∀ w : Disk, analyticValue χ.val w.val = FKernel u η.val w.val w.val)

/-- Independently written expected mathematical statement. -/
def ExpectedR10 : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u,
    ∃ D S : Ambient u →ₗ.[ℂ] Ambient u, ExpectedEnergyGeometry u Q D S ∧ ExpectedDifferential u Q D ∧
      ∃ d : DiagonalKernelData u Q, ExpectedR10Quotient u Q D d

/-- Independently written expected mathematical statement. -/
def ExpectedCoanalyticBesov (p : ℝ) : Prop :=
  ∃ c C ch Ch : ℝ, 0 < c ∧ 0 < C ∧ 0 < ch ∧ 0 < Ch ∧
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasSchattenTTO p u (star φ.val) ↔ InBesov p (conjugation u φ.val)) ∧
    (HasSchattenTTO p u (star φ.val) ↔
      homogeneousBesovEnergy p (fun z => z * analyticValue (conjugation u φ.val) z) < ∞) ∧
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (star φ.val) A → Schatten p A →
      c * besovNorm p (conjugation u φ.val) ≤ schattenNorm p A ∧
      schattenNorm p A ≤ C * besovNorm p (conjugation u φ.val) ∧
      ch * homogeneousBesovNorm p (fun z => z * analyticValue (conjugation u φ.val) z) ≤ schattenNorm p A ∧
      schattenNorm p A ≤ Ch * homogeneousBesovNorm p (fun z => z * analyticValue (conjugation u φ.val) z)

theorem checkedT1 (p : ℝ) (hp : 0<p) : ExpectedT1 p :=
  t1_view p (Proved.besovClassificationTheorem p hp)

theorem checkedT2 : ExpectedT2 := by
  intro u hu hn φ
  have ht := Proved.compactClassificationTheorem u hu hn φ
  exact ⟨ht.1, ht.1.symm.trans ht.2⟩

theorem checkedT3 : ExpectedT3 := by
  intro u hu hn a ha hb hi
  obtain ⟨⟨R,hRs⟩,ht⟩ := Proved.interpolatingClassificationTheorem u hu hn a ha hb hi
  exact ⟨R,hRs,fun φ => ⟨(ht φ).1,(ht φ).2.1,
    fun p hp => ⟨((ht φ).2.2 p hp).1,((ht φ).2.2 p hp).2 R hRs⟩⟩⟩

theorem checkedT4 : ExpectedT4 := by
  intro u hu hn a hi hz
  have ht := Proved.perturbedKernelBasisClassificationTheorem u hu hn a hi hz
  exact ⟨ht.1, fun φ ψ hφ hψ A hA =>
    ⟨(ht.2 φ ψ hφ hψ A hA).2, (ht.2 φ ψ hφ hψ A hA).1⟩⟩

theorem checkedT5 : ExpectedT5 :=
  fun u hu hn μ hμ I hI r hr hr1 φ ψ hg =>
    Proved.gapSplittingTheorem u hu hn μ hμ I hI φ ψ r hr hr1 hg

theorem checkedCorollary1 : ExpectedCorollary1 := by
  intro u hu hn μ hμ I hI r hr hr1 φ ψ hψ
  have ht := Proved.canonicalGapSplittingTheorem u hu hn μ hμ I hI φ ψ hψ r hr hr1
  exact ⟨ht.1, fun hh => ht.2 hh.1 hh.2⟩

theorem checkedT6 : ExpectedT6 := t6_view Proved.finiteAtomClassificationTheorem

theorem checkedT7 : ExpectedT7Blaschke ∧ ExpectedT7ContinuousSingular ∧
    ExpectedT7Atomic ∧ ExpectedT7NonzeroExample :=
  t7_view Proved.polynomialClassificationTheorem

theorem checkedT8 : ExpectedT8 := t8_view Proved.hilbertSchmidtEnergyTheorem

theorem checkedT9 : ExpectedT9 := Proved.differentialRealizationTheorem

theorem checkedR10 : ExpectedR10 := Proved.squaredKernelQuotientTheorem

theorem checkedCoanalyticBesov (p : ℝ) (hp : 0<p) : ExpectedCoanalyticBesov p := by
  obtain ⟨hc,c,C,ch,Ch,hpos,hC,hch,hCh,hb⟩ := Proved.coanalyticBesovTheorem p hp
  exact ⟨c,C,ch,Ch,hpos,hC,hch,hCh,fun u hu hn φ =>
    ⟨(hc u hu hn φ).1,(hc u hu hn φ).2,hb u hu hn φ⟩⟩

-- Consequential meanings: bounded-core forms, natural graph composition, source core condition.
example (u : BoundaryLInf) (σ : BoundaryL2) (A : Model u →L[ℂ] Model u) :
    RepresentsTTO u σ A ↔ ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
      inner ℂ g (A f) = ∫ t, σ t * f.val t * conj (g.val t) ∂circleMeasure := Iff.rfl

example (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D : Ambient u →ₗ.[ℂ] Ambient u) :
    IsAdjointSquare u Q D ↔ ∀ x y : Ambient u, (x, y) ∈ D.graph ↔
      ∃ v : TensorModel u, (x, v) ∈ Q.graph ∧ (v, y) ∈ Q.adjoint.graph := Iff.rfl

example (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u) (d : DiagonalKernelData u Q) :
    KernelGraphCore d ↔ (Submodule.span ℂ (Set.range (fun w : Disk =>
      (d.kernel w, d.tensorKernel w)))).topologicalClosure = Q.graph := Iff.rfl

example : ∀ p : ℝ, 0<p → BesovConclusion p := @Proved.besovClassificationTheorem
example : CompactConclusion := @Proved.compactClassificationTheorem
example : InterpolatingConclusion := @Proved.interpolatingClassificationTheorem
example : PerturbedBasisConclusion := @Proved.perturbedKernelBasisClassificationTheorem
example : GapConclusion := @Proved.gapSplittingTheorem
example : CanonicalGapConclusion := @Proved.canonicalGapSplittingTheorem
example : FiniteAtomConclusion := @Proved.finiteAtomClassificationTheorem
example : PolynomialConclusion := @Proved.polynomialClassificationTheorem
example : HilbertSchmidtConclusion := @Proved.hilbertSchmidtEnergyTheorem
example : DifferentialConclusion := @Proved.differentialRealizationTheorem
example : ∀ p : ℝ, 0<p → CoanalyticBesovConclusion p := @Proved.coanalyticBesovTheorem
example : SquaredKernelConclusion := @Proved.squaredKernelQuotientTheorem

#print axioms TTO.Paper.Proved.besovClassificationTheorem
#print axioms TTO.Paper.Proved.compactClassificationTheorem
#print axioms TTO.Paper.Proved.interpolatingClassificationTheorem
#print axioms TTO.Paper.Proved.perturbedKernelBasisClassificationTheorem
#print axioms TTO.Paper.Proved.gapSplittingTheorem
#print axioms TTO.Paper.Proved.canonicalGapSplittingTheorem
#print axioms TTO.Paper.Proved.finiteAtomClassificationTheorem
#print axioms TTO.Paper.Proved.polynomialClassificationTheorem
#print axioms TTO.Paper.Proved.hilbertSchmidtEnergyTheorem
#print axioms TTO.Paper.Proved.differentialRealizationTheorem
#print axioms TTO.Paper.Proved.coanalyticBesovTheorem
#print axioms TTO.Paper.Proved.squaredKernelQuotientTheorem
#print axioms TTO.Paper.StatementChecks.checkedT1
#print axioms TTO.Paper.StatementChecks.checkedT2
#print axioms TTO.Paper.StatementChecks.checkedT3
#print axioms TTO.Paper.StatementChecks.checkedT4
#print axioms TTO.Paper.StatementChecks.checkedT5
#print axioms TTO.Paper.StatementChecks.checkedCorollary1
#print axioms TTO.Paper.StatementChecks.checkedT6
#print axioms TTO.Paper.StatementChecks.checkedT7
#print axioms TTO.Paper.StatementChecks.checkedT8
#print axioms TTO.Paper.StatementChecks.checkedT9
#print axioms TTO.Paper.StatementChecks.checkedR10
#print axioms TTO.Paper.StatementChecks.checkedCoanalyticBesov

end TTO.Paper.StatementChecks
