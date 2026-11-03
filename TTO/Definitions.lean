/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! Mathematical definitions and statement contracts for truncated Toeplitz operators. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper

abbrev Boundary := AddCircle (1 : ℝ)
abbrev circleMeasure : Measure Boundary := AddCircle.haarAddCircle (T := 1)
abbrev BoundaryL2 := Lp ℂ 2 circleMeasure
abbrev BoundaryLInf := Lp ℂ ∞ circleMeasure

def constL2 (c : ℂ) : BoundaryL2 := (memLp_const c).toLp (fun _ => c)
def constLInf (c : ℂ) : BoundaryLInf := (memLp_const c).toLp (fun _ => c)
def toL2 (a : BoundaryLInf) : BoundaryL2 :=
  ((Lp.memLp a).mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).toLp a

def multiply (a : BoundaryLInf) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ 2 2 a

def multiplyInf (a b : BoundaryLInf) : BoundaryLInf :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ ∞ ∞ a b

def coordinate : BoundaryLInf :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (fourier (T := 1) 1)

def hardy : Submodule ℂ BoundaryL2 :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => fourierBasis (T := 1) (n : ℤ)))).topologicalClosure
abbrev Hardy := ↥hardy
instance : CompleteSpace Hardy := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def model (u : BoundaryLInf) : Submodule ℂ BoundaryL2 :=
  hardy ⊓ (Submodule.span ℂ (Set.range (fun n : ℕ =>
    multiply u (fourierBasis (T := 1) (n : ℤ))))).orthogonal
abbrev Model (u : BoundaryLInf) := ↥(model u)
instance (u : BoundaryLInf) : CompleteSpace (Model u) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (Submodule.isClosed_orthogonal _)).completeSpace_coe

def IsInner (u : BoundaryLInf) : Prop :=
  toL2 u ∈ hardy ∧ ∀ᵐ t ∂circleMeasure, ‖u t‖ = 1

def Nonconstant (u : BoundaryLInf) : Prop := ¬∃ c : ℂ, u = constLInf c

def disk : Set ℂ := {z | ‖z‖ < 1}
abbrev Disk := ↥disk

def analyticValue (f : BoundaryL2) (z : ℂ) : ℂ :=
  ∑' n : ℕ, fourierCoeff f (n : ℤ) * z ^ n

def innerValue (u : BoundaryLInf) : ℂ → ℂ := analyticValue (toL2 u)
def IsBounded (f : BoundaryL2) : Prop := MemLp f ∞ circleMeasure

def conjugation (u : BoundaryLInf) (f : BoundaryL2) : BoundaryL2 :=
  multiply u (multiply (star coordinate) (star f))

def splitSymbol (φ ψ : BoundaryL2) : BoundaryL2 := φ + star ψ

def coreForm (σ f g : BoundaryL2) : ℂ :=
  ∫ t, σ t * f t * conj (g t) ∂circleMeasure

def RepresentsTTO (u : BoundaryLInf) (σ : BoundaryL2)
    (A : Model u →L[ℂ] Model u) : Prop :=
  ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
    inner ℂ g (A f) = coreForm σ f.val g.val

def HasBoundedTTO (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A

def HasCompactTTO (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ IsCompactOperator A

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def approximationNumber (A : E →L[ℂ] F) (n : ℕ) : ℝ≥0 :=
  ⨅ R : {R : E →L[ℂ] F // R.rank ≤ n}, ‖A - R.val‖₊

def Schatten (p : ℝ) (A : E →L[ℂ] F) : Prop :=
  0 < p ∧ IsCompactOperator A ∧
    Summable (fun n : ℕ => (approximationNumber A n : ℝ) ^ p)

def schattenNorm (p : ℝ) (A : E →L[ℂ] F) : ℝ :=
  (∑' n : ℕ, (approximationNumber A n : ℝ) ^ p) ^ (1 / p)

def HasSchattenTTO (p : ℝ) (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ Schatten p A


/-- The conjugate model space, retaining its constant mode. -/
def conjugateModel (u : BoundaryLInf) : Submodule ℂ BoundaryL2 :=
  (Submodule.span ℂ (star '' (model u : Set BoundaryL2))).topologicalClosure
abbrev ConjugateModel (u : BoundaryLInf) := ↥(conjugateModel u)
instance (u : BoundaryLInf) : CompleteSpace (ConjugateModel u) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- THO core form: the codomain is the conjugate model, not the negative Hardy space. -/
def RepresentsTHO (u : BoundaryLInf) (σ : BoundaryL2)
    (B : Model u →L[ℂ] ConjugateModel u) : Prop :=
  ∀ f : Model u, ∀ g : ConjugateModel u,
    IsBounded f.val → IsBounded g.val →
    inner ℂ g (B f) = coreForm σ f.val g.val

def HasSchattenTHO (p : ℝ) (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u σ B ∧ Schatten p B

def SameHankel (σ τ : BoundaryL2) : Prop :=
  ∀ f : Hardy, ∀ g : ↥hardy.orthogonal,
    IsBounded f.val → IsBounded g.val →
    coreForm σ f.val g.val = coreForm τ f.val g.val

def hankelSymbol (u : BoundaryLInf) (φ : BoundaryL2) : BoundaryL2 :=
  star (multiply coordinate (conjugation u φ))

/-- Normalized area measure on the disk; it is not circle Haar measure. -/
def diskArea : Measure ℂ := (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict disk

def besovOrder (p : ℝ) : ℕ := ⌊1 / p⌋₊ + 1

def besovEnergy (p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (besovOrder p), ENNReal.ofReal (‖iteratedDeriv j f 0‖ ^ p)) +
  ∫⁻ z, ENNReal.ofReal (‖iteratedDeriv (besovOrder p) f z‖ ^ p *
    (1 - ‖z‖ ^ 2) ^ ((besovOrder p : ℝ) * p - 2)) ∂diskArea

def homogeneousBesovEnergy (p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (besovOrder p),
    if j = 0 then 0 else ENNReal.ofReal (‖iteratedDeriv j f 0‖ ^ p)) +
  ∫⁻ z, ENNReal.ofReal (‖iteratedDeriv (besovOrder p) f z‖ ^ p *
    (1 - ‖z‖ ^ 2) ^ ((besovOrder p : ℝ) * p - 2)) ∂diskArea

def InBesov (p : ℝ) (f : BoundaryL2) : Prop :=
  f ∈ hardy ∧ besovEnergy p (analyticValue f) < ∞

def besovNorm (p : ℝ) (f : BoundaryL2) : ℝ :=
  (besovEnergy p (analyticValue f)).toReal ^ (1 / p)

def homogeneousBesovNorm (p : ℝ) (f : ℂ → ℂ) : ℝ :=
  (homogeneousBesovEnergy p f).toReal ^ (1 / p)

/-- Arc means use the lift to real coordinates of period one. -/
def arcMean (f : BoundaryL2) (a b : ℝ) : ℂ :=
  ((b - a : ℝ) : ℂ)⁻¹ * ∫ t in Set.Ioc a b, f (t : Boundary)

def meanOscillation (f : BoundaryL2) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ t in Set.Ioc a b, ‖f (t : Boundary) - arcMean f a b‖

/-- Analytic VMO, with no pointwise-continuity assumption. -/
def InVMOA (f : BoundaryL2) : Prop :=
  f ∈ hardy ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ a b : ℝ, a < b → b - a ≤ min δ 1 → meanOscillation f a b < ε

/-- Theorem 1, including both inhomogeneous and shifted homogeneous formulations. -/
def BesovConclusion (p : ℝ) : Prop :=
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasSchattenTTO p u φ.val ↔ InBesov p (conjugation u φ.val)) ∧
    (HasSchattenTTO p u φ.val ↔
      homogeneousBesovEnergy p (fun z => z * analyticValue (conjugation u φ.val) z) < ∞)) ∧
  ∃ c C ch Ch : ℝ, 0 < c ∧ 0 < C ∧ 0 < ch ∧ 0 < Ch ∧
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A → Schatten p A →
      c * besovNorm p (conjugation u φ.val) ≤ schattenNorm p A ∧
      schattenNorm p A ≤ C * besovNorm p (conjugation u φ.val) ∧
      ch * homogeneousBesovNorm p (fun z => z * analyticValue (conjugation u φ.val) z)
        ≤ schattenNorm p A ∧
      schattenNorm p A ≤ Ch * homogeneousBesovNorm p
        (fun z => z * analyticValue (conjugation u φ.val) z)

/-- Theorem 2, including the continuous classical-Hankel representative. -/
def CompactConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasCompactTTO u φ.val ↔ InVMOA (conjugation u φ.val)) ∧
    (HasCompactTTO u φ.val ↔ ∃ g : C(Boundary, ℂ),
      SameHankel (hankelSymbol u φ.val) (ContinuousMap.toLp 2 circleMeasure ℂ g))


/-- Canonically normalized Blaschke factor, including the zero at the origin. -/
def blaschkeFactor (a : Disk) (z : ℂ) : ℂ :=
  if a.val = 0 then z else ((‖a.val‖ : ℂ) / a.val) * (a.val - z) / (1 - conj a.val * z)

/-- Multiplicities are retained: injectivity is required separately only in Sections 2--3. -/
def HasBlaschkeZeros {ι : Type*} (u : BoundaryLInf) (a : ι → Disk) : Prop :=
  Summable (fun i => 1 - ‖(a i).val‖) ∧
  ∃ α : ℂ, ‖α‖ = 1 ∧ ∀ z ∈ disk,
    innerValue u z = α * ∏' i, blaschkeFactor (a i) z

def Interpolating (a : ℕ → Disk) : Prop :=
  ∀ w : ℕ → ℂ, (∃ M : ℝ, ∀ n, ‖w n‖ ≤ M) →
    ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ ∀ n, innerValue g (a n).val = w n

def NodeKernel (a : Disk) (f : BoundaryL2) : Prop :=
  ∀ᵐ t ∂circleMeasure,
    f t = (Real.sqrt (1 - ‖a.val‖ ^ 2) : ℂ) /
      (1 - conj a.val * fourier (T := 1) 1 t)

def RieszSynthesis (u : BoundaryLInf) (a : ℕ → Disk)
    (R : lp (fun _ : ℕ => ℂ) 2 ≃L[ℂ] Model u) : Prop :=
  ∀ n, NodeKernel (a n) (R (lp.single 2 n (1 : ℂ))).val

def summableValues {ι : Type*} (p : ℝ) (w : ι → ℂ) : Prop :=
  Summable (fun n => ‖w n‖ ^ p)

def valueNorm {ι : Type*} (p : ℝ) (w : ι → ℂ) : ℝ :=
  (∑' n, ‖w n‖ ^ p) ^ (1 / p)

/-- Theorem 3. The norm comparison uses the actual kernel synthesis and inverse bounds. -/
def InterpolatingConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ a : ℕ → Disk, Function.Injective a → HasBlaschkeZeros u a → Interpolating a →
    (∃ R : lp (fun _ : ℕ => ℂ) 2 ≃L[ℂ] Model u, RieszSynthesis u a R) ∧
    ∀ φ : Hardy,
      (HasBoundedTTO u φ.val ↔ ∃ M : ℝ, ∀ n, ‖analyticValue φ.val (a n).val‖ ≤ M) ∧
      (HasCompactTTO u φ.val ↔ Tendsto (fun n => analyticValue φ.val (a n).val) atTop (𝓝 0)) ∧
      ∀ p : ℝ, 0 < p →
        (HasSchattenTTO p u φ.val ↔ summableValues p (fun n => analyticValue φ.val (a n).val)) ∧
        ∀ R : lp (fun _ : ℕ => ℂ) 2 ≃L[ℂ] Model u, RieszSynthesis u a R →
        ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A → Schatten p A →
          (‖R.toContinuousLinearMap‖ * ‖R.symm.toContinuousLinearMap‖)⁻¹ * valueNorm p (fun n => analyticValue φ.val (a n).val)
            ≤ schattenNorm p A ∧
          schattenNorm p A ≤ (‖R.toContinuousLinearMap‖ * ‖R.symm.toContinuousLinearMap‖) *
            valueNorm p (fun n => analyticValue φ.val (a n).val)

def PerturbedKernelBasis (u : BoundaryLInf) (a : ℕ → Disk)
    (ideal : Set (Model u →L[ℂ] Model u)) : Prop :=
  ∃ e : HilbertBasis ℕ ℂ (Model u), ∃ V : Model u ≃ₗᵢ[ℂ] Model u,
    ∃ Γ : Model u →L[ℂ] Model u, Γ ∈ ideal ∧
      ∀ n, NodeKernel (a n) (V (e n) + Γ (e n)).val

def HasBoundedAnalyticSplit (u : BoundaryLInf) (A : Model u →L[ℂ] Model u) : Prop :=
  ∃ φ ψ : Hardy, ∃ X Y : Model u →L[ℂ] Model u,
    RepresentsTTO u φ.val X ∧ RepresentsTTO u (star ψ.val) Y ∧ A = X + Y

def HasBoundedSymbolSplit (u : BoundaryLInf) (A : Model u →L[ℂ] Model u) : Prop :=
  ∃ φ ψ : BoundaryLInf, toL2 φ ∈ hardy ∧ toL2 ψ ∈ hardy ∧
    RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A

def HasSchattenSplit (p : ℝ) (u : BoundaryLInf) (A : Model u →L[ℂ] Model u) : Prop :=
  ∃ φ ψ : Hardy, ∃ X Y : Model u →L[ℂ] Model u,
    RepresentsTTO u φ.val X ∧ RepresentsTTO u (star ψ.val) Y ∧
    Schatten p X ∧ Schatten p Y ∧ A = X + Y

/-- Theorem 4, including the bounded-component equivalent formulation. -/
def PerturbedBasisConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ a : ℕ → Disk, Function.Injective a → HasBlaschkeZeros u a →
    (∀ A : Model u →L[ℂ] Model u,
      HasBoundedAnalyticSplit u A ↔ HasBoundedSymbolSplit u A) ∧
    ∀ φ ψ : BoundaryLInf, toL2 φ ∈ hardy → toL2 ψ ∈ hardy →
    ∀ A : Model u →L[ℂ] Model u,
    RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A →
      ((PerturbedKernelBasis u a {Γ | IsCompactOperator Γ}) →
        (IsCompactOperator A ↔ Tendsto (fun n =>
          innerValue φ (a n).val + conj (innerValue ψ (a n).val)) atTop (𝓝 0))) ∧
      ∀ p : ℝ, 0 < p → PerturbedKernelBasis u a {Γ | Schatten p Γ} →
        (Schatten p A ↔ summableValues p (fun n =>
          innerValue φ (a n).val + conj (innerValue ψ (a n).val)))


/-- An ordinary two-sided ideal, with no norm-closure requirement. -/
def TwoSided (u : BoundaryLInf) (I : Submodule ℂ (Model u →L[ℂ] Model u)) : Prop :=
  ∀ A ∈ I, ∀ L R : Model u →L[ℂ] Model u, L ∘L A ∘L R ∈ I

def InTTOIdeal (u : BoundaryLInf) (I : Submodule ℂ (Model u →L[ℂ] Model u))
    (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ A ∈ I

def finiteSingular (μ : Measure Boundary) : Prop :=
  μ Set.univ < ∞ ∧ Measure.MutuallySingular μ circleMeasure

def singularInnerValue (μ : Measure Boundary) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (- (r : ℂ) * ∫ t,
    (fourier (T := 1) 1 t + z) / (fourier (T := 1) 1 t - z) ∂μ)

def HasSingularRepresentation (u : BoundaryLInf) (μ : Measure Boundary) : Prop :=
  finiteSingular μ ∧ ∃ α : ℂ, ‖α‖ = 1 ∧
    ∀ z ∈ disk, innerValue u z = α * singularInnerValue μ 1 z

/-- General canonical singular measure, permitting a Blaschke factor with finite/infinite zeros. -/
def HasCanonicalMeasure (u : BoundaryLInf) (μ : Measure Boundary) : Prop :=
  finiteSingular μ ∧ ∃ a : ℕ → Option Disk,
    Summable (fun n => (a n).elim 0 (fun w => 1 - ‖w.val‖)) ∧
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∀ z ∈ disk,
      innerValue u z = α * (∏' n, (a n).elim 1 (fun w => blaschkeFactor w z)) *
        singularInnerValue μ 1 z

/-- Boundary reconstruction from the Taylor coefficients. The series uses the ordinary Hardy Fourier basis. -/
def analyticBoundary (f : ℂ → ℂ) : BoundaryL2 :=
  ∑' n : ℕ, (iteratedDeriv n f 0 / (n.factorial : ℂ)) • fourierBasis (T := 1) (n : ℤ)

def mode (n : ℤ) : BoundaryLInf :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (fourier (T := 1) n)

def powerModel (μ : Measure Boundary) (r : ℝ) : Submodule ℂ BoundaryL2 :=
  hardy ⊓ (Submodule.span ℂ (Set.range (fun n : ℕ =>
    multiply (mode (n : ℤ)) (analyticBoundary (singularInnerValue μ r))))).orthogonal

instance (μ : Measure Boundary) (r : ℝ) : CompleteSpace ↥(powerModel μ r) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (Submodule.isClosed_orthogonal _)).completeSpace_coe

def powerProjection (μ : Measure Boundary) (r : ℝ) (f : BoundaryL2) : BoundaryL2 :=
  ((powerModel μ r).orthogonalProjectionOnto f).val

def HasAnalyticGap (μ : Measure Boundary) (r : ℝ) (φ : BoundaryL2) : Prop :=
  ∃ h : Hardy, ∀ z ∈ disk,
    analyticValue φ z = singularInnerValue μ r z * analyticValue h.val z

/-- Theorem 5, for every finite-sum two-sided ideal, not only norm-closed ideals. -/
def GapConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ →
  ∀ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I →
  ∀ φ ψ : Hardy, ∀ r : ℝ, 0 < r → r < 1 → HasAnalyticGap μ r φ.val →
    InTTOIdeal u I (splitSymbol φ.val ψ.val) →
      InTTOIdeal u I φ.val ∧ InTTOIdeal u I (star ψ.val)

/-- Corollary 1 retains the normalized canonical symbol and both low-frequency hypotheses. -/
def CanonicalGapConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ →
  ∀ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I →
  ∀ φ ψ : Model u, analyticValue ψ.val 0 = 0 →
  ∀ r : ℝ, 0 < r → r < 1 →
    (InTTOIdeal u I (powerProjection μ r φ.val) ↔
      InTTOIdeal u I (powerProjection μ r (splitSymbol φ.val ψ.val))) ∧
    (InTTOIdeal u I (splitSymbol φ.val ψ.val) →
      InTTOIdeal u I (powerProjection μ r φ.val) →
        InTTOIdeal u I φ.val ∧ InTTOIdeal u I (star ψ.val))

def AngularLimit (f : ℂ → ℂ) (ζ : Boundary) (c : ℂ) : Prop :=
  ∀ M : ℝ, 1 < M → Tendsto f
    (𝓝[disk ∩ {z | ‖z - fourier (T := 1) 1 ζ‖ ≤ M * (1 - ‖z‖)}]
      (fourier (T := 1) 1 ζ)) (𝓝 c)

/-- Lemma 6 has arbitrary-inner scope and requires no boundedness of the analytic symbol. -/
def AtomicBoundaryConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasCanonicalMeasure u μ →
  ∀ ζ : Boundary, 0 < μ {ζ} → ∀ φ : Hardy, ∀ c : ℂ,
    (∃ X : Model u →L[ℂ] Model u,
      RepresentsTTO u φ.val X ∧ IsCompactOperator (X - c • ContinuousLinearMap.id ℂ (Model u))) →
      AngularLimit (analyticValue φ.val) ζ c

def SingleAtom (u : BoundaryLInf) (ζ : Boundary) : Prop :=
  ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ α : ℂ, ‖α‖ = 1 ∧ ∀ z ∈ disk,
    innerValue u z = α * Complex.exp (-(ℓ : ℂ) *
      (fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z))

/-- Finite boundary products are explicit Holder multiplications. -/
def finiteProduct {m : ℕ} (u : Fin m → BoundaryLInf) : BoundaryLInf :=
  (List.ofFn u).foldr multiplyInf (constLInf 1)

def cofactor {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) : BoundaryLInf :=
  finiteProduct (fun k => if k = j then constLInf 1 else u k)

def Corona {m : ℕ} (u : Fin m → BoundaryLInf) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ disk, δ ≤ ∑ j, ‖innerValue (cofactor u j) z‖

def Bezout {m : ℕ} (u a : Fin m → BoundaryLInf) : Prop :=
  (∀ j, toL2 (a j) ∈ hardy) ∧ ∀ z ∈ disk,
    ∑ j, innerValue (a j) z * innerValue (cofactor u j) z = 1

/-- Shift an analytic/coanalytic core by a bounded correction without assuming the component bounded. -/
def AnalyticRemainder (p : ℝ) (u : BoundaryLInf) (φ : BoundaryL2)
    (F : Model u →L[ℂ] Model u) : Prop :=
  ∃ X : Model u →L[ℂ] Model u, RepresentsTTO u φ X ∧ Schatten p (X - F)

def CoanalyticRemainder (p : ℝ) (u : BoundaryLInf) (ψ : BoundaryL2)
    (F : Model u →L[ℂ] Model u) : Prop :=
  ∃ Y : Model u →L[ℂ] Model u, RepresentsTTO u (star ψ) Y ∧ Schatten p (Y + F)


def correction {m : ℕ} {u : BoundaryLInf}
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) : Model u →L[ℂ] Model u :=
  ∑ j, c j • E j

def Remainders {m : ℕ} (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2)
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) : Prop :=
  AnalyticRemainder p u φ (correction E c) ∧ CoanalyticRemainder p u ψ (correction E c)

def RepresentsIdempotents {m : ℕ} (u a : Fin m → BoundaryLInf)
    (E : Fin m → Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)) : Prop :=
  ∀ j, RepresentsTTO (finiteProduct u) (toL2 (multiplyInf (a j) (cofactor u j))) (E j)

def ComplementaryIdempotents {m : ℕ} {u : BoundaryLInf}
    (E : Fin m → Model u →L[ℂ] Model u) : Prop :=
  (∑ j, E j) = ContinuousLinearMap.id ℂ (Model u) ∧
  (∀ j, E j ∘L E j = E j) ∧ ∀ i j, i ≠ j → E i ∘L E j = 0

def cofactorRange {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) : Submodule ℂ BoundaryL2 :=
  (multiply (cofactor u j) ∘L (model (u j)).subtypeL).toLinearMap.range

def IdempotentRanges {m : ℕ} (u : Fin m → BoundaryLInf)
    (E : Fin m → Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)) : Prop :=
  ∀ j, (E j).toLinearMap.range.map (model (finiteProduct u)).subtype = cofactorRange u j

/-- Theorem 6: constants are quantified before symbols and before Bezout witnesses. -/
def FiniteAtomConclusion : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf, ∀ ζ : Fin m → Boundary,
  Function.Injective ζ → (∀ j, IsInner (u j) ∧ Nonconstant (u j) ∧ SingleAtom (u j) (ζ j)) →
    IsInner (finiteProduct u) ∧ Nonconstant (finiteProduct u) ∧
    (∃ a : Fin m → BoundaryLInf, Bezout u a) ∧
    (∀ a, Bezout u a → ∃ E, RepresentsIdempotents u a E ∧
      ComplementaryIdempotents E ∧ IdempotentRanges u E ∧
      ∀ a' E', Bezout u a' → RepresentsIdempotents u a' E' → E' = E) ∧
    ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ a, Bezout u a → ∀ E, RepresentsIdempotents u a E →
    ∀ φ ψ : Hardy,
      (HasSchattenTTO p (finiteProduct u) (splitSymbol φ.val ψ.val) ↔
        ∃ c, Remainders p (finiteProduct u) φ.val ψ.val E c) ∧
      (∀ c d, Remainders p (finiteProduct u) φ.val ψ.val E c →
        Remainders p (finiteProduct u) φ.val ψ.val E d → c = d) ∧
      ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
        (∀ c, Remainders p (finiteProduct u) φ.val ψ.val E c ↔
          ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ (Model (u j)))) ∧
        (∀ c, Remainders p (finiteProduct u) φ.val ψ.val E c →
          (∀ j, AngularLimit (analyticValue φ.val) (ζ j) (c j) ∧
            AngularLimit (analyticValue ψ.val) (ζ j) (-conj (c j))) ∧
          ∀ X Y : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
          RepresentsTTO (finiteProduct u) φ.val X →
          RepresentsTTO (finiteProduct u) (star ψ.val) Y →
          Schatten p (X - correction E c) → Schatten p (Y + correction E c) →
            schattenNorm p (X - correction E c) + schattenNorm p (Y + correction E c)
              ≤ C * schattenNorm p A) ∧
        (HasSchattenSplit p (finiteProduct u) A ↔
          ∃ c : ℂ, ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c) ∧
        (∀ c : ℂ,
          (AnalyticRemainder p (finiteProduct u) φ.val (c • ContinuousLinearMap.id ℂ _) ∧
            CoanalyticRemainder p (finiteProduct u) ψ.val (c • ContinuousLinearMap.id ℂ _)) ↔
          ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c) ∧
        ((HasSchattenTTO p (finiteProduct u) φ.val ∧
          HasSchattenTTO p (finiteProduct u) (star ψ.val)) ↔
          ∀ j, AngularLimit (analyticValue φ.val) (ζ j) 0)

abbrev BiPolynomial := (ℕ × ℕ) →₀ ℂ

def polynomialValue (q : BiPolynomial) (z : ℂ) : ℂ :=
  q.sum (fun jk c => c * z ^ jk.1 * conj z ^ jk.2)

def powerInf (a : BoundaryLInf) (n : ℕ) : BoundaryLInf :=
  Nat.rec (constLInf 1) (fun _ b => multiplyInf a b) n

def polynomialSymbol (q : BiPolynomial) : BoundaryL2 :=
  toL2 (q.sum (fun jk c => c • multiplyInf (powerInf coordinate jk.1)
    (powerInf (star coordinate) jk.2)))

def AtomicMeasure (μ : Measure Boundary) : Prop :=
  ∃ s : Set Boundary, s.Countable ∧ μ sᶜ = 0

def NonatomicMeasure (μ : Measure Boundary) : Prop := ∀ ζ : Boundary, μ {ζ} = 0

/-- Theorem 7. The general countable index also covers finite Blaschke products. -/
def PolynomialConclusion : Prop :=
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ι : Type, ∀ a : ι → Disk,
    Countable ι → HasBlaschkeZeros u a → ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔
        Tendsto (fun i => polynomialValue q (a i).val) cofinite (𝓝 0)) ∧
      ∀ p : ℝ, 2 ≤ p → (HasSchattenTTO p u (polynomialSymbol q) ↔
        summableValues p (fun i => polynomialValue q (a i).val))) ∧
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ μ : Measure Boundary, HasSingularRepresentation u μ → NonatomicMeasure μ →
    ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔
        ∀ ζ : Boundary, polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
      ((∀ ζ : Boundary, polynomialValue q (fourier (T := 1) 1 ζ) = 0) →
        ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A → A = 0)) ∧
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ μ : Measure Boundary, HasSingularRepresentation u μ → AtomicMeasure μ →
    ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔
        ∀ ζ : Boundary, 0 < μ {ζ} → polynomialValue q (fourier (T := 1) 1 ζ) = 0) ∧
      (HasCompactTTO u (polynomialSymbol q) → HasSchattenTTO 2 u (polynomialSymbol q))) ∧
  (∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ SingleAtom u 0 ∧
    ∃ q : BiPolynomial, (∀ z : ℂ, polynomialValue q z = 2 - z - conj z) ∧
    ∃ A : Model u →L[ℂ] Model u,
      RepresentsTTO u (polynomialSymbol q) A ∧ Schatten 2 A ∧ A ≠ 0)


abbrev BidiskL2 := Lp ℂ 2 (circleMeasure.prod circleMeasure)

def bidiskMode (m n : ℕ) : C(Boundary × Boundary, ℂ) :=
  ⟨fun t => fourier (T := 1) (m : ℤ) t.1 * fourier (T := 1) (n : ℤ) t.2,
    ((fourier (T := 1) (m : ℤ)).continuous.comp continuous_fst).mul
      ((fourier (T := 1) (n : ℤ)).continuous.comp continuous_snd)⟩

def bidiskHardy : Submodule ℂ BidiskL2 :=
  (Submodule.span ℂ (Set.range (fun mn : ℕ × ℕ =>
    ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode mn.1 mn.2)))).topologicalClosure

/-- Closed span of actual separated products: the concrete completed Hilbert tensor model. -/
def tensorModel (u : BoundaryLInf) : Submodule ℂ BidiskL2 :=
  (Submodule.span ℂ {G | ∃ f g : Model u,
    ∀ᵐ t ∂(circleMeasure.prod circleMeasure), G t = f.val t.1 * g.val t.2}).topologicalClosure
abbrev TensorModel (u : BoundaryLInf) := ↥(tensorModel u)
instance (u : BoundaryLInf) : CompleteSpace (TensorModel u) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

abbrev Ambient (u : BoundaryLInf) := Model (multiplyInf u u)

def analyticValue₂ (G : BidiskL2) (z w : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ,
    (∫ t, G t * conj (bidiskMode mn.1 mn.2 t) ∂(circleMeasure.prod circleMeasure)) *
      z ^ mn.1 * w ^ mn.2

def kernelValue (u : BoundaryLInf) (w z : ℂ) : ℂ :=
  (1 - conj (innerValue u w) * innerValue u z) / (1 - conj w * z)

def kernelBoundary (u : BoundaryLInf) (w : ℂ) (t : Boundary) : ℂ :=
  (1 - conj (innerValue u w) * u t) / (1 - conj w * fourier (T := 1) 1 t)

/-- First-linear kernel pairing; this definition does not presuppose Hilbert--Schmidt membership. -/
def FKernel (u : BoundaryLInf) (η : BoundaryL2) (z w : ℂ) : ℂ :=
  ∫ t, η t * conj (kernelBoundary u z t * kernelBoundary u w t) ∂circleMeasure

def eta₁ (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 :=
  ((model u).orthogonalProjectionOnto η).val

def eta₂ (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 :=
  ((model u).orthogonalProjectionOnto (multiply (star u) η)).val

def energyH (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 := multiply coordinate (eta₁ u η)
def energyG (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 := multiply coordinate (eta₂ u η)

def energyQuotient (u : BoundaryLInf) (η : BoundaryL2) (t s : Boundary) : ℂ :=
  (energyH u η t - energyH u η s + u t * energyG u η s - u s * energyG u η t) /
    (fourier (T := 1) 1 t - fourier (T := 1) 1 s)

/-- Extended energy; diagonal division is zero, on a product-null set. -/
def energy (u : BoundaryLInf) (η : BoundaryL2) : ℝ≥0∞ :=
  ∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖energyQuotient u η t s‖ ^ 2) ∂circleMeasure ∂circleMeasure

def energyPairing (u : BoundaryLInf) (η γ : BoundaryL2) : ℂ :=
  ∫ t, ∫ s, energyQuotient u η t s * conj (energyQuotient u γ t s) ∂circleMeasure ∂circleMeasure

/-- Explicit analytic graph, with no finite-energy hypothesis built into it. -/
def QGraph (u : BoundaryLInf) (η : Ambient u) (G : TensorModel u) : Prop :=
  ∀ z ∈ disk, ∀ w ∈ disk, analyticValue₂ G.val z w = FKernel u η.val z w

def HasBidiskRepresentative (u : BoundaryLInf) (η : BoundaryL2) : Prop :=
  ∃ G : BidiskL2, G ∈ bidiskHardy ∧
    ∀ z ∈ disk, ∀ w ∈ disk, analyticValue₂ G z w = FKernel u η z w

def diagonalDifferential (u : BoundaryLInf) (η : BoundaryL2) (z : ℂ) : ℂ :=
  deriv (fun w => w * analyticValue η w) z -
    2 * innerValue u z * deriv (fun w => w * analyticValue (eta₂ u η) w) z

def expandedDifferential (u : BoundaryLInf) (η : BoundaryL2) (z : ℂ) : ℂ :=
  deriv (analyticValue (energyH u η)) z +
    deriv (innerValue u) z * analyticValue (energyG u η) z -
    innerValue u z * deriv (analyticValue (energyG u η)) z

def dividedDifference (u : BoundaryLInf) (η : BoundaryL2) (z w : ℂ) : ℂ :=
  if z = w then expandedDifferential u η z else
    (analyticValue (energyH u η) z - analyticValue (energyH u η) w +
      innerValue u z * analyticValue (energyG u η) w -
      innerValue u w * analyticValue (energyG u η) z) / (z - w)

/-- Native densely-defined operators; positivity includes reality of the quadratic form. -/
def PositiveSelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D : H →ₗ.[ℂ] H) : Prop :=
  IsSelfAdjoint D ∧ ∀ x : D.domain, (inner ℂ x.val (D x)).im = 0 ∧
    0 ≤ (inner ℂ x.val (D x)).re

def IsSquareRoot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D S : H →ₗ.[ℂ] H) : Prop :=
  PositiveSelfAdjoint S ∧ ∀ x y : H,
    (x, y) ∈ D.graph ↔ ∃ v : H, (x, v) ∈ S.graph ∧ (v, y) ∈ S.graph

/-- Natural restricted Q*Q composition, not LinearPMap.comp's full-range variant. -/
def IsAdjointSquare (u : BoundaryLInf)
    (Q : Ambient u →ₗ.[ℂ] TensorModel u) (D : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  ∀ x y : Ambient u, (x, y) ∈ D.graph ↔
    ∃ v : TensorModel u, (x, v) ∈ Q.graph ∧ (v, y) ∈ Q.adjoint.graph

def EnergyGeometry (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D S : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  (∀ η G, (η, G) ∈ Q.graph ↔ QGraph u η G) ∧
  (∀ η : Ambient u, η ∈ Q.domain ↔ energy u η.val < ∞) ∧
  Q.IsClosed ∧ Dense (Q.domain : Set (Ambient u)) ∧
  IsAdjointSquare u Q D ∧ PositiveSelfAdjoint D ∧ IsSquareRoot D S ∧
  S.domain = Q.domain ∧
  (∀ η : S.domain, ENNReal.ofReal (‖S η‖ ^ 2) = energy u η.val.val) ∧
  (∀ η χ : Ambient u, (η, χ) ∈ D.graph ↔
    η ∈ Q.domain ∧ ∀ γ : Q.domain,
      inner ℂ γ.val χ = energyPairing u η.val γ.val.val) ∧
  (∀ η γ : Q.domain, energyPairing u η.val.val γ.val.val = inner ℂ (Q γ) (Q η))

/-- Theorem 8's exact function/norm statements, prior to constructing the positive operator. -/
def EnergyIdentities (u : BoundaryLInf) : Prop :=
  (∀ η : Ambient u,
    η.val = eta₁ u η.val + multiply u (eta₂ u η.val) ∧
    (∀ z ∈ disk, ∀ w ∈ disk, FKernel u η.val z w = dividedDifference u η.val z w) ∧
    (HasSchattenTHO 2 u (star η.val) ↔ HasBidiskRepresentative u η.val) ∧
    (HasSchattenTHO 2 u (star η.val) ↔ energy u η.val < ∞) ∧
    (energy u η.val < ∞ → ∃ G : TensorModel u, QGraph u η G) ∧
    (∀ G : TensorModel u, QGraph u η G →
      ENNReal.ofReal (‖G‖ ^ 2) = energy u η.val) ∧
    ∀ B : Model u →L[ℂ] ConjugateModel u,
      RepresentsTHO u (star η.val) B → Schatten 2 B →
      ENNReal.ofReal (schattenNorm 2 B ^ 2) = energy u η.val) ∧
  (∀ φ ψ : Model u, analyticValue ψ.val 0 = 0 →
    ∃ η : Ambient u,
      η.val = conjugation u φ.val + multiply u (multiply (star coordinate) ψ.val) ∧
      energyH u η.val = multiply coordinate (conjugation u φ.val) ∧
      energyG u η.val = ψ.val ∧
      (HasSchattenTTO 2 u (splitSymbol φ.val ψ.val) ↔ energy u η.val < ∞) ∧
      (∀ A : Model u →L[ℂ] Model u,
        RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten 2 A →
        ENNReal.ofReal (schattenNorm 2 A ^ 2) = energy u η.val))

/-- Theorem 9, with both pointwise formulas and the exact operator domain. -/
def DifferentialProperties (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u)
    (D : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  (∀ η : Ambient u, ∀ z ∈ disk,
    FKernel u η.val z z = diagonalDifferential u η.val z ∧
    FKernel u η.val z z = expandedDifferential u η.val z) ∧
  (∀ w ∈ disk, ∃ κ χ : Ambient u,
    (∀ z ∈ disk, analyticValue κ.val z = kernelValue (multiplyInf u u) w z) ∧
    (∀ z ∈ disk, analyticValue χ.val z = kernelValue u w z ^ 2) ∧
    (κ, χ) ∈ D.graph) ∧
  (∀ η : D.domain,
    (∀ z ∈ disk, analyticValue (D η).val z = FKernel u η.val.val z z) ∧
    inner ℂ η.val (D η) = ((energy u η.val.val).toReal : ℂ)) ∧
  (∀ η : Ambient u, η ∈ D.domain ↔ η ∈ Q.domain ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : Q.domain,
      ‖energyPairing u η.val γ.val.val‖ ≤ C * ‖γ.val‖)

/-- Theorem 8. Finite-dimensional model spaces are included. -/
def HilbertSchmidtConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    EnergyIdentities u ∧ ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u,
      ∃ D S : Ambient u →ₗ.[ℂ] Ambient u, EnergyGeometry u Q D S

/-- Theorem 9 specifies the same canonical graph and adjoint square as Theorem 8. -/
def DifferentialConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u, ∃ D S : Ambient u →ₗ.[ℂ] Ambient u,
      EnergyGeometry u Q D S ∧ DifferentialProperties u Q D


def FiniteRank (A : E →L[ℂ] F) : Prop := ∃ n : ℕ, A.rank ≤ n

def HasFiniteRankTTO (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ FiniteRank A

/-- Explicit ideal specializations advertised in Theorem 5. -/
def GapSpecializationsConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ →
  ∀ φ ψ : Hardy, ∀ r : ℝ, 0 < r → r < 1 → HasAnalyticGap μ r φ.val →
    (∀ p : ℝ, 0 < p → HasSchattenTTO p u (splitSymbol φ.val ψ.val) →
      HasSchattenTTO p u φ.val ∧ HasSchattenTTO p u (star ψ.val)) ∧
    (HasCompactTTO u (splitSymbol φ.val ψ.val) →
      HasCompactTTO u φ.val ∧ HasCompactTTO u (star ψ.val)) ∧
    (HasFiniteRankTTO u (splitSymbol φ.val ψ.val) →
      HasFiniteRankTTO u φ.val ∧ HasFiniteRankTTO u (star ψ.val))

/-- Finite Blaschke case, including arbitrary L² symbols and every p>0. -/
def FiniteBlaschkeConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ n : ℕ, ∀ a : Fin n → Disk,
    HasBlaschkeZeros u a → FiniteDimensional ℂ (Model u) ∧
    ∀ σ : BoundaryL2, HasBoundedTTO u σ ∧ HasCompactTTO u σ ∧
      ∀ p : ℝ, 0 < p → HasSchattenTTO p u σ

/-- Remarks 2 and 9, with divergence visible in the extended coefficient sum. -/
def analyticCoefficientEnergy (u : BoundaryLInf) (φ : BoundaryL2) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((n + 1 : ℝ) * ‖fourierCoeff (conjugation u φ) (n : ℤ)‖ ^ 2)

def AnalyticDirichletConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasSchattenTTO 2 u φ.val ↔ analyticCoefficientEnergy u φ.val < ∞) ∧
    (∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A → Schatten 2 A →
      ENNReal.ofReal (schattenNorm 2 A ^ 2) = analyticCoefficientEnergy u φ.val) ∧
    (∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖
      (fourier (T := 1) 1 t * conjugation u φ.val t -
        fourier (T := 1) 1 s * conjugation u φ.val s) /
      (fourier (T := 1) 1 t - fourier (T := 1) 1 s)‖ ^ 2)
      ∂circleMeasure ∂circleMeasure) = analyticCoefficientEnergy u φ.val

/-- The bounded-component consequence in Remark 8 retains the entire p>0 range. -/
def AtomicBoundednessConclusion : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf, ∀ ζ : Fin m → Boundary,
  Function.Injective ζ → (∀ j, IsInner (u j) ∧ Nonconstant (u j) ∧ SingleAtom (u j) (ζ j)) →
  ∀ p : ℝ, 0 < p → ∀ φ ψ : Hardy,
    HasSchattenTTO p (finiteProduct u) (splitSymbol φ.val ψ.val) →
      HasBoundedTTO (finiteProduct u) φ.val ∧
      HasBoundedTTO (finiteProduct u) (star ψ.val) ∧
      (∀ j, ∃ c : ℂ, AngularLimit (analyticValue φ.val) (ζ j) c ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj c)) ∧
      (∀ j, AngularLimit (fun z => analyticValue φ.val z + conj (analyticValue ψ.val z)) (ζ j) 0)

/-- Whole source identity is specified on bounded tests even before boundedness. -/
def SameTTO (u : BoundaryLInf) (σ τ : BoundaryL2) : Prop :=
  ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
    coreForm σ f.val g.val = coreForm τ f.val g.val

/-- Lemma 4: equality of core splittings leaves only a scalar defect. -/
def ScalarAmbiguityObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ₁ φ₂ ψ₁ ψ₂ : Hardy,
    SameTTO u (splitSymbol φ₁.val ψ₁.val) (splitSymbol φ₂.val ψ₂.val) →
      ∃ c : ℂ, RepresentsTTO u (φ₁.val - φ₂.val) (c • ContinuousLinearMap.id ℂ _) ∧
        RepresentsTTO u (star ψ₂.val - star ψ₁.val) (c • ContinuousLinearMap.id ℂ _)

/-- Coanalytic version of Theorem 1, as asserted in Remark 3. -/
def CoanalyticBesovConclusion (p : ℝ) : Prop :=
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasSchattenTTO p u (star φ.val) ↔ InBesov p (conjugation u φ.val)) ∧
    (HasSchattenTTO p u (star φ.val) ↔
      homogeneousBesovEnergy p (fun z => z * analyticValue (conjugation u φ.val) z) < ∞)) ∧
  ∃ c C ch Ch : ℝ, 0 < c ∧ 0 < C ∧ 0 < ch ∧ 0 < Ch ∧
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (star φ.val) A → Schatten p A →
      c * besovNorm p (conjugation u φ.val) ≤ schattenNorm p A ∧
      schattenNorm p A ≤ C * besovNorm p (conjugation u φ.val) ∧
      ch * homogeneousBesovNorm p (fun z => z * analyticValue (conjugation u φ.val) z)
        ≤ schattenNorm p A ∧
      schattenNorm p A ≤ Ch * homogeneousBesovNorm p
        (fun z => z * analyticValue (conjugation u φ.val) z)

def CoanalyticCompactConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    (HasCompactTTO u (star φ.val) ↔ InVMOA (conjugation u φ.val)) ∧
    (HasCompactTTO u (star φ.val) ↔ ∃ g : C(Boundary, ℂ),
      SameHankel (hankelSymbol u φ.val) (ContinuousMap.toLp 2 circleMeasure ℂ g))

def boundarySign (t : Boundary) : ℂ :=
  if 0 < (fourier (T := 1) 1 t).im then 1 else
    if (fourier (T := 1) 1 t).im < 0 then -1 else 0

/-- Remark 4's explicit logarithmic bounded-operator/unbounded-components example. -/
def UnboundedComponentsConclusion : Prop :=
  ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧
  ∃ a : ℕ → Disk, Function.Injective a ∧ HasBlaschkeZeros u a ∧ Interpolating a ∧
    (∀ n, (a n).val = 1 - (2 : ℂ) ^ (-(n : ℤ) - 1)) ∧
  ∃ φ : Hardy, analyticValue φ.val 0 = 0 ∧
    (∀ z ∈ disk, analyticValue φ.val z = -(Complex.I / (Real.pi : ℂ)) *
      Complex.log ((1 + z) / (1 - z))) ∧
    (∀ᵐ t ∂circleMeasure, splitSymbol φ.val φ.val t =
      boundarySign t) ∧
  ∃ A : Model u →L[ℂ] Model u,
    RepresentsTTO u (splitSymbol φ.val φ.val) A ∧ ‖A‖ ≤ 1 ∧ ¬HasBoundedTTO u φ.val ∧
    ∀ α β : Hardy, SameTTO u (splitSymbol α.val β.val) (splitSymbol φ.val φ.val) →
      ¬HasBoundedTTO u α.val

def alternatingValues (n : ℕ) : ℂ := if Even n then 0 else 1

/-- Remark 5: the splitting criterion and its obstruction in every stated U+S_p setting. -/
def BlaschkeSplittingConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
  Function.Injective a → HasBlaschkeZeros u a → ∀ p : ℝ, 0 < p →
  PerturbedKernelBasis u a {Γ | Schatten p Γ} →
    (∀ φ ψ : BoundaryLInf, toL2 φ ∈ hardy → toL2 ψ ∈ hardy →
      ∀ A : Model u →L[ℂ] Model u,
      RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A → Schatten p A →
        (HasSchattenSplit p u A ↔ ∃ c : ℂ,
          summableValues p (fun n => innerValue φ (a n).val - c))) ∧
    (∃ φ : BoundaryLInf, toL2 φ ∈ hardy ∧
      (∀ n, innerValue φ (a n).val = alternatingValues n) ∧
      ∃ A : Model u →L[ℂ] Model u,
        RepresentsTTO u (splitSymbol (toL2 φ) (toL2 (-φ))) A ∧
        Schatten p A ∧ ¬HasSchattenSplit p u A)

abbrev IntervalL2 (ℓ : ℝ) := Lp ℂ 2 (volume.restrict (Set.Ioo (0 : ℝ) ℓ))

def RepresentsVolterra (ℓ : ℝ) (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) : Prop :=
  ∀ f : IntervalL2 ℓ, ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) ℓ)),
    (V f) t = ∫ s in Set.Ioo (0 : ℝ) t, f s

def PaleyWienerUnitary (u : BoundaryLInf) (ℓ : ℝ)
    (piModel : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) : Prop :=
  ∀ f : IntervalL2 ℓ, ∀ w : ℂ, 0 < w.im →
    analyticValue (piModel f).val ((w - Complex.I) / (w + Complex.I)) /
        ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) =
    (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * ∫ t in Set.Ioo (0 : ℝ) ℓ,
      Complex.exp ((t : ℂ) * w * Complex.I) * f t

/-- A concrete Cayley/Fourier--Laplace model, containing no ideal/compactness conclusions. -/
structure VolterraModelData (ℓ : ℝ) where
  u : BoundaryLInf
  inner : IsInner u
  nonconstant : Nonconstant u
  u_value : ∀ z ∈ disk, innerValue u z = Complex.exp (-(ℓ : ℂ) * (1 + z) / (1 - z))
  symbol : Hardy
  symbol_value : ∀ z ∈ disk, analyticValue symbol.val z = (1 - z) * (1 - innerValue u z) / (1 + z)
  bound : ∀ᵐ t ∂circleMeasure, ‖symbol.val t‖ ≤ ℓ
  piModel : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u
  piModel_formula : PaleyWienerUnitary u ℓ piModel
  V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ
  volterra : RepresentsVolterra ℓ V
  analyticOperator : Model u →L[ℂ] Model u
  represents : RepresentsTTO u symbol.val analyticOperator
  intertwines : ∀ f : IntervalL2 ℓ, analyticOperator (piModel f) = piModel (V f)
  rank_one : (V + V.adjoint).rank = 1
  rank_one_formula : ∀ f : IntervalL2 ℓ,
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) ℓ)),
      ((V + V.adjoint) f) t = ∫ s in Set.Ioo (0 : ℝ) ℓ, f s

/-- Remark 6: below-one boundedness and the explicit same-p Volterra obstruction. -/
def EndpointConclusion : Prop :=
  (∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ζ : Boundary, SingleAtom u ζ →
    ∀ φ ψ : Hardy, ∀ p : ℝ, 0 < p → p ≤ 1 →
      HasSchattenTTO p u (splitSymbol φ.val ψ.val) →
      HasBoundedTTO u φ.val ∧ HasBoundedTTO u (star ψ.val) ∧
      ∃ c : ℂ, AnalyticRemainder 2 u φ.val (c • ContinuousLinearMap.id ℂ _) ∧
        CoanalyticRemainder 2 u ψ.val (c • ContinuousLinearMap.id ℂ _)) ∧
  (∀ ℓ : ℝ, 0 < ℓ → ∃ d : VolterraModelData ℓ,
    IsCompactOperator d.V ∧
    (∀ n, (approximationNumber d.V n : ℝ) = ℓ / (Real.pi * ((n : ℝ) + 1 / 2))) ∧
    (∀ c : ℂ, c ≠ 0 → ¬IsCompactOperator (d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ))) ∧
    ∃ A : Model d.u →L[ℂ] Model d.u,
      RepresentsTTO d.u (splitSymbol d.symbol.val d.symbol.val) A ∧
      (∀ p : ℝ, 0 < p → Schatten p A) ∧
      (∀ p : ℝ, 0 < p → p ≤ 1 → ¬Schatten p d.V ∧
        (∀ c : ℂ, ¬Schatten p (d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ))) ∧
        ¬HasSchattenSplit p d.u A))

theorem boundary_star_neg (f : BoundaryL2) : star (-f) = -star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (-f), Lp.coeFn_neg f, Lp.coeFn_neg (star f), Lp.coeFn_star f] with t h₁ h₂ h₃ h₄
  change (star (-f)) t = star ((-f) t) at h₁
  change (-f) t = -f t at h₂
  change (-star f) t = -(star f) t at h₃
  change (star f) t = star (f t) at h₄
  rw [h₁, h₂, h₃, h₄]
  exact map_neg (starRingEnd ℂ) (f t)

def unitaryConjugate {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K)
    (D : H →L[ℂ] H) : K →L[ℂ] K :=
  U.toContinuousLinearEquiv.toContinuousLinearMap ∘L D ∘L
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Explicit pure-atomic shift normal form for the two-atom example, before taking S-S*. -/
structure TwoAtomShiftData (a b : ℝ) where
  u : Fin 2 → BoundaryLInf
  atoms : Fin 2 → Boundary
  atom₀ : atoms 0 = 0
  atom₁ : atoms 1 = ((1 / 2 : ℝ) : Boundary)
  value₀ : fourier (T := 1) 1 (atoms 0) = 1
  value₁ : fourier (T := 1) 1 (atoms 1) = -1
  distinct : Function.Injective atoms
  factors : ∀ j, IsInner (u j) ∧ Nonconstant (u j) ∧ SingleAtom (u j) (atoms j)
  factor₀ : ∀ z ∈ disk, innerValue (u 0) z = Complex.exp (-(a : ℂ) * (1 + z) / (1 - z))
  factor₁ : ∀ z ∈ disk, innerValue (u 1) z = Complex.exp (-(b : ℂ) * (1 - z) / (1 + z))
  S : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)
  represents : RepresentsTTO (finiteProduct u) (toL2 coordinate) S
  M : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)
  H : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)
  modelUnitary : IntervalL2 (a + b) ≃ₗᵢ[ℂ] Model (finiteProduct u)
  multiplier : IntervalL2 (a + b) →L[ℂ] IntervalL2 (a + b)
  multiplier_formula : ∀ f : IntervalL2 (a + b),
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) (a + b))),
      (multiplier f) t = (if t < a then (1 : ℂ) else -1) * f t
  normalform : M = unitaryConjugate modelUnitary multiplier
  selfadjoint : M.adjoint = M
  hilbertSchmidt : Schatten 2 H
  equation : S = M + H

/-- Remark 7's explicit two-atom cancellation and incompatible local constants. -/
def TwoAtomObstructionConclusion : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∃ d : TwoAtomShiftData a b,
    ∃ A : Model (finiteProduct d.u) →L[ℂ] Model (finiteProduct d.u),
      A = d.S - d.S.adjoint ∧
      RepresentsTTO (finiteProduct d.u) (toL2 coordinate - star (toL2 coordinate)) A ∧
      Schatten 2 A ∧
      (∀ j, AnalyticRemainder 2 (d.u j) (toL2 coordinate)
        (fourier (T := 1) 1 (d.atoms j) • ContinuousLinearMap.id ℂ _)) ∧
      ¬HasSchattenSplit 2 (finiteProduct d.u) A

/-- Actual diagonal kernel tensors and reproducing identities, before quotient norms. -/
structure DiagonalKernelData (u : BoundaryLInf) (Q : Ambient u →ₗ.[ℂ] TensorModel u) where
  kernel : Disk → Ambient u
  tensorKernel : Disk → TensorModel u
  kernel_value : ∀ w z : Disk,
    analyticValue (kernel w).val z.val = kernelValue (multiplyInf u u) w.val z.val
  product_value : ∀ w z t : Disk, analyticValue₂ (tensorKernel w).val z.val t.val =
    kernelValue u w.val z.val * kernelValue u w.val t.val
  graph : ∀ w : Disk, (kernel w, tensorKernel w) ∈ Q.graph
  diagonal_reproduces : ∀ G : TensorModel u, ∀ w : Disk,
    analyticValue₂ G.val w.val w.val = inner ℂ (tensorKernel w) G
  ambient_reproduces : ∀ η : Ambient u, ∀ w : Disk,
    analyticValue η.val w.val = inner ℂ (kernel w) η

def diagonalNull {u : BoundaryLInf} {Q : Ambient u →ₗ.[ℂ] TensorModel u}
    (d : DiagonalKernelData u Q) : Submodule ℂ (TensorModel u) :=
  (Submodule.span ℂ (Set.range d.tensorKernel)).orthogonal

def diagonalProjection {u : BoundaryLInf} {Q : Ambient u →ₗ.[ℂ] TensorModel u}
    (d : DiagonalKernelData u Q) (G : TensorModel u) : ↥(diagonalNull d).orthogonal :=
  (diagonalNull d).orthogonal.orthogonalProjectionOnto G

/-- The manuscript's graph-norm core condition, not a universal claim. -/
def KernelGraphCore {u : BoundaryLInf} {Q : Ambient u →ₗ.[ℂ] TensorModel u}
    (d : DiagonalKernelData u Q) : Prop :=
  (Submodule.span ℂ (Set.range (fun w : Disk => (d.kernel w, d.tensorKernel w)))).topologicalClosure = Q.graph

/-- Remark 10 uses the canonical Hilbert quotient as its squared-kernel RKHS.
The inherited norm on Z-perp is the minimum/quotient norm, and its point evaluations are explicit. -/
def SquaredKernelConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u, ∃ D S : Ambient u →ₗ.[ℂ] Ambient u,
    EnergyGeometry u Q D S ∧ DifferentialProperties u Q D ∧
    ∃ d : DiagonalKernelData u Q,
      (∀ G : TensorModel u, G ∈ diagonalNull d ↔
        ∀ w : Disk, analyticValue₂ G.val w.val w.val = 0) ∧
      (diagonalNull d).orthogonal =
        (Submodule.span ℂ (Set.range d.tensorKernel)).topologicalClosure ∧
      (∀ G : TensorModel u, ∀ w : Disk,
        analyticValue₂ (diagonalProjection d G).val.val w.val w.val = analyticValue₂ G.val w.val w.val) ∧
      (∀ h : ↥(diagonalNull d).orthogonal, diagonalProjection d h.val = h) ∧
      (∀ G T : TensorModel u, (∀ w : Disk, analyticValue₂ T.val w.val w.val = analyticValue₂ G.val w.val w.val) →
        ‖diagonalProjection d G‖ ≤ ‖T‖) ∧
      (∀ w : Disk, ∃ k : ↥(diagonalNull d).orthogonal,
        k.val = d.tensorKernel w ∧
        (∀ z : Disk, analyticValue₂ k.val.val z.val z.val = kernelValue u w.val z.val ^ 2) ∧
        ∀ h : ↥(diagonalNull d).orthogonal,
          analyticValue₂ h.val.val w.val w.val = inner ℂ k h) ∧
      (∀ η : Q.domain,
        (∀ w : Disk, analyticValue₂ (diagonalProjection d (Q η)).val.val w.val w.val = FKernel u η.val.val w.val w.val) ∧
        ∀ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u (star η.val.val) B → Schatten 2 B →
          ‖diagonalProjection d (Q η)‖ ≤ schattenNorm 2 B ∧
          (‖diagonalProjection d (Q η)‖ = schattenNorm 2 B ↔ Q η ∈ (diagonalNull d).orthogonal)) ∧
      (KernelGraphCore d →
        (∀ η : Q.domain, ‖diagonalProjection d (Q η)‖ = ‖Q η‖) ∧
        (∀ η : Ambient u, η ∈ D.domain ↔ η ∈ Q.domain ∧
          ∃ χ : Ambient u, ∀ w : Disk, analyticValue χ.val w.val = FKernel u η.val w.val w.val))

def triangularCut {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {N : ℕ} (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, ∑ j, if j < i then Q i ∘L A ∘L Q j else 0

def TriangularConstant (p τ : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ N : ℕ, ∀ Q : Fin N → H →L[ℂ] H,
    (∑ i, Q i) = ContinuousLinearMap.id ℂ H →
    (∀ i, (Q i).adjoint = Q i ∧ Q i ∘L Q i = Q i) →
    (∀ i j, i ≠ j → Q i ∘L Q j = 0) → ∀ A : H →L[ℂ] H, Schatten p A →
      Schatten p (triangularCut Q A) ∧ schattenNorm p (triangularCut Q A) ≤ τ * schattenNorm p A

/-- Full supporting Lemma 8 contract, including the meaning of the uniform triangular constant. -/
def OneAtomConclusion : Prop :=
  ∀ p : ℝ, 1 < p → ∃ τ : ℝ, 0 < τ ∧ TriangularConstant p τ ∧
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ζ : Boundary, SingleAtom u ζ →
  ∀ φ ψ : Hardy, ∀ A : Model u →L[ℂ] Model u,
    RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten p A →
    HasBoundedTTO u φ.val ∧ HasBoundedTTO u (star ψ.val) ∧
    (∃! c : ℂ, AnalyticRemainder p u φ.val (c • ContinuousLinearMap.id ℂ _) ∧
      CoanalyticRemainder p u ψ.val (c • ContinuousLinearMap.id ℂ _)) ∧
    ∀ c : ℂ, AnalyticRemainder p u φ.val (c • ContinuousLinearMap.id ℂ _) →
      CoanalyticRemainder p u ψ.val (c • ContinuousLinearMap.id ℂ _) →
      AngularLimit (analyticValue φ.val) ζ c ∧ AngularLimit (analyticValue ψ.val) ζ (-conj c) ∧
      ∀ X Y : Model u →L[ℂ] Model u, RepresentsTTO u φ.val X → RepresentsTTO u (star ψ.val) Y →
        schattenNorm p (X - c • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
        schattenNorm p (Y + c • ContinuousLinearMap.id ℂ _) ≤ (1 + τ) * schattenNorm p A

def CoreValue (u : BoundaryLInf) (σ : BoundaryL2) (f y : Model u) : Prop :=
  ∀ g : Model u, IsBounded g.val → inner ℂ g y = coreForm σ f.val g.val

abbrev FiniteModelSum {m : ℕ} (u : Fin m → BoundaryLInf) := PiLp 2 (fun j => Model (u j))

/-- Full supporting Lemma 9 contract. W is an actual native bounded equivalence. -/
def AnalyticGluingConclusion : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf,
  (∀ j, IsInner (u j) ∧ Nonconstant (u j)) → Corona u →
    (∃ a : Fin m → BoundaryLInf, Bezout u a) ∧
    ∀ a, Bezout u a → ∃ W : FiniteModelSum u ≃L[ℂ] Model (finiteProduct u),
      (∀ g : FiniteModelSum u, (W g).val = ∑ j, multiply (cofactor u j) (g j).val) ∧
      (∀ x : Model (finiteProduct u), ∀ j,
        (W.symm x j).val = ((model (u j)).orthogonalProjectionOnto (multiply (a j) x.val)).val) ∧
      (∀ γ : Hardy, ∀ g : FiniteModelSum u, (∀ j, IsBounded (g j).val) →
        IsBounded (W g).val ∧ ∃ y : FiniteModelSum u,
          (∀ j, CoreValue (u j) γ.val (g j) (y j)) ∧
          CoreValue (finiteProduct u) γ.val (W g) (W y)) ∧
      (∀ γ : Hardy, (HasBoundedTTO (finiteProduct u) γ.val ↔ ∀ j, HasBoundedTTO (u j) γ.val) ∧
        (∀ p : ℝ, 0 < p → (HasSchattenTTO p (finiteProduct u) γ.val ↔
          ∀ j, HasSchattenTTO p (u j) γ.val)) ∧
        ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
          RepresentsTTO (finiteProduct u) γ.val A →
        ∀ T : (j : Fin m) → Model (u j) →L[ℂ] Model (u j),
          (∀ j, RepresentsTTO (u j) γ.val (T j)) →
          ∀ g : FiniteModelSum u, A (W g) = W (WithLp.toLp 2 (fun j => T j (g j)))) ∧
      (∃ E, RepresentsIdempotents u a E ∧ ComplementaryIdempotents E ∧ IdempotentRanges u E ∧
        (∀ j, ∀ g : FiniteModelSum u,
          E j (W g) = W (WithLp.toLp 2 (fun k => if k = j then g k else 0))) ∧
        ∀ a' E', Bezout u a' → RepresentsIdempotents u a' E' → E' = E) ∧
      (∀ p : ℝ, 0 < p → ∀ φ ψ : Hardy,
        ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
        RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
        (HasSchattenSplit p (finiteProduct u) A ↔ ∃ c : ℂ,
          ∀ j, AnalyticRemainder p (u j) φ.val (c • ContinuousLinearMap.id ℂ _)))

def normalizedModelKernel (u : BoundaryLInf) (z : Disk) (k : Model u) : Prop :=
  ∀ᵐ t ∂circleMeasure, k.val t = kernelBoundary u z.val t /
    (Real.sqrt ((1 - ‖innerValue u z.val‖ ^ 2) / (1 - ‖z.val‖ ^ 2)) : ℂ)

def StolzFilter (ζ : Boundary) (M : ℝ) : Filter ℂ :=
  𝓝[disk ∩ {z | ‖z - fourier (T := 1) 1 ζ‖ ≤ M * (1 - ‖z‖)}] (fourier (T := 1) 1 ζ)

def berezin {u : BoundaryLInf} (k : Disk → Model u)
    (X : Model u →L[ℂ] Model u) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ disk then inner ℂ (k ⟨z, hz⟩) (X (k ⟨z, hz⟩)) else 0

def poissonError (u : BoundaryLInf) (φ : BoundaryL2) (z : ℂ) : ℂ :=
  ∫ t, conj (u t) * φ t *
    (((1 - ‖z‖ ^ 2) / ‖fourier (T := 1) 1 t - z‖ ^ 2 : ℝ) : ℂ) ∂circleMeasure

end TTO.Paper
