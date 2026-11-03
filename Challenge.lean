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

/-! Principal statements from the local manuscript, related to Lopatto–Rochberg, arXiv:1410.1906.
All definitions below have their ordinary analytic and operator-theoretic meanings.
The theorem bodies are deliberate statement placeholders; Solution supplies their proofs. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper

/-- The unit circle parametrized by the additive circle R/Z. -/
abbrev Boundary := AddCircle (1 : ℝ)
/-- Normalized Haar measure on the circle. -/
abbrev circleMeasure : Measure Boundary := AddCircle.haarAddCircle (T := 1)
/-- Square-integrable complex boundary functions modulo almost-everywhere equality. -/
abbrev BoundaryL2 := Lp ℂ 2 circleMeasure
/-- Essentially bounded complex boundary functions modulo almost-everywhere equality. -/
abbrev BoundaryLInf := Lp ℂ ∞ circleMeasure

/-- The constant essentially bounded boundary function. -/
def constLInf (c : ℂ) : BoundaryLInf := (memLp_const c).toLp (fun _ => c)
/-- The natural inclusion of L-infinity into L2 on the probability circle. -/
def toL2 (a : BoundaryLInf) : BoundaryL2 :=
  ((Lp.memLp a).mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).toLp a

/-- Bounded multiplication by an L-infinity boundary function on L2. -/
def multiply (a : BoundaryLInf) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ 2 2 a

/-- Pointwise multiplication of essentially bounded boundary functions. -/
def multiplyInf (a b : BoundaryLInf) : BoundaryLInf :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ ∞ ∞ a b

/-- The boundary coordinate exp(2*pi*i*t). -/
def coordinate : BoundaryLInf :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (fourier (T := 1) 1)

/-- Hardy H2, the closed span of the nonnegative Fourier modes in boundary L2. -/
def hardy : Submodule ℂ BoundaryL2 :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => fourierBasis (T := 1) (n : ℤ)))).topologicalClosure
/-- The Hilbert space of boundary Hardy H2 functions. -/
abbrev Hardy := ↥hardy
instance : CompleteSpace Hardy := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The model space H2 orthogonal to uH2, as a closed subspace of boundary L2. -/
def model (u : BoundaryLInf) : Submodule ℂ BoundaryL2 :=
  hardy ⊓ (Submodule.span ℂ (Set.range (fun n : ℕ =>
    multiply u (fourierBasis (T := 1) (n : ℤ))))).orthogonal
/-- The Hilbert model space associated with u. -/
abbrev Model (u : BoundaryLInf) := ↥(model u)
instance (u : BoundaryLInf) : CompleteSpace (Model u) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (Submodule.isClosed_orthogonal _)).completeSpace_coe

/-- An H-infinity boundary function that belongs to H2 and has modulus one almost everywhere. -/
def IsInner (u : BoundaryLInf) : Prop :=
  toL2 u ∈ hardy ∧ ∀ᵐ t ∂circleMeasure, ‖u t‖ = 1

/-- The boundary function is not almost everywhere a constant. -/
def Nonconstant (u : BoundaryLInf) : Prop := ¬∃ c : ℂ, u = constLInf c

/-- The open complex unit disk. -/
def disk : Set ℂ := {z | ‖z‖ < 1}
/-- Points of the open complex unit disk. -/
abbrev Disk := ↥disk

/-- The analytic function in the disk given by the nonnegative Fourier coefficients. -/
def analyticValue (f : BoundaryL2) (z : ℂ) : ℂ :=
  ∑' n : ℕ, fourierCoeff f (n : ℤ) * z ^ n

/-- The analytic disk representative of an essentially bounded Hardy boundary function. -/
def innerValue (u : BoundaryLInf) : ℂ → ℂ := analyticValue (toL2 u)
/-- The boundary L2 function is essentially bounded. -/
def IsBounded (f : BoundaryL2) : Prop := MemLp f ∞ circleMeasure

/-- The model conjugation u times conjugate(z*f), defined on boundary values. -/
def conjugation (u : BoundaryLInf) (f : BoundaryL2) : BoundaryL2 :=
  multiply u (multiply (star coordinate) (star f))

/-- The L2 symbol consisting of an analytic part and a conjugated analytic part. -/
def splitSymbol (φ ψ : BoundaryL2) : BoundaryL2 := φ + star ψ

/-- The first-linear multiplication form: the circle integral of symbol*f*conjugate(g). -/
def coreForm (σ f g : BoundaryL2) : ℂ :=
  ∫ t, σ t * f t * conj (g t) ∂circleMeasure

/-- A bounded model-space operator agrees with the symbol multiplication form on all bounded model tests. -/
def RepresentsTTO (u : BoundaryLInf) (σ : BoundaryL2)
    (A : Model u →L[ℂ] Model u) : Prop :=
  ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
    inner ℂ g (A f) = coreForm σ f.val g.val

/-- The L2 symbol has a bounded TTO extension from the bounded model core. -/
def HasBoundedTTO (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A

/-- The L2 symbol has a compact TTO extension from the bounded model core. -/
def HasCompactTTO (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ IsCompactOperator A

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Approximation number at index n: distance in operator norm to maps of rank at most n; index zero is the norm. -/
def approximationNumber (A : E →L[ℂ] F) (n : ℕ) : ℝ≥0 :=
  ⨅ R : {R : E →L[ℂ] F // R.rank ≤ n}, ‖A - R.val‖₊

/-- The compact operator has a positive exponent and summable p-th powers of its approximation numbers. -/
def Schatten (p : ℝ) (A : E →L[ℂ] F) : Prop :=
  0 < p ∧ IsCompactOperator A ∧
    Summable (fun n : ℕ => (approximationNumber A n : ℝ) ^ p)

/-- The p-th root of the approximation-number power sum, used on the corresponding Schatten class. -/
def schattenNorm (p : ℝ) (A : E →L[ℂ] F) : ℝ :=
  (∑' n : ℕ, (approximationNumber A n : ℝ) ^ p) ^ (1 / p)

/-- The bounded-core TTO form extends to a Schatten-p operator. -/
def HasSchattenTTO (p : ℝ) (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ Schatten p A


/-- The conjugate model space, retaining its constant mode. -/
def conjugateModel (u : BoundaryLInf) : Submodule ℂ BoundaryL2 :=
  (Submodule.span ℂ (star '' (model u : Set BoundaryL2))).topologicalClosure
/-- The Hilbert space of conjugated model functions. -/
abbrev ConjugateModel (u : BoundaryLInf) := ↥(conjugateModel u)
instance (u : BoundaryLInf) : CompleteSpace (ConjugateModel u) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- THO core form: the codomain is the conjugate model, not the negative Hardy space. -/
def RepresentsTHO (u : BoundaryLInf) (σ : BoundaryL2)
    (B : Model u →L[ℂ] ConjugateModel u) : Prop :=
  ∀ f : Model u, ∀ g : ConjugateModel u,
    IsBounded f.val → IsBounded g.val →
    inner ℂ g (B f) = coreForm σ f.val g.val

/-- The bounded-core truncated Hankel form extends to a Schatten-p operator. -/
def HasSchattenTHO (p : ℝ) (u : BoundaryLInf) (σ : BoundaryL2) : Prop :=
  ∃ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u σ B ∧ Schatten p B

/-- The two classical Hankel symbols have identical forms on bounded Hardy and negative-Hardy tests. -/
def SameHankel (σ τ : BoundaryL2) : Prop :=
  ∀ f : Hardy, ∀ g : ↥hardy.orthogonal,
    IsBounded f.val → IsBounded g.val →
    coreForm σ f.val g.val = coreForm τ f.val g.val

/-- The classical Hankel symbol conjugate(z*C(phi)) associated with an analytic model symbol. -/
def hankelSymbol (u : BoundaryLInf) (φ : BoundaryL2) : BoundaryL2 :=
  star (multiply coordinate (conjugation u φ))

/-- Normalized area measure on the disk; it is not circle Haar measure. -/
def diskArea : Measure ℂ := (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict disk

/-- The fixed Besov derivative order floor(1/p)+1. -/
def besovOrder (p : ℝ) : ℕ := ⌊1 / p⌋₊ + 1

/-- Inhomogeneous analytic Besov energy, including every derivative at zero below the chosen order. -/
def besovEnergy (p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (besovOrder p), ENNReal.ofReal (‖iteratedDeriv j f 0‖ ^ p)) +
  ∫⁻ z, ENNReal.ofReal (‖iteratedDeriv (besovOrder p) f z‖ ^ p *
    (1 - ‖z‖ ^ 2) ^ ((besovOrder p : ℝ) * p - 2)) ∂diskArea

/-- The same analytic Besov energy with only the value-at-zero term omitted. -/
def homogeneousBesovEnergy (p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (besovOrder p),
    if j = 0 then 0 else ENNReal.ofReal (‖iteratedDeriv j f 0‖ ^ p)) +
  ∫⁻ z, ENNReal.ofReal (‖iteratedDeriv (besovOrder p) f z‖ ^ p *
    (1 - ‖z‖ ^ 2) ^ ((besovOrder p : ℝ) * p - 2)) ∂diskArea

/-- The boundary Hardy function has finite inhomogeneous analytic Besov energy. -/
def InBesov (p : ℝ) (f : BoundaryL2) : Prop :=
  f ∈ hardy ∧ besovEnergy p (analyticValue f) < ∞

/-- The p-th root of finite inhomogeneous analytic Besov energy. -/
def besovNorm (p : ℝ) (f : BoundaryL2) : ℝ :=
  (besovEnergy p (analyticValue f)).toReal ^ (1 / p)

/-- The p-th root of finite homogeneous analytic Besov energy. -/
def homogeneousBesovNorm (p : ℝ) (f : ℂ → ℂ) : ℝ :=
  (homogeneousBesovEnergy p f).toReal ^ (1 / p)

/-- Arc means use the lift to real coordinates of period one. -/
def arcMean (f : BoundaryL2) (a b : ℝ) : ℂ :=
  ((b - a : ℝ) : ℂ)⁻¹ * ∫ t in Set.Ioc a b, f (t : Boundary)

/-- Average absolute deviation from the interval mean. -/
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

/-- Every bounded value sequence on the nodes is realized by a bounded analytic function. -/
def Interpolating (a : ℕ → Disk) : Prop :=
  ∀ w : ℕ → ℂ, (∃ M : ℝ, ∀ n, ‖w n‖ ≤ M) →
    ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ ∀ n, innerValue g (a n).val = w n

/-- The actual normalized Hardy reproducing kernel at a disk node, as a boundary L2 function. -/
def NodeKernel (a : Disk) (f : BoundaryL2) : Prop :=
  ∀ᵐ t ∂circleMeasure,
    f t = (Real.sqrt (1 - ‖a.val‖ ^ 2) : ℂ) /
      (1 - conj a.val * fourier (T := 1) 1 t)

/-- A bounded invertible synthesis map taking sequence unit vectors to the normalized node kernels. -/
def RieszSynthesis (u : BoundaryLInf) (a : ℕ → Disk)
    (R : lp (fun _ : ℕ => ℂ) 2 ≃L[ℂ] Model u) : Prop :=
  ∀ n, NodeKernel (a n) (R (lp.single 2 n (1 : ℂ))).val

/-- The p-th powers of the absolute values form a summable family. -/
def summableValues {ι : Type*} (p : ℝ) (w : ι → ℂ) : Prop :=
  Summable (fun n => ‖w n‖ ^ p)

/-- The p-th root of the value power sum, used for a summable value family. -/
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

/-- Normalized kernels are a unitary image of an orthonormal basis plus a perturbation in the specified ideal. -/
def PerturbedKernelBasis (u : BoundaryLInf) (a : ℕ → Disk)
    (ideal : Set (Model u →L[ℂ] Model u)) : Prop :=
  ∃ e : HilbertBasis ℕ ℂ (Model u), ∃ V : Model u ≃ₗᵢ[ℂ] Model u,
    ∃ Γ : Model u →L[ℂ] Model u, Γ ∈ ideal ∧
      ∀ n, NodeKernel (a n) (V (e n) + Γ (e n)).val

/-- A bounded TTO splits into bounded analytic and coanalytic TTOs. -/
def HasBoundedAnalyticSplit (u : BoundaryLInf) (A : Model u →L[ℂ] Model u) : Prop :=
  ∃ φ ψ : Hardy, ∃ X Y : Model u →L[ℂ] Model u,
    RepresentsTTO u φ.val X ∧ RepresentsTTO u (star ψ.val) Y ∧ A = X + Y

/-- The TTO has an analytic-plus-coanalytic symbol with both analytic functions bounded. -/
def HasBoundedSymbolSplit (u : BoundaryLInf) (A : Model u →L[ℂ] Model u) : Prop :=
  ∃ φ ψ : BoundaryLInf, toL2 φ ∈ hardy ∧ toL2 ψ ∈ hardy ∧
    RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A

/-- The operator splits into an analytic and a coanalytic TTO, both in the same Schatten class. -/
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

/-- The symbol form has a bounded representing TTO in the given operator ideal. -/
def InTTOIdeal (u : BoundaryLInf) (I : Submodule ℂ (Model u →L[ℂ] Model u))
    (σ : BoundaryL2) : Prop :=
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ A ∈ I

/-- A finite positive circle measure singular with respect to normalized Haar measure. -/
def finiteSingular (μ : Measure Boundary) : Prop :=
  μ Set.univ < ∞ ∧ Measure.MutuallySingular μ circleMeasure

/-- The singular inner exponential obtained by scaling the singular measure by r. -/
def singularInnerValue (μ : Measure Boundary) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (- (r : ℂ) * ∫ t,
    (fourier (T := 1) 1 t + z) / (fourier (T := 1) 1 t - z) ∂μ)

/-- The inner function is the singular inner exponential up to unimodular phase. -/
def HasSingularRepresentation (u : BoundaryLInf) (μ : Measure Boundary) : Prop :=
  finiteSingular μ ∧ ∃ α : ℂ, ‖α‖ = 1 ∧
    ∀ z ∈ disk, innerValue u z = α * singularInnerValue μ 1 z

/-- Canonical singular measure, allowing a countable Blaschke factor in the inner function. -/
def HasCanonicalMeasure (u : BoundaryLInf) (μ : Measure Boundary) : Prop :=
  finiteSingular μ ∧ ∃ a : ℕ → Option Disk,
    Summable (fun n => (a n).elim 0 (fun w => 1 - ‖w.val‖)) ∧
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∀ z ∈ disk,
      innerValue u z = α * (∏' n, (a n).elim 1 (fun w => blaschkeFactor w z)) *
        singularInnerValue μ 1 z

/-- The L² Fourier series of the Taylor coefficients at zero; used when this series converges. -/
def analyticBoundary (f : ℂ → ℂ) : BoundaryL2 :=
  ∑' n : ℕ, (iteratedDeriv n f 0 / (n.factorial : ℂ)) • fourierBasis (T := 1) (n : ℤ)

/-- The integer Fourier mode as an essentially bounded circle function. -/
def mode (n : ℤ) : BoundaryLInf :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (fourier (T := 1) n)

/-- The model space for the singular inner power associated with the scaled measure. -/
def powerModel (μ : Measure Boundary) (r : ℝ) : Submodule ℂ BoundaryL2 :=
  hardy ⊓ (Submodule.span ℂ (Set.range (fun n : ℕ =>
    multiply (mode (n : ℤ)) (analyticBoundary (singularInnerValue μ r))))).orthogonal

instance (μ : Measure Boundary) (r : ℝ) : CompleteSpace ↥(powerModel μ r) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (Submodule.isClosed_orthogonal _)).completeSpace_coe

/-- Orthogonal projection onto the model space of the singular power. -/
def powerProjection (μ : Measure Boundary) (r : ℝ) (f : BoundaryL2) : BoundaryL2 :=
  ((powerModel μ r).orthogonalProjectionOnto f).val

/-- The analytic function factors by the specified positive singular inner power with an H2 quotient. -/
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

/-- A limit within every fixed Stolz angle of aperture M>1 at the specified boundary point. -/
def AngularLimit (f : ℂ → ℂ) (ζ : Boundary) (c : ℂ) : Prop :=
  ∀ M : ℝ, 1 < M → Tendsto f
    (𝓝[disk ∩ {z | ‖z - fourier (T := 1) 1 ζ‖ ≤ M * (1 - ‖z‖)}]
      (fourier (T := 1) 1 ζ)) (𝓝 c)

/-- At each positive canonical-measure atom, compact scalar correction forces the angular limit. -/
def AtomicBoundaryConclusion : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasCanonicalMeasure u μ →
  ∀ ζ : Boundary, 0 < μ {ζ} → ∀ φ : Hardy, ∀ c : ℂ,
    (∃ X : Model u →L[ℂ] Model u,
      RepresentsTTO u φ.val X ∧ IsCompactOperator (X - c • ContinuousLinearMap.id ℂ (Model u))) →
      AngularLimit (analyticValue φ.val) ζ c

/-- A positive single-atom singular inner function, up to a unimodular constant. -/
def SingleAtom (u : BoundaryLInf) (ζ : Boundary) : Prop :=
  ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ α : ℂ, ‖α‖ = 1 ∧ ∀ z ∈ disk,
    innerValue u z = α * Complex.exp (-(ℓ : ℂ) *
      (fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z))

/-- Finite boundary products are explicit Holder multiplications. -/
def finiteProduct {m : ℕ} (u : Fin m → BoundaryLInf) : BoundaryLInf :=
  (List.ofFn u).foldr multiplyInf (constLInf 1)

/-- The product of all factors except the indicated one. -/
def cofactor {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) : BoundaryLInf :=
  finiteProduct (fun k => if k = j then constLInf 1 else u k)

/-- Bounded analytic coefficients give an exact cofactor Bezout identity in the disk. -/
def Bezout {m : ℕ} (u a : Fin m → BoundaryLInf) : Prop :=
  (∀ j, toL2 (a j) ∈ hardy) ∧ ∀ z ∈ disk,
    ∑ j, innerValue (a j) z * innerValue (cofactor u j) z = 1

/-- Shift an analytic/coanalytic core by a bounded correction without assuming the component bounded. -/
def AnalyticRemainder (p : ℝ) (u : BoundaryLInf) (φ : BoundaryL2)
    (F : Model u →L[ℂ] Model u) : Prop :=
  ∃ X : Model u →L[ℂ] Model u, RepresentsTTO u φ X ∧ Schatten p (X - F)

/-- The coanalytic component has a bounded extension whose sum with the correction is Schatten-p. -/
def CoanalyticRemainder (p : ℝ) (u : BoundaryLInf) (ψ : BoundaryL2)
    (F : Model u →L[ℂ] Model u) : Prop :=
  ∃ Y : Model u →L[ℂ] Model u, RepresentsTTO u (star ψ) Y ∧ Schatten p (Y + F)


/-- The finite linear combination of complementary idempotents with the local scalar values. -/
def correction {m : ℕ} {u : BoundaryLInf}
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) : Model u →L[ℂ] Model u :=
  ∑ j, c j • E j

/-- Both analytic and coanalytic corrected components belong to the same Schatten class. -/
def Remainders {m : ℕ} (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2)
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ) : Prop :=
  AnalyticRemainder p u φ (correction E c) ∧ CoanalyticRemainder p u ψ (correction E c)

/-- The idempotents are represented by the actual analytic Bezout cofactor symbols. -/
def RepresentsIdempotents {m : ℕ} (u a : Fin m → BoundaryLInf)
    (E : Fin m → Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)) : Prop :=
  ∀ j, RepresentsTTO (finiteProduct u) (toL2 (multiplyInf (a j) (cofactor u j))) (E j)

/-- Pairwise annihilating bounded idempotents sum to the identity. -/
def ComplementaryIdempotents {m : ℕ} {u : BoundaryLInf}
    (E : Fin m → Model u →L[ℂ] Model u) : Prop :=
  (∑ j, E j) = ContinuousLinearMap.id ℂ (Model u) ∧
  (∀ j, E j ∘L E j = E j) ∧ ∀ i j, i ≠ j → E i ∘L E j = 0

/-- The literal image of the corresponding model space under multiplication by its cofactor. -/
def cofactorRange {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) : Submodule ℂ BoundaryL2 :=
  (multiply (cofactor u j) ∘L (model (u j)).subtypeL).toLinearMap.range

/-- Each idempotent has precisely the corresponding cofactor-multiplied model range. -/
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

/-- A finite complex coefficient family for polynomials in z and conjugate(z). -/
abbrev BiPolynomial := (ℕ × ℕ) →₀ ℂ

/-- Evaluation of the two-variable polynomial at z and conjugate(z). -/
def polynomialValue (q : BiPolynomial) (z : ℂ) : ℂ :=
  q.sum (fun jk c => c * z ^ jk.1 * conj z ^ jk.2)

/-- The nonnegative integer power of a bounded boundary function. -/
def powerInf (a : BoundaryLInf) (n : ℕ) : BoundaryLInf :=
  Nat.rec (constLInf 1) (fun _ b => multiplyInf a b) n

/-- The actual boundary L-infinity polynomial in the circle coordinate and its conjugate, included in L2. -/
def polynomialSymbol (q : BiPolynomial) : BoundaryL2 :=
  toL2 (q.sum (fun jk c => c • multiplyInf (powerInf coordinate jk.1)
    (powerInf (star coordinate) jk.2)))

/-- The measure is concentrated on a countable set of circle points. -/
def AtomicMeasure (μ : Measure Boundary) : Prop :=
  ∃ s : Set Boundary, s.Countable ∧ μ sᶜ = 0

/-- Every singleton has measure zero. -/
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


/-- Complex L2 on the product of two normalized circles. -/
abbrev BidiskL2 := Lp ℂ 2 (circleMeasure.prod circleMeasure)

/-- The separated nonnegative Fourier mode on the bidisk boundary. -/
def bidiskMode (m n : ℕ) : C(Boundary × Boundary, ℂ) :=
  ⟨fun t => fourier (T := 1) (m : ℤ) t.1 * fourier (T := 1) (n : ℤ) t.2,
    ((fourier (T := 1) (m : ℤ)).continuous.comp continuous_fst).mul
      ((fourier (T := 1) (n : ℤ)).continuous.comp continuous_snd)⟩

/-- The closed nonnegative bidisk Fourier span. -/
def bidiskHardy : Submodule ℂ BidiskL2 :=
  (Submodule.span ℂ (Set.range (fun mn : ℕ × ℕ =>
    ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode mn.1 mn.2)))).topologicalClosure

/-- Closed span of actual separated products: the concrete completed Hilbert tensor model. -/
def tensorModel (u : BoundaryLInf) : Submodule ℂ BidiskL2 :=
  (Submodule.span ℂ {G | ∃ f g : Model u,
    ∀ᵐ t ∂(circleMeasure.prod circleMeasure), G t = f.val t.1 * g.val t.2}).topologicalClosure
/-- The Hilbert space of tensors in that concrete bidisk L2 model. -/
abbrev TensorModel (u : BoundaryLInf) := ↥(tensorModel u)
instance (u : BoundaryLInf) : CompleteSpace (TensorModel u) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The model space for u squared. -/
abbrev Ambient (u : BoundaryLInf) := Model (multiplyInf u u)

/-- The analytic bidisk function obtained from the nonnegative two-variable Fourier coefficients. -/
def analyticValue₂ (G : BidiskL2) (z w : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ,
    (∫ t, G t * conj (bidiskMode mn.1 mn.2 t) ∂(circleMeasure.prod circleMeasure)) *
      z ^ mn.1 * w ^ mn.2

/-- The model reproducing kernel evaluated at two disk points. -/
def kernelValue (u : BoundaryLInf) (w z : ℂ) : ℂ :=
  (1 - conj (innerValue u w) * innerValue u z) / (1 - conj w * z)

/-- Boundary values of the model reproducing kernel at a disk point. -/
def kernelBoundary (u : BoundaryLInf) (w : ℂ) (t : Boundary) : ℂ :=
  (1 - conj (innerValue u w) * u t) / (1 - conj w * fourier (T := 1) 1 t)

/-- First-linear kernel pairing; this definition does not presuppose Hilbert--Schmidt membership. -/
def FKernel (u : BoundaryLInf) (η : BoundaryL2) (z w : ℂ) : ℂ :=
  ∫ t, η t * conj (kernelBoundary u z t * kernelBoundary u w t) ∂circleMeasure

/-- The first model component in the decomposition eta=eta1+u*eta2. -/
def eta₁ (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 :=
  ((model u).orthogonalProjectionOnto η).val

/-- The second model component, obtained by projection after multiplication by conjugate(u). -/
def eta₂ (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 :=
  ((model u).orthogonalProjectionOnto (multiply (star u) η)).val

/-- The boundary function z*eta1 in the energy numerator. -/
def energyH (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 := multiply coordinate (eta₁ u η)
/-- The boundary function z*eta2 in the energy numerator. -/
def energyG (u : BoundaryLInf) (η : BoundaryL2) : BoundaryL2 := multiply coordinate (eta₂ u η)

/-- The literal two-boundary-variable divided-difference expression, defined almost everywhere. -/
def energyQuotient (u : BoundaryLInf) (η : BoundaryL2) (t s : Boundary) : ℂ :=
  (energyH u η t - energyH u η s + u t * energyG u η s - u s * energyG u η t) /
    (fourier (T := 1) 1 t - fourier (T := 1) 1 s)

/-- Extended energy; diagonal division is zero, on a product-null set. -/
def energy (u : BoundaryLInf) (η : BoundaryL2) : ℝ≥0∞ :=
  ∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖energyQuotient u η t s‖ ^ 2) ∂circleMeasure ∂circleMeasure

/-- The polarized boundary energy pairing on the finite-energy form domain. -/
def energyPairing (u : BoundaryLInf) (η γ : BoundaryL2) : ℂ :=
  ∫ t, ∫ s, energyQuotient u η t s * conj (energyQuotient u γ t s) ∂circleMeasure ∂circleMeasure

/-- Explicit analytic graph, with no finite-energy hypothesis built into it. -/
def QGraph (u : BoundaryLInf) (η : Ambient u) (G : TensorModel u) : Prop :=
  ∀ z ∈ disk, ∀ w ∈ disk, analyticValue₂ G.val z w = FKernel u η.val z w

/-- The actual kernel pairing is represented by a bidisk Hardy L2 function. -/
def HasBidiskRepresentative (u : BoundaryLInf) (η : BoundaryL2) : Prop :=
  ∃ G : BidiskL2, G ∈ bidiskHardy ∧
    ∀ z ∈ disk, ∀ w ∈ disk, analyticValue₂ G z w = FKernel u η z w

/-- The differential expression (z*eta)′-2*u*(z*eta2)′. -/
def diagonalDifferential (u : BoundaryLInf) (η : BoundaryL2) (z : ℂ) : ℂ :=
  deriv (fun w => w * analyticValue η w) z -
    2 * innerValue u z * deriv (fun w => w * analyticValue (eta₂ u η) w) z

/-- The expanded differential expression h′+u′*g-u*g′. -/
def expandedDifferential (u : BoundaryLInf) (η : BoundaryL2) (z : ℂ) : ℂ :=
  deriv (analyticValue (energyH u η)) z +
    deriv (innerValue u) z * analyticValue (energyG u η) z -
    innerValue u z * deriv (analyticValue (energyG u η)) z

/-- The disk divided difference with its explicit removable diagonal value. -/
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

/-- A positive selfadjoint operator whose natural graph square is the given operator. -/
def IsSquareRoot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D S : H →ₗ.[ℂ] H) : Prop :=
  PositiveSelfAdjoint S ∧ ∀ x y : H,
    (x, y) ∈ D.graph ↔ ∃ v : H, (x, v) ∈ S.graph ∧ (v, y) ∈ S.graph

/-- Natural restricted Q*Q composition, not LinearPMap.comp's full-range variant. -/
def IsAdjointSquare (u : BoundaryLInf)
    (Q : Ambient u →ₗ.[ℂ] TensorModel u) (D : Ambient u →ₗ.[ℂ] Ambient u) : Prop :=
  ∀ x y : Ambient u, (x, y) ∈ D.graph ↔
    ∃ v : TensorModel u, (x, v) ∈ Q.graph ∧ (v, y) ∈ Q.adjoint.graph

/-- The exact closed dense graph, finite-energy domain, natural Q*Q, square root and energy-form identities. -/
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


/-- Both coanalytic TTO Besov criteria and all four uniform norm comparisons. -/
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

/-- Actual model kernels and their diagonal tensor kernels, with the pointwise reproducing identities. -/
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

/-- The tensor subspace orthogonal to every diagonal reproducing tensor. -/
def diagonalNull {u : BoundaryLInf} {Q : Ambient u →ₗ.[ℂ] TensorModel u}
    (d : DiagonalKernelData u Q) : Submodule ℂ (TensorModel u) :=
  (Submodule.span ℂ (Set.range d.tensorKernel)).orthogonal

/-- Orthogonal projection onto the minimum-norm representative space for diagonal restriction. -/
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

end TTO.Paper

namespace TTO.Paper.Proved

/-- Theorem 1: both Besov criteria and four uniform bounds for every p>0. -/
theorem besovClassificationTheorem (p : ℝ) (hp : 0<p) : BesovConclusion p := by sorry

/-- Theorem 2: compactness, VMOA and a continuous equivalent Hankel symbol. -/
theorem compactClassificationTheorem : CompactConclusion := by sorry

/-- Theorem 3: bounded, compact and all-p criteria at interpolating zeros. -/
theorem interpolatingClassificationTheorem : InterpolatingConclusion := by sorry

/-- Theorem 4: compact and all-p criteria for a perturbed normalized-kernel basis. -/
theorem perturbedKernelBasisClassificationTheorem : PerturbedBasisConclusion := by sorry

/-- Theorem 5: analytic-gap splitting in every finite-sum two-sided ideal. -/
theorem gapSplittingTheorem : GapConclusion := by sorry

/-- Corollary 1: canonical-symbol low-frequency form of the gap criterion. -/
theorem canonicalGapSplittingTheorem : CanonicalGapConclusion := by sorry

/-- Theorem 6: finite-atom scalar corrections, uniform bounds and compatible splitting for p>1. -/
theorem finiteAtomClassificationTheorem : FiniteAtomConclusion := by sorry

/-- Theorem 7: polynomial symbols for Blaschke, nonatomic and atomic singular inner functions. -/
theorem polynomialClassificationTheorem : PolynomialConclusion := by sorry

/-- Theorem 8: exact bidisk and boundary energy, closed graph and positive operator. -/
theorem hilbertSchmidtEnergyTheorem : HilbertSchmidtConclusion := by sorry

/-- Theorem 9: the differential realization and its precise operator domain. -/
theorem differentialRealizationTheorem : DifferentialConclusion := by sorry

/-- Remark 3: coanalytic Besov criteria and four uniform bounds for every p>0. -/
theorem coanalyticBesovTheorem (p : ℝ) (hp : 0<p) : CoanalyticBesovConclusion p := by sorry

/-- Remark 10: squared-kernel quotient; universal equality and domain refinement retain the graph-core hypothesis. -/
theorem squaredKernelQuotientTheorem : SquaredKernelConclusion := by sorry

end TTO.Paper.Proved
