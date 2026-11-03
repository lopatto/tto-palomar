/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.Definitions

/-! Mathematical reductions from explicitly stated intermediate hypotheses. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace Reduction

abbrev HankelOperator := Hardy →L[ℂ] ↥hardy.orthogonal

def RepresentsHankel (σ : BoundaryL2) (H : HankelOperator) : Prop :=
  ∀ f : Hardy, ∀ g : ↥hardy.orthogonal, IsBounded f.val → IsBounded g.val →
    inner ℂ g (H f) = coreForm σ f.val g.val

def HasSchattenHankel (p : ℝ) (σ : BoundaryL2) : Prop :=
  ∃ H : HankelOperator, RepresentsHankel σ H ∧ Schatten p H

def HasCompactHankel (σ : BoundaryL2) : Prop :=
  ∃ H : HankelOperator, RepresentsHankel σ H ∧ IsCompactOperator H

/-- Exact restriction/zero extension, before any Peller/Hartman classification. -/
def ExactHankelObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Model u,
    conjugation u φ.val ∈ hardy ∧
    (∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A →
      ∃ H : HankelOperator, RepresentsHankel (hankelSymbol u φ.val) H ∧
        (IsCompactOperator A ↔ IsCompactOperator H) ∧
        ∀ n, approximationNumber A n = approximationNumber H n) ∧
    (∀ H : HankelOperator, RepresentsHankel (hankelSymbol u φ.val) H →
      ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A ∧
        (IsCompactOperator A ↔ IsCompactOperator H) ∧
        ∀ n, approximationNumber A n = approximationNumber H n)

/-- Generic classical Hankel theorem; no inner function or TTO occurs.
Source: Peller arXiv:2402.09853v1 Thm4.1/4.2. The quantitative all-p proof is provided in PellerFoundations. -/
def PellerObligation (p : ℝ) : Prop :=
  (∀ g : BoundaryL2, g ∈ hardy →
    (HasSchattenHankel p (star (multiply coordinate g)) ↔ InBesov p g) ∧
    (HasSchattenHankel p (star (multiply coordinate g)) ↔
      homogeneousBesovEnergy p (fun z => z * analyticValue g z) < ∞)) ∧
  ∃ c C ch Ch : ℝ, 0 < c ∧ 0 < C ∧ 0 < ch ∧ 0 < Ch ∧
    ∀ g : BoundaryL2, g ∈ hardy → ∀ H : HankelOperator,
    RepresentsHankel (star (multiply coordinate g)) H → Schatten p H →
      c * besovNorm p g ≤ schattenNorm p H ∧ schattenNorm p H ≤ C * besovNorm p g ∧
      ch * homogeneousBesovNorm p (fun z => z * analyticValue g z) ≤ schattenNorm p H ∧
      schattenNorm p H ≤ Ch * homogeneousBesovNorm p (fun z => z * analyticValue g z)

/-- Classical Hardy statement, not the TTO compactness target.
Source: Peller1998 Thms5.5/5.8, with the compact bounded-symbol lift. -/
def HartmanObligation : Prop :=
  ∀ g : BoundaryL2, g ∈ hardy →
    (HasCompactHankel (star (multiply coordinate g)) ↔ InVMOA g) ∧
    (HasCompactHankel (star (multiply coordinate g)) ↔
      ∃ a : C(Boundary, ℂ), SameHankel (star (multiply coordinate g))
        (ContinuousMap.toLp 2 circleMeasure ℂ a))

theorem schatten_transfer {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {p : ℝ} {A : E →L[ℂ] F} {B : G →L[ℂ] K}
    (hc : IsCompactOperator A ↔ IsCompactOperator B)
    (hs : ∀ n, approximationNumber A n = approximationNumber B n) :
    Schatten p A ↔ Schatten p B := by
  have heq : (fun n => (approximationNumber A n : ℝ) ^ p) =
      (fun n => (approximationNumber B n : ℝ) ^ p) := funext fun n => by rw [hs n]
  simp only [Schatten, hc, heq]

theorem schattenNorm_transfer {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {p : ℝ} {A : E →L[ℂ] F} {B : G →L[ℂ] K}
    (hs : ∀ n, approximationNumber A n = approximationNumber B n) :
    schattenNorm p A = schattenNorm p B := by
  unfold schattenNorm
  congr 1
  apply tsum_congr
  intro n
  rw [hs n]

theorem hankel_schatten_iff (h : ExactHankelObligation) (p : ℝ)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (φ : Model u) :
    HasSchattenTTO p u φ.val ↔ HasSchattenHankel p (hankelSymbol u φ.val) := by
  rcases h u hu hn φ with ⟨_, hf, hb⟩
  constructor
  · rintro ⟨A, ha, hp⟩
    obtain ⟨H, hh, hc, hs⟩ := hf A ha
    exact ⟨H, hh, (schatten_transfer hc hs).mp hp⟩
  · rintro ⟨H, hh, hp⟩
    obtain ⟨A, ha, hc, hs⟩ := hb H hh
    exact ⟨A, ha, (schatten_transfer hc hs).mpr hp⟩

/-- Besov classification from the exact Hankel correspondence and the classical Hankel criterion. -/
theorem besovClassification (h : ExactHankelObligation) (p : ℝ) (_hp : 0 < p)
    (hP : PellerObligation p) : BesovConclusion p := by
  constructor
  · intro u hu hn φ
    have hg := (h u hu hn φ).1
    have hh := hankel_schatten_iff h p u hu hn φ
    exact ⟨hh.trans (hP.1 _ hg).1, hh.trans (hP.1 _ hg).2⟩
  · rcases hP.2 with ⟨c, C, ch, Ch, hc, hC, hch, hCh, hb⟩
    refine ⟨c, C, ch, Ch, hc, hC, hch, hCh, ?_⟩
    intro u hu hn φ A ha hp
    obtain ⟨H, hh, hcomp, hs⟩ := (h u hu hn φ).2.1 A ha
    have hb' := hb _ (h u hu hn φ).1 H hh ((schatten_transfer hcomp hs).mp hp)
    have he := schattenNorm_transfer (p := p) hs
    simpa only [he] using hb'

theorem compactClassification (h : ExactHankelObligation) (hH : HartmanObligation) :
    CompactConclusion := by
  intro u hu hn φ
  have he : HasCompactTTO u φ.val ↔ HasCompactHankel (hankelSymbol u φ.val) := by
    constructor
    · rintro ⟨A, ha, hc⟩
      obtain ⟨H, hh, he, _⟩ := (h u hu hn φ).2.1 A ha
      exact ⟨H, hh, he.mp hc⟩
    · rintro ⟨H, hh, hc⟩
      obtain ⟨A, ha, he, _⟩ := (h u hu hn φ).2.2 H hh
      exact ⟨A, ha, he.mpr hc⟩
  exact ⟨he.trans (hH _ (h u hu hn φ).1).1,
    he.trans (hH _ (h u hu hn φ).1).2⟩

/-- Explicit finite compression, with no ideal-membership conclusion in its specification. -/
def lowerTriangle {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {N : ℕ} (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, ∑ j, if j < i then Q i ∘L A ∘L Q j else 0

/-- Manuscript's finite matrix reconstruction on the bounded core. -/
def FiniteCompressionObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ →
  ∀ φ ψ : Hardy, ∀ r : ℝ, 0 < r → r < 1 → HasAnalyticGap μ r φ.val →
  ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol φ.val ψ.val) A →
    ∃ N : ℕ, ∃ Q : Fin N → Model u →L[ℂ] Model u,
      RepresentsTTO u φ.val (lowerTriangle Q A) ∧
      RepresentsTTO u (star ψ.val) (A - lowerTriangle Q A)

theorem lowerTriangle_mem (u : BoundaryLInf)
    (I : Submodule ℂ (Model u →L[ℂ] Model u)) (hi : TwoSided u I)
    {N : ℕ} (Q : Fin N → Model u →L[ℂ] Model u)
    (A : Model u →L[ℂ] Model u) (ha : A ∈ I) : lowerTriangle Q A ∈ I := by
  classical
  apply I.sum_mem
  intro i _
  apply I.sum_mem
  intro j _
  split_ifs
  · exact hi A ha (Q i) (Q j)
  · exact I.zero_mem

theorem gapSplitting (h : FiniteCompressionObligation) : GapConclusion := by
  intro u hu hn μ hμ I hi φ ψ r hr hr1 hg
  rintro ⟨A, ha, hai⟩
  obtain ⟨N, Q, hx, hy⟩ := h u hu hn μ hμ φ ψ r hr hr1 hg A ha
  have hb := lowerTriangle_mem u I hi Q A hai
  exact ⟨⟨lowerTriangle Q A, hx, hb⟩, ⟨A - lowerTriangle Q A, hy, by exact Submodule.sub_mem (R := ℂ) (M := Model u →L[ℂ] Model u) I hai hb⟩⟩


abbrev SequenceL2 := lp (fun _ : ℕ => ℂ) 2
abbrev SequenceOperator := SequenceL2 →L[ℂ] SequenceL2

def Diagonal (w : ℕ → ℂ) (D : SequenceOperator) : Prop :=
  ∀ n, D (lp.single 2 n (1 : ℂ)) = w n • lp.single 2 n (1 : ℂ)

def similarity {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) : H →L[ℂ] H :=
  S.toContinuousLinearMap ∘L D ∘L S.symm.toContinuousLinearMap

/-- Generic sequence-space facts, not analytic-symbol statements. -/
structure DiagonalLaws : Prop where
  bounded : ∀ w : ℕ → ℂ, (∃ D : SequenceOperator, Diagonal w D) ↔
    ∃ M : ℝ, ∀ n, ‖w n‖ ≤ M
  compact : ∀ w : ℕ → ℂ, ∀ D : SequenceOperator, Diagonal w D →
    (IsCompactOperator D ↔ Tendsto w atTop (𝓝 0))
  schatten : ∀ w : ℕ → ℂ, ∀ D : SequenceOperator, Diagonal w D → ∀ p : ℝ, 0 < p →
    (Schatten p D ↔ summableValues p w)
  norm : ∀ w : ℕ → ℂ, ∀ D : SequenceOperator, Diagonal w D → ∀ p : ℝ,
    Schatten p D → schattenNorm p D = valueNorm p w

/-- Generic ideal algebra and similarity estimates, containing no symbols or nodes. -/
structure IdealLaws : Prop where
  schatten_add : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (p : ℝ) (A B : H →L[ℂ] H), Schatten p A → Schatten p B → Schatten p (A + B)
  schatten_neg : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (p : ℝ) (A : H →L[ℂ] H), Schatten p A → Schatten p (-A)
  compact_add : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A B : H →L[ℂ] H), IsCompactOperator A → IsCompactOperator B → IsCompactOperator (A + B)
  compact_neg : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H), IsCompactOperator A → IsCompactOperator (-A)
  compact_similarity : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator),
    IsCompactOperator (similarity S D) ↔ IsCompactOperator D
  schatten_similarity : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) (p : ℝ),
    Schatten p (similarity S D) ↔ Schatten p D
  similarity_norm : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) (p : ℝ), Schatten p D →
      (‖S.toContinuousLinearMap‖ * ‖S.symm.toContinuousLinearMap‖)⁻¹ * schattenNorm p D
        ≤ schattenNorm p (similarity S D) ∧
      schattenNorm p (similarity S D) ≤
        (‖S.toContinuousLinearMap‖ * ‖S.symm.toContinuousLinearMap‖) * schattenNorm p D

/-- Functional interpolation implies the actual normalized-kernel synthesis. -/
def RieszObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
  Function.Injective a → HasBlaschkeZeros u a → Interpolating a →
    ∃ R : SequenceL2 ≃L[ℂ] Model u, RieszSynthesis u a R

/-- The analytic eigenbasis is the DUAL kernel basis, not the kernels. -/
def DualDiagonalObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
  Function.Injective a → HasBlaschkeZeros u a →
  ∀ R : SequenceL2 ≃L[ℂ] Model u, RieszSynthesis u a R →
    ∃ S : SequenceL2 ≃L[ℂ] Model u,
      S.toContinuousLinearMap = R.symm.toContinuousLinearMap.adjoint ∧
      ‖S.toContinuousLinearMap‖ = ‖R.symm.toContinuousLinearMap‖ ∧
      ‖S.symm.toContinuousLinearMap‖ = ‖R.toContinuousLinearMap‖ ∧
      ∀ φ : Hardy,
        (∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A →
          ∃ D : SequenceOperator, Diagonal (fun n => analyticValue φ.val (a n).val) D ∧
            A = similarity S D) ∧
        (∀ D : SequenceOperator, Diagonal (fun n => analyticValue φ.val (a n).val) D →
          RepresentsTTO u φ.val (similarity S D))

theorem interpolatingClassification (hR : RieszObligation) (hM : DualDiagonalObligation)
    (hD : DiagonalLaws) (hI : IdealLaws) : InterpolatingConclusion := by
  intro u hu hn a ha hb hi
  obtain ⟨R, hr⟩ := hR u hu hn a ha hb hi
  refine ⟨⟨R, hr⟩, ?_⟩
  intro φ
  obtain ⟨S, _, hsn, hsin, hm⟩ := hM u hu hn a ha hb R hr
  have hbnd : HasBoundedTTO u φ.val ↔
      ∃ D : SequenceOperator, Diagonal (fun n => analyticValue φ.val (a n).val) D := by
    constructor
    · rintro ⟨A, he⟩
      obtain ⟨D, hd, _⟩ := (hm φ).1 A he
      exact ⟨D, hd⟩
    · rintro ⟨D, hd⟩
      exact ⟨similarity S D, (hm φ).2 D hd⟩
  refine ⟨hbnd.trans (hD.bounded _), ?_, ?_⟩
  · constructor
    · rintro ⟨A, he, hc⟩
      obtain ⟨D, hd, rfl⟩ := (hm φ).1 A he
      exact (hD.compact _ D hd).mp ((hI.compact_similarity S D).mp hc)
    · intro hz
      obtain ⟨D, hd⟩ := (hD.bounded _).mpr (by
        obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hz).exists_norm_le
        exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩)
      exact ⟨similarity S D, (hm φ).2 D hd,
        (hI.compact_similarity S D).mpr ((hD.compact _ D hd).mpr hz)⟩
  · intro p hp
    constructor
    · constructor
      · rintro ⟨A, he, hs⟩
        obtain ⟨D, hd, rfl⟩ := (hm φ).1 A he
        exact (hD.schatten _ D hd p hp).mp ((hI.schatten_similarity S D p).mp hs)
      · intro hw
        have hbounded : ∃ M : ℝ, ∀ n, ‖analyticValue φ.val (a n).val‖ ≤ M := by
          exact ⟨(∑' n, ‖analyticValue φ.val (a n).val‖ ^ p) ^ (1 / p) + 1, fun n => by
            have hterm := Summable.le_tsum hw n (fun n _ => Real.rpow_nonneg (norm_nonneg _) _)
            have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hterm
              (le_of_lt (one_div_pos.mpr hp))
            rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel (ne_of_gt hp), Real.rpow_one] at hroot
            exact le_trans hroot (le_add_of_nonneg_right zero_le_one)⟩
        obtain ⟨D, hd⟩ := (hD.bounded _).mpr hbounded
        exact ⟨similarity S D, (hm φ).2 D hd,
          (hI.schatten_similarity S D p).mpr ((hD.schatten _ D hd p hp).mpr hw)⟩
    · intro R' hr' A he hs
      obtain ⟨S', _, hn', hin', hm'⟩ := hM u hu hn a ha hb R' hr'
      obtain ⟨D, hd, hA⟩ := (hm' φ).1 A he
      have hsd := (hI.schatten_similarity S' D p).mp (hA ▸ hs)
      have hnorm := hI.similarity_norm S' D p hsd
      have hdn := hD.norm _ D hd p hsd
      simpa only [← hA, hn', hin', hdn, mul_comm] using hnorm

/-- Diagonal normal form of the computed near-orthonormal kernel matrix. -/
def KernelRemainderObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ a : ℕ → Disk, Function.Injective a → HasBlaschkeZeros u a →
  ∀ φ ψ : BoundaryLInf, toL2 φ ∈ hardy → toL2 ψ ∈ hardy →
  ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A →
    ((PerturbedKernelBasis u a {Γ | IsCompactOperator Γ}) →
      ∃ S : SequenceL2 ≃L[ℂ] Model u, ∃ D : SequenceOperator,
        Diagonal (fun n => innerValue φ (a n).val + conj (innerValue ψ (a n).val)) D ∧
        ∃ K : Model u →L[ℂ] Model u, IsCompactOperator K ∧ A = similarity S D + K) ∧
    ∀ p : ℝ, 0 < p → PerturbedKernelBasis u a {Γ | Schatten p Γ} →
      ∃ S : SequenceL2 ≃L[ℂ] Model u, ∃ D : SequenceOperator,
        Diagonal (fun n => innerValue φ (a n).val + conj (innerValue ψ (a n).val)) D ∧
        ∃ K : Model u →L[ℂ] Model u, Schatten p K ∧ A = similarity S D + K

/-- Analytic bounded-symbol lift for bounded TTOs with Hardy symbols. -/
def AnalyticLiftObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ : Hardy,
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A →
      ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ RepresentsTTO u (toL2 g) A

/-- Generic bounded multiplication and additivity/uniqueness of core representations. -/
structure CoreLaws : Prop where
  zero : ∀ u : BoundaryLInf, RepresentsTTO u 0 (0 : Model u →L[ℂ] Model u)
  bounded : ∀ u : BoundaryLInf, ∀ g : BoundaryLInf,
    ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (toL2 g) A
  add : ∀ u : BoundaryLInf, ∀ σ τ : BoundaryL2, ∀ A B : Model u →L[ℂ] Model u,
    RepresentsTTO u σ A → RepresentsTTO u τ B → RepresentsTTO u (σ + τ) (A + B)
  sub : ∀ u : BoundaryLInf, ∀ σ τ : BoundaryL2, ∀ A B : Model u →L[ℂ] Model u,
    RepresentsTTO u σ A → RepresentsTTO u τ B → RepresentsTTO u (σ - τ) (A - B)
  unique : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ σ : BoundaryL2,
    ∀ A B : Model u →L[ℂ] Model u, RepresentsTTO u σ A → RepresentsTTO u σ B → A = B
  adjoint : ∀ u : BoundaryLInf, ∀ σ : BoundaryL2, ∀ A : Model u →L[ℂ] Model u,
    RepresentsTTO u σ A → RepresentsTTO u (star σ) A.adjoint
  star_toL2 : ∀ g : BoundaryLInf, toL2 (star g) = star (toL2 g)

theorem boundedSplit_iff (h : CoreLaws) (hl : AnalyticLiftObligation)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (A : Model u →L[ℂ] Model u) : HasBoundedAnalyticSplit u A ↔ HasBoundedSymbolSplit u A := by
  constructor
  · rintro ⟨φ, ψ, X, Y, hx, hy, rfl⟩
    obtain ⟨g, hg, hX⟩ := hl u hu hn φ X hx
    have hψ : RepresentsTTO u ψ.val Y.adjoint := by simpa using h.adjoint u _ Y hy
    obtain ⟨k, hk, hY⟩ := hl u hu hn ψ Y.adjoint hψ
    have hY' : RepresentsTTO u (star (toL2 k)) Y := by
      simpa using h.adjoint u _ Y.adjoint hY
    exact ⟨g, k, hg, hk, h.add u _ _ _ _ hX hY'⟩
  · rintro ⟨g, k, hg, hk, he⟩
    obtain ⟨X, hx⟩ := h.bounded u g
    obtain ⟨Y, hy⟩ := h.bounded u (star k)
    have hy' : RepresentsTTO u (star (toL2 k)) Y := (h.star_toL2 k) ▸ hy
    exact ⟨⟨toL2 g, hg⟩, ⟨toL2 k, hk⟩, X, Y, hx, hy',
      h.unique u hu hn _ A (X + Y) he (h.add u _ _ _ _ hx hy')⟩

theorem perturbedKernelBasisClassification (hC : CoreLaws) (hl : AnalyticLiftObligation)
    (hK : KernelRemainderObligation) (hD : DiagonalLaws) (hI : IdealLaws) : PerturbedBasisConclusion := by
  intro u hu hn a ha hb
  refine ⟨boundedSplit_iff hC hl u hu hn, ?_⟩
  intro φ ψ hφ hψ A he
  have hk := hK u hu hn a ha hb φ ψ hφ hψ A he
  constructor
  · intro hbase
    obtain ⟨S, D, hd, K, hkc, rfl⟩ := hk.1 hbase
    have hp : IsCompactOperator (similarity S D + K) ↔ IsCompactOperator (similarity S D) := by
      constructor
      · intro hsum
        have hz := hI.compact_add _ _ hsum (hI.compact_neg _ hkc)
        simpa using hz
      · intro h0
        exact hI.compact_add _ _ h0 hkc
    exact hp.trans ((hI.compact_similarity S D).trans (hD.compact _ D hd))
  · intro p hp hbase
    obtain ⟨S, D, hd, K, hks, rfl⟩ := hk.2 p hp hbase
    have hpert : Schatten p (similarity S D + K) ↔ Schatten p (similarity S D) := by
      constructor
      · intro hsum
        have hz := hI.schatten_add p _ _ hsum (hI.schatten_neg p _ hks)
        simpa using hz
      · intro h0
        exact hI.schatten_add p _ _ h0 hks
    exact hpert.trans ((hI.schatten_similarity S D p).trans (hD.schatten _ D hd p hp))


/-- Generic closure properties of the three advertised ideals. -/
structure IdealCarriers : Prop where
  schatten : ∀ u : BoundaryLInf, ∀ p : ℝ, 0 < p →
    ∃ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I ∧
      ∀ A, A ∈ I ↔ Schatten p A
  compact : ∀ u : BoundaryLInf,
    ∃ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I ∧
      ∀ A, A ∈ I ↔ IsCompactOperator A
  finiteRank : ∀ u : BoundaryLInf,
    ∃ I : Submodule ℂ (Model u →L[ℂ] Model u), TwoSided u I ∧
      ∀ A, A ∈ I ↔ FiniteRank A

theorem gapSpecializations (h : FiniteCompressionObligation) (hI : IdealCarriers) :
    GapSpecializationsConclusion := by
  intro u hu hn μ hμ φ ψ r hr hr1 hg
  constructor
  · intro p hp ha
    obtain ⟨I, hi, hc⟩ := hI.schatten u p hp
    obtain ⟨A, he, hs⟩ := ha
    obtain ⟨⟨X, hx, hxi⟩, ⟨Y, hy, hyi⟩⟩ :=
      gapSplitting h u hu hn μ hμ I hi φ ψ r hr hr1 hg ⟨A, he, (hc A).mpr hs⟩
    exact ⟨⟨X, hx, (hc X).mp hxi⟩, ⟨Y, hy, (hc Y).mp hyi⟩⟩
  constructor
  · rintro ⟨A, he, hs⟩
    obtain ⟨I, hi, hc⟩ := hI.compact u
    obtain ⟨⟨X, hx, hxi⟩, ⟨Y, hy, hyi⟩⟩ :=
      gapSplitting h u hu hn μ hμ I hi φ ψ r hr hr1 hg ⟨A, he, (hc A).mpr hs⟩
    exact ⟨⟨X, hx, (hc X).mp hxi⟩, ⟨Y, hy, (hc Y).mp hyi⟩⟩
  · rintro ⟨A, he, hs⟩
    obtain ⟨I, hi, hc⟩ := hI.finiteRank u
    obtain ⟨⟨X, hx, hxi⟩, ⟨Y, hy, hyi⟩⟩ :=
      gapSplitting h u hu hn μ hμ I hi φ ψ r hr hr1 hg ⟨A, he, (hc A).mpr hs⟩
    exact ⟨⟨X, hx, (hc X).mp hxi⟩, ⟨Y, hy, (hc Y).mp hyi⟩⟩

/-- Canonical orthogonality and the high-frequency factor, no ideal conclusion. -/
def GapProjectionObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ →
  ∀ φ ψ : Model u, analyticValue ψ.val 0 = 0 →
  ∀ r : ℝ, 0 < r → r < 1 →
    powerProjection μ r (splitSymbol φ.val ψ.val) = powerProjection μ r φ.val ∧
    powerProjection μ r φ.val ∈ hardy ∧
    φ.val - powerProjection μ r φ.val ∈ hardy ∧
    HasAnalyticGap μ r (φ.val - powerProjection μ r φ.val)

theorem canonicalGapSplitting (h : FiniteCompressionObligation) (hC : CoreLaws)
    (hP : GapProjectionObligation) : CanonicalGapConclusion := by
  intro u hu hn μ hμ I hi φ ψ hψ r hr hr1
  obtain ⟨heq, hl, hh, hg⟩ := hP u hu hn μ hμ φ ψ hψ r hr hr1
  refine ⟨by rw [heq], ?_⟩
  rintro ⟨A, ha, hai⟩ ⟨L, hL, hLi⟩
  let φ' : Hardy := ⟨φ.val - powerProjection μ r φ.val, hh⟩
  let ψ' : Hardy := ⟨ψ.val, ψ.property.1⟩
  have hhigh : RepresentsTTO u (splitSymbol φ'.val ψ'.val) (A - L) := by
    simpa only [φ', ψ', splitSymbol, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hC.sub u _ _ A L ha hL
  have hAI : A - L ∈ I :=
    Submodule.sub_mem (R := ℂ) (M := Model u →L[ℂ] Model u) I hai hLi
  obtain ⟨⟨X, hx, hxi⟩, hy⟩ :=
    gapSplitting h u hu hn μ hμ I hi φ' ψ' r hr hr1 hg ⟨A - L, hhigh, hAI⟩
  have hsum : RepresentsTTO u φ.val (X + L) := by
    simpa only [φ', splitSymbol, sub_add_cancel] using hC.add u _ _ X L hx hL
  exact ⟨⟨X + L, hsum, I.add_mem hxi hLi⟩, hy⟩


structure UnitaryIdealLaws : Prop where
  compact : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (D : H →L[ℂ] H),
    IsCompactOperator (unitaryConjugate U D) ↔ IsCompactOperator D
  schatten : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (D : H →L[ℂ] H) (p : ℝ),
    Schatten p (unitaryConjugate U D) ↔ Schatten p D
  inclusion : ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (p : ℝ), 2 ≤ p → Schatten 2 A → Schatten p A

def IndexedDiagonal {ι : Type} (w : ι → ℂ)
    (D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) : Prop := by
  classical
  exact ∀ i, D (lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)) =
    w i • lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)

def RepresentsMultiplier {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ a : Lp ℂ 2 μ, ∀ᵐ x ∂μ, (M a) x = f x * a x

abbrev fiberMeasure (μ : Measure Boundary) : Measure (Boundary × ℝ) :=
  μ.prod (volume.restrict (Set.Ioo (0 : ℝ) 1))

/-- The actual polynomial operators are HS perturbations of explicit
pure multiplication/diagonal models. This states no membership classification. -/
structure PolynomialModels : Prop where
  blaschke : ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ ι : Type, ∀ a : ι → Disk, Countable ι → HasBlaschkeZeros u a → ∀ q : BiPolynomial,
      ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A ∧
      ∃ U : lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] Model u,
      ∃ D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
        IndexedDiagonal (fun i => polynomialValue q (a i).val) D ∧
      ∃ K : Model u →L[ℂ] Model u, Schatten 2 K ∧ A = unitaryConjugate U D + K
  nonatomic : ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ μ : Measure Boundary, HasSingularRepresentation u μ → NonatomicMeasure μ → ∀ q : BiPolynomial,
      ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Model u, ∃ M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
        RepresentsMultiplier μ (fun t => polynomialValue q (fourier (T := 1) 1 t)) M ∧
      ∃ K : Model u →L[ℂ] Model u, Schatten 2 K ∧ A = unitaryConjugate U M + K
  atomic : ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ μ : Measure Boundary, HasSingularRepresentation u μ → AtomicMeasure μ → ∀ q : BiPolynomial,
      ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A ∧
      ∃ U : Lp ℂ 2 (fiberMeasure μ) ≃ₗᵢ[ℂ] Model u,
      ∃ M : Lp ℂ 2 (fiberMeasure μ) →L[ℂ] Lp ℂ 2 (fiberMeasure μ),
        RepresentsMultiplier (fiberMeasure μ) (fun t => polynomialValue q (fourier (T := 1) 1 t.1)) M ∧
      ∃ K : Model u →L[ℂ] Model u, Schatten 2 K ∧ A = unitaryConjugate U M + K

/-- Generic diagonal and multiplication compactness/summability laws. -/
structure MultiplicationLaws : Prop where
  diagonal_compact : ∀ ι : Type, ∀ w : ι → ℂ,
    ∀ D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
    IndexedDiagonal w D → (IsCompactOperator D ↔ Tendsto w cofinite (𝓝 0))
  diagonal_schatten : ∀ ι : Type, ∀ w : ι → ℂ,
    ∀ D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
    IndexedDiagonal w D → ∀ p : ℝ, 0 < p → (Schatten p D ↔ summableValues p w)
  nonatomic_compact : ∀ μ : Measure Boundary, μ Set.univ < ∞ → NonatomicMeasure μ →
    ∀ f : Boundary → ℂ, ∀ M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      RepresentsMultiplier μ f M → (IsCompactOperator M ↔ ∀ᵐ t ∂μ, f t = 0)
  fiber_compact : ∀ μ : Measure Boundary, μ Set.univ < ∞ → ∀ f : Boundary → ℂ,
    ∀ M : Lp ℂ 2 (fiberMeasure μ) →L[ℂ] Lp ℂ 2 (fiberMeasure μ),
      RepresentsMultiplier (fiberMeasure μ) (fun t => f t.1) M →
      (IsCompactOperator M ↔ ∀ᵐ t ∂μ, f t = 0)
  multiplier_zero : ∀ μ : Measure Boundary, ∀ f : Boundary → ℂ,
    ∀ M : Lp ℂ 2 (fiberMeasure μ) →L[ℂ] Lp ℂ 2 (fiberMeasure μ),
      RepresentsMultiplier (fiberMeasure μ) (fun t => f t.1) M →
      (∀ᵐ t ∂μ, f t = 0) → M = 0
  atomic_ae : ∀ μ : Measure Boundary, AtomicMeasure μ → ∀ f : Boundary → ℂ,
    (∀ᵐ t ∂μ, f t = 0) ↔ ∀ t, 0 < μ {t} → f t = 0

/-- A nonzero nonatomic measure has infinite support, determining a trigonometric polynomial. -/
def TrigonometricUniqueness : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ μ : Measure Boundary, HasSingularRepresentation u μ → NonatomicMeasure μ →
  ∀ q : BiPolynomial,
    (∀ᵐ t ∂μ, polynomialValue q (fourier (T := 1) 1 t) = 0) ↔
      ∀ t : Boundary, polynomialValue q (fourier (T := 1) 1 t) = 0

def PolynomialSymbolMeaning : Prop :=
  ∀ q : BiPolynomial, ∀ᵐ t ∂circleMeasure,
    polynomialSymbol q t = polynomialValue q (fourier (T := 1) 1 t)

/-- The explicit symbol 2-z-conj z has a strictly positive matrix coefficient.
No compactness, Schatten or nonzero-operator conclusion is included. -/
def AtomicQuadraticWitness : Prop :=
  ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ SingleAtom u 0 ∧
  ∃ μ : Measure Boundary, HasSingularRepresentation u μ ∧ AtomicMeasure μ ∧
  ∃ q : BiPolynomial, (∀ z : ℂ, polynomialValue q z = 2 - z - conj z) ∧
    (∀ t : Boundary, 0 < μ {t} → polynomialValue q (fourier (T := 1) 1 t) = 0) ∧
  ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A ∧
  ∃ f : Model u, 0 < (inner ℂ f (A f)).re

theorem compact_perturb_iff (hI : IdealLaws) {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A K : H →L[ℂ] H) (hk : IsCompactOperator K) :
    IsCompactOperator (A + K) ↔ IsCompactOperator A := by
  constructor
  · intro ha
    simpa using hI.compact_add _ _ ha (hI.compact_neg _ hk)
  · intro ha
    exact hI.compact_add _ _ ha hk

theorem schatten_perturb_iff (hI : IdealLaws) {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (p : ℝ) (A K : H →L[ℂ] H) (hk : Schatten p K) :
    Schatten p (A + K) ↔ Schatten p A := by
  constructor
  · intro ha
    simpa using hI.schatten_add p _ _ ha (hI.schatten_neg p _ hk)
  · intro ha
    exact hI.schatten_add p _ _ ha hk

theorem polynomialClassification (hC : CoreLaws) (hI : IdealLaws) (hU : UnitaryIdealLaws)
    (hP : PolynomialModels) (hM : MultiplicationLaws) (hT : TrigonometricUniqueness)
    (hS : PolynomialSymbolMeaning) (hQ : AtomicQuadraticWitness) : PolynomialConclusion := by
  have atomicCase : ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
      ∀ μ : Measure Boundary, HasSingularRepresentation u μ → AtomicMeasure μ → ∀ q : BiPolynomial,
      (HasCompactTTO u (polynomialSymbol q) ↔
        ∀ t : Boundary, 0 < μ {t} → polynomialValue q (fourier (T := 1) 1 t) = 0) ∧
      (HasCompactTTO u (polynomialSymbol q) → HasSchattenTTO 2 u (polynomialSymbol q)) := by
    intro u hu hn μ hμ ha q
    obtain ⟨A, he, U, M, hm, K, hk, hA⟩ := hP.atomic u hu hn μ hμ ha q
    have hcomp : HasCompactTTO u (polynomialSymbol q) ↔ IsCompactOperator A := by
      constructor
      · rintro ⟨B, hb, hc⟩
        exact (hC.unique u hu hn _ B A hb he) ▸ hc
      · exact fun hc => ⟨A, he, hc⟩
    have hmult := hM.fiber_compact μ hμ.1.1 (fun t => polynomialValue q (fourier (T := 1) 1 t)) M hm
    have hc : IsCompactOperator A ↔ ∀ᵐ t ∂μ, polynomialValue q (fourier (T := 1) 1 t) = 0 := by
      rw [hA]
      exact (compact_perturb_iff hI _ _ hk.2.1).trans ((hU.compact U M).trans hmult)
    refine ⟨hcomp.trans (hc.trans (hM.atomic_ae μ ha _)), ?_⟩
    intro hfinite
    have hz := hc.mp (hcomp.mp hfinite)
    have hzero := hM.multiplier_zero μ (fun t => polynomialValue q (fourier (T := 1) 1 t)) M hm hz
    have hAK : A = K := by simp only [hA, hzero, unitaryConjugate, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, zero_add]
    exact ⟨A, he, hAK.symm ▸ hk⟩
  refine ⟨?_, ?_, atomicCase, ?_⟩
  · intro u hu hn ι a hι ha q
    obtain ⟨A, he, U, D, hd, K, hk, hA⟩ := hP.blaschke u hu hn ι a hι ha q
    have hc : HasCompactTTO u (polynomialSymbol q) ↔ IsCompactOperator A := by
      constructor
      · rintro ⟨B, hb, hc⟩
        exact (hC.unique u hu hn _ B A hb he) ▸ hc
      · exact fun hc => ⟨A, he, hc⟩
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
        · rintro ⟨B, hb, hs⟩
          exact (hC.unique u hu hn _ B A hb he) ▸ hs
        · exact fun hs => ⟨A, he, hs⟩
      apply hs.trans
      rw [hA]
      exact (schatten_perturb_iff hI p _ _ hkp).trans
        ((hU.schatten U D p).trans (hM.diagonal_schatten ι _ D hd p hpos))
  · intro u hu hn μ hμ hnμ q
    obtain ⟨A, he, U, M, hm, K, hk, hA⟩ := hP.nonatomic u hu hn μ hμ hnμ q
    have hc : HasCompactTTO u (polynomialSymbol q) ↔ IsCompactOperator A := by
      constructor
      · rintro ⟨B, hb, hc⟩
        exact (hC.unique u hu hn _ B A hb he) ▸ hc
      · exact fun hc => ⟨A, he, hc⟩
    constructor
    · apply hc.trans
      rw [hA]
      exact (compact_perturb_iff hI _ _ hk.2.1).trans
        ((hU.compact U M).trans ((hM.nonatomic_compact μ hμ.1.1 hnμ _ M hm).trans
          (hT u hu hn μ hμ hnμ q)))
    · intro hz B hb
      have hzero : polynomialSymbol q = 0 := by
        apply Lp.ext
        filter_upwards [hS q, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := circleMeasure)] with t ht h0
        exact ht.trans ((hz t).trans h0.symm)
      rw [hzero] at hb
      exact hC.unique u hu hn 0 B 0 hb (hC.zero u)
  · obtain ⟨u, hu, hn, hs, μ, hμ, ha, q, hq, hz, A, he, f, hf⟩ := hQ
    have hc := (atomicCase u hu hn μ hμ ha q).1.mpr hz
    obtain ⟨B, hb, hsp⟩ := (atomicCase u hu hn μ hμ ha q).2 hc
    have hAB := hC.unique u hu hn _ A B he hb
    refine ⟨u, hu, hn, hs, q, hq, A, he, hAB.symm ▸ hsp, ?_⟩
    intro hzero
    simp only [hzero, zero_apply, inner_zero_right, Complex.zero_re, lt_self_iff_false] at hf


/-- General finite-inner gluing, without any atomic classification. -/
def CoronaStructureObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf,
    (∀ j, IsInner (u j) ∧ Nonconstant (u j)) → Corona u →
    IsInner (finiteProduct u) ∧ Nonconstant (finiteProduct u) ∧
    (∃ a : Fin m → BoundaryLInf, Bezout u a) ∧
    (∀ a, Bezout u a → ∃ E, RepresentsIdempotents u a E ∧
      ComplementaryIdempotents E ∧ IdempotentRanges u E ∧
      ∀ a' E', Bezout u a' → RepresentsIdempotents u a' E' → E' = E)

/-- The cofactor lower bound follows from the explicit separated singular factors. -/
def DistinctAtomCoronaObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf, ∀ ζ : Fin m → Boundary,
    Function.Injective ζ → (∀ j, IsInner (u j) ∧ SingleAtom (u j) (ζ j)) → Corona u

/-- Compressing a global core to a divisor preserves its symbol and contracts S_p. -/
def AtomCompressionObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf, ∀ ζ : Fin m → Boundary,
  Function.Injective ζ → (∀ j, IsInner (u j) ∧ Nonconstant (u j) ∧ SingleAtom (u j) (ζ j)) →
  ∀ φ ψ : Hardy, ∀ p : ℝ, 0 < p →
  ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
    RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
    ∀ j, ∃ Aⱼ : Model (u j) →L[ℂ] Model (u j),
      RepresentsTTO (u j) (splitSymbol φ.val ψ.val) Aⱼ ∧
      Schatten p Aⱼ ∧ schattenNorm p Aⱼ ≤ schattenNorm p A

/-- Uniform one-atom scalar decomposition used by T6, including cut estimates and angular limits.
This intermediate claim is proved by the atomic regularization modules. -/
def OneAtomObligation : Prop :=
  ∀ p : ℝ, 1 < p → ∃ τ : ℝ, 0 < τ ∧
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ζ : Boundary, SingleAtom u ζ →
  ∀ φ ψ : Hardy, ∀ A : Model u →L[ℂ] Model u,
    RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten p A →
    ∃ c : ℂ, ∃ X Y : Model u →L[ℂ] Model u,
      RepresentsTTO u φ.val X ∧ RepresentsTTO u (star ψ.val) Y ∧
      Schatten p (X - c • ContinuousLinearMap.id ℂ _) ∧
      Schatten p (Y + c • ContinuousLinearMap.id ℂ _) ∧
      schattenNorm p (X - c • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
      schattenNorm p (Y + c • ContinuousLinearMap.id ℂ _) ≤ (1 + τ) * schattenNorm p A ∧
      AngularLimit (analyticValue φ.val) ζ c ∧
      AngularLimit (analyticValue ψ.val) ζ (-conj c)

/-- General-inner diagonal similarity of analytic remainders, before local scalar existence. -/
def VectorGluingObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf,
  (∀ j, IsInner (u j) ∧ Nonconstant (u j)) → Corona u →
  ∀ p : ℝ, 0 < p → ∃ K : ℝ, 0 < K ∧
  ∀ a, Bezout u a → ∀ E, RepresentsIdempotents u a E →
    (∀ φ : Hardy, ∀ c : Fin m → ℂ,
      (AnalyticRemainder p (finiteProduct u) φ.val (correction E c) ↔
        ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _)) ∧
      ∀ B : ℝ, 0 ≤ B → ∀ X : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) φ.val X →
      (∀ j, ∃ Xⱼ : Model (u j) →L[ℂ] Model (u j), RepresentsTTO (u j) φ.val Xⱼ ∧
        Schatten p (Xⱼ - c j • ContinuousLinearMap.id ℂ _) ∧
        schattenNorm p (Xⱼ - c j • ContinuousLinearMap.id ℂ _) ≤ B) →
      schattenNorm p (X - correction E c) ≤ K * B) ∧
    (∀ φ ψ : Hardy, ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
      (HasSchattenSplit p (finiteProduct u) A ↔
        ∃ c : ℂ, ∀ j, AnalyticRemainder p (u j) φ.val (c • ContinuousLinearMap.id ℂ _)))

/-- Generic infinite-dimensional obstruction, independent of symbols and angular limits. -/
def ScalarCompactObligation : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (¬FiniteDimensional ℂ H) → ∀ c : ℂ,
      IsCompactOperator (c • ContinuousLinearMap.id ℂ H) → c = 0

def SingleAtomDimensionObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ζ : Boundary, SingleAtom u ζ →
    ¬FiniteDimensional ℂ (Model u)

/-- Ordinary uniqueness of a non-tangential limit; approach filters are nontrivial. -/
def AngularUniquenessObligation : Prop :=
  ∀ f : ℂ → ℂ, ∀ ζ : Boundary, ∀ c d : ℂ,
    AngularLimit f ζ c → AngularLimit f ζ d → c = d

structure SchattenNormLaws : Prop where
  sub_bound : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (p : ℝ) (A B : H →L[ℂ] H), 1 ≤ p → Schatten p A → Schatten p B →
      schattenNorm p (A - B) ≤ schattenNorm p A + schattenNorm p B

theorem schattenNorm_nonneg (p : ℝ) (A : E →L[ℂ] F) : 0 ≤ schattenNorm p A :=
  Real.rpow_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _) _

theorem scalar_remainder_unique (hC : CoreLaws) (hI : IdealLaws)
    (hS : ScalarCompactObligation) (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (hdim : ¬FiniteDimensional ℂ (Model u)) (φ : BoundaryL2) (p : ℝ) (c d : ℂ)
    (hc : AnalyticRemainder p u φ (c • ContinuousLinearMap.id ℂ _))
    (hd : AnalyticRemainder p u φ (d • ContinuousLinearMap.id ℂ _)) : c = d := by
  obtain ⟨X, hx, hsx⟩ := hc
  obtain ⟨Y, hy, hsy⟩ := hd
  have he := hC.unique u hu hn φ X Y hx hy
  subst Y
  have hs := hI.schatten_add p _ _ hsx (hI.schatten_neg p _ hsy)
  have halg : (X - c • ContinuousLinearMap.id ℂ (Model u)) +
      -(X - d • ContinuousLinearMap.id ℂ (Model u)) =
      (d - c) • ContinuousLinearMap.id ℂ (Model u) := by
    calc
      _ = d • ContinuousLinearMap.id ℂ (Model u) - c • ContinuousLinearMap.id ℂ (Model u) := by abel
      _ = _ := (sub_smul d c (ContinuousLinearMap.id ℂ (Model u))).symm
  rw [halg] at hs
  have hzero := hS hdim (d - c) hs.2.1
  exact (sub_eq_zero.mp hzero).symm

theorem analytic_remainder_pair (hC : CoreLaws) (hI : IdealLaws)
    (u : BoundaryLInf) (_hu : IsInner u) (_hn : Nonconstant u) (p : ℝ)
    (φ ψ : BoundaryL2) (A F : Model u →L[ℂ] Model u)
    (ha : RepresentsTTO u (splitSymbol φ ψ) A) (hsp : Schatten p A)
    (hx : AnalyticRemainder p u φ F) :
    AnalyticRemainder p u φ F ∧ CoanalyticRemainder p u ψ F := by
  obtain ⟨X, he, hs⟩ := hx
  have hy : RepresentsTTO u (star ψ) (A - X) := by
    simpa only [splitSymbol, add_sub_cancel_left] using hC.sub u _ _ A X ha he
  have halg : (A - X) + F = A + -(X - F) := by abel
  refine ⟨⟨X, he, hs⟩, ⟨A - X, hy, ?_⟩⟩
  rw [halg]
  exact hI.schatten_add p _ _ hsp (hI.schatten_neg p _ hs)

theorem hasSchatten_of_remainders (hC : CoreLaws) (hI : IdealLaws)
    {m : ℕ} (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2)
    (E : Fin m → Model u →L[ℂ] Model u) (c : Fin m → ℂ)
    (h : Remainders p u φ ψ E c) : HasSchattenTTO p u (splitSymbol φ ψ) := by
  obtain ⟨⟨X, hx, hsx⟩, ⟨Y, hy, hsy⟩⟩ := h
  refine ⟨X + Y, hC.add u _ _ _ _ hx hy, ?_⟩
  have halg : X + Y = (X - correction E c) + (Y + correction E c) := by abel
  rw [halg]
  exact hI.schatten_add p _ _ hsx hsy

theorem constant_correction {m : ℕ} {u : BoundaryLInf}
    (E : Fin m → Model u →L[ℂ] Model u) (he : ComplementaryIdempotents E) (c : ℂ) :
    correction E (fun _ => c) = c • ContinuousLinearMap.id ℂ (Model u) := by
  simp only [correction, ← Finset.smul_sum, he.1]

theorem zero_remainders (p : ℝ) (u : BoundaryLInf) (φ ψ : BoundaryL2) :
    (AnalyticRemainder p u φ 0 ∧ CoanalyticRemainder p u ψ 0) ↔
      HasSchattenTTO p u φ ∧ HasSchattenTTO p u (star ψ) := by
  constructor
  · rintro ⟨⟨X, hx, hsx⟩, ⟨Y, hy, hsy⟩⟩
    exact ⟨⟨X, hx, (sub_zero X) ▸ hsx⟩, ⟨Y, hy, (add_zero Y) ▸ hsy⟩⟩
  · rintro ⟨⟨X, hx, hsx⟩, ⟨Y, hy, hsy⟩⟩
    exact ⟨⟨X, hx, (sub_zero X).symm ▸ hsx⟩, ⟨Y, hy, (add_zero Y).symm ▸ hsy⟩⟩


private theorem real_two_remainders_bound (x y a K τ : ℝ)
    (hx : x ≤ K * (τ * a)) (hy : y ≤ a + x) :
    x + y ≤ (1 + 2 * K * τ) * a := by nlinarith

set_option maxHeartbeats 400000 in
theorem finiteAtomClassification (hC : CoreLaws) (hI : IdealLaws)
    (hS : CoronaStructureObligation) (hD : DistinctAtomCoronaObligation)
    (hComp : AtomCompressionObligation) (hOne : OneAtomObligation)
    (hV : VectorGluingObligation) (hScalar : ScalarCompactObligation)
    (hDim : SingleAtomDimensionObligation) (hAng : AngularUniquenessObligation)
    (hN : SchattenNormLaws) : FiniteAtomConclusion := by
  classical
  intro m hm u ζ hζ hu
  have hui : ∀ j, IsInner (u j) ∧ Nonconstant (u j) := fun j => ⟨(hu j).1, (hu j).2.1⟩
  have hcoro := hD m hm u ζ hζ (fun j => ⟨(hu j).1, (hu j).2.2⟩)
  obtain ⟨hut, hnt, ha0, hstruct⟩ := hS m hm u hui hcoro
  refine ⟨hut, hnt, ha0, hstruct, ?_⟩
  intro p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨τ, hτ, hone⟩ := hOne p hp
  obtain ⟨K, hK, hglue⟩ := hV m hm u hui hcoro p hp0
  refine ⟨1 + 2 * K * τ, by positivity, ?_⟩
  intro a ha E hE φ ψ
  obtain ⟨E₀, hE₀, he₀, hr₀, hind⟩ := hstruct a ha
  have heq := hind a E ha hE
  subst E
  obtain ⟨hvec, hsplit⟩ := hglue a ha E₀ hE₀
  have hdim : ∀ j, ¬FiniteDimensional ℂ (Model (u j)) :=
    fun j => hDim (u j) (hu j).1 (hu j).2.1 (ζ j) (hu j).2.2
  have localData : ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
      ∃ c : Fin m → ℂ, ∀ j, ∃ X Y : Model (u j) →L[ℂ] Model (u j),
        RepresentsTTO (u j) φ.val X ∧ RepresentsTTO (u j) (star ψ.val) Y ∧
        Schatten p (X - c j • ContinuousLinearMap.id ℂ _) ∧
        Schatten p (Y + c j • ContinuousLinearMap.id ℂ _) ∧
        schattenNorm p (X - c j • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
        AngularLimit (analyticValue φ.val) (ζ j) (c j) ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj (c j)) := by
    intro A he hs
    have hx : ∀ j, ∃ c : ℂ, ∃ X Y : Model (u j) →L[ℂ] Model (u j),
        RepresentsTTO (u j) φ.val X ∧ RepresentsTTO (u j) (star ψ.val) Y ∧
        Schatten p (X - c • ContinuousLinearMap.id ℂ _) ∧
        Schatten p (Y + c • ContinuousLinearMap.id ℂ _) ∧
        schattenNorm p (X - c • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
        AngularLimit (analyticValue φ.val) (ζ j) c ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj c) := by
      intro j
      obtain ⟨Aj, hj, hsj, hnj⟩ := hComp m hm u ζ hζ hu φ ψ p hp0 A he hs j
      obtain ⟨c, X, Y, hX, hY, hsX, hsY, hnX, _, haX, haY⟩ :=
        hone (u j) (hu j).1 (hu j).2.1 (ζ j) (hu j).2.2 φ ψ Aj hj hsj
      exact ⟨c, X, Y, hX, hY, hsX, hsY,
        hnX.trans (mul_le_mul_of_nonneg_left hnj hτ.le), haX, haY⟩
    choose c X Y hX hY hsX hsY hnX haX haY using hx
    exact ⟨c, fun j => ⟨X j, Y j, hX j, hY j, hsX j, hsY j, hnX j, haX j, haY j⟩⟩
  have hlocal (c : Fin m → ℂ) :
      Remainders p (finiteProduct u) φ.val ψ.val E₀ c →
      ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) :=
    fun h => (hvec φ c).1.mp h.1
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨A, he, hs⟩
      obtain ⟨c, hd⟩ := localData A he hs
      have hl : ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) := by
        intro j
        obtain ⟨X, Y, hx, _, hsx, _⟩ := hd j
        exact ⟨X, hx, hsx⟩
      exact ⟨c, analytic_remainder_pair hC hI _ hut hnt p _ _ A _ he hs ((hvec φ c).1.mpr hl)⟩
    · rintro ⟨c, hc⟩
      exact hasSchatten_of_remainders hC hI p _ _ _ E₀ c hc
  · intro c d hc hd
    funext j
    exact scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1 (hdim j)
      φ.val p (c j) (d j) (hlocal c hc j) (hlocal d hd j)
  · intro A he hs
    obtain ⟨c₀, hd⟩ := localData A he hs
    have hl₀ : ∀ j, AnalyticRemainder p (u j) φ.val (c₀ j • ContinuousLinearMap.id ℂ _) := by
      intro j
      obtain ⟨X, Y, hx, _, hsx, _⟩ := hd j
      exact ⟨X, hx, hsx⟩
    have localAngle (j : Fin m) (c : ℂ) :
        AnalyticRemainder p (u j) φ.val (c • ContinuousLinearMap.id ℂ _) ↔
        AngularLimit (analyticValue φ.val) (ζ j) c := by
      obtain ⟨X, Y, hx, hy, hsx, hsy, hnX, haX, haY⟩ := hd j
      constructor
      · intro hc
        have hcc := scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1
          (hdim j) φ.val p c (c₀ j) hc (hl₀ j)
        exact hcc.symm ▸ haX
      · intro hc
        have hcc := hAng _ (ζ j) c (c₀ j) hc haX
        exact hcc.symm ▸ hl₀ j
    have hpair (c : Fin m → ℂ) : Remainders p (finiteProduct u) φ.val ψ.val E₀ c ↔
        ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) := by
      constructor
      · exact hlocal c
      · intro hl
        exact analytic_remainder_pair hC hI _ hut hnt p _ _ A _ he hs ((hvec φ c).1.mpr hl)
    have hscalar (c : ℂ) :
        (AnalyticRemainder p (finiteProduct u) φ.val (c • ContinuousLinearMap.id ℂ _) ∧
          CoanalyticRemainder p (finiteProduct u) ψ.val (c • ContinuousLinearMap.id ℂ _)) ↔
        ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c := by
      have hc := constant_correction E₀ he₀ c
      constructor
      · intro hrem
        have hrem' : Remainders p (finiteProduct u) φ.val ψ.val E₀ (fun _ => c) := by
          simpa only [Remainders, hc] using hrem
        exact fun j => (localAngle j c).mp ((hpair _).mp hrem' j)
      · intro hang
        have hl := fun j => (localAngle j c).mpr (hang j)
        have hrem' := (hpair (fun _ => c)).mpr hl
        simpa only [Remainders, hc] using hrem'
    refine ⟨hpair, ?_, ?_, hscalar, ?_⟩
    · intro c hc
      have hcc : ∀ j, c j = c₀ j := fun j =>
        scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1 (hdim j)
          φ.val p (c j) (c₀ j) ((hpair c).mp hc j) (hl₀ j)
      constructor
      · intro j
        obtain ⟨X, Y, hx, hy, hsx, hsy, hnX, haX, haY⟩ := hd j
        exact ⟨(hcc j).symm ▸ haX, (hcc j).symm ▸ haY⟩
      · intro X Y hx hy hsx hsy
        have hB : 0 ≤ τ * schattenNorm p A := mul_nonneg hτ.le (schattenNorm_nonneg p A)
        have hxbound : schattenNorm p (X - correction E₀ c) ≤ K * (τ * schattenNorm p A) := by
          apply (hvec φ c).2 (τ * schattenNorm p A) hB X hx
          intro j
          obtain ⟨Xj, Yj, hxj, hyj, hsxj, hsyj, hnxj, haj, hbj⟩ := hd j
          exact ⟨Xj, hxj, (hcc j).symm ▸ hsxj, (hcc j).symm ▸ hnxj⟩
        have hsum : A = X + Y := hC.unique _ hut hnt _ A (X + Y) he (hC.add _ _ _ X Y hx hy)
        have hyalg : Y + correction E₀ c = A - (X - correction E₀ c) := by rw [hsum]; abel
        have hybound : schattenNorm p (Y + correction E₀ c) ≤
            schattenNorm p A + schattenNorm p (X - correction E₀ c) := by
          rw [hyalg]
          exact hN.sub_bound p A _ hp.le hs hsx
        exact real_two_remainders_bound _ _ _ K τ hxbound hybound
    · exact (hsplit φ ψ A he hs).trans ⟨by
        rintro ⟨c, hc⟩
        exact ⟨c, fun j => (localAngle j c).mp (hc j)⟩, by
        rintro ⟨c, hc⟩
        exact ⟨c, fun j => (localAngle j c).mpr (hc j)⟩⟩
    · have h0 : (0 : ℂ) • ContinuousLinearMap.id ℂ (Model (finiteProduct u)) = 0 := by
        ext x
        simp
      have hp0 := hscalar 0
      rw [h0] at hp0
      exact (zero_remainders p (finiteProduct u) φ.val ψ.val).symm.trans hp0


/-- A genuine coefficient model: entries are specified integrals of products of a bounded ONB. -/
structure MatrixData (u : BoundaryLInf) where
  Index : Type
  countable : Countable Index
  basis : HilbertBasis Index ℂ (Model u)
  bounded : ∀ i, IsBounded (basis i).val
  coefficient : (Index × Index) → Ambient u →L[ℂ] ℂ
  coefficient_eq : ∀ ij η, coefficient ij η =
    ∫ t, η.val t * conj ((basis ij.1).val t * (basis ij.2).val t) ∂circleMeasure
  tensor : lp (fun _ : Index × Index => ℂ) 2 ≃ₗᵢ[ℂ] TensorModel u
  graph_coefficients : ∀ η G, QGraph u η G ↔
    ∀ ij, tensor.symm G ij = coefficient ij η
  kernel : Disk → Ambient u
  kernel_value : ∀ w z : Disk, analyticValue (kernel w).val z.val = kernelValue (multiplyInf u u) w.val z.val
  total : Dense (Submodule.span ℂ (Set.range kernel) : Set (Ambient u))
  kernel_coefficients : ∀ w, ∃ x : lp (fun _ : Index × Index => ℂ) 2,
    ∀ ij, x ij = coefficient ij (kernel w)
  squareKernel : Disk → Ambient u
  squareKernel_value : ∀ w z : Disk, analyticValue (squareKernel w).val z.val = kernelValue u w.val z.val ^ 2
  reproduces : ∀ (η : Ambient u) (w : Disk), analyticValue η.val w.val = inner ℂ (kernel w) η


def matrixEnergy {u : BoundaryLInf} (b : MatrixData u) (η : Ambient u) : ℝ≥0∞ :=
  ∑' ij, ENNReal.ofReal (‖b.coefficient ij η‖ ^ 2)

def coefficientPair {u : BoundaryLInf} (b : MatrixData u) (η γ : Ambient u) : ℂ :=
  ∑' ij, b.coefficient ij η * conj (b.coefficient ij γ)

/-- Generic closed coefficient analysis, with no inner functions or boundary energy. -/
def ClosedAnalysisObligation : Prop :=
  ∀ (H K I : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
  ∀ c : I → H →L[ℂ] ℂ, ∀ U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] K,
  ∃ Q : H →ₗ.[ℂ] K, Q.IsClosed ∧
    (∀ x y, (x, y) ∈ Q.graph ↔ ∀ i, U.symm y i = c i x) ∧
    (∀ x, x ∈ Q.domain ↔ (∑' i, ENNReal.ofReal (‖c i x‖ ^ 2)) < ∞)

/-- Generic Hilbert coordinate identities, available from native l² APIs after adaptation. -/
structure L2CoordinateLaws : Prop where
  norm : ∀ I : Type, ∀ x : lp (fun _ : I => ℂ) 2,
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' i, ENNReal.ofReal (‖x i‖ ^ 2)
  inner : ∀ I : Type, ∀ x y : lp (fun _ : I => ℂ) 2,
    inner ℂ y x = ∑' i, x i * conj (y i)

/-- Generic HS matrix reconstruction specialized to the explicit bounded-core coefficients.
No FKernel, energy or differential operator occurs in this criterion. -/
def MatrixOperatorObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ b : MatrixData u, ∀ η : Ambient u,
    (HasSchattenTHO 2 u (star η.val) ↔ matrixEnergy b η < ∞) ∧
    ∀ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u (star η.val) B → Schatten 2 B →
      ENNReal.ofReal (schattenNorm 2 B ^ 2) = matrixEnergy b η

/-- Fourier division by z-w and Parseval for the actual coefficient array. -/
structure BoundaryParsevalObligation : Prop where
  norm : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ b : MatrixData u, ∀ η : Ambient u,
    energy u η.val = matrixEnergy b η
  pairing : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ b : MatrixData u, ∀ η γ : Ambient u,
    matrixEnergy b η < ∞ → matrixEnergy b γ < ∞ →
      energyPairing u η.val γ.val = coefficientPair b η γ

/-- Concrete section calculations and the generic Hardy tensor-section criterion. -/
structure TensorSectionObligation : Prop where
  tensor_hardy : ∀ u : BoundaryLInf, IsInner u → tensorModel u ≤ bidiskHardy
  sections : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u,
    (∀ w ∈ disk, ∃ f : Model u, ∀ z ∈ disk, analyticValue f.val z = FKernel u η.val z w) ∧
    (∀ z ∈ disk, ∃ f : Model u, ∀ w ∈ disk, analyticValue f.val w = FKernel u η.val z w)
  criterion : ∀ u : BoundaryLInf, IsInner u → ∀ G : BidiskL2, G ∈ bidiskHardy →
    (∀ w ∈ disk, ∃ f : Model u, ∀ z ∈ disk, analyticValue f.val z = analyticValue₂ G z w) →
    (∀ z ∈ disk, ∃ f : Model u, ∀ w ∈ disk, analyticValue f.val w = analyticValue₂ G z w) →
      G ∈ tensorModel u

/-- Explicit coefficient tests on reproducing kernels, prior to forming Q*Q. -/
def KernelCoefficientObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ b : MatrixData u,
    ∀ η : Ambient u, matrixEnergy b η < ∞ → ∀ w : Disk,
      coefficientPair b (b.kernel w) η = inner ℂ η (b.squareKernel w) ∧
      coefficientPair b η (b.kernel w) = FKernel u η.val w.val w.val

/-- Raw partial fractions from multiplying the model kernels, before the final h/g formula. -/
structure KernelCalculusObligation : Prop where
  decomposition : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u,
    η.val = eta₁ u η.val + multiply u (eta₂ u η.val)
  value : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u, ∀ z ∈ disk,
    analyticValue η.val z = analyticValue (eta₁ u η.val) z +
      innerValue u z * analyticValue (eta₂ u η.val) z
  hvalue : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u, ∀ z ∈ disk,
    analyticValue (energyH u η.val) z = z * analyticValue (eta₁ u η.val) z
  gvalue : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u, ∀ z ∈ disk,
    analyticValue (energyG u η.val) z = z * analyticValue (eta₂ u η.val) z
  differentiable : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u,
    DifferentiableOn ℂ (innerValue u) disk ∧
    DifferentiableOn ℂ (analyticValue (eta₁ u η.val)) disk ∧
    DifferentiableOn ℂ (analyticValue (eta₂ u η.val)) disk
  continuous_diagonal : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u,
    ∀ z ∈ disk, ContinuousAt (FKernel u η.val z) z
  fractions : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ η : Ambient u,
    ∀ z ∈ disk, ∀ w ∈ disk, z ≠ w →
      FKernel u η.val z w = (z * analyticValue η.val z - w * analyticValue η.val w -
        (innerValue u z + innerValue u w) *
          (z * analyticValue (eta₂ u η.val) z - w * analyticValue (eta₂ u η.val) w)) / (z - w)

/-- Ordinary one-variable removable-divided-difference calculus for arbitrary differentiable data.
This is independent of Hardy/model spaces, Hilbert--Schmidt membership and energy. -/
def RemovableCalculusObligation : Prop :=
  ∀ v a b : ℂ → ℂ, ∀ F : ℂ → ℂ → ℂ,
    DifferentiableOn ℂ v disk → DifferentiableOn ℂ a disk → DifferentiableOn ℂ b disk →
    (∀ z ∈ disk, ContinuousAt (F z) z) →
    (∀ z ∈ disk, ∀ w ∈ disk, z ≠ w → F z w =
      (z * (a z + v z * b z) - w * (a w + v w * b w) -
        (v z + v w) * (z * b z - w * b w)) / (z - w)) →
    (∀ z ∈ disk, ∀ w ∈ disk, F z w =
      if z = w then deriv (fun t => t * a t) z + deriv v z * (z * b z) -
        v z * deriv (fun t => t * b t) z else
        (z * a z - w * a w + v z * (w * b w) - v w * (z * b z)) / (z - w)) ∧
    (∀ z ∈ disk, F z z = deriv (fun t => t * (a t + v t * b t)) z -
      2 * v z * deriv (fun t => t * b t) z)

/-- Generic graph form, without manuscript energy, kernels or differential expressions. -/
structure GraphFormData {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (Q : H →ₗ.[ℂ] K) (D S : H →ₗ.[ℂ] H) : Prop where
  adjoint_square : ∀ x y, (x, y) ∈ D.graph ↔ ∃ v : K, (x, v) ∈ Q.graph ∧ (v, y) ∈ Q.adjoint.graph
  positive : PositiveSelfAdjoint D
  sqrt : IsSquareRoot D S
  domain : S.domain = Q.domain
  norm : ∀ x : S.domain, ∀ y : Q.domain, x.val = y.val → ‖S x‖ ^ 2 = ‖Q y‖ ^ 2
  form : ∀ x y, (x, y) ∈ D.graph ↔ ∃ hx : x ∈ Q.domain,
    ∀ γ : Q.domain, inner ℂ γ.val y = inner ℂ (Q γ) (Q ⟨x, hx⟩)
  bounded : ∀ x, x ∈ D.domain ↔ ∃ hx : x ∈ Q.domain,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : Q.domain,
      ‖inner ℂ (Q γ) (Q ⟨x, hx⟩)‖ ≤ C * ‖γ.val‖

/-- Generic closed densely-defined graph-form/square-root theorem. -/
def GraphFormObligation : Prop :=
  ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
  ∀ Q : H →ₗ.[ℂ] K, Q.IsClosed → Dense (Q.domain : Set H) →
    ∃ D S : H →ₗ.[ℂ] H, GraphFormData Q D S

/-- Actual canonical-symbol unitary transfer, independent of the energy criterion. -/
def CanonicalTHOObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ ψ : Model u,
  analyticValue ψ.val 0 = 0 → ∃ η : Ambient u,
    η.val = conjugation u φ.val + multiply u (multiply (star coordinate) ψ.val) ∧
    energyH u η.val = multiply coordinate (conjugation u φ.val) ∧ energyG u η.val = ψ.val ∧
    (HasSchattenTTO 2 u (splitSymbol φ.val ψ.val) ↔ HasSchattenTHO 2 u (star η.val)) ∧
    ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten 2 A →
      ∃ B : Model u →L[ℂ] ConjugateModel u, RepresentsTHO u (star η.val) B ∧ Schatten 2 B ∧
        ∀ n, approximationNumber A n = approximationNumber B n


def MatrixDataObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → Nonempty (MatrixData u)

private theorem deriv_eq_on_disk (f g : ℂ → ℂ) (h : ∀ z ∈ disk, f z = g z)
    (z : ℂ) (hz : z ∈ disk) : deriv f z = deriv g z := by
  have ho : IsOpen disk := isOpen_lt continuous_norm continuous_const
  have he : f =ᶠ[𝓝 z] g := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact h w hw
  exact he.deriv_eq

theorem kernel_calculus (hK : KernelCalculusObligation) (hR : RemovableCalculusObligation)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (η : Ambient u) :
    (∀ z ∈ disk, ∀ w ∈ disk, FKernel u η.val z w = dividedDifference u η.val z w) ∧
    (∀ z ∈ disk, FKernel u η.val z z = diagonalDifferential u η.val z ∧
      FKernel u η.val z z = expandedDifferential u η.val z) := by
  obtain ⟨hv, ha, hb⟩ := hK.differentiable u hu hn η
  have hraw : ∀ z ∈ disk, ∀ w ∈ disk, z ≠ w → FKernel u η.val z w =
      (z * (analyticValue (eta₁ u η.val) z + innerValue u z * analyticValue (eta₂ u η.val) z) -
       w * (analyticValue (eta₁ u η.val) w + innerValue u w * analyticValue (eta₂ u η.val) w) -
       (innerValue u z + innerValue u w) *
        (z * analyticValue (eta₂ u η.val) z - w * analyticValue (eta₂ u η.val) w)) / (z - w) := by
    intro z hz w hw hne
    rw [hK.fractions u hu hn η z hz w hw hne, hK.value u hu hn η z hz, hK.value u hu hn η w hw]
  obtain ⟨hdiv, hdiag⟩ := hR (innerValue u) (analyticValue (eta₁ u η.val))
    (analyticValue (eta₂ u η.val)) (FKernel u η.val) hv ha hb
    (hK.continuous_diagonal u hu hn η) hraw
  have hhexp (z : ℂ) (hz : z ∈ disk) : expandedDifferential u η.val z =
      deriv (fun t => t * analyticValue (eta₁ u η.val) t) z +
      deriv (innerValue u) z * (z * analyticValue (eta₂ u η.val) z) -
      innerValue u z * deriv (fun t => t * analyticValue (eta₂ u η.val) t) z := by
    unfold expandedDifferential
    rw [deriv_eq_on_disk _ _ (hK.hvalue u hu hn η) z hz,
      deriv_eq_on_disk _ _ (hK.gvalue u hu hn η) z hz, hK.gvalue u hu hn η z hz]
  constructor
  · intro z hz w hw
    by_cases hzw : z = w
    · subst w
      simpa [dividedDifference, hhexp z hz] using hdiv z hz z hz
    · simpa only [dividedDifference, ite_eq_right hzw,
        hK.hvalue u hu hn η z hz, hK.hvalue u hu hn η w hw,
        hK.gvalue u hu hn η z hz, hK.gvalue u hu hn η w hw] using hdiv z hz w hw
  · intro z hz
    have hd : FKernel u η.val z z = expandedDifferential u η.val z := by
      simpa [← hhexp z hz] using hdiv z hz z hz
    refine ⟨?_, hd⟩
    unfold diagonalDifferential
    have hdη : deriv (fun t => t * analyticValue η.val t) z =
        deriv (fun t => t * (analyticValue (eta₁ u η.val) t +
          innerValue u t * analyticValue (eta₂ u η.val) t)) z :=
      deriv_eq_on_disk _ _ (fun t ht => congrArg (fun a => t * a) (hK.value u hu hn η t ht)) z hz
    rw [hdη]
    exact hdiag z hz

theorem bidisk_iff_tensor (hT : TensorSectionObligation) (u : BoundaryLInf)
    (hu : IsInner u) (hn : Nonconstant u) (η : Ambient u) :
    HasBidiskRepresentative u η.val ↔ ∃ G : TensorModel u, QGraph u η G := by
  constructor
  · rintro ⟨G, hg, he⟩
    obtain ⟨hs₁, hs₂⟩ := hT.sections u hu hn η
    have ht : G ∈ tensorModel u := by
      apply hT.criterion u hu G hg
      · intro w hw
        obtain ⟨f, hf⟩ := hs₁ w hw
        exact ⟨f, fun z hz => (hf z hz).trans (he z hz w hw).symm⟩
      · intro z hz
        obtain ⟨f, hf⟩ := hs₂ z hz
        exact ⟨f, fun w hw => (hf w hw).trans (he z hz w hw).symm⟩
    exact ⟨⟨G, ht⟩, he⟩
  · rintro ⟨G, he⟩
    exact ⟨G.val, hT.tensor_hardy u hu G.property, he⟩

private theorem graph_apply {H K : Type} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup K] [Module ℂ K] (Q : H →ₗ.[ℂ] K) (x : Q.domain) :
    (x.val, Q x) ∈ Q.graph := Q.mem_graph x

private theorem domain_of_graph {H K : Type} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup K] [Module ℂ K] (Q : H →ₗ.[ℂ] K) {x : H} {y : K}
    (h : (x, y) ∈ Q.graph) : x ∈ Q.domain := by
  obtain ⟨a, ha, _⟩ := (Q.mem_graph_iff).mp h
  have ha' : a.val = x := ha
  exact ha' ▸ a.property

theorem tensor_norm_coefficients (hL : L2CoordinateLaws) (u : BoundaryLInf) (b : MatrixData u)
    (η : Ambient u) (G : TensorModel u) (hg : QGraph u η G) :
    ENNReal.ofReal (‖G‖ ^ 2) = matrixEnergy b η := by
  have hcoords := (b.graph_coefficients η G).mp hg
  calc
    _ = ENNReal.ofReal (‖b.tensor.symm G‖ ^ 2) := by rw [b.tensor.symm.norm_map]
    _ = ∑' ij, ENNReal.ofReal (‖b.tensor.symm G ij‖ ^ 2) := hL.norm _ _
    _ = _ := tsum_congr fun ij => by rw [hcoords ij]


set_option maxHeartbeats 500000 in
theorem energyAssembly (hB : MatrixDataObligation) (hA : ClosedAnalysisObligation)
    (hL : L2CoordinateLaws) (hM : MatrixOperatorObligation) (hP : BoundaryParsevalObligation)
    (hT : TensorSectionObligation) (hK : KernelCalculusObligation) (hR : RemovableCalculusObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) (hCan : CanonicalTHOObligation)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) :
    EnergyIdentities u ∧ ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u,
      ∃ D S : Ambient u →ₗ.[ℂ] Ambient u, EnergyGeometry u Q D S ∧ DifferentialProperties u Q D := by
  classical
  let b := Classical.choice (hB u hu hn)
  obtain ⟨Q, hClosed, hcoords, hdom⟩ := hA (Ambient u) (TensorModel u) (b.Index × b.Index)
    b.coefficient b.tensor
  have hq (η : Ambient u) (G : TensorModel u) : (η, G) ∈ Q.graph ↔ QGraph u η G :=
    (hcoords η G).trans (b.graph_coefficients η G).symm
  have hdm (η : Ambient u) : η ∈ Q.domain ↔ matrixEnergy b η < ∞ := hdom η
  have hde (η : Ambient u) : η ∈ Q.domain ↔ energy u η.val < ∞ := by
    rw [hP.norm u hu hn b η]
    exact hdm η
  have hk (w : Disk) : b.kernel w ∈ Q.domain := by
    obtain ⟨x, hx⟩ := b.kernel_coefficients w
    apply domain_of_graph Q (y := b.tensor x)
    apply (hcoords _ _).mpr
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hx
  have hspan : Submodule.span ℂ (Set.range b.kernel) ≤ Q.domain := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact hk w
  have hDense : Dense (Q.domain : Set (Ambient u)) := b.total.mono hspan
  have hqg (η : Q.domain) : QGraph u η.val (Q η) := (hq _ _).mp (graph_apply Q η)
  have qnorm (η : Q.domain) : ENNReal.ofReal (‖Q η‖ ^ 2) = energy u η.val.val :=
    (tensor_norm_coefficients hL u b η.val (Q η) (hqg η)).trans (hP.norm u hu hn b η.val).symm
  have qSeries (η γ : Q.domain) : inner ℂ (Q γ) (Q η) = coefficientPair b η.val γ.val := by
    have hη := (b.graph_coefficients _ _).mp (hqg η)
    have hγ := (b.graph_coefficients _ _).mp (hqg γ)
    calc
      _ = inner ℂ (b.tensor.symm (Q γ)) (b.tensor.symm (Q η)) :=
        (b.tensor.symm.inner_map_map _ _).symm
      _ = ∑' ij, b.tensor.symm (Q η) ij * conj (b.tensor.symm (Q γ) ij) := hL.inner _ _ _
      _ = _ := tsum_congr fun ij => by rw [hη ij, hγ ij]
  have qPair (η γ : Q.domain) : energyPairing u η.val.val γ.val.val = inner ℂ (Q γ) (Q η) :=
    (hP.pairing u hu hn b η.val γ.val ((hdm _).mp η.property) ((hdm _).mp γ.property)).trans
      (qSeries η γ).symm
  have hIdent : EnergyIdentities u := by
    constructor
    · intro η
      have hhs : HasSchattenTHO 2 u (star η.val) ↔ energy u η.val < ∞ :=
        (hM u hu hn b η).1.trans (by rw [hP.norm u hu hn b η])
      have hbid : HasBidiskRepresentative u η.val ↔ energy u η.val < ∞ := by
        apply (bidisk_iff_tensor hT u hu hn η).trans
        constructor
        · rintro ⟨G, hg⟩
          exact (hde η).mp (domain_of_graph Q ((hq η G).mpr hg))
        · intro he
          let η' : Q.domain := ⟨η, (hde η).mpr he⟩
          exact ⟨Q η', hqg η'⟩
      refine ⟨hK.decomposition u hu hn η, (kernel_calculus hK hR u hu hn η).1,
        hhs.trans hbid.symm, hhs, ?_, ?_, ?_⟩
      · intro he
        let η' : Q.domain := ⟨η, (hde η).mpr he⟩
        exact ⟨Q η', hqg η'⟩
      · intro G hg
        exact (tensor_norm_coefficients hL u b η G hg).trans (hP.norm u hu hn b η).symm
      · intro B hb hs
        exact (hM u hu hn b η).2 B hb hs |>.trans (hP.norm u hu hn b η).symm
    · intro φ ψ hψ
      obtain ⟨η, he, hh, hg, hsp, hnB⟩ := hCan u hu hn φ ψ hψ
      have hhs : HasSchattenTHO 2 u (star η.val) ↔ energy u η.val < ∞ :=
        (hM u hu hn b η).1.trans (by rw [hP.norm u hu hn b η])
      refine ⟨η, he, hh, hg, hsp.trans hhs, ?_⟩
      intro A ha hs
      obtain ⟨B, hb, hsb, hsing⟩ := hnB A ha hs
      rw [schattenNorm_transfer (p := 2) hsing]
      exact ((hM u hu hn b η).2 B hb hsb).trans (hP.norm u hu hn b η).symm
  obtain ⟨D, S, hform⟩ := hF (Ambient u) (TensorModel u) Q hClosed hDense
  have hGeometry : EnergyGeometry u Q D S := by
    refine ⟨hq, hde, hClosed, hDense, hform.adjoint_square, hform.positive, hform.sqrt,
      hform.domain, ?_, ?_, qPair⟩
    · intro η
      have hη : η.val ∈ Q.domain := hform.domain ▸ η.property
      let η' : Q.domain := ⟨η.val, hη⟩
      rw [hform.norm η η' rfl]
      exact qnorm η'
    · intro η χ
      constructor
      · intro hd
        obtain ⟨hη, hh⟩ := (hform.form η χ).mp hd
        exact ⟨hη, fun γ => (hh γ).trans (qPair ⟨η, hη⟩ γ).symm⟩
      · rintro ⟨hη, hh⟩
        exact (hform.form η χ).mpr ⟨hη, fun γ => (hh γ).trans (qPair ⟨η, hη⟩ γ)⟩
  have hDifferential : DifferentialProperties u Q D := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro η
      exact (kernel_calculus hK hR u hu hn η).2
    · intro w hw
      let w' : Disk := ⟨w, hw⟩
      refine ⟨b.kernel w', b.squareKernel w', ?_, ?_, ?_⟩
      · intro z hz
        exact b.kernel_value w' ⟨z, hz⟩
      · intro z hz
        exact b.squareKernel_value w' ⟨z, hz⟩
      · apply (hform.form _ _).mpr
        refine ⟨hk w', ?_⟩
        intro γ
        exact ((hTests u hu hn b γ.val ((hdm _).mp γ.property) w').1).symm.trans
          (qSeries ⟨b.kernel w', hk w'⟩ γ).symm
    · intro η
      obtain ⟨hη, hh⟩ := (hform.form η.val (D η)).mp (graph_apply D η)
      let η' : Q.domain := ⟨η.val, hη⟩
      constructor
      · intro z hz
        let w : Disk := ⟨z, hz⟩
        calc
          _ = inner ℂ (b.kernel w) (D η) := b.reproduces (D η) w
          _ = inner ℂ (Q ⟨b.kernel w, hk w⟩) (Q η') := hh ⟨b.kernel w, hk w⟩
          _ = coefficientPair b η.val (b.kernel w) := qSeries η' ⟨b.kernel w, hk w⟩
          _ = _ := (hTests u hu hn b η.val ((hdm _).mp hη) w).2
      · have hself : inner ℂ η.val (D η) = inner ℂ (Q η') (Q η') := hh η'
        rw [hself, inner_self_eq_norm_sq_to_K]
        have hnE : (energy u η.val.val).toReal = ‖Q η'‖ ^ 2 := by
          rw [← qnorm η', ENNReal.toReal_ofReal (sq_nonneg _)]
        rw [hnE]
        norm_cast
    · intro η
      constructor
      · intro hd
        obtain ⟨hη, C, hC, hb⟩ := (hform.bounded η).mp hd
        refine ⟨hη, C, hC, ?_⟩
        intro γ
        rw [qPair ⟨η, hη⟩ γ]
        exact hb γ
      · rintro ⟨hη, C, hC, hb⟩
        apply (hform.bounded η).mpr
        refine ⟨hη, C, hC, ?_⟩
        intro γ
        rw [← qPair ⟨η, hη⟩ γ]
        exact hb γ
  exact ⟨hIdent, Q, D, S, hGeometry, hDifferential⟩

theorem hilbertSchmidtEnergy (hB : MatrixDataObligation) (hA : ClosedAnalysisObligation)
    (hL : L2CoordinateLaws) (hM : MatrixOperatorObligation) (hP : BoundaryParsevalObligation)
    (hT : TensorSectionObligation) (hK : KernelCalculusObligation) (hR : RemovableCalculusObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) (hCan : CanonicalTHOObligation) :
    HilbertSchmidtConclusion := by
  intro u hu hn
  obtain ⟨hi, Q, D, S, hg, _⟩ := energyAssembly hB hA hL hM hP hT hK hR hF hTests hCan u hu hn
  exact ⟨hi, Q, D, S, hg⟩

theorem differentialRealization (hB : MatrixDataObligation) (hA : ClosedAnalysisObligation)
    (hL : L2CoordinateLaws) (hM : MatrixOperatorObligation) (hP : BoundaryParsevalObligation)
    (hT : TensorSectionObligation) (hK : KernelCalculusObligation) (hR : RemovableCalculusObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) (hCan : CanonicalTHOObligation) :
    DifferentialConclusion := by
  intro u hu hn
  exact (energyAssembly hB hA hL hM hP hT hK hR hF hTests hCan u hu hn).2


def classicalCoefficientEnergy (g : BoundaryL2) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((n + 1 : ℝ) * ‖fourierCoeff g (n : ℤ)‖ ^ 2)

/-- Generic classical Hankel HS matrix/Dirichlet Parseval law; no model-space data. -/
structure ClassicalDirichletObligation : Prop where
  membership : ∀ g : BoundaryL2, g ∈ hardy →
    (HasSchattenHankel 2 (star (multiply coordinate g)) ↔ classicalCoefficientEnergy g < ∞)
  norm : ∀ g : BoundaryL2, g ∈ hardy → ∀ H : HankelOperator,
    RepresentsHankel (star (multiply coordinate g)) H → Schatten 2 H →
      ENNReal.ofReal (schattenNorm 2 H ^ 2) = classicalCoefficientEnergy g
  boundary : ∀ g : BoundaryL2, g ∈ hardy →
    (∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖
      (fourier (T := 1) 1 t * g t - fourier (T := 1) 1 s * g s) /
      (fourier (T := 1) 1 t - fourier (T := 1) 1 s)‖ ^ 2) ∂circleMeasure ∂circleMeasure) =
      classicalCoefficientEnergy g

theorem analyticDirichletEnergy (h : ExactHankelObligation) (hD : ClassicalDirichletObligation) :
    AnalyticDirichletConclusion := by
  intro u hu hn φ
  have hg := (h u hu hn φ).1
  refine ⟨(hankel_schatten_iff h 2 u hu hn φ).trans (hD.membership _ hg), ?_, hD.boundary _ hg⟩
  intro A ha hs
  obtain ⟨H, hh, hc, hsing⟩ := (h u hu hn φ).2.1 A ha
  rw [schattenNorm_transfer (p := 2) hsing]
  exact hD.norm _ hg H hh ((schatten_transfer hc hsing).mp hs)

structure AdjointLaws : Prop where
  compact : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H), IsCompactOperator A.adjoint ↔ IsCompactOperator A
  schatten : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (p : ℝ), Schatten p A.adjoint ↔ Schatten p A
  approximation : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (n : ℕ), approximationNumber A.adjoint n = approximationNumber A n

theorem star_schatten_iff (hC : CoreLaws) (hA : AdjointLaws) (p : ℝ)
    (u : BoundaryLInf) (σ : BoundaryL2) : HasSchattenTTO p u (star σ) ↔ HasSchattenTTO p u σ := by
  constructor
  · rintro ⟨A, he, hs⟩
    exact ⟨A.adjoint, by simpa using hC.adjoint u _ A he, (hA.schatten A p).mpr hs⟩
  · rintro ⟨A, he, hs⟩
    exact ⟨A.adjoint, hC.adjoint u _ A he, (hA.schatten A p).mpr hs⟩

theorem coanalyticBesov (hC : CoreLaws) (hA : AdjointLaws) (p : ℝ)
    (h : BesovConclusion p) : CoanalyticBesovConclusion p := by
  constructor
  · intro u hu hn φ
    have he := star_schatten_iff hC hA p u φ.val
    exact ⟨he.trans (h.1 u hu hn φ).1, he.trans (h.1 u hu hn φ).2⟩
  · obtain ⟨c, C, ch, Ch, hc, hC', hch, hCh, hb⟩ := h.2
    refine ⟨c, C, ch, Ch, hc, hC', hch, hCh, ?_⟩
    intro u hu hn φ A he hs
    have he' : RepresentsTTO u φ.val A.adjoint := by simpa using hC.adjoint u _ A he
    have hb' := hb u hu hn φ A.adjoint he' ((hA.schatten A p).mpr hs)
    have hnA := schattenNorm_transfer (p := p) (hA.approximation A)
    simpa only [hnA] using hb'

theorem coanalyticCompact (hC : CoreLaws) (hA : AdjointLaws)
    (h : CompactConclusion) : CoanalyticCompactConclusion := by
  intro u hu hn φ
  have he : HasCompactTTO u (star φ.val) ↔ HasCompactTTO u φ.val := by
    constructor
    · rintro ⟨A, he, hc⟩
      exact ⟨A.adjoint, by simpa using hC.adjoint u _ A he, (hA.compact A).mpr hc⟩
    · rintro ⟨A, he, hc⟩
      exact ⟨A.adjoint, hC.adjoint u _ A he, (hA.compact A).mpr hc⟩
  exact ⟨he.trans (h u hu hn φ).1, he.trans (h u hu hn φ).2⟩

def SchattenMonotonicity : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (p q : ℝ), 0 < p → p ≤ q → Schatten p A → Schatten q A

theorem angular_cancel (f g : ℂ → ℂ) (ζ : Boundary) (c : ℂ)
    (hf : AngularLimit f ζ c) (hg : AngularLimit g ζ (-conj c)) :
    AngularLimit (fun z => f z + conj (g z)) ζ 0 := by
  intro M hM
  simpa using (hf M hM).add ((continuous_star.tendsto (-conj c)).comp (hg M hM))

/-- R8 is a corollary of the previously reduced finite-atom theorem and generic ideal inclusion. -/
theorem atomicBoundedness (h6 : FiniteAtomConclusion) (hMono : SchattenMonotonicity) :
    AtomicBoundednessConclusion := by
  intro m hm u ζ hζ hu p hp φ ψ hsp
  obtain ⟨A, he, hs⟩ := hsp
  have aux (q : ℝ) (hq : 1 < q) (hsq : Schatten q A) :
      HasBoundedTTO (finiteProduct u) φ.val ∧ HasBoundedTTO (finiteProduct u) (star ψ.val) ∧
      (∀ j, ∃ c : ℂ, AngularLimit (analyticValue φ.val) (ζ j) c ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj c)) ∧
      (∀ j, AngularLimit (fun z => analyticValue φ.val z + conj (analyticValue ψ.val z)) (ζ j) 0) := by
    obtain ⟨hut, hnt, ⟨a, ha⟩, hstruct, hpc⟩ := h6 m hm u ζ hζ hu
    obtain ⟨E, hE, _, _, _⟩ := hstruct a ha
    obtain ⟨C, hC, hdata⟩ := hpc q hq
    have hmain := hdata a ha E hE φ ψ
    obtain ⟨c, hc⟩ := hmain.1.mp ⟨A, he, hsq⟩
    obtain ⟨X, hx, _⟩ := hc.1
    obtain ⟨Y, hy, _⟩ := hc.2
    have hang := (hmain.2.2 A he hsq).2.1 c hc |>.1
    exact ⟨⟨X, hx⟩, ⟨Y, hy⟩, (fun j => ⟨c j, hang j⟩),
      fun j => angular_cancel _ _ _ _ (hang j).1 (hang j).2⟩
  by_cases hp1 : 1 < p
  · exact aux p hp1 hs
  · exact aux 2 (by norm_num) (hMono A p 2 hp (by linarith) hs)


/-- Raw function/interpolation computations for the explicit log witness; no operator conclusion. -/
structure LogExampleData where
  u : BoundaryLInf
  inner : IsInner u
  nonconstant : Nonconstant u
  nodes : ℕ → Disk
  injective : Function.Injective nodes
  blaschke : HasBlaschkeZeros u nodes
  interpolating : Interpolating nodes
  nodes_eq : ∀ n, (nodes n).val = 1 - (2 : ℂ) ^ (-(n : ℤ) - 1)
  symbol : Hardy
  zero : analyticValue symbol.val 0 = 0
  value : ∀ z ∈ disk, analyticValue symbol.val z = -(Complex.I / (Real.pi : ℂ)) *
    Complex.log ((1 + z) / (1 - z))
  sign : ∀ᵐ t ∂circleMeasure, splitSymbol symbol.val symbol.val t =
    boundarySign t
  bound : ∀ᵐ t ∂circleMeasure, ‖splitSymbol symbol.val symbol.val t‖ ≤ 1
  unbounded : ∀ M : ℝ, ∃ n, M < ‖analyticValue symbol.val (nodes n).val‖

/-- Generic norm bound for multiplication/compression of an essentially bounded symbol. -/
def BoundedCoreNormObligation : Prop :=
  ∀ u : BoundaryLInf, ∀ σ : BoundaryL2, ∀ M : ℝ, 0 ≤ M →
    (∀ᵐ t ∂circleMeasure, ‖σ t‖ ≤ M) →
    ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A ∧ ‖A‖ ≤ M

theorem unboundedComponentsExample (h3 : InterpolatingConclusion) (hC : CoreLaws)
    (hS : ScalarAmbiguityObligation) (hB : BoundedCoreNormObligation)
    (hLog : Nonempty LogExampleData) : UnboundedComponentsConclusion := by
  classical
  let d := Classical.choice hLog
  have hnob : ¬HasBoundedTTO d.u d.symbol.val := by
    intro hb
    obtain ⟨M, hm⟩ := ((h3 d.u d.inner d.nonconstant d.nodes d.injective d.blaschke
      d.interpolating).2 d.symbol).1.mp hb
    obtain ⟨n, hn⟩ := d.unbounded M
    exact (not_lt_of_ge (hm n)) hn
  obtain ⟨A, ha, hnA⟩ := hB d.u _ 1 zero_le_one d.bound
  refine ⟨d.u, d.inner, d.nonconstant, d.nodes, d.injective, d.blaschke, d.interpolating,
    d.nodes_eq, d.symbol, d.zero, d.value, d.sign, A, ha, hnA, hnob, ?_⟩
  intro α β heq hα
  obtain ⟨c, hc, _⟩ := hS d.u d.inner d.nonconstant α d.symbol β d.symbol heq
  obtain ⟨B, hb⟩ := hα
  have hφ : RepresentsTTO d.u d.symbol.val (B - c • ContinuousLinearMap.id ℂ _) := by
    have hrep := hC.sub d.u α.val (α.val - d.symbol.val) B (c • ContinuousLinearMap.id ℂ _) hb hc
    convert hrep using 1; abel
  exact hnob ⟨_, hφ⟩


/-- Generic scalar ambiguity plus ideal algebra; no Blaschke values occur. -/
def ScalarSplitObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ φ ψ : Hardy, ∀ p : ℝ,
  ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten p A →
    (HasSchattenSplit p u A ↔ ∃ c : ℂ,
      AnalyticRemainder p u φ.val (c • ContinuousLinearMap.id ℂ _))

structure ShiftSymbolLaws : Prop where
  analytic_zero : toL2 (0 : BoundaryLInf) ∈ hardy
  zero_value : ∀ z ∈ disk, innerValue (0 : BoundaryLInf) z = 0
  zero_split : ∀ g : BoundaryLInf, splitSymbol (toL2 g) (toL2 0) = toL2 g
  analytic_shift : ∀ g : BoundaryLInf, toL2 g ∈ hardy → ∀ c : ℂ,
    toL2 (g - constLInf c) ∈ hardy
  shift_value : ∀ g : BoundaryLInf, ∀ c : ℂ, ∀ z ∈ disk,
    innerValue (g - constLInf c) z = innerValue g z - c
  shift_operator : ∀ u g : BoundaryLInf, ∀ c : ℂ, ∀ X : Model u →L[ℂ] Model u,
    RepresentsTTO u (toL2 g) X → RepresentsTTO u (toL2 (g - constLInf c))
      (X - c • ContinuousLinearMap.id ℂ _)
  unshift_operator : ∀ u g : BoundaryLInf, ∀ c : ℂ, ∀ X : Model u →L[ℂ] Model u,
    RepresentsTTO u (toL2 (g - constLInf c)) X → RepresentsTTO u (toL2 g)
      (X + c • ContinuousLinearMap.id ℂ _)
  negative_l2 : ∀ g : BoundaryLInf, toL2 (-g) = -toL2 g
  negative_value : ∀ g : BoundaryLInf, ∀ z ∈ disk, innerValue (-g) z = -innerValue g z

def AlternatingInterpolationObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ a : ℕ → Disk,
    Function.Injective a → HasBlaschkeZeros u a → ∀ p : ℝ, 0 < p →
    PerturbedKernelBasis u a {Γ | Schatten p Γ} →
      ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ ∀ n, innerValue g (a n).val = alternatingValues n

def AlternatingDivergenceObligation : Prop :=
  ∀ p : ℝ, 0 < p → ∀ c : ℂ, ¬summableValues p (fun n => alternatingValues n - c)

theorem shifted_values_iff (h4 : PerturbedBasisConclusion) (hC : CoreLaws) (hShift : ShiftSymbolLaws)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (a : ℕ → Disk)
    (ha : Function.Injective a) (hb : HasBlaschkeZeros u a) (p : ℝ) (hp : 0 < p)
    (hbase : PerturbedKernelBasis u a {Γ | Schatten p Γ})
    (g : BoundaryLInf) (hg : toL2 g ∈ hardy) (c : ℂ) :
    AnalyticRemainder p u (toL2 g) (c • ContinuousLinearMap.id ℂ _) ↔
      summableValues p (fun n => innerValue g (a n).val - c) := by
  have crit (X : Model u →L[ℂ] Model u) (hx : RepresentsTTO u (toL2 (g - constLInf c)) X) :
      Schatten p X ↔ summableValues p (fun n => innerValue g (a n).val - c) := by
    have hspl : RepresentsTTO u (splitSymbol (toL2 (g - constLInf c)) (toL2 0)) X := by
      rw [hShift.zero_split]
      exact hx
    have hh := ((h4 u hu hn a ha hb).2 (g - constLInf c) 0
      (hShift.analytic_shift g hg c) hShift.analytic_zero X hspl).2 p hp hbase
    have hv : (fun n => innerValue (g - constLInf c) (a n).val +
        conj (innerValue 0 (a n).val)) = (fun n => innerValue g (a n).val - c) := by
      funext n
      rw [hShift.shift_value g c _ (a n).property, hShift.zero_value _ (a n).property]
      simp
    exact hv ▸ hh
  constructor
  · rintro ⟨X, hx, hs⟩
    exact (crit _ (hShift.shift_operator u g c X hx)).mp hs
  · intro hw
    obtain ⟨X, hx⟩ := hC.bounded u (g - constLInf c)
    have hs := (crit X hx).mpr hw
    refine ⟨X + c • ContinuousLinearMap.id ℂ _, hShift.unshift_operator u g c X hx, ?_⟩
    exact (add_sub_cancel_right X (c • ContinuousLinearMap.id ℂ _)).symm ▸ hs

theorem blaschkeSplitting (h4 : PerturbedBasisConclusion) (hC : CoreLaws)
    (hScalar : ScalarSplitObligation) (hShift : ShiftSymbolLaws)
    (hAlt : AlternatingInterpolationObligation) (hDiv : AlternatingDivergenceObligation) :
    BlaschkeSplittingConclusion := by
  intro u hu hn a ha hb p hp hbase
  have crit : ∀ φ ψ : BoundaryLInf, toL2 φ ∈ hardy → toL2 ψ ∈ hardy →
      ∀ A : Model u →L[ℂ] Model u,
      RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A → Schatten p A →
      (HasSchattenSplit p u A ↔ ∃ c : ℂ,
        summableValues p (fun n => innerValue φ (a n).val - c)) := by
    intro φ ψ hφ hψ A he hs
    apply (hScalar u hu hn ⟨toL2 φ, hφ⟩ ⟨toL2 ψ, hψ⟩ p A he hs).trans
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, (shifted_values_iff h4 hC hShift u hu hn a ha hb p hp hbase φ hφ c).mp hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, (shifted_values_iff h4 hC hShift u hu hn a ha hb p hp hbase φ hφ c).mpr hc⟩
  refine ⟨crit, ?_⟩
  obtain ⟨φ, hφ, hv⟩ := hAlt u hu hn a ha hb p hp hbase
  obtain ⟨X, hx⟩ := hC.bounded u φ
  let A := X - X.adjoint
  have he : RepresentsTTO u (splitSymbol (toL2 φ) (toL2 (-φ))) A := by
    simpa only [A, splitSymbol, hShift.negative_l2 φ, boundary_star_neg, sub_eq_add_neg] using
      hC.sub u _ _ X X.adjoint hx (hC.adjoint u _ X hx)
  have hneg : toL2 (-φ) ∈ hardy := by
    rw [hShift.negative_l2]
    exact Submodule.neg_mem (R := ℂ) (M := BoundaryL2) hardy hφ
  have hh := ((h4 u hu hn a ha hb).2 φ (-φ) hφ hneg A he).2 p hp hbase
  have hzero : (fun n => innerValue φ (a n).val + conj (innerValue (-φ) (a n).val)) = 0 := by
    funext n
    rw [hShift.negative_value φ _ (a n).property, hv n]
    unfold alternatingValues
    split_ifs <;> simp
  have hs : Schatten p A := hh.mpr (by
    rw [hzero]
    simp only [summableValues, Pi.zero_apply, norm_zero, Real.zero_rpow hp.ne', summable_zero])
  refine ⟨φ, hφ, hv, A, he, hs, ?_⟩
  intro hsplit
  obtain ⟨c, hc⟩ := (crit φ (-φ) hφ hneg A he hs).mp hsplit
  apply hDiv p hp c
  simpa only [hv] using hc


/-- Volterra's spectral computation (E12), before any p-summability conclusion. -/
def VolterraSpectrumObligation : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ, RepresentsVolterra ℓ V →
    IsCompactOperator V ∧ ∀ n, (approximationNumber V n : ℝ) =
      ℓ / (Real.pi * ((n : ℝ) + 1 / 2))

def VolterraSeriesObligation : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ p : ℝ, 0 < p →
    (Summable (fun n : ℕ => (ℓ / (Real.pi * ((n : ℝ) + 1 / 2))) ^ p) ↔ 1 < p)

def IntervalDimensionObligation : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ¬FiniteDimensional ℂ (IntervalL2 ℓ)

def FiniteRankSchattenObligation : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ A : H →L[ℂ] H, FiniteRank A → ∀ p : ℝ, 0 < p → Schatten p A

/-- Generic unitary conjugation algebra, containing no symbols or membership criteria. -/
structure UnitaryAlgebraLaws : Prop where
  add : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K],
    ∀ U : H ≃ₗᵢ[ℂ] K, ∀ A B : H →L[ℂ] H,
      unitaryConjugate U (A + B) = unitaryConjugate U A + unitaryConjugate U B
  sub : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K],
    ∀ U : H ≃ₗᵢ[ℂ] K, ∀ A B : H →L[ℂ] H,
      unitaryConjugate U (A - B) = unitaryConjugate U A - unitaryConjugate U B
  scalar : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K],
    ∀ U : H ≃ₗᵢ[ℂ] K, ∀ c : ℂ,
      unitaryConjugate U (c • ContinuousLinearMap.id ℂ H) = c • ContinuousLinearMap.id ℂ K
  adjoint : ∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∀ U : H ≃ₗᵢ[ℂ] K, ∀ A : H →L[ℂ] H,
      unitaryConjugate U A.adjoint = (unitaryConjugate U A).adjoint

theorem endpointObstruction (hOne : OneAtomObligation) (hMono : SchattenMonotonicity)
    (hModel : ∀ ℓ : ℝ, 0 < ℓ → Nonempty (VolterraModelData ℓ))
    (hSpec : VolterraSpectrumObligation) (hSeries : VolterraSeriesObligation)
    (hDim : IntervalDimensionObligation) (hScalar : ScalarCompactObligation)
    (hI : IdealLaws) (hU : UnitaryIdealLaws) (hAlg : UnitaryAlgebraLaws)
    (hFR : FiniteRankSchattenObligation) (hC : CoreLaws) (hSplit : ScalarSplitObligation) :
    EndpointConclusion := by
  classical
  constructor
  · intro u hu hn ζ hζ φ ψ p hp hp1 hsp
    obtain ⟨A, he, hs⟩ := hsp
    have hs2 := hMono A p 2 hp (by linarith) hs
    obtain ⟨τ, hτ, hcut⟩ := hOne 2 (by norm_num)
    obtain ⟨c, X, Y, hx, hy, hsx, hsy, _⟩ := hcut u hu hn ζ hζ φ ψ A he hs2
    exact ⟨⟨X, hx⟩, ⟨Y, hy⟩, c, ⟨X, hx, hsx⟩, ⟨Y, hy, hsy⟩⟩
  · intro ℓ hℓ
    let d := Classical.choice (hModel ℓ hℓ)
    obtain ⟨hc, hvals⟩ := hSpec ℓ hℓ d.V d.volterra
    have hnot (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : ¬Schatten p d.V := by
      intro hs
      have hsum : Summable (fun n : ℕ => (ℓ / (Real.pi * ((n : ℝ) + 1 / 2))) ^ p) := by
        simpa only [hvals] using hs.2.2
      exact (not_lt_of_ge hp1) ((hSeries ℓ hℓ p hp).mp hsum)
    have hshift (c : ℂ) (hc0 : c ≠ 0) :
        ¬IsCompactOperator (d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ)) := by
      intro hh
      have hcc := hI.compact_add _ _ hc (hI.compact_neg _ hh)
      have halg : d.V + -(d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ)) =
          c • ContinuousLinearMap.id ℂ _ := by abel
      rw [halg] at hcc
      exact hc0 (hScalar (hDim ℓ hℓ) c hcc)
    have heq : d.analyticOperator = unitaryConjugate d.piModel d.V := by
      apply ContinuousLinearMap.ext
      intro x
      obtain ⟨f, rfl⟩ := d.piModel.surjective x
      change d.analyticOperator (d.piModel f) = d.piModel (d.V (d.piModel.symm (d.piModel f)))
      rw [d.piModel.symm_apply_apply]
      exact d.intertwines f
    let A := d.analyticOperator + d.analyticOperator.adjoint
    have he : RepresentsTTO d.u (splitSymbol d.symbol.val d.symbol.val) A :=
      hC.add _ _ _ _ _ d.represents (hC.adjoint _ _ _ d.represents)
    have hAe : A = unitaryConjugate d.piModel (d.V + d.V.adjoint) := by
      rw [hAlg.add, hAlg.adjoint, ← heq]
    have hsA (p : ℝ) (hp : 0 < p) : Schatten p A := by
      rw [hAe]
      apply (hU.schatten d.piModel _ p).mpr
      apply hFR _ (by exact ⟨1, d.rank_one.le⟩) p hp
    refine ⟨d, hc, hvals, hshift, A, he, hsA, ?_⟩
    intro p hp hp1
    have hnshift (c : ℂ) : ¬Schatten p (d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ)) := by
      intro hh
      by_cases hc0 : c = 0
      · subst c
        have hz : (0 : ℂ) • ContinuousLinearMap.id ℂ (IntervalL2 ℓ) = 0 := by ext x; simp
        rw [hz, sub_zero] at hh
        exact hnot p hp hp1 hh
      · exact hshift c hc0 hh.2.1
    refine ⟨hnot p hp hp1, hnshift, ?_⟩
    intro hsplit
    obtain ⟨c, X, hx, hsx⟩ := (hSplit d.u d.inner d.nonconstant d.symbol d.symbol p A he (hsA p hp)).mp hsplit
    have hX := hC.unique d.u d.inner d.nonconstant _ X d.analyticOperator hx d.represents
    subst X
    have hec : d.analyticOperator - c • ContinuousLinearMap.id ℂ _ =
        unitaryConjugate d.piModel (d.V - c • ContinuousLinearMap.id ℂ (IntervalL2 ℓ)) := by
      rw [hAlg.sub, hAlg.scalar, ← heq]
    rw [hec] at hsx
    exact hnshift c ((hU.schatten d.piModel _ p).mp hsx)


def CoordinateBoundaryObligation : Prop :=
  toL2 coordinate ∈ hardy ∧ ∀ ζ : Boundary,
    AngularLimit (analyticValue (toL2 coordinate)) ζ (fourier (T := 1) 1 ζ)

theorem twoAtomObstruction (h6 : FiniteAtomConclusion) (hC : CoreLaws) (hI : IdealLaws)
    (hAdj : AdjointLaws) (hAng : AngularUniquenessObligation) (hCoord : CoordinateBoundaryObligation)
    (hModel : ∀ a b : ℝ, 0 < a → 0 < b → Nonempty (TwoAtomShiftData a b)) :
    TwoAtomObstructionConclusion := by
  classical
  intro a b ha hb
  let d := Classical.choice (hModel a b ha hb)
  let A := d.S - d.S.adjoint
  have halg : A = d.H - d.H.adjoint := by
    dsimp [A]
    have hadd : (d.M + d.H).adjoint = d.M.adjoint + d.H.adjoint :=
      map_add ContinuousLinearMap.adjoint d.M d.H
    rw [d.equation, hadd, d.selfadjoint]
    abel
  have hs : Schatten 2 A := by
    rw [halg]
    have hh := hI.schatten_add 2 _ _ d.hilbertSchmidt
      (hI.schatten_neg 2 _ ((hAdj.schatten d.H 2).mpr d.hilbertSchmidt))
    rw [show d.H - d.H.adjoint = d.H + -d.H.adjoint from sub_eq_add_neg d.H d.H.adjoint]
    exact hh
  have he : RepresentsTTO (finiteProduct d.u) (toL2 coordinate - star (toL2 coordinate)) A :=
    hC.sub _ _ _ _ _ d.represents (hC.adjoint _ _ _ d.represents)
  let φ : Hardy := ⟨toL2 coordinate, hCoord.1⟩
  let ψ : Hardy := -φ
  have he' : RepresentsTTO (finiteProduct d.u) (splitSymbol φ.val ψ.val) A := by
    change RepresentsTTO _ (toL2 coordinate + star (-toL2 coordinate)) A
    rw [boundary_star_neg]
    exact he
  obtain ⟨hut, hnt, ⟨aa, haa⟩, hstruct, hpc⟩ := h6 2 (by norm_num) d.u d.atoms d.distinct d.factors
  obtain ⟨E, hE, _, _, _⟩ := hstruct aa haa
  obtain ⟨C, hC', hdata⟩ := hpc 2 (by norm_num)
  have hm := hdata aa haa E hE φ ψ
  obtain ⟨c, hc⟩ := hm.1.mp ⟨A, he', hs⟩
  have hang := (hm.2.2 A he' hs).2.1 c hc |>.1
  have hlocal := (hm.2.2 A he' hs).1 c |>.mp hc
  refine ⟨d, A, rfl, he, hs, ?_, ?_⟩
  · intro j
    have hval := hAng _ (d.atoms j) (c j) _ (hang j).1 (hCoord.2 (d.atoms j))
    exact hval ▸ hlocal j
  · intro hsplit
    obtain ⟨cc, hh⟩ := ((hm.2.2 A he' hs).2.2.1).mp hsplit
    have h₀ := hAng _ (d.atoms 0) cc _ (hh 0) (hCoord.2 (d.atoms 0))
    have h₁ := hAng _ (d.atoms 1) cc _ (hh 1) (hCoord.2 (d.atoms 1))
    rw [d.value₀] at h₀
    rw [d.value₁] at h₁
    have hbad : (1 : ℂ) = -1 := h₀.symm.trans h₁
    norm_num at hbad


/-- Generic Hilbert projection facts, to be replaced by the inspected native API. -/
structure ProjectionLaws : Prop where
  span_orthogonal : ∀ {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : W → H) (x : H), x ∈ (Submodule.span ℂ (Set.range k)).orthogonal ↔
      ∀ w, inner ℂ (k w) x = 0
  double : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ H), K.orthogonal.orthogonal = K.topologicalClosure
  norm_le : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (x : H), ‖Z.orthogonal.orthogonalProjectionOnto x‖ ≤ ‖x‖
  norm_eq : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (x : H),
    ‖Z.orthogonal.orthogonalProjectionOnto x‖ = ‖x‖ ↔ x ∈ Z.orthogonal
  fix : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (x : Z.orthogonal), Z.orthogonal.orthogonalProjectionOnto x.val = x
  modulo : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (x y : H), x - y ∈ Z →
    Z.orthogonal.orthogonalProjectionOnto x = Z.orthogonal.orthogonalProjectionOnto y
  inner : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (x z : H), z ∈ Z.orthogonal →
    inner ℂ z (Z.orthogonal.orthogonalProjectionOnto x).val = inner ℂ z x

/-- Ordinary closure of linear graph tests; it contains no manuscript kernels or differential expression. -/
structure GraphCoreLaws : Prop where
  range : ∀ {H K W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∀ Q : H →ₗ.[ℂ] K, ∀ a : W → H, ∀ b : W → K,
    (Submodule.span ℂ (Set.range (fun w => (a w, b w)))).topologicalClosure = Q.graph →
    ∀ Z : Submodule ℂ K, IsClosed (Z : Set K) → (∀ w, b w ∈ Z) → ∀ x : Q.domain, Q x ∈ Z
  form : ∀ {H K W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∀ Q : H →ₗ.[ℂ] K, ∀ a : W → H, ∀ b : W → K,
    (Submodule.span ℂ (Set.range (fun w => (a w, b w)))).topologicalClosure = Q.graph →
    ∀ x : Q.domain, ∀ y : H,
      (∀ w, inner ℂ (b w) (Q x) = inner ℂ (a w) y) →
      ∀ γ : Q.domain, inner ℂ (Q γ) (Q x) = inner ℂ γ.val y

def DiagonalKernelObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
  ∀ Q : Ambient u →ₗ.[ℂ] TensorModel u, (∀ η G, (η, G) ∈ Q.graph ↔ QGraph u η G) →
    Nonempty (DiagonalKernelData u Q)

private theorem eq_of_extended_squares (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ENNReal.ofReal (x ^ 2) = ENNReal.ofReal (y ^ 2)) : x = y := by
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (sq_nonneg x), ENNReal.toReal_ofReal (sq_nonneg y)] at hh
  nlinarith

set_option maxHeartbeats 400000 in
theorem squaredKernelQuotient
    (hEnergy : ∀ u : BoundaryLInf, IsInner u → Nonconstant u → EnergyIdentities u ∧
      ∃ Q : Ambient u →ₗ.[ℂ] TensorModel u, ∃ D S : Ambient u →ₗ.[ℂ] Ambient u,
        EnergyGeometry u Q D S ∧ DifferentialProperties u Q D)
    (hDiag : DiagonalKernelObligation) (hP : ProjectionLaws) (hCore : GraphCoreLaws) :
    SquaredKernelConclusion := by
  classical
  intro u hu hn
  obtain ⟨hIdent, Q, D, S, hGeom, hDiff⟩ := hEnergy u hu hn
  let d := Classical.choice (hDiag u hu hn Q hGeom.1)
  have hnull (G : TensorModel u) : G ∈ diagonalNull d ↔
      ∀ w : Disk, analyticValue₂ G.val w.val w.val = 0 := by
    exact (hP.span_orthogonal d.tensorKernel G).trans ⟨fun h w =>
      (d.diagonal_reproduces G w).trans (h w), fun h w =>
      (d.diagonal_reproduces G w).symm.trans (h w)⟩
  have hkperp (w : Disk) : d.tensorKernel w ∈ (diagonalNull d).orthogonal :=
    (Submodule.le_orthogonal_orthogonal _)
      (Submodule.subset_span ⟨w, rfl⟩)
  have hpreserve (G : TensorModel u) (w : Disk) :
      analyticValue₂ (diagonalProjection d G).val.val w.val w.val = analyticValue₂ G.val w.val w.val := by
    rw [d.diagonal_reproduces, d.diagonal_reproduces]
    exact hP.inner (diagonalNull d) G (d.tensorKernel w) (hkperp w)
  refine ⟨Q, D, S, hGeom, hDiff, d, hnull, hP.double _, hpreserve, hP.fix _, ?_, ?_, ?_, ?_⟩
  · intro G T heq
    have hmod : T - G ∈ diagonalNull d := by
      apply (hP.span_orthogonal d.tensorKernel (T - G)).mpr
      intro w
      rw [inner_sub_right, ← d.diagonal_reproduces T w, ← d.diagonal_reproduces G w, heq w]
      exact sub_self _
    have he := hP.modulo (diagonalNull d) T G hmod
    change ‖(diagonalNull d).orthogonal.orthogonalProjectionOnto G‖ ≤ ‖T‖
    rw [← he]
    exact hP.norm_le _ _
  · intro w
    refine ⟨⟨d.tensorKernel w, hkperp w⟩, rfl, ?_, ?_⟩
    · intro z
      simpa only [pow_two] using d.product_value w z z
    · intro h
      exact d.diagonal_reproduces h.val w
  · intro η
    refine ⟨?_, ?_⟩
    · intro w
      exact (hpreserve (Q η) w).trans ((hGeom.1 _ _).mp (graph_apply Q η) w.val w.property w.val w.property)
    · intro B hb hs
      obtain ⟨_, _, _, _, _, hnQ, hnB⟩ := hIdent.1 η.val
      have hqgraph := (hGeom.1 _ _).mp (graph_apply Q η)
      have hnorm : ‖Q η‖ = schattenNorm 2 B :=
        eq_of_extended_squares _ _ (norm_nonneg _) (schattenNorm_nonneg _ _)
          ((hnQ _ hqgraph).trans (hnB B hb hs).symm)
      exact ⟨(hP.norm_le _ _).trans hnorm.le, by rw [← hnorm]; exact hP.norm_eq _ _⟩
  · intro hcore
    have hrange : ∀ η : Q.domain, Q η ∈ (diagonalNull d).orthogonal :=
      hCore.range Q d.kernel d.tensorKernel hcore _ (Submodule.isClosed_orthogonal _) hkperp
    constructor
    · intro η
      exact (hP.norm_eq _ _).mpr (hrange η)
    · intro η
      constructor
      · intro hd
        have hη : η ∈ Q.domain := by
          obtain ⟨hη, _⟩ := (hGeom.2.2.2.2.2.2.2.2.2.1 η (D ⟨η, hd⟩)).mp (graph_apply D ⟨η, hd⟩)
          exact hη
        refine ⟨hη, D ⟨η, hd⟩, ?_⟩
        intro w
        exact ((hDiff.2.2.1 ⟨η, hd⟩).1 w.val w.property)
      · rintro ⟨hη, χ, hχ⟩
        have htests (w : Disk) : inner ℂ (d.tensorKernel w) (Q ⟨η, hη⟩) = inner ℂ (d.kernel w) χ := by
          rw [← d.diagonal_reproduces, ← d.ambient_reproduces, hχ w]
          exact ((hGeom.1 _ _).mp (graph_apply Q ⟨η, hη⟩) w.val w.property w.val w.property)
        have hext := hCore.form Q d.kernel d.tensorKernel hcore ⟨η, hη⟩ χ htests
        have hform := hGeom.2.2.2.2.2.2.2.2.2.1
        have hePair (γ : Q.domain) : energyPairing u η.val γ.val.val = inner ℂ (Q γ) (Q ⟨η, hη⟩) :=
          hGeom.2.2.2.2.2.2.2.2.2.2 ⟨η, hη⟩ γ
        have hdgraph : (η, χ) ∈ D.graph := (hform η χ).mpr ⟨hη, fun γ =>
          (hext γ).symm.trans (hePair γ).symm⟩
        exact domain_of_graph D hdgraph


/-- Kernel/Poisson computation and compact normalized-kernel limit, not the symbol's angular limit. -/
def AtomicBerezinObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasCanonicalMeasure u μ → ∀ ζ : Boundary, 0 < μ {ζ} →
    ∃ k : Disk → Model u, (∀ z, normalizedModelKernel u z (k z)) ∧
    (∀ X : Model u →L[ℂ] Model u, ∀ c : ℂ,
      IsCompactOperator (X - c • ContinuousLinearMap.id ℂ (Model u)) →
      ∀ M : ℝ, 1 < M → Tendsto (berezin k X) (StolzFilter ζ M) (𝓝 c)) ∧
    (∀ φ : Hardy, ∀ X : Model u →L[ℂ] Model u, RepresentsTTO u φ.val X → ∀ z ∈ disk,
      analyticValue φ.val z =
        ((1 - ‖innerValue u z‖ ^ 2 : ℝ) : ℂ) * berezin k X z + innerValue u z * poissonError u φ.val z)

/-- Singular-atom exponential decay kills the explicit Poisson error; E14 plus Cauchy--Schwarz. -/
def AtomicDecayObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ μ : Measure Boundary,
  HasCanonicalMeasure u μ → ∀ ζ : Boundary, 0 < μ {ζ} → ∀ φ : Hardy, ∀ M : ℝ, 1 < M →
    Tendsto (innerValue u) (StolzFilter ζ M) (𝓝 0) ∧
    Tendsto (fun z => innerValue u z * poissonError u φ.val z) (StolzFilter ζ M) (𝓝 0)

theorem compactScalarAngularLimit (hB : AtomicBerezinObligation) (hD : AtomicDecayObligation) :
    AtomicBoundaryConclusion := by
  intro u hu hn μ hμ ζ hζ φ c hcomp
  obtain ⟨X, hx, hc⟩ := hcomp
  obtain ⟨k, _, hβ, hid⟩ := hB u hu hn μ hμ ζ hζ
  intro M hM
  obtain ⟨hu0, herr⟩ := hD u hu hn μ hμ ζ hζ φ M hM
  have hβc := hβ X c hc M hM
  have hcoeff : Tendsto (fun z => ((1 - ‖innerValue u z‖ ^ 2 : ℝ) : ℂ))
      (StolzFilter ζ M) (𝓝 1) := by
    have hh : Tendsto (fun z => (1 : ℝ) - ‖innerValue u z‖ ^ 2)
        (StolzFilter ζ M) (𝓝 (1 - ‖(0 : ℂ)‖ ^ 2)) :=
      tendsto_const_nhds.sub (hu0.norm.pow 2)
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp hh
  have hsum := (hcoeff.mul hβc).add herr
  have heq : analyticValue φ.val =ᶠ[StolzFilter ζ M]
      (fun z => ((1 - ‖innerValue u z‖ ^ 2 : ℝ) : ℂ) * berezin k X z +
        innerValue u z * poissonError u φ.val z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hid φ X hx z hz.1
  simpa only [StolzFilter, one_mul, add_zero] using hsum.congr' heq.symm

/-- E4: a uniform finite orthogonal-block truncation bound, independent of model spaces. -/
def TriangularBoundObligation : Prop :=
  ∀ p : ℝ, 1 < p → ∃ τ : ℝ, 0 < τ ∧ TriangularConstant p τ

/-- E10: weak subsequence extraction from a bounded Schatten ball (strict p>1). -/
def SchattenWeakSubsequenceObligation : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ p : ℝ, 1 < p → ∀ B : ℝ, ∀ T : ℕ → H →L[ℂ] H,
    (∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ B) →
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ Z : H →L[ℂ] H, Schatten p Z ∧ schattenNorm p Z ≤ B ∧
      ∀ f g : H, Tendsto (fun n => inner ℂ g (T (k n) f)) atTop (𝓝 (inner ℂ g (Z f)))

/-- Own-paper regularization, equations (4)--(7): bounded cuts and a scalar *sequence*.
No scalar limit, bounded analytic extension, angular limit or splitting conclusion is supplied.
The Fourier/distribution construction is supplied separately by the Cayley foundation modules. -/
def AtomicRegularizationObligation : Prop :=
  ∀ p : ℝ, 1 < p → ∀ τ : ℝ, 0 < τ → TriangularConstant p τ →
  ∀ u : BoundaryLInf, IsInner u → Nonconstant u → ∀ ζ : Boundary, SingleAtom u ζ →
  ∀ φ ψ : Hardy, ∀ A : Model u →L[ℂ] Model u,
  RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten p A →
  ∃ M : Submodule ℂ (Model u), Dense (M : Set (Model u)) ∧
    (∀ f : M, IsBounded f.val.val) ∧ ∃ e : M, inner ℂ e.val e.val = 1 ∧
    ∃ T : ℕ → Model u →L[ℂ] Model u, ∃ μ : ℕ → ℂ,
      (∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ τ * schattenNorm p A) ∧
      ∀ f g : M, Tendsto (fun n => inner ℂ g.val (T n f.val) -
        coreForm φ.val f.val.val g.val.val - μ n * inner ℂ g.val f.val) atTop (𝓝 0)

/-- Lemma 1's generic dense-core extension step, for any L² symbol. -/
def DenseCoreExtensionObligation : Prop :=
  ∀ u : BoundaryLInf, ∀ σ : BoundaryL2, ∀ Z : Model u →L[ℂ] Model u,
  ∀ M : Submodule ℂ (Model u), Dense (M : Set (Model u)) →
  (∀ f : M, IsBounded f.val.val) →
  (∀ f g : M, inner ℂ g.val (Z f.val) = coreForm σ f.val.val g.val.val) → RepresentsTTO u σ Z

/-- The explicit single atom also supplies its canonical measure; no general factorization is assumed here. -/
def SingleAtomMeasureObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → ∀ ζ : Boundary, SingleAtom u ζ →
    ∃ μ : Measure Boundary, HasCanonicalMeasure u μ ∧ 0 < μ {ζ}

set_option maxHeartbeats 400000 in
theorem oneAtomSplitting (hT : TriangularBoundObligation)
    (hW : SchattenWeakSubsequenceObligation) (hR : AtomicRegularizationObligation)
    (hD : DenseCoreExtensionObligation) (hC : CoreLaws) (hI : IdealLaws)
    (hN : SchattenNormLaws) (hS : ScalarCompactObligation) (hDim : SingleAtomDimensionObligation)
    (hM : SingleAtomMeasureObligation) (hB : AtomicBoundaryConclusion) (hAdj : AdjointLaws) :
    OneAtomConclusion := by
  classical
  intro p hp
  obtain ⟨τ, hτ, ht⟩ := hT p hp
  refine ⟨τ,hτ,ht,?_⟩
  intro u hu hn ζ hζ φ ψ A ha hs
  obtain ⟨M,hd,hbd,e,he,T,μ,hTn,herr⟩ := hR p hp τ hτ ht u hu hn ζ hζ φ ψ A ha hs
  obtain ⟨k,hk,Z,hZ,hZn,hlim⟩ := hW (Model u) p hp _ T hTn
  let c : ℂ := -(inner ℂ e.val (Z e.val) - coreForm φ.val e.val.val e.val.val)
  have hμ : Tendsto (fun n => μ (k n)) atTop (𝓝 (-c)) := by
    have hh := ((hlim e.val e.val).sub (tendsto_const_nhds (x := coreForm φ.val e.val.val e.val.val))).sub ((herr e e).comp hk.tendsto_atTop)
    simp only [he, mul_one, sub_zero] at hh
    simp only [c, neg_neg]
    convert hh using 1
    funext n
    simp only [Function.comp_apply]
    ring
  have hcoeff (f g : M) : inner ℂ g.val (Z f.val) =
      coreForm φ.val f.val.val g.val.val - c * inner ℂ g.val f.val := by
    have hh := ((hlim f.val g.val).sub (tendsto_const_nhds (x := coreForm φ.val f.val.val g.val.val))).sub (hμ.mul (tendsto_const_nhds (x := inner ℂ g.val f.val)))
    have hzero := tendsto_nhds_unique hh ((herr f g).comp hk.tendsto_atTop)
    linear_combination hzero
  let X := Z + c • ContinuousLinearMap.id ℂ (Model u)
  have hx : RepresentsTTO u φ.val X := by
    apply hD u φ.val X M hd hbd
    intro f g
    change inner ℂ g.val (Z f.val + c • f.val) = _
    have hi : inner ℂ g.val (c • f.val) = c * inner ℂ g.val f.val :=
      inner_smul_right g.val f.val c
    rw [inner_add_right, hi, hcoeff]
    ring
  let Y := A - X
  have hy : RepresentsTTO u (star ψ.val) Y := by
    have hh := hC.sub u (splitSymbol φ.val ψ.val) φ.val A X ha hx
    simpa only [splitSymbol, add_sub_cancel_left] using hh
  have hxe : X - c • ContinuousLinearMap.id ℂ (Model u) = Z := by simp [X]
  have hye : Y + c • ContinuousLinearMap.id ℂ (Model u) = A - Z := by dsimp [Y,X]; abel
  have hsy : Schatten p (Y + c • ContinuousLinearMap.id ℂ _) := by
    rw [hye]
    rw [sub_eq_add_neg A Z]
    exact hI.schatten_add p A (-Z) hs (hI.schatten_neg p Z hZ)
  have hyn : schattenNorm p (Y + c • ContinuousLinearMap.id ℂ _) ≤ (1+τ) * schattenNorm p A := by
    rw [hye]
    have hh := hN.sub_bound p A Z (le_of_lt hp) hs hZ
    nlinarith
  have huniq (d : ℂ) (hd' : AnalyticRemainder p u φ.val (d • ContinuousLinearMap.id ℂ _)) : d = c :=
    scalar_remainder_unique hC hI hS u hu hn (hDim u hu hn ζ hζ) φ.val p d c hd'
      ⟨X,hx,hxe ▸ hZ⟩
  refine ⟨⟨X,hx⟩,⟨Y,hy⟩,⟨c,⟨⟨X,hx,hxe ▸ hZ⟩,⟨Y,hy,hsy⟩⟩,fun d hd' => huniq d hd'.1⟩,?_⟩
  intro d hd' _
  have hdc := huniq d hd'
  subst d
  obtain ⟨ν,hν,hνζ⟩ := hM u hu ζ hζ
  have hangφ := hB u hu hn ν hν ζ hνζ φ c ⟨X,hx,(hxe ▸ hZ).2.1⟩
  have hyψ : RepresentsTTO u ψ.val Y.adjoint := by
    simpa only [star_star] using hC.adjoint u (star ψ.val) Y hy
  have hadj : (Y + c • ContinuousLinearMap.id ℂ (Model u)).adjoint =
      Y.adjoint - (-conj c) • ContinuousLinearMap.id ℂ (Model u) := by
    simp only [map_add, map_smulₛₗ, ContinuousLinearMap.adjoint_id, sub_eq_add_neg]
    congr 1
    exact ((neg_smul (-conj c) (ContinuousLinearMap.id ℂ (Model u))).symm.trans (by rw [neg_neg])).symm
  have hangψ := hB u hu hn ν hν ζ hνζ ψ (-conj c)
    ⟨Y.adjoint,hyψ,hadj ▸ (hAdj.schatten _ p).mpr hsy |>.2.1⟩
  refine ⟨hangφ,hangψ,?_⟩
  intro X' Y' hx' hy'
  have hxEq := hC.unique u hu hn φ.val X' X hx' hx
  have hyEq := hC.unique u hu hn (star ψ.val) Y' Y hy' hy
  subst X'; subst Y'
  exact ⟨hxe ▸ hZn,hyn⟩

def finiteDiagonal {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)]
    [∀ j, NormedSpace ℂ (H j)] (T : (j : Fin m) → H j →L[ℂ] H j) : PiLp 2 H →L[ℂ] PiLp 2 H :=
  (PiLp.continuousLinearEquiv 2 ℂ H).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.piMap T ∘L (PiLp.continuousLinearEquiv 2 ℂ H).toContinuousLinearMap

def finiteSingle {m : ℕ} (H : Fin m → Type) [∀ j, NormedAddCommGroup (H j)]
    [∀ j, NormedSpace ℂ (H j)] (j : Fin m) : H j →L[ℂ] PiLp 2 H :=
  (PiLp.continuousLinearEquiv 2 ℂ H).symm.toContinuousLinearMap ∘L ContinuousLinearMap.single ℂ H j

def coordinateResolution {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)]
    [∀ j, NormedSpace ℂ (H j)] {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (W : PiLp 2 H ≃L[ℂ] K) (j : Fin m) : K →L[ℂ] K :=
  W.toContinuousLinearMap ∘L finiteSingle H j ∘L PiLp.proj 2 H j ∘L W.symm.toContinuousLinearMap

def localBlock {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)]
    [∀ j, NormedSpace ℂ (H j)] {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (W : PiLp 2 H ≃L[ℂ] K) (A : K →L[ℂ] K) (j : Fin m) : H j →L[ℂ] H j :=
  PiLp.proj 2 H j ∘L W.symm.toContinuousLinearMap ∘L A ∘L W.toContinuousLinearMap ∘L finiteSingle H j

/-- Generic finite-coordinate algebra only; no symbols, corona hypotheses or operator ideals. -/
structure CoordinateResolutionLaws : Prop where
  sum : ∀ {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] (W : PiLp 2 H ≃L[ℂ] K),
    (∑ j, coordinateResolution W j) = ContinuousLinearMap.id ℂ K
  idempotent : ∀ {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] (W : PiLp 2 H ≃L[ℂ] K) (j : Fin m),
    coordinateResolution W j ∘L coordinateResolution W j = coordinateResolution W j
  disjoint : ∀ {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] (W : PiLp 2 H ≃L[ℂ] K) (i j : Fin m), i ≠ j →
    coordinateResolution W i ∘L coordinateResolution W j = 0
  range : ∀ {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]
    {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] (W : PiLp 2 H ≃L[ℂ] K) (j : Fin m),
    (coordinateResolution W j).toLinearMap.range =
      (W.toContinuousLinearMap ∘L finiteSingle H j).toLinearMap.range

/-- Lemma 1 for a dense bounded test set; no spectral conclusion is part of this input. -/
def DenseCoreSetObligation : Prop :=
  ∀ u : BoundaryLInf, ∀ σ : BoundaryL2, ∀ Z : Model u →L[ℂ] Model u,
  ∀ S : Set (Model u), Dense S → (∀ f ∈ S, IsBounded f.val) →
  (∀ f ∈ S, ∀ g ∈ S, inner ℂ g (Z f) = coreForm σ f.val g.val) → RepresentsTTO u σ Z

/-- Concrete inverse/projection/core calculations. Candidate operators are explicitly computed;
no bounded-extension existence or Schatten classification is included in these data. -/
structure GluingGraphData {m : ℕ} (u a : Fin m → BoundaryLInf)
    (W : FiniteModelSum u ≃L[ℂ] Model (finiteProduct u)) : Prop where
  forward : ∀ g, (W g).val = ∑ j, multiply (cofactor u j) (g j).val
  inverse : ∀ x, ∀ j, (W.symm x j).val =
    ((model (u j)).orthogonalProjectionOnto (multiply (a j) x.val)).val
  core : ∀ γ : Hardy, ∀ g : FiniteModelSum u, (∀ j, IsBounded (g j).val) →
    IsBounded (W g).val ∧ ∃ y : FiniteModelSum u,
      (∀ j, CoreValue (u j) γ.val (g j) (y j)) ∧ CoreValue (finiteProduct u) γ.val (W g) (W y)
  dense : Dense (W '' {g : FiniteModelSum u | ∀ j, IsBounded (g j).val})
  local_coeff : ∀ γ : Hardy, ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
    RepresentsTTO (finiteProduct u) γ.val A → ∀ j, ∀ f g : Model (u j),
    IsBounded f.val → IsBounded g.val →
      inner ℂ g (localBlock W A j f) = coreForm γ.val f.val g.val
  diagonal : ∀ γ : Hardy, ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
    RepresentsTTO (finiteProduct u) γ.val A → ∀ g,
      A (W g) = W (WithLp.toLp 2 (fun j => localBlock W A j (g j)))
  global_coeff : ∀ γ : Hardy, ∀ T : (j : Fin m) → Model (u j) →L[ℂ] Model (u j),
    (∀ j, RepresentsTTO (u j) γ.val (T j)) → ∀ g h : FiniteModelSum u,
    (∀ j, IsBounded (g j).val) → (∀ j, IsBounded (h j).val) →
      inner ℂ (W h) (W (finiteDiagonal T g)) = coreForm γ.val (W g).val (W h).val
  coordinate_symbol : ∀ a', Bezout u a' → ∀ j,
    RepresentsTTO (finiteProduct u) (toL2 (multiplyInf (a' j) (cofactor u j))) (coordinateResolution W j)

/-- Raw inverse/projection/core computations from Lemma 9; the model identities are supplied by the proof modules. -/
def GluingGraphObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf,
    (∀ j, IsInner (u j) ∧ Nonconstant (u j)) → Corona u →
    ∀ a, Bezout u a →
    ∃ F : FiniteModelSum u →L[ℂ] Model (finiteProduct u),
    ∃ G : Model (finiteProduct u) →L[ℂ] FiniteModelSum u,
    ∃ hL : Function.LeftInverse G F, ∃ hR : Function.RightInverse G F,
      GluingGraphData u a (ContinuousLinearEquiv.equivOfInverse F G hL hR)

/-- Product/Bezout existence (E8 plus finite cofactor algebra), with no idempotent conclusions. -/
def CoronaWitnessObligation : Prop :=
  ∀ m : ℕ, 0 < m → ∀ u : Fin m → BoundaryLInf,
    (∀ j, IsInner (u j) ∧ Nonconstant (u j)) → Corona u →
    IsInner (finiteProduct u) ∧ Nonconstant (finiteProduct u) ∧ ∃ a, Bezout u a

theorem GluingGraphData.local_graph {m : ℕ} {u a : Fin m → BoundaryLInf}
    {W : FiniteModelSum u ≃L[ℂ] Model (finiteProduct u)} (d : GluingGraphData u a W)
    (γ : Hardy) (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hA : RepresentsTTO (finiteProduct u) γ.val A) :
    ∃ T : (j : Fin m) → Model (u j) →L[ℂ] Model (u j),
      (∀ j, RepresentsTTO (u j) γ.val (T j)) ∧
      ∀ g, A (W g) = W (WithLp.toLp 2 (fun j => T j (g j))) :=
  ⟨localBlock W A,d.local_coeff γ A hA,d.diagonal γ A hA⟩

theorem GluingGraphData.global_graph {m : ℕ} {u a : Fin m → BoundaryLInf}
    {W : FiniteModelSum u ≃L[ℂ] Model (finiteProduct u)} (d : GluingGraphData u a W)
    (hD : DenseCoreSetObligation) (γ : Hardy)
    (T : (j : Fin m) → Model (u j) →L[ℂ] Model (u j)) (hT : ∀ j, RepresentsTTO (u j) γ.val (T j)) :
    ∃ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u), RepresentsTTO (finiteProduct u) γ.val A ∧
      ∀ g, A (W g) = W (WithLp.toLp 2 (fun j => T j (g j))) := by
  let A := W.toContinuousLinearMap ∘L finiteDiagonal T ∘L W.symm.toContinuousLinearMap
  have hi (g : FiniteModelSum u) : A (W g) = W (finiteDiagonal T g) := by simp [A]
  refine ⟨A,?_,hi⟩
  apply hD (finiteProduct u) γ.val A _ d.dense
  · rintro _ ⟨g,hg,rfl⟩
    exact (d.core γ g hg).1
  · rintro _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩
    rw [hi]
    exact d.global_coeff γ T hT g h hg hh

theorem GluingGraphData.single_formula {m : ℕ} {u a : Fin m → BoundaryLInf}
    {W : FiniteModelSum u ≃L[ℂ] Model (finiteProduct u)} (d : GluingGraphData u a W)
    (j : Fin m) (f : Model (u j)) :
    (W (finiteSingle (fun i => Model (u i)) j f)).val = multiply (cofactor u j) f.val := by
  classical
  rw [d.forward]
  simp [finiteSingle, ContinuousLinearMap.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Generic finite Hilbert-block similarity, with no inner functions or symbols. -/
def FiniteBlockSchattenObligation : Prop :=
  ∀ m : ℕ, ∀ (H : Fin m → Type),
  ∀ [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)] [∀ j, CompleteSpace (H j)],
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
  ∀ W : PiLp 2 H ≃L[ℂ] K, ∀ A : K →L[ℂ] K, ∀ T : (j : Fin m) → H j →L[ℂ] H j,
    (∀ g, A (W g) = W (WithLp.toLp 2 (fun j => T j (g j)))) →
      ∀ p : ℝ, 0 < p → (Schatten p A ↔ ∀ j, Schatten p (T j))

structure ConstantCoreLaws : Prop where
  hardy : ∀ c : ℂ, constL2 c ∈ hardy
  represents : ∀ u : BoundaryLInf, ∀ c : ℂ,
    RepresentsTTO u (constL2 c) (c • ContinuousLinearMap.id ℂ (Model u))

theorem shifted_schatten (hC : CoreLaws) (hK : ConstantCoreLaws) (p : ℝ)
    (u : BoundaryLInf) (φ : Hardy) (c : ℂ) :
    HasSchattenTTO p u (φ.val - constL2 c) ↔
      AnalyticRemainder p u φ.val (c • ContinuousLinearMap.id ℂ _) := by
  constructor
  · rintro ⟨Z,hZ,hs⟩
    refine ⟨Z + c • ContinuousLinearMap.id ℂ _, ?_, ?_⟩
    · simpa only [sub_add_cancel] using hC.add u (φ.val - constL2 c) (constL2 c) Z
        (c • ContinuousLinearMap.id ℂ _) hZ (hK.represents u c)
    · rw [add_sub_cancel_right Z (c • ContinuousLinearMap.id ℂ (Model u))]
      exact hs
  · rintro ⟨X,hX,hs⟩
    exact ⟨X - c • ContinuousLinearMap.id ℂ _,
      hC.sub u φ.val (constL2 c) X _ hX (hK.represents u c), hs⟩

set_option maxHeartbeats 400000 in
theorem analyticGluing (hC : CoreLaws) (hCo : CoronaWitnessObligation)
    (hG : GluingGraphObligation) (hD : DenseCoreSetObligation) (hQ : CoordinateResolutionLaws) (hF : FiniteBlockSchattenObligation)
    (hK : ConstantCoreLaws) (hSplit : ScalarSplitObligation) : AnalyticGluingConclusion := by
  classical
  intro m hm u hu hc
  obtain ⟨hi,hn,hb⟩ := hCo m hm u hu hc
  refine ⟨hb,?_⟩
  intro a ha
  obtain ⟨F,G,hL,hR,d⟩ := hG m hm u hu hc a ha
  let W := ContinuousLinearEquiv.equivOfInverse F G hL hR
  have hbdd (γ : Hardy) : HasBoundedTTO (finiteProduct u) γ.val ↔ ∀ j, HasBoundedTTO (u j) γ.val := by
    constructor
    · rintro ⟨A,hA⟩
      obtain ⟨T,hT,_⟩ := d.local_graph γ A hA
      exact fun j => ⟨T j,hT j⟩
    · intro hh
      choose T hT using hh
      obtain ⟨A,hA,_⟩ := d.global_graph hD γ T hT
      exact ⟨A,hA⟩
  have hsp (γ : Hardy) (p : ℝ) (hp : 0 < p) :
      HasSchattenTTO p (finiteProduct u) γ.val ↔ ∀ j, HasSchattenTTO p (u j) γ.val := by
    constructor
    · rintro ⟨A,hA,hs⟩
      obtain ⟨T,hT,hdiag⟩ := d.local_graph γ A hA
      have ht := (hF m (fun j => Model (u j)) (Model (finiteProduct u)) W A T hdiag p hp).mp hs
      exact fun j => ⟨T j,hT j,ht j⟩
    · intro hh
      choose T hT hs using hh
      obtain ⟨A,hA,hdiag⟩ := d.global_graph hD γ T hT
      exact ⟨A,hA,(hF m (fun j => Model (u j)) (Model (finiteProduct u)) W A T hdiag p hp).mpr hs⟩
  refine ⟨W,d.forward,d.inverse,d.core,?_,?_,?_⟩
  · intro γ
    refine ⟨hbdd γ,hsp γ,?_⟩
    intro A hA T hT g
    obtain ⟨T',hT',hdiag⟩ := d.local_graph γ A hA
    have heq : T' = T := by
      funext j
      exact hC.unique (u j) (hu j).1 (hu j).2 γ.val (T' j) (T j) (hT' j) (hT j)
    exact heq ▸ hdiag g
  · let E := coordinateResolution W
    have he : RepresentsIdempotents u a E := d.coordinate_symbol a ha
    refine ⟨E,he,⟨hQ.sum W,hQ.idempotent W,hQ.disjoint W⟩,?_,?_,?_⟩
    · intro j
      change (coordinateResolution W j).toLinearMap.range.map (model (finiteProduct u)).subtype = _
      rw [hQ.range W j]
      ext f
      constructor
      · rintro ⟨x,⟨g,rfl⟩,rfl⟩
        exact ⟨g,(d.single_formula j g).symm⟩
      · rintro ⟨g,rfl⟩
        exact ⟨W (finiteSingle (fun i => Model (u i)) j g),⟨g,rfl⟩,d.single_formula j g⟩
    · intro j g
      change W (finiteSingle (fun i => Model (u i)) j (W.symm (W g) j)) = _
      rw [W.symm_apply_apply]
      apply congrArg W
      apply (WithLp.equiv 2 _).injective
      funext k
      change (Pi.single j (g j) : (i : Fin m) → Model (u i)) k = if k = j then g k else 0
      by_cases h : k = j
      · subst k; simp
      · simp [h]
    · intro a' E' ha' he'
      funext j
      exact hC.unique (finiteProduct u) hi hn _ (E' j) (E j) (he' j) (d.coordinate_symbol a' ha' j)
  · intro p hp φ ψ A hA hs
    rw [hSplit (finiteProduct u) hi hn φ ψ p A hA hs]
    apply exists_congr
    intro c
    let γ : Hardy := ⟨φ.val - constL2 c, Submodule.sub_mem hardy φ.property (hK.hardy c)⟩
    calc
      AnalyticRemainder p (finiteProduct u) φ.val (c • ContinuousLinearMap.id ℂ _) ↔
          HasSchattenTTO p (finiteProduct u) γ.val := (shifted_schatten hC hK p _ φ c).symm
      _ ↔ ∀ j, HasSchattenTTO p (u j) γ.val := hsp γ p hp
      _ ↔ ∀ j, AnalyticRemainder p (u j) φ.val (c • ContinuousLinearMap.id ℂ _) :=
        forall_congr' (fun j => shifted_schatten hC hK p (u j) φ c)

/-- Extract the local input used by T6 from the full standalone Lemma 8 contract. -/
theorem oneAtomExtraction (h : OneAtomConclusion) : OneAtomObligation := by
  intro p hp
  obtain ⟨τ,hτ,_,ht⟩ := h p hp
  refine ⟨τ,hτ,?_⟩
  intro u hu hn ζ hζ φ ψ A ha hs
  obtain ⟨_,_,⟨c,hc,_⟩,hd⟩ := ht u hu hn ζ hζ φ ψ A ha hs
  obtain ⟨X,hx,hsx⟩ := hc.1
  obtain ⟨Y,hy,hsy⟩ := hc.2
  obtain ⟨hφ,hψ,hb⟩ := hd c ⟨X,hx,hsx⟩ ⟨Y,hy,hsy⟩
  exact ⟨c,X,Y,hx,hy,hsx,hsy,(hb X Y hx hy).1,(hb X Y hx hy).2,hφ,hψ⟩

end Reduction

end TTO.Paper
