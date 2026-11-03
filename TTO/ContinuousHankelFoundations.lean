/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CompactHankelFoundations

/-! Continuous symbols give actual compact classical Hankel operators.
The finite-basis-support and Fourier-density arguments narrowly adapt the Apache-2.0
Tau Ceti HilbertBasis/Basic.lean:43 and Fourier/Hardy/Compact.lean:55–86,
revision d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad. No Tau dependency is imported. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

local instance continuousHankelOperatorNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance continuousHankelOperatorNormedSpace : NormedSpace ℂ HankelOperator := inferInstance

/-- A map killing every basis vector outside a finite set has genuinely finite-dimensional range. -/
theorem rank_le_of_finite_basis_support
    {I E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : HilbertBasis I ℂ E) (T : E →L[ℂ] F) (s : Finset I)
    (hT : ∀ i,i∉s→T (b i)=0) : T.rank≤(s.card : Cardinal) := by
  classical
  have hRange : T.range≤Submodule.span ℂ ((fun i => T (b i)) '' (s : Set I)) := by
    rintro _ ⟨x,rfl⟩
    have hsum := T.hasSum (b.hasSum_repr x)
    rw [ContinuousLinearMap.coe_coe,hsum.unique (hasSum_sum_of_ne_finset_zero (fun i hi => by rw [map_smul,hT i hi,smul_zero]))]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  calc
    _ ≤ Module.rank ℂ (Submodule.span ℂ ((fun i => T (b i)) '' (s : Set I))) := Submodule.rank_mono hRange
    _ ≤ (s.card : Cardinal) := by
      rw [←Finset.coe_image]
      exact (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le)

theorem compact_of_finite_basis_support
    {I E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : HilbertBasis I ℂ E) (T : E →L[ℂ] F) (s : Finset I)
    (hT : ∀ i,i∉s→T (b i)=0) : IsCompactOperator T := by
  have hRank := rank_le_of_finite_basis_support b T s hT
  let : FiniteDimensional ℂ T.range := Module.rank_lt_aleph0_iff.mp
    (hRank.trans_lt (Cardinal.natCast_lt_aleph0 (n:=s.card)))
  exact (isCompactOperator_of_locallyCompactSpace_dom T.rangeRestrict).clm_comp T.range.subtypeL

def boundedHankelOperator (a : BoundaryLInf) : HankelOperator :=
  hardy.orthogonal.orthogonalProjectionOnto ∘L multiply a ∘L hardy.subtypeL

def boundedHankelSymbolMap : BoundaryLInf →L[ℂ] HankelOperator :=
  ContinuousLinearMap.postcomp Hardy hardy.orthogonal.orthogonalProjectionOnto ∘L
    ContinuousLinearMap.precomp BoundaryL2 hardy.subtypeL ∘L
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ 2 2

@[simp] theorem boundedHankelSymbolMap_apply (a : BoundaryLInf) :
    boundedHankelSymbolMap a=boundedHankelOperator a := rfl

theorem boundedHankelOperator_represents (a : BoundaryLInf) :
    RepresentsHankel (toL2 a) (boundedHankelOperator a) := by
  intro f g _hf _hg
  have hi : inner ℂ g (boundedHankelOperator a f)=inner ℂ g.val (multiply a f.val) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left g _
  rw [hi,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae a f.val,toL2_ae a] with t hm ht
  simp only [RCLike.inner_apply,hm,ht]

theorem boundedHankelOperator_mode_kills (m : ℤ) (j : ℕ) (h : 0≤m+(j : ℤ)) :
    boundedHankelOperator (mode m) (hardyBasis j)=0 := by
  have he : multiply (mode m) (hardyBasis j).val=fourierBasis (T:=1) (m+(j : ℤ)) := by
    rw [hardyBasis_apply]
    change multiply (mode m) (fourierBasis (T:=1) (j : ℤ))=fourierBasis (T:=1) (m+(j : ℤ))
    apply Lp.ext
    filter_upwards [multiply_ae (mode m) (fourierBasis (T:=1) (j : ℤ)),mode_ae m,
      fourierBasis_ae (j : ℤ),fourierBasis_ae (m+(j : ℤ))] with t hm ha hj hsum
    rw [hm,ha,hj,hsum,←fourier_add]
  have hm : multiply (mode m) (hardyBasis j).val∈hardy := by
    rw [he]
    obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le h
    rw [hk]
    exact fourierBasis_mem_hardy k
  change hardy.orthogonal.orthogonalProjectionOnto (multiply (mode m) (hardyBasis j).val)=0
  exact hardy.orthogonalProjectionOnto_orthogonal_apply_eq_zero hm

theorem compact_boundedHankelOperator_mode (m : ℤ) : IsCompactOperator (boundedHankelOperator (mode m)) := by
  apply compact_of_finite_basis_support hardyBasis _ (Finset.range (-m).toNat)
  intro j hj
  apply boundedHankelOperator_mode_kills
  simp only [Finset.mem_range,not_lt] at hj
  omega


/-- The actual bounded continuous-symbol-to-Hankel map. -/
def continuousHankelSymbolMap : C(Boundary,ℂ) →L[ℂ] HankelOperator :=
  boundedHankelSymbolMap ∘L ContinuousMap.toLp ∞ circleMeasure ℂ

theorem toL2_continuousSymbol (a : C(Boundary,ℂ)) :
    toL2 (ContinuousMap.toLp ∞ circleMeasure ℂ a)=ContinuousMap.toLp 2 circleMeasure ℂ a := by
  apply Lp.ext
  filter_upwards [toL2_ae (ContinuousMap.toLp ∞ circleMeasure ℂ a),
    ContinuousMap.coeFn_toLp (p:=∞) (𝕜:=ℂ) circleMeasure a,
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure a] with t h2 hi hc
  rw [h2,hi,hc]

theorem continuousHankelSymbolMap_represents (a : C(Boundary,ℂ)) :
    RepresentsHankel (ContinuousMap.toLp 2 circleMeasure ℂ a) (continuousHankelSymbolMap a) := by
  have h := boundedHankelOperator_represents (ContinuousMap.toLp ∞ circleMeasure ℂ a)
  rw [toL2_continuousSymbol] at h
  exact h

/-- Continuous symbols have compact Hankel operators, proved from finite Fourier
support, native uniform density, and the closed subspace of compact operators. -/
theorem compact_continuousHankelSymbolMap (a : C(Boundary,ℂ)) :
    IsCompactOperator (continuousHankelSymbolMap a) := by
  let K : Submodule ℂ C(Boundary,ℂ) :=
    (compactOperator (RingHom.id ℂ) Hardy ↥hardy.orthogonal).comap continuousHankelSymbolMap.toLinearMap
  have hK : IsClosed (K : Set C(Boundary,ℂ)) :=
    isClosed_setOfPred_isCompactOperator.preimage continuousHankelSymbolMap.continuous
  have hSpan : Submodule.span ℂ (Set.range (fourier (T:=1)))≤K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m,rfl⟩
    change IsCompactOperator (boundedHankelOperator (mode m))
    exact compact_boundedHankelOperator_mode m
  have ha : a∈(Submodule.span ℂ (Set.range (fourier (T:=1)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  exact Submodule.topologicalClosure_minimal _ hSpan hK ha

theorem hasCompactHankel_continuousSymbol (a : C(Boundary,ℂ)) :
    HasCompactHankel (ContinuousMap.toLp 2 circleMeasure ℂ a) :=
  ⟨continuousHankelSymbolMap a,continuousHankelSymbolMap_represents a,compact_continuousHankelSymbolMap a⟩

/-- Every represented operator with a genuine continuous equivalent symbol is compact. -/
theorem compactHankel_of_same_continuousSymbol (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (a : C(Boundary,ℂ))
    (hSame : SameHankel σ (ContinuousMap.toLp 2 circleMeasure ℂ a)) : IsCompactOperator H := by
  have hA : RepresentsHankel σ (continuousHankelSymbolMap a) := by
    intro f g hf hg
    exact (continuousHankelSymbolMap_represents a f g hf hg).trans (hSame f g hf hg).symm
  have he := representsHankel_unique σ H (continuousHankelSymbolMap a) hH hA
  rw [he]
  exact compact_continuousHankelSymbolMap a

/-- The continuous-representative-to-compact direction of Hartman's equivalence. -/
theorem continuousHankel_lift_implies_compact (σ : BoundaryL2)
    (hLift : ∃ a : C(Boundary,ℂ), SameHankel σ (ContinuousMap.toLp 2 circleMeasure ℂ a)) :
    HasCompactHankel σ := by
  obtain ⟨a,hSame⟩ := hLift
  refine ⟨continuousHankelSymbolMap a,?_,compact_continuousHankelSymbolMap a⟩
  intro f g hf hg
  exact (continuousHankelSymbolMap_represents a f g hf hg).trans (hSame f g hf hg).symm

end TTO.Paper.Proved
