/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ModelNestFoundations
public import TTO.CoordinateOrthogonalFoundations
public import TTO.DiscreteGapRootFoundations
public import TTO.GapProjectionFoundations

/-! Finite bounded-core matrix reconstruction for an actual analytic gap. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Actual bounded core multiplication commutes with multiplication in its symbol. -/
theorem coreMultiply_inner_symbol (v : BoundaryLInf) (q f : BoundaryL2) (hf : IsBounded f) :
    coreMultiply (multiply v q) ⟨f, hf⟩ = multiply v (coreMultiply q ⟨f, hf⟩) := by
  change multiply (hf.toLp f) (multiply v q) = multiply v (multiply (hf.toLp f) q)
  exact multiply_comm _ _ _

/-- An analytic symbol has no strictly upper block in the genuine power-model nest. -/
theorem analytic_power_block_zero (v : BoundaryLInf) (hv : IsInner v) (γ : Hardy)
    (i j : ℕ) (hij : i < j) (f g : Model v) (hf : IsBounded f.val) :
    coreForm γ.val (multiply (powerInf v j) f.val) (multiply (powerInf v i) g.val) = 0 := by
  rw [coreForm_eq_inner_left _ _ _ (bounded_multiply _ _ hf)]
  change inner ℂ (multiply (powerInf v i) g.val)
    (coreMultiply γ.val ⟨multiply (powerInf v j) f.val, bounded_multiply _ _ hf⟩) = 0
  rw [coreMultiply_multiply]
  apply inner_eq_zero_symm.mp
  exact inner_multiply_model (powerInf v j)
    ⟨multiply (powerInf v i) g.val, power_model_block_mem v hv j i hij g⟩
    ⟨coreMultiply γ.val ⟨f.val, hf⟩, coreMultiply_mem_hardy γ ⟨f.val, f.property.1⟩ hf⟩

/-- One genuine inner factor in the analytic symbol removes every diagonal block as well. -/
theorem gap_power_block_zero (v : BoundaryLInf) (hv : IsInner v) (q : Hardy)
    (i j : ℕ) (hij : i ≤ j) (f g : Model v) (hf : IsBounded f.val) :
    coreForm (multiply v q.val) (multiply (powerInf v j) f.val)
      (multiply (powerInf v i) g.val) = 0 := by
  rw [coreForm_eq_inner_left _ _ _ (bounded_multiply _ _ hf)]
  change inner ℂ (multiply (powerInf v i) g.val)
    (coreMultiply (multiply v q.val)
      ⟨multiply (powerInf v j) f.val, bounded_multiply _ _ hf⟩) = 0
  rw [coreMultiply_multiply, coreMultiply_inner_symbol, multiply_assoc]
  have hp : multiplyInf (powerInf v j) v = powerInf v (j + 1) :=
    multiplyInf_comm (powerInf v j) v
  rw [hp]
  apply inner_eq_zero_symm.mp
  exact inner_multiply_model (powerInf v (j + 1))
    ⟨multiply (powerInf v i) g.val, power_model_block_mem v hv (j + 1) i (by omega) g⟩
    ⟨coreMultiply q.val ⟨f.val, hf⟩, coreMultiply_mem_hardy q ⟨f.val, f.property.1⟩ hf⟩

/-- The coanalytic symbol has no strictly lower block; both bounded test inputs are explicit. -/
theorem coanalytic_power_block_zero (v : BoundaryLInf) (hv : IsInner v) (ψ : Hardy)
    (i j : ℕ) (hij : j < i) (f g : Model v)
    (hf : IsBounded f.val) (hg : IsBounded g.val) :
    coreForm (star ψ.val) (multiply (powerInf v j) f.val)
      (multiply (powerInf v i) g.val) = 0 := by
  rw [coreForm_star _ _ _ (bounded_multiply _ _ hf),
    analytic_power_block_zero v hv ψ j i hij g f hg, map_zero]

/-- A finite expansion of the actual core form. Boundedness is kept on the literal input
and output vectors, so every rewritten pairing is an honest native L² pairing. -/
theorem coreForm_finite_sums {I J : Type*} [Fintype I] [Fintype J]
    (σ : BoundaryL2) (f : I → BoundaryL2) (g : J → BoundaryL2)
    (hf : ∀ i, IsBounded (f i)) (hg : ∀ j, IsBounded (g j)) :
    coreForm σ (∑ i, f i) (∑ j, g j) = ∑ j, ∑ i, coreForm σ (f i) (g j) := by
  have hsum : IsBounded (∑ i, f i) := boundedL2.sum_mem (fun i _ => hf i)
  rw [coreForm_eq_inner_left _ _ _ hsum, sum_inner]
  apply Finset.sum_congr rfl
  intro j _
  rw [← coreForm_eq_inner_left _ _ _ hsum,
    coreForm_eq_inner_right _ _ _ (hg j), inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coreForm_eq_inner_right _ _ _ (hg j)).symm

/-- A synthesis with the literal finite power formula sends bounded tuples to bounded vectors. -/
theorem gapSynthesis_bounded (u v : BoundaryLInf) (N : ℕ)
    (W : FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model u)
    (hW : ∀ f, (W f).val = ∑ j, multiply (powerInf v j.val) (f j).val)
    (f : FiniteModelSum (fun _ : Fin N => v)) (hf : ∀ j, IsBounded (f j).val) :
    IsBounded (W f).val := by
  rw [hW]
  exact boundedL2.sum_mem (fun j _ => bounded_multiply _ _ (hf j))

/-- The chosen bounded finite-block image is dense, with no assumption that arbitrary
orthogonal projections preserve the bounded core. -/
theorem gapSynthesis_bounded_dense (u v : BoundaryLInf) (hv : IsInner v) (N : ℕ)
    (W : FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model u) :
    Dense (W '' {f | ∀ j, IsBounded (f j).val}) :=
  W.surjective.denseRange.dense_image W.continuous
    (bounded_finiteModelSum_dense (fun _ : Fin N => v) (fun _ => hv))

/-- The literal image of one standard coordinate is the corresponding power block. -/
theorem gapSynthesis_single (u v : BoundaryLInf) (N : ℕ)
    (W : FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model u)
    (hW : ∀ f, (W f).val = ∑ j, multiply (powerInf v j.val) (f j).val)
    (j : Fin N) (f : Model v) :
    (W (finiteSingle (fun _ : Fin N => Model v) j f)).val = multiply (powerInf v j.val) f.val := by
  classical
  rw [hW, Finset.sum_eq_single j]
  · rw [finiteSingle_apply, Pi.single_eq_same]
  · intro i _ hij
    rw [finiteSingle_apply, Pi.single_eq_of_ne hij]
    simp only [Submodule.coe_zero, map_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Finite strict-lower reconstruction on an actual orthogonal power decomposition.
The proof is first on the dense image of bounded tuples, then extends to the entire frozen core. -/
theorem finiteGap_reconstruction (u v : BoundaryLInf) (hv : IsInner v) (N : ℕ)
    (W : FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model u)
    (hW : ∀ f, (W f).val = ∑ j, multiply (powerInf v j.val) (f j).val)
    (φ ψ q : Hardy) (hφ : φ.val = multiply v q.val)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u (splitSymbol φ.val ψ.val) A) :
    RepresentsTTO u φ.val
      (lowerTriangle (fun j => coordinateResolution W.toContinuousLinearEquiv j) A) := by
  classical
  let Q := fun j => coordinateResolution W.toContinuousLinearEquiv j
  have hpair (f g : FiniteModelSum (fun _ : Fin N => v))
      (hf : ∀ j, IsBounded (f j).val) (hg : ∀ i, IsBounded (g i).val) :
      inner ℂ (W g) (lowerTriangle Q A (W f)) = coreForm φ.val (W f).val (W g).val := by
    have hforms : coreForm φ.val (W f).val (W g).val =
        ∑ i, ∑ j, coreForm φ.val (multiply (powerInf v j.val) (f j).val)
          (multiply (powerInf v i.val) (g i).val) := by
      rw [hW f, hW g]
      exact coreForm_finite_sums _ _ _ (fun j => bounded_multiply _ _ (hf j))
        (fun i => bounded_multiply _ _ (hg i))
    rw [hforms]
    simp only [lowerTriangle, sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : j < i
    · simp only [ite_eq_left hij, ContinuousLinearMap.comp_apply]
      change inner ℂ (W g) (coordinateResolution W.toContinuousLinearEquiv i
        (A (coordinateResolution W.toContinuousLinearEquiv j (W f)))) = _
      rw [coordinateResolution_unitary_block_inner]
      have hfi := gapSynthesis_single u v N W hW j (f j)
      have hgi := gapSynthesis_single u v N W hW i (g i)
      have hfb : IsBounded (W (finiteSingle (fun _ : Fin N => Model v) j (f j))).val := by
        rw [hfi]
        exact bounded_multiply _ _ (hf j)
      have hgb : IsBounded (W (finiteSingle (fun _ : Fin N => Model v) i (g i))).val := by
        rw [hgi]
        exact bounded_multiply _ _ (hg i)
      rw [hA _ _ hfb hgb, hfi, hgi]
      rw [splitSymbol, coreForm_add _ _ _ _ (bounded_multiply _ _ (hf j)),
        coanalytic_power_block_zero v hv ψ i.val j.val hij (f j) (g i) (hf j) (hg i), add_zero]
    · simp only [ite_eq_right hij, zero_apply, inner_zero_right]
      rw [hφ]
      exact (gap_power_block_zero v hv q i.val j.val (by omega) (f j) (g i) (hf j)).symm
  apply denseCoreSet u φ.val (lowerTriangle Q A)
    (W '' {f | ∀ j, IsBounded (f j).val}) (gapSynthesis_bounded_dense u v hv N W)
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact gapSynthesis_bounded u v N W hW f hf
  · intro x hx y hy
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact hpair f g hf hg

/-- Equality of the actual ambient model submodules gives the literal identity isometry. -/
def modelIdentityEquiv (a b : BoundaryLInf) (hab : model a = model b) :
    Model a ≃ₗᵢ[ℂ] Model b := LinearIsometryEquiv.ofEq (model a) (model b) hab

set_option maxHeartbeats 100000 in
/-- The actual finite compression identity, with every manuscript hypothesis retained.
No triangular projection, closure of the ideal, or restriction p≥1 is used. -/
theorem finiteCompression : FiniteCompressionObligation := by
  intro u hu hn μ hμ φ ψ r hr hr1 hg A hA
  obtain ⟨N, _hN, _hNr, v, hv, _α, _hα, _hu, hm, q, hφ⟩ :=
    exists_discreteSingularGapRoot u hu hn μ hμ φ r hr hr1 hg
  let W : FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model u :=
    (powerModelEquiv v hv N).trans (modelIdentityEquiv (powerInf v N) u hm.symm)
  have hW : ∀ f, (W f).val = ∑ j, multiply (powerInf v j.val) (f j).val := by
    intro f
    change (modelIdentityEquiv (powerInf v N) u hm.symm (powerModelEquiv v hv N f)).val = _
    rw [modelIdentityEquiv, LinearIsometryEquiv.coe_ofEq_apply]
    change (powerModelSynthesisCLM v hv N f).val = _
    exact powerModelSynthesisCLM_apply v hv N f
  let Q := fun j => coordinateResolution W.toContinuousLinearEquiv j
  have hrep : RepresentsTTO u φ.val (lowerTriangle Q A) :=
    finiteGap_reconstruction u v hv N W hW φ ψ q hφ A hA
  refine ⟨N, Q, hrep, ?_⟩
  have he := represents_sub u (splitSymbol φ.val ψ.val) φ.val A (lowerTriangle Q A) hA hrep
  simpa only [splitSymbol, add_sub_cancel_left] using he

/-- Theorem 5 for every ordinary finite-sum two-sided ideal, with its full original scope. -/
theorem gapSplittingTheorem : GapConclusion := Reduction.gapSplitting finiteCompression

/-- All stated ideal specializations, including every p>0, compactness and finite rank. -/
theorem gapSpecializationsTheorem : GapSpecializationsConclusion := gapSpecializations finiteCompression

/-- Corollary 1 for the normalized canonical symbol, retaining both low-frequency formulations. -/
theorem canonicalGapSplittingTheorem : CanonicalGapConclusion :=
  Reduction.canonicalGapSplitting finiteCompression coreLaws gapProjection

end TTO.Paper.Proved
