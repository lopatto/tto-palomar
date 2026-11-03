/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations

/-! Actual model-space decompositions for the finite analytic-gap nest. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Multiplying the defining inner factor by an analytic bounded factor enlarges its model. -/
theorem model_le_product_left (a b : BoundaryLInf) (hb : toL2 b ∈ hardy) :
    model a ≤ model (multiplyInf a b) := by
  intro f hf
  refine ⟨hf.1, (Submodule.mem_orthogonal' _ _).mpr ?_⟩
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    change inner ℂ f (multiply (multiplyInf a b) (fourierBasis (T := 1) (n : ℤ))) = 0
    rw [← multiply_assoc]
    exact inner_eq_zero_symm.mp (inner_multiply_model a ⟨f, hf⟩
      ⟨multiply b (fourierBasis (T := 1) (n : ℤ)),
        multiply_mem_hardy b hb _ (fourierBasis_mem_hardy n)⟩)
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right, hx', hy', add_zero]
  | smul c x hx hx' => rw [inner_smul_right, hx', mul_zero]

/-- The native two-factor model decomposition K_ab = K_a ⊕ a K_b. -/
theorem model_product_decomposition (a b : BoundaryLInf) (ha : IsInner a) (hb : IsInner b)
    (f : Model (multiplyInf a b)) :
    ∃ x : Model a, ∃ y : Model b, f.val = x.val + multiply a y.val := by
  let x := (model a).orthogonalProjectionOnto f.val
  let r : Hardy := ⟨f.val - x.val, hardy.sub_mem f.property.1 x.property.1⟩
  have hr : (model a).orthogonalProjectionOnto r.val = 0 := by
    change (model a).orthogonalProjectionOnto (f.val - x.val) = 0
    rw [map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, sub_self]
  obtain ⟨y, hy⟩ := innerFactor_of_modelProjection_zero a ha r hr
  have horth (g : Hardy) : inner ℂ (multiply b g.val) y.val = 0 := by
    have he := (innerMultiplyIsometry a ha).inner_map_map (multiply b g.val) y.val
    change inner ℂ (multiply a (multiply b g.val)) (multiply a y.val) =
      inner ℂ (multiply b g.val) y.val at he
    rw [← he, multiply_assoc, ← hy]
    change inner ℂ (multiply (multiplyInf a b) g.val) (f.val - x.val) = 0
    rw [inner_sub_right, inner_multiply_model (multiplyInf a b) f g]
    have hx := inner_multiply_model a x
      ⟨multiply b g.val, multiply_mem_hardy b hb.1 g.val g.property⟩
    rw [multiply_assoc] at hx
    rw [hx, sub_self]
  have hym : y.val ∈ model b := by
    refine ⟨y.property, (Submodule.mem_orthogonal _ _).mpr ?_⟩
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      exact horth ⟨fourierBasis (T := 1) (n : ℤ), fourierBasis_mem_hardy n⟩
    | zero => simp
    | add x y hx hy hx' hy' => rw [inner_add_left, hx', hy', add_zero]
    | smul c x hx hx' => rw [inner_smul_left, hx', mul_zero]
  refine ⟨x, ⟨y.val, hym⟩, ?_⟩
  change f.val = x.val + multiply a y.val
  rw [← hy]
  change f.val = x.val + (f.val - x.val)
  abel

/-- Every actual nonnegative integer power of an inner boundary symbol is inner. -/
theorem isInner_powerInf (v : BoundaryLInf) (hv : IsInner v) (n : ℕ) : IsInner (powerInf v n) := by
  induction n with
  | zero => exact isInner_constLInf_one
  | succ n ih => exact isInner_multiplyInf v (powerInf v n) hv ih

/-- Integer powers retain their literal multiplicative meaning. -/
theorem powerInf_add (v : BoundaryLInf) (m n : ℕ) :
    powerInf v (m + n) = multiplyInf (powerInf v m) (powerInf v n) := by
  apply Lp.ext
  filter_upwards [powerInf_ae v (m + n), multiplyInf_ae (powerInf v m) (powerInf v n),
    powerInf_ae v m, powerInf_ae v n] with t ha hm h1 h2
  rw [ha, hm, h1, h2, pow_add]

/-- The constant-one factor has the genuine zero-dimensional model space. -/
theorem model_constLInf_one_eq_bot : model (constLInf 1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have he := inner_multiply_model (constLInf 1) ⟨f, hf⟩ ⟨f, hf.1⟩
  rw [multiply_constLInf_one] at he
  simpa only [Submodule.mem_bot] using (inner_self_eq_zero.mp he)

/-- The actual finite repeated-factor expansion. Every summand is V^j times a vector in K_V. -/
theorem power_model_expansion (v : BoundaryLInf) (hv : IsInner v) (N : ℕ)
    (f : Model (powerInf v N)) :
    ∃ g : Fin N → Model v, f.val = ∑ j, multiply (powerInf v j.val) (g j).val := by
  induction N with
  | zero =>
    have hz : f.val = 0 := by
      have hm : f.val ∈ model (constLInf 1) := f.property
      rw [model_constLInf_one_eq_bot] at hm
      simpa only [Submodule.mem_bot] using hm
    refine ⟨Fin.elim0, ?_⟩
    simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hz
  | succ N ih =>
    obtain ⟨x, y, hxy⟩ := model_product_decomposition v (powerInf v N) hv (isInner_powerInf v hv N) f
    obtain ⟨g, hg⟩ := ih y
    let g' : Fin (N + 1) → Model v := Fin.cons x g
    refine ⟨g', ?_⟩
    rw [Fin.sum_univ_succ]
    change f.val = multiply (powerInf v 0) x.val +
      ∑ j : Fin N, multiply (powerInf v (j.val + 1)) (g j).val
    have hstep (j : Fin N) : multiply (powerInf v (j.val + 1)) (g j).val =
        multiply v (multiply (powerInf v j.val) (g j).val) := by
      change multiply (multiplyInf v (powerInf v j.val)) (g j).val = _
      rw [← multiply_assoc]
    simp_rw [hstep]
    change f.val = multiply (constLInf 1) x.val +
      ∑ j : Fin N, multiply v (multiply (powerInf v j.val) (g j).val)
    rw [multiply_constLInf_one, ← map_sum, ← hg]
    exact hxy

/-- The actual integer-power models form an increasing nest. -/
theorem model_powerInf_mono (v : BoundaryLInf) (hv : IsInner v) {m n : ℕ} (hmn : m ≤ n) :
    model (powerInf v m) ≤ model (powerInf v n) := by
  have hn : n = m + (n - m) := by omega
  rw [hn, powerInf_add]
  exact model_le_product_left _ _ (isInner_powerInf v hv (n - m)).1

/-- A repeated-factor block lies in its actual finite power model. -/
theorem power_model_block_mem (v : BoundaryLInf) (hv : IsInner v) (N j : ℕ)
    (hj : j < N) (f : Model v) : multiply (powerInf v j) f.val ∈ model (powerInf v N) := by
  apply model_powerInf_mono v hv (show j + 1 ≤ N by omega)
  change multiply (powerInf v j) f.val ∈ model (multiplyInf v (powerInf v j))
  rw [multiplyInf_comm v (powerInf v j)]
  exact multiply_model_mem_product v (powerInf v j) (isInner_powerInf v hv j) f

/-- Different powers of K_V are genuinely orthogonal in the ambient native L² space. -/
theorem power_model_blocks_inner_zero_of_lt (v : BoundaryLInf) (hv : IsInner v)
    (i j : ℕ) (hij : i < j) (f g : Model v) :
    inner ℂ (multiply (powerInf v i) f.val) (multiply (powerInf v j) g.val) = 0 := by
  have hj : j = (i + 1) + (j - (i + 1)) := by omega
  rw [hj, powerInf_add, ← multiply_assoc]
  apply inner_eq_zero_symm.mp
  exact inner_multiply_model (powerInf v (i + 1))
    ⟨multiply (powerInf v i) f.val, power_model_block_mem v hv (i + 1) i (by omega) f⟩
    ⟨multiply (powerInf v (j - (i + 1))) g.val,
      multiply_mem_hardy _ (isInner_powerInf v hv _).1 _ g.property.1⟩

theorem power_model_blocks_inner_zero (v : BoundaryLInf) (hv : IsInner v)
    (i j : ℕ) (hij : i ≠ j) (f g : Model v) :
    inner ℂ (multiply (powerInf v i) f.val) (multiply (powerInf v j) g.val) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact power_model_blocks_inner_zero_of_lt v hv i j h f g
  · exact inner_eq_zero_symm.mp (power_model_blocks_inner_zero_of_lt v hv j i h g f)

/-- The actual finite model blocks are isometric embeddings. -/
def powerModelBlock (v : BoundaryLInf) (hv : IsInner v) (N : ℕ) (j : Fin N) :
    Model v →ₗᵢ[ℂ] Model (powerInf v N) where
  toLinearMap := LinearMap.codRestrict (model (powerInf v N))
    ((multiply (powerInf v j.val)).toLinearMap.comp (model v).subtype)
    (power_model_block_mem v hv N j.val j.isLt)
  norm_map' f := (innerMultiplyIsometry (powerInf v j.val) (isInner_powerInf v hv j.val)).norm_map f.val

/-- The finite sum preserves every actual inner product. -/
theorem power_model_sum_inner (v : BoundaryLInf) (hv : IsInner v) (N : ℕ)
    (f g : Fin N → Model v) :
    inner ℂ (∑ j, multiply (powerInf v j.val) (f j).val)
      (∑ j, multiply (powerInf v j.val) (g j).val) = ∑ j, inner ℂ (f j) (g j) := by
  classical
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (innerMultiplyIsometry (powerInf v i.val) (isInner_powerInf v hv i.val)).inner_map_map
      (f i).val (g i).val
  · intro j _ hji
    exact power_model_blocks_inner_zero v hv j.val i.val
      (fun h => hji (Fin.ext h)) (f j) (g i)
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The actual bounded finite synthesis, before recording its stronger isometry property. -/
def powerModelSynthesisCLM (v : BoundaryLInf) (hv : IsInner v) (N : ℕ) :
    FiniteModelSum (fun _ : Fin N => v) →L[ℂ] Model (powerInf v N) :=
  ∑ j, (powerModelBlock v hv N j).toContinuousLinearMap ∘L
    PiLp.proj 2 (fun _ : Fin N => Model v) j

theorem powerModelSynthesisCLM_apply (v : BoundaryLInf) (hv : IsInner v) (N : ℕ)
    (f : FiniteModelSum (fun _ : Fin N => v)) :
    (powerModelSynthesisCLM v hv N f).val =
      ∑ j, multiply (powerInf v j.val) (f j).val := by
  rw [powerModelSynthesisCLM, sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- The standard finite Hilbert direct sum is exactly the repeated-factor model. -/
def powerModelSynthesis (v : BoundaryLInf) (hv : IsInner v) (N : ℕ) :
    FiniteModelSum (fun _ : Fin N => v) →ₗᵢ[ℂ] Model (powerInf v N) where
  toLinearMap := (powerModelSynthesisCLM v hv N).toLinearMap
  norm_map' f := by
    change ‖powerModelSynthesisCLM v hv N f‖ = ‖f‖
    have hi : inner ℂ (powerModelSynthesisCLM v hv N f) (powerModelSynthesisCLM v hv N f) =
        inner ℂ f f := by
      change inner ℂ (powerModelSynthesisCLM v hv N f).val (powerModelSynthesisCLM v hv N f).val = _
      rw [powerModelSynthesisCLM_apply, PiLp.inner_apply]
      exact power_model_sum_inner v hv N f f
    have hn := congrArg (fun z : ℂ => RCLike.re z) hi
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ), ← norm_sq_eq_re_inner (𝕜 := ℂ)] at hn
    nlinarith [norm_nonneg (powerModelSynthesisCLM v hv N f), norm_nonneg f]

theorem powerModelSynthesis_surjective (v : BoundaryLInf) (hv : IsInner v) (N : ℕ) :
    Function.Surjective (powerModelSynthesis v hv N) := by
  intro f
  obtain ⟨g, hg⟩ := power_model_expansion v hv N f
  refine ⟨WithLp.toLp 2 g, ?_⟩
  apply Subtype.ext
  change (powerModelSynthesisCLM v hv N (WithLp.toLp 2 g)).val = f.val
  rw [powerModelSynthesisCLM_apply]
  exact hg.symm

/-- The exact orthogonal finite model-space decomposition, including the zero-dimensional base. -/
def powerModelEquiv (v : BoundaryLInf) (hv : IsInner v) (N : ℕ) :
    FiniteModelSum (fun _ : Fin N => v) ≃ₗᵢ[ℂ] Model (powerInf v N) :=
  LinearIsometryEquiv.ofSurjective (powerModelSynthesis v hv N) (powerModelSynthesis_surjective v hv N)

end TTO.Paper.Proved
