/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.VolterraFoundations
public import TTO.TriangularBoundFoundations

/-! Actual bounded integral kernels and their lower-triangular interval restrictions. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal row representing the linear input integral. -/
def intervalKernelRow (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) : IntervalL2 ℓ :=
  (MemLp.of_bound ((hK.comp_measurable (measurable_const.prodMk measurable_id)).star.aestronglyMeasurable)
    M (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      change ‖conj (K s t)‖ ≤ M
      rw [Complex.norm_conj]
      exact hBound s hs t ht)).toLp
      (fun t => conj (K s t))

theorem intervalKernelRow_ae (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) :
    intervalKernelRow ℓ K hK M hBound s hs =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] fun t => conj (K s t) :=
  MemLp.coeFn_toLp _

/-- The actual input integral at the output point s. -/
def intervalKernelRaw (ℓ : ℝ) (K : ℝ → ℝ → ℂ) (f : IntervalL2 ℓ) (s : ℝ) : ℂ :=
  ∫ t, K s t * f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ))

theorem intervalKernelRaw_eq_inner (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) (f : IntervalL2 ℓ) :
    intervalKernelRaw ℓ K f s = inner ℂ (intervalKernelRow ℓ K hK M hBound s hs) f := by
  rw [intervalKernelRaw,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalKernelRow_ae ℓ K hK M hBound s hs] with t ht
  rw [ht,RCLike.inner_apply,starRingEnd_self_apply]
  ring

theorem norm_intervalKernelRow_le (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) :
    ‖intervalKernelRow ℓ K hK M hBound s hs‖ ≤ M*‖intervalOne ℓ‖ := by
  have h := Lp.norm_le_norm_of_ae_le (f := intervalKernelRow ℓ K hK M hBound s hs)
    (g := (M : ℂ) • intervalOne ℓ) (by
      filter_upwards [intervalKernelRow_ae ℓ K hK M hBound s hs,
        Lp.coeFn_smul (M : ℂ) (intervalOne ℓ),intervalOne_ae ℓ,
        ae_restrict_mem measurableSet_Ioo] with t hr hsm ho ht
      rw [hr,hsm]
      simp only [Pi.smul_apply,ho,smul_eq_mul,mul_one,Complex.norm_conj,Complex.norm_real,
        Real.norm_of_nonneg hM]
      exact hBound s hs t ht)
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hM] using h

theorem norm_intervalKernelRaw_le (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) (f : IntervalL2 ℓ) :
    ‖intervalKernelRaw ℓ K f s‖ ≤ M*‖intervalOne ℓ‖*‖f‖ := by
  rw [intervalKernelRaw_eq_inner ℓ K hK M hBound s hs f]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_intervalKernelRow_le ℓ K hK M hM hBound s hs) (norm_nonneg f))

theorem stronglyMeasurable_intervalKernelRaw (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (f : IntervalL2 ℓ) :
    StronglyMeasurable (intervalKernelRaw ℓ K f) :=
  (hK.mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)).integral_prod_right'
    (ν := volume.restrict (Ioo (0 : ℝ) ℓ))

theorem memLp_intervalKernelRaw (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (f : IntervalL2 ℓ) : MemLp (intervalKernelRaw ℓ K f) 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  apply MemLp.of_bound (stronglyMeasurable_intervalKernelRaw ℓ K hK f).aestronglyMeasurable
    (M*‖intervalOne ℓ‖*‖f‖)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact norm_intervalKernelRaw_le ℓ K hK M hM hBound s hs f

section BoundedKernelOperator
variable (ℓ : ℝ) (K : ℝ → ℝ → ℂ) (hK : StronglyMeasurable (Function.uncurry K))
  (M : ℝ) (hM : 0 ≤ M)
  (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)

def intervalKernelVector (f : IntervalL2 ℓ) : IntervalL2 ℓ :=
  (memLp_intervalKernelRaw ℓ K hK M hM hBound f).toLp (intervalKernelRaw ℓ K f)

theorem intervalKernelVector_ae (f : IntervalL2 ℓ) :
    intervalKernelVector ℓ K hK M hM hBound f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      intervalKernelRaw ℓ K f := (memLp_intervalKernelRaw ℓ K hK M hM hBound f).coeFn_toLp

theorem intervalKernelVector_add (f g : IntervalL2 ℓ) :
    intervalKernelVector ℓ K hK M hM hBound (f+g) =
      intervalKernelVector ℓ K hK M hM hBound f + intervalKernelVector ℓ K hK M hM hBound g := by
  apply Lp.ext
  filter_upwards [intervalKernelVector_ae ℓ K hK M hM hBound (f+g),
    intervalKernelVector_ae ℓ K hK M hM hBound f,intervalKernelVector_ae ℓ K hK M hM hBound g,
    Lp.coeFn_add (intervalKernelVector ℓ K hK M hM hBound f)
      (intervalKernelVector ℓ K hK M hM hBound g),ae_restrict_mem measurableSet_Ioo]
    with s hfg hf hg hadd hs
  rw [hfg,hadd,Pi.add_apply,hf,hg,
    intervalKernelRaw_eq_inner ℓ K hK M hBound s hs (f+g),
    intervalKernelRaw_eq_inner ℓ K hK M hBound s hs f,
    intervalKernelRaw_eq_inner ℓ K hK M hBound s hs g,inner_add_right]

theorem intervalKernelVector_smul (c : ℂ) (f : IntervalL2 ℓ) :
    intervalKernelVector ℓ K hK M hM hBound (c • f) =
      c • intervalKernelVector ℓ K hK M hM hBound f := by
  apply Lp.ext
  filter_upwards [intervalKernelVector_ae ℓ K hK M hM hBound (c • f),
    intervalKernelVector_ae ℓ K hK M hM hBound f,
    Lp.coeFn_smul c (intervalKernelVector ℓ K hK M hM hBound f),
    ae_restrict_mem measurableSet_Ioo] with s hcf hf hsm hs
  rw [hcf,hsm,Pi.smul_apply,hf,
    intervalKernelRaw_eq_inner ℓ K hK M hBound s hs (c • f),
    intervalKernelRaw_eq_inner ℓ K hK M hBound s hs f,inner_smul_right,smul_eq_mul]

def intervalKernelLinear (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    IntervalL2 ℓ →ₗ[ℂ] IntervalL2 ℓ where
  toFun := intervalKernelVector ℓ K hK M hM hBound
  map_add' := intervalKernelVector_add ℓ K hK M hM hBound
  map_smul' := intervalKernelVector_smul ℓ K hK M hM hBound

theorem norm_intervalKernelVector_le (f : IntervalL2 ℓ) :
    ‖intervalKernelVector ℓ K hK M hM hBound f‖ ≤ M*‖intervalOne ℓ‖^2*‖f‖ := by
  let C := M*‖intervalOne ℓ‖*‖f‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have he := Lp.norm_le_norm_of_ae_le (f := intervalKernelVector ℓ K hK M hM hBound f)
    (g := (C : ℂ) • intervalOne ℓ) (by
      filter_upwards [intervalKernelVector_ae ℓ K hK M hM hBound f,
        Lp.coeFn_smul (C : ℂ) (intervalOne ℓ),intervalOne_ae ℓ,
        ae_restrict_mem measurableSet_Ioo] with s hv hsm ho hs
      rw [hv,hsm]
      simp only [Pi.smul_apply,ho,smul_eq_mul,mul_one,Complex.norm_real,Real.norm_of_nonneg hC]
      exact norm_intervalKernelRaw_le ℓ K hK M hM hBound s hs f)
  calc
    _ ≤ ‖(C : ℂ) • intervalOne ℓ‖ := he
    _ = M*‖intervalOne ℓ‖^2*‖f‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      dsimp only [C]
      ring

/-- The genuine bounded kernel integral operator, with a proved operator bound. -/
def intervalKernelOperator : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  (intervalKernelLinear ℓ K hK M hM hBound).mkContinuous (M*‖intervalOne ℓ‖^2)
    (norm_intervalKernelVector_le ℓ K hK M hM hBound)

theorem intervalKernelOperator_ae (f : IntervalL2 ℓ) :
    intervalKernelOperator ℓ K hK M hM hBound f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      fun s => ∫ t, K s t*f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) :=
  intervalKernelVector_ae ℓ K hK M hM hBound f

theorem norm_intervalKernelOperator_le : ‖intervalKernelOperator ℓ K hK M hM hBound‖ ≤
    M*‖intervalOne ℓ‖^2 :=
  (intervalKernelLinear ℓ K hK M hM hBound).mkContinuous_norm_le (by positivity) _

end BoundedKernelOperator
theorem norm_intervalOne_sq (ℓ : ℝ) (hℓ : 0 < ℓ) : ‖intervalOne ℓ‖^2 = ℓ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_intervalOne_self ℓ hℓ]
  exact Complex.ofReal_re ℓ

theorem norm_intervalKernelOperator_le_length (ℓ : ℝ) (hℓ : 0 < ℓ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    ‖intervalKernelOperator ℓ K hK M hM hBound‖ ≤ M*ℓ := by
  simpa only [norm_intervalOne_sq ℓ hℓ] using norm_intervalKernelOperator_le ℓ K hK M hM hBound

/-- Local block bounds combine without a factor equal to the number of cells. -/
theorem norm_blockPinching_le_of_local_bound {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {N : ℕ} (Q : Fin N → H →L[ℂ] H)
    (hQ : TriangularBlocks Q) (A : H →L[ℂ] H) (B : ℝ) (hB : 0 ≤ B)
    (hLocal : ∀ i x, ‖Q i (A (Q i x))‖ ≤ B*‖Q i x‖) :
    ‖blockPinching Q A‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  have ho := orthogonal_block_ranges Q hQ.adjoint_eq hQ.orthogonal
  have he : ‖blockPinching Q A x‖^2 = ∑ i,‖Q i (A (Q i x))‖^2 := by
    have h := norm_sum_sq_of_orthogonal univ (fun i => Q i (A (Q i x)))
      (fun i _ j _ hij => ho i j hij (A (Q i x)) (A (Q j x)))
    simpa [blockPinching,blockMultiplierLinear,blockMultiplier,operatorBlock] using h
  have hx : ‖x‖^2 = ∑ i,‖Q i x‖^2 := by
    simpa only [sum_blocks_apply Q hQ] using
      norm_sum_sq_of_orthogonal univ (fun i => Q i x) (fun i _ j _ hij => ho i j hij x x)
  have hb : (∑ i,‖Q i (A (Q i x))‖^2) ≤ B^2*(∑ i,‖Q i x‖^2) := by
    calc
      _ ≤ ∑ i,(B*‖Q i x‖)^2 := sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hLocal i x) 2)
      _ = _ := by simp_rw [mul_pow]; rw [mul_sum]
  apply le_of_sq_le_sq _ (mul_nonneg hB (norm_nonneg x))
  rw [he,mul_pow,hx]
  exact hb

end TTO.Paper.Proved
