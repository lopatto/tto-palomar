/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Controlled affine-orbit approximation gives an exact preimage.
The geometric-series part narrowly adapts Mathlib's proof of
ContinuousLinearMap.exists_preimage_norm_le at the pinned Mathlib revision.
No completeness of the target and no Hankel existence premise are imposed. -/
@[expose] public section
noncomputable section
open Function Filter Finset
open scoped Topology
namespace TTO.Paper.Proved

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The step is required only at residuals of the actual affine orbit. -/
theorem exists_exact_lift_of_controlled_residual (T : E →L[𝕜] F) (y : F)
    (C : ℝ) (hC : 0 ≤ C)
    (hStep : ∀ x : E, ∃ d : E,
      ‖d‖ ≤ C*‖y-T x‖ ∧ ‖y-T x-T d‖ ≤ (1/2 : ℝ)*‖y-T x‖) :
    ∃ x : E, T x=y ∧ ‖x‖ ≤ 2*C*‖y‖ := by
  choose d hd using hStep
  let X : ℕ → E := fun n => (fun x : E => x+d x)^[n] 0
  have hX0 : X 0=0 := rfl
  have hXsucc (n : ℕ) : X (n+1)=X n+d (X n) := by
    exact Function.iterate_succ_apply' _ _ _
  have hResidual (n : ℕ) : ‖y-T (X n)‖ ≤ (1/2 : ℝ)^n*‖y‖ := by
    induction n with
    | zero => simp only [hX0,map_zero,sub_zero,pow_zero,one_mul,le_rfl]
    | succ n ih =>
      calc
        _ = ‖y-T (X n)-T (d (X n))‖ := by rw [hXsucc,map_add,sub_add_eq_sub_sub]
        _ ≤ (1/2 : ℝ)*‖y-T (X n)‖ := (hd (X n)).2
        _ ≤ (1/2 : ℝ)*((1/2 : ℝ)^n*‖y‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  let u : ℕ → E := fun n => d (X n)
  have hU (n : ℕ) : ‖u n‖ ≤ (1/2 : ℝ)^n*(C*‖y‖) := by
    calc
      _ ≤ C*‖y-T (X n)‖ := (hd (X n)).1
      _ ≤ C*((1/2 : ℝ)^n*‖y‖) := mul_le_mul_of_nonneg_left (hResidual n) hC
      _ = _ := by ring
  have hSumNorm : Summable (fun n => ‖u n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg (u n)) hU ?_
    exact summable_geometric_two.mul_right (C*‖y‖)
  have hSum : Summable u := hSumNorm.of_norm
  let x : E := ∑' n,u n
  have hNorm : ‖x‖ ≤ 2*C*‖y‖ := by
    calc
      _ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm hSumNorm
      _ ≤ ∑' n, (1/2 : ℝ)^n*(C*‖y‖) :=
        hSumNorm.tsum_le_tsum hU (summable_geometric_two.mul_right (C*‖y‖))
      _ = (∑' n, (1/2 : ℝ)^n)*(C*‖y‖) := tsum_mul_right
      _ = _ := by rw [tsum_geometric_two]; ring
  have hXsum (n : ℕ) : X n=∑ i ∈ range n,u i := by
    induction n with
    | zero => simp only [hX0,range_zero,sum_empty]
    | succ n ih => rw [hXsucc,sum_range_succ,← ih]
  have hLimit : Tendsto X atTop (𝓝 x) := by
    simpa only [← hXsum] using hSum.hasSum.tendsto_sum_nat
  have hImage : Tendsto (fun n => T (X n)) atTop (𝓝 (T x)) :=
    (T.continuous.tendsto x).comp hLimit
  have hZero : Tendsto (fun n => y-T (X n)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun n => norm_nonneg (y-T (X n))) hResidual ?_
    have ht := (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_const ‖y‖
    simpa only [zero_mul] using ht
  have hImageY : Tendsto (fun n => T (X n)) atTop (𝓝 y) := by
    have ht : Tendsto (fun n : ℕ => y-(y-T (X n))) atTop (𝓝 (y-0)) :=
      tendsto_const_nhds.sub hZero
    simpa only [sub_sub_cancel,sub_zero] using! ht
  exact ⟨x,tendsto_nhds_unique hImage hImageY,hNorm⟩

end TTO.Paper.Proved
