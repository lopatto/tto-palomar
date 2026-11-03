/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto, The Tau Ceti contributors
-/
module
public import TTO.WeakOperatorFoundations

/-! Finite real power norms under prefix domination. -/
@[expose] public section
noncomputable section
open Finset
namespace TTO.Paper.Proved

/- The weighted-prefix proof is adapted narrowly from Tau Ceti,
Algebra/Order/BigOperators/Sum/ByParts.lean, revision
 d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad (Apache-2.0).
Tau Ceti is not a dependency of this project. -/

/-- Abel comparison for the nonnegative decreasing weights used below. -/
theorem power_weighted_prefix_comparison {f g w : ℕ → ℝ} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ∑ i ∈ range N, w i*f i ≤ ∑ i ∈ range N, w i*g i := by
  let d : ℕ → ℝ := fun i => g i-f i
  have hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ range k, d i := fun k hk => by
    simpa [d,sum_sub_distrib] using hfg k hk
  suffices 0 ≤ ∑ i ∈ range N, w i*d i by
    simpa [d,mul_sub,sum_sub_distrib] using this
  have hparts := sum_range_by_parts w d N
  simp only [smul_eq_mul] at hparts
  rw [hparts,sub_nonneg]
  calc
    ∑ i ∈ range (N-1), (w (i+1)-w i)*∑ j ∈ range (i+1), d j
      ≤ ∑ _ ∈ range (N-1), (0 : ℝ) := by
        apply sum_le_sum
        intro i hi
        rw [mem_range] at hi
        rw [← neg_sub (w i) (w (i+1)),neg_mul]
        exact neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr (hw i (by omega)))
          (hD (i+1) (by omega)))
    _ = 0 := sum_const_zero
    _ ≤ w (N-1)*∑ j ∈ range N, d j := mul_nonneg hw0 (hD N le_rfl)

/-- A decreasing nonnegative finite sequence has smaller Lp norm under prefix domination. -/
theorem finite_power_norm_le_of_prefix (a d : ℕ → ℝ) (N : ℕ) (p : ℝ) (hp : 1 ≤ p)
    (ha : ∀ i < N, 0 ≤ a i) (hd : ∀ i < N, 0 ≤ d i)
    (hanti : ∀ i, i+1 < N → a (i+1) ≤ a i)
    (hprefix : ∀ k ≤ N, ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, d i) :
    (∑ i ∈ range N, a i^p)^(1/p) ≤ (∑ i ∈ range N, d i^p)^(1/p) := by
  by_cases hN : N=0
  · subst N
    simp
  by_cases hp1 : p=1
  · subst p
    simpa only [Real.rpow_one,one_div_one] using hprefix N le_rfl
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
  have hp0 : 0 < p := zero_lt_one.trans hpgt
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hpgt
  let w : ℕ → ℝ := fun i => a i^(p-1)
  let Sa : ℝ := ∑ i ∈ range N, a i^p
  let Sd : ℝ := ∑ i ∈ range N, d i^p
  have hSa : 0 ≤ Sa := sum_nonneg (fun i hi => Real.rpow_nonneg (ha i (mem_range.mp hi)) p)
  have hSd : 0 ≤ Sd := sum_nonneg (fun i hi => Real.rpow_nonneg (hd i (mem_range.mp hi)) p)
  have hw0 (i : ℕ) (hi : i < N) : 0 ≤ w i := Real.rpow_nonneg (ha i hi) (p-1)
  have hwanti (i : ℕ) (hi : i+1 < N) : w (i+1) ≤ w i :=
    Real.rpow_le_rpow (ha (i+1) hi) (hanti i hi) (sub_nonneg.mpr hp)
  have hlast : 0 ≤ w (N-1) := hw0 _ (by omega)
  have hdom := power_weighted_prefix_comparison hprefix hwanti hlast
  have hsum : (∑ i ∈ range N, w i*a i) = Sa := by
    apply sum_congr rfl
    intro i hi
    exact (by
      simpa only [sub_add_cancel] using
        (Real.rpow_add_one' (ha i (mem_range.mp hi)) (by linarith : p-1+1 ≠ 0)).symm)
  have hwq : (∑ i ∈ range N, w i^q) = Sa := by
    apply sum_congr rfl
    intro i hi
    dsimp only [w]
    rw [← Real.rpow_mul (ha i (mem_range.mp hi)),hpq.sub_one_mul_conj]
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := range N) (f := d) (g := w) hpq
    (fun i hi => hd i (mem_range.mp hi)) (fun i hi => hw0 i (mem_range.mp hi))
  rw [hwq] at hHolder
  have hswap : (∑ i ∈ range N, w i*d i) = ∑ i ∈ range N, d i*w i :=
    sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hsum,hswap] at hdom
  have hmain : Sa ≤ Sd^(1/p)*Sa^(1/q) := hdom.trans hHolder
  change Sa^(1/p) ≤ Sd^(1/p)
  by_cases hzero : Sa=0
  · rw [hzero,Real.zero_rpow (one_div_ne_zero hp0.ne')]
    exact Real.rpow_nonneg hSd _
  have hSapos : 0 < Sa := lt_of_le_of_ne hSa (Ne.symm hzero)
  have hsplit : Sa^(1/p)*Sa^(1/q) = Sa := by
    rw [← Real.rpow_add_of_nonneg hSa (one_div_nonneg.mpr hpq.pos.le)
      (one_div_nonneg.mpr hpq.symm.pos.le)]
    simp only [one_div,hpq.inv_add_inv_eq_one,Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hSapos (1/q))).mp
  rw [hsplit]
  exact hmain

/-- Prefix Ky Fan dominance implies the sharp finite Lp sum inequality, for every p≥1. -/
theorem finite_power_norm_add_of_prefix (a b c : ℕ → ℝ) (N : ℕ) (p : ℝ) (hp : 1 ≤ p)
    (ha : ∀ i < N, 0 ≤ a i) (hb : ∀ i < N, 0 ≤ b i) (hc : ∀ i < N, 0 ≤ c i)
    (hanti : ∀ i, i+1 < N → a (i+1) ≤ a i)
    (hprefix : ∀ k ≤ N, ∑ i ∈ range k, a i ≤
      (∑ i ∈ range k, b i)+(∑ i ∈ range k, c i)) :
    (∑ i ∈ range N, a i^p)^(1/p) ≤
      (∑ i ∈ range N, b i^p)^(1/p)+(∑ i ∈ range N, c i^p)^(1/p) := by
  have hmono := finite_power_norm_le_of_prefix a (fun i => b i+c i) N p hp ha
    (fun i hi => add_nonneg (hb i hi) (hc i hi)) hanti (fun k hk => by
      simpa only [sum_add_distrib] using hprefix k hk)
  have hm := Real.Lp_add_le (range N) b c hp
  have hsb : (∑ i ∈ range N, |b i|^p) = ∑ i ∈ range N, b i^p :=
    sum_congr rfl (fun i hi => by rw [abs_of_nonneg (hb i (mem_range.mp hi))])
  have hsc : (∑ i ∈ range N, |c i|^p) = ∑ i ∈ range N, c i^p :=
    sum_congr rfl (fun i hi => by rw [abs_of_nonneg (hc i (mem_range.mp hi))])
  have hsbc : (∑ i ∈ range N, |b i+c i|^p) = ∑ i ∈ range N, (b i+c i)^p :=
    sum_congr rfl (fun i hi => by rw [abs_of_nonneg (add_nonneg (hb i (mem_range.mp hi)) (hc i (mem_range.mp hi)))])
  rw [hsb,hsc,hsbc] at hm
  exact hmono.trans hm

end TTO.Paper.Proved
