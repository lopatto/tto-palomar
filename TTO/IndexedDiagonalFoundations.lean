/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations

/-! Arbitrarily indexed diagonal operators. The finite-coordinate proofs generalize the native
sequence proofs in `TTO.Proofs`, whose elementary minmax route records Tau Ceti provenance.
No enumeration, countability or nonemptiness of the index type is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

abbrev IndexedL2 (ι : Type) := lp (fun _ : ι => ℂ) 2
abbrev IndexedOperator (ι : Type) := IndexedL2 ι →L[ℂ] IndexedL2 ι

section IndexedDiagonals
variable {ι : Type}
local instance : DecidableEq ι := Classical.decEq ι

@[simp] theorem indexed_eval_apply (n : ι) (x : IndexedL2 ι) :
    lp.evalCLM ℂ (fun _ : ι => ℂ) 2 n x = x n := rfl

/-- The frozen basis-vector condition determines every coordinate on native ℓ². -/
theorem indexedDiagonal_apply (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (x : IndexedL2 ι) (n : ι) : D x n = w n*x n := by
  classical
  let F : IndexedL2 ι →L[ℂ] ℂ := innerSL ℂ (lp.single 2 n (1 : ℂ)) ∘L D
  let G : IndexedL2 ι →L[ℂ] ℂ := w n • innerSL ℂ (lp.single 2 n (1 : ℂ))
  have he : F = G := by
    apply lp.ext_continuousLinearMap (𝕜 := ℂ) (E := fun _ : ι => ℂ) (p := 2) (f := F) (g := G) (by norm_num)
    intro i
    apply ContinuousLinearMap.ext_ring
    change inner ℂ (lp.single 2 n (1 : ℂ)) (D (lp.single 2 i (1 : ℂ))) =
      w n * inner ℂ (lp.single 2 n (1 : ℂ) : IndexedL2 ι) (lp.single 2 i (1 : ℂ))
    rw [hd i,inner_smul_right]
    by_cases hni : n = i
    · subst i; rfl
    · simp [lp.inner_single_left,RCLike.inner_apply,lp.single_apply,Pi.single_eq_of_ne hni]
  have h := congrArg (fun L : IndexedL2 ι →L[ℂ] ℂ => L x) he
  simpa [F,G,lp.inner_single_left,RCLike.inner_apply] using h

/-- The literal finite-coordinate diagonal truncation. -/
def indexedDiagonalTruncation (w : ι → ℂ) (s : Finset ι) : IndexedOperator ι :=
  ∑ i ∈ s, (w i • lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 i) ∘L
    lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i

theorem indexedDiagonalTruncation_eq_sum_single (w : ι → ℂ) (s : Finset ι) (x : IndexedL2 ι) :
    indexedDiagonalTruncation w s x = ∑ i ∈ s, (w i*x i) • (lp.single 2 i (1 : ℂ) : IndexedL2 ι) := by
  rw [indexedDiagonalTruncation,_root_.sum_apply]
  simp [lp.singleContinuousLinearMap_apply,← lp.single_smul,indexed_eval_apply]

@[simp] theorem indexedDiagonalTruncation_apply (w : ι → ℂ) (s : Finset ι) (x : IndexedL2 ι) (n : ι) :
    indexedDiagonalTruncation w s x n = if n ∈ s then w n*x n else 0 := by
  classical
  rw [indexedDiagonalTruncation_eq_sum_single]
  change lp.evalCLM ℂ (fun _ : ι => ℂ) 2 n (∑ i ∈ s, (w i*x i) • (lp.single 2 i (1 : ℂ) : IndexedL2 ι)) = _
  rw [map_sum]
  simp [indexed_eval_apply,lp.single_apply,Pi.single_apply]

theorem rank_indexedDiagonalTruncation_le (w : ι → ℂ) (s : Finset ι) :
    (indexedDiagonalTruncation w s).rank ≤ (s.card : Cardinal) := by
  classical
  let v : ι → IndexedL2 ι := fun i => lp.single 2 i (1 : ℂ)
  have hrange : (indexedDiagonalTruncation w s).toLinearMap.range ≤ Submodule.span ℂ (v '' (s : Set ι)) := by
    rintro _ ⟨x,rfl⟩
    rw [ContinuousLinearMap.coe_coe,indexedDiagonalTruncation_eq_sum_single]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  calc
    _ ≤ Module.rank ℂ (Submodule.span ℂ (v '' (s : Set ι))) := Submodule.rank_mono hrange
    _ ≤ (s.card : Cardinal) := by
      rw [← Finset.coe_image]
      exact (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le)

theorem norm_indexedDiagonal_sub_truncation_le (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (s : Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∉ s, ‖w i‖ ≤ C) : ‖D-indexedDiagonalTruncation w s‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  calc
    ‖(D-indexedDiagonalTruncation w s) x‖ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      simp only [sub_apply,lp.coeFn_sub,Pi.sub_apply,
        indexedDiagonal_apply w D hd,indexedDiagonalTruncation_apply]
      by_cases hi : i ∈ s
      · simp only [hi,ite_true,sub_self,norm_zero]; exact norm_nonneg _
      · simpa [hi,norm_mul,abs_of_nonneg hC] using
          mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg (x i))
    _ = C*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,lp.norm_toNorm]

theorem indexed_units_linearIndependent :
    LinearIndependent ℂ (fun i : ι => (lp.single 2 i (1 : ℂ) : IndexedL2 ι)) := by
  classical
  apply LinearIndependent.of_comp (lpSubmodule ℂ (fun _ : ι => ℂ) 2).subtype
  have hcoe : (lpSubmodule ℂ (fun _ : ι => ℂ) 2).subtype ∘
      (fun i : ι => (lp.single 2 i (1 : ℂ) : IndexedL2 ι)) = fun i => Pi.single i (1 : ℂ) := by
    funext i; exact lp.coeFn_single 2 i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ι ℂ

theorem indexed_span_support {κ : Type*} (e : κ → ι) {x : IndexedL2 ι}
    (hx : x ∈ Submodule.span ℂ (Set.range (fun j => (lp.single 2 (e j) (1 : ℂ) : IndexedL2 ι))))
    {i : ι} (hi : i ∉ Set.range e) : x i = 0 := by
  classical
  have hle : Submodule.span ℂ (Set.range (fun j => (lp.single 2 (e j) (1 : ℂ) : IndexedL2 ι))) ≤
      (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change (lp.single 2 (e j) (1 : ℂ) : IndexedL2 ι) i = 0
    simp [lp.single_apply,Pi.single_eq_of_ne (fun h => hi ⟨j,h.symm⟩)]
  exact hle hx

theorem approximationNumber_indexedDiagonal_le (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (n : ℕ) (s : Finset ι) (hs : s.card ≤ n)
    (C : ℝ≥0) (hc : ∀ i ∉ s, ‖w i‖ ≤ C) : approximationNumber D n ≤ C := by
  have hr : (indexedDiagonalTruncation w s).rank ≤ (n : Cardinal) :=
    (rank_indexedDiagonalTruncation_le w s).trans (by exact_mod_cast hs)
  apply (approximationNumber_le_nnnorm_sub D hr).trans
  exact_mod_cast norm_indexedDiagonal_sub_truncation_le w D hd s C C.property hc

theorem le_approximationNumber_indexedDiagonal_of_card (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) {n : ℕ} (s : Finset ι) (hs : n < s.card)
    (c : ℝ) (hc : ∀ i ∈ s, c ≤ ‖w i‖) : c ≤ (approximationNumber D n : ℝ) := by
  classical
  rcases le_or_gt c 0 with h | h
  · exact h.trans (NNReal.coe_nonneg _)
  let e : s → ι := fun j => j.val
  let v : s → IndexedL2 ι := fun j => lp.single 2 (e j) (1 : ℂ)
  have hv : LinearIndependent ℂ v := indexed_units_linearIndependent.comp e Subtype.val_injective
  let V := Submodule.span ℂ (Set.range v)
  have hV : (n : Cardinal) < Module.rank ℂ V := by
    let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
    rw [← Module.finrank_eq_rank,finrank_span_eq_card hv,Fintype.card_coe]
    exact_mod_cast hs
  apply le_approximationNumber_of_lt_rank D hV
  intro x hx
  calc
    c*‖x‖ = ‖c • lp.toNorm x‖ := by simp [norm_smul,abs_of_pos h,lp.norm_toNorm]
    _ ≤ ‖D x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      by_cases hi : i ∈ s
      · simpa [indexedDiagonal_apply w D hd,norm_mul,abs_of_pos h] using
          mul_le_mul_of_nonneg_right (hc i hi) (norm_nonneg (x i))
      · have hz : x i = 0 := indexed_span_support e hx (by
          rintro ⟨j,hj⟩; exact hi (hj ▸ j.property))
        simp [indexedDiagonal_apply w D hd,hz]

/-- Finite coordinate cuts converge in operator norm along the full finite-subset net. -/
theorem indexedDiagonalTruncation_tendsto (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (hw : Tendsto w cofinite (𝓝 0)) :
    Tendsto (fun s : Finset ι => indexedDiagonalTruncation w s) atTop (𝓝 D) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hsmall : ∀ᶠ i in cofinite, ‖w i‖ < ε/2 := by
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp hw (ε/2) (by positivity)
  have hbad := Filter.eventually_cofinite.mp hsmall
  refine ⟨hbad.toFinset,fun s hs => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  apply (norm_indexedDiagonal_sub_truncation_le w D hd s (ε/2) (by positivity) ?_).trans_lt
    (half_lt_self hε)
  intro i hi
  by_contra hn
  exact hi (hs (hbad.mem_toFinset.mpr (not_lt.mpr (le_of_lt (lt_of_not_ge hn)))))

theorem compact_indexedDiagonal_of_tendsto (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (hw : Tendsto w cofinite (𝓝 0)) : IsCompactOperator D := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto (indexedDiagonalTruncation_tendsto w D hd hw)
  exact Eventually.of_forall fun s => finiteRank_compact _ ⟨s.card,rank_indexedDiagonalTruncation_le w s⟩

theorem tendsto_indexedDiagonal_of_compact (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (hD : IsCompactOperator D) : Tendsto w cofinite (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf : Set.Finite {i | ε ≤ ‖w i‖} := by
    by_contra hi
    obtain ⟨R,⟨m,hm⟩,hclose⟩ := compact_finiteRank_approx D hD (ε/2) (by positivity)
    obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (m+1)
    have hlo := le_approximationNumber_indexedDiagonal_of_card w D hd (n := m) s (by omega) ε (fun i hi => hs hi)
    have hup : (approximationNumber D m : ℝ) ≤ ‖D-R‖ := by
      exact_mod_cast approximationNumber_le_nnnorm_sub D hm
    linarith
  filter_upwards [hf.eventually_cofinite_notMem] with i hi
  simpa only [dist_zero_right] using lt_of_not_ge hi

/-- The exact compactness field, for arbitrary index sets including the empty type. -/
theorem indexedDiagonal_compact_iff (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) : IsCompactOperator D ↔ Tendsto w cofinite (𝓝 0) :=
  ⟨tendsto_indexedDiagonal_of_compact w D hd,compact_indexedDiagonal_of_tendsto w D hd⟩

/-- Finite sorted-support coefficients are exactly the first approximation numbers. -/
theorem approximationNumber_finite_indexedDiagonal (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) {N : ℕ} (e : Fin N ↪ ι)
    (he : Antitone (fun i => ‖w (e i)‖))
    (hzero : ∀ i, i ∉ Set.range e → w i = 0) (k : Fin N) :
    approximationNumber D k = ‖w (e k)‖₊ := by
  classical
  apply le_antisymm
  · apply approximationNumber_indexedDiagonal_le w D hd k ((Finset.Iio k).map e) (by simp) ‖w (e k)‖₊
    intro i hi
    by_cases hr : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hr
      exact he (by simpa using hi)
    · simp [hzero i hr]
  · exact_mod_cast le_approximationNumber_indexedDiagonal_of_card w D hd ((Finset.Iic k).map e) (by simp)
      ‖w (e k)‖ (fun i hi => by
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
        exact he (Finset.mem_Iic.mp hj))

theorem indexedDiagonalTruncation_isDiagonal (w : ι → ℂ) (s : Finset ι) :
    IndexedDiagonal (fun i => if i ∈ s then w i else 0) (indexedDiagonalTruncation w s) := by
  intro n
  apply lp.ext
  funext i
  simp only [indexedDiagonalTruncation_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hi : i = n
  · subst i; simp [lp.single_apply]
  · simp [lp.single_apply,Pi.single_eq_of_ne hi]

/-- Exact spectral power sum of an arbitrary finite coordinate cut. -/
theorem indexedDiagonalTruncation_power_sum (w : ι → ℂ) (s : Finset ι) (p : ℝ) (hp : 0 < p) :
    (∑' n, (approximationNumber (indexedDiagonalTruncation w s) n : ℝ)^p) =
      ∑ i ∈ s, ‖w i‖^p := by
  classical
  let D := indexedDiagonalTruncation w s
  let v : ι → ℂ := fun i => if i ∈ s then w i else 0
  let f : Fin s.card ≃ s := s.equivFin.symm
  let σ := Tuple.sort (α := OrderDual ℝ) (fun i : Fin s.card => ‖w (f i).val‖)
  let e : Fin s.card ↪ ι := ⟨fun i => (f (σ i)).val,Subtype.val_injective.comp (f.injective.comp σ.injective)⟩
  have he : ∀ i : Fin s.card, v (e i) = w (f (σ i)).val := by
    intro i
    simp [v,e,(f (σ i)).property]
  have hmono : Antitone (fun i => ‖v (e i)‖) := by
    intro i j hij
    simp only [he]
    exact Tuple.monotone_sort (α := OrderDual ℝ) (fun i : Fin s.card => ‖w (f i).val‖) hij
  have hz : ∀ i, i ∉ Set.range e → v i = 0 := by
    intro i hi
    have hn : i ∉ s := by
      intro hin
      apply hi
      refine ⟨σ.symm (f.symm ⟨i,hin⟩),?_⟩
      simp [e]
    simp [v,hn]
  have ha (i : Fin s.card) : approximationNumber D i = ‖w (f (σ i)).val‖₊ := by
    simpa only [he] using approximationNumber_finite_indexedDiagonal v D
      (indexedDiagonalTruncation_isDiagonal w s) e hmono hz i
  calc
    _ = ∑ n ∈ Finset.range s.card, (approximationNumber D n : ℝ)^p := by
      apply tsum_eq_sum
      intro n hn
      rw [approximationNumber_eq_zero_of_rank_le D n
        ((rank_indexedDiagonalTruncation_le w s).trans (by
          exact_mod_cast Nat.le_of_not_gt (by simpa using hn))),NNReal.coe_zero,Real.zero_rpow hp.ne']
    _ = ∑ i : Fin s.card, (approximationNumber D i : ℝ)^p := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin s.card, ‖w (f (σ i)).val‖^p := by simp_rw [ha,coe_nnnorm]
    _ = ∑ i : Fin s.card, ‖w (f i).val‖^p := Equiv.sum_comp σ (fun i : Fin s.card => ‖w (f i).val‖^p)
    _ = ∑ i : s, ‖w i.val‖^p := Equiv.sum_comp f (fun i : s => ‖w i.val‖^p)
    _ = ∑ i ∈ s, ‖w i‖^p := Finset.sum_coe_sort s (fun i => ‖w i‖^p)

theorem norm_indexedDiagonalTruncation_le (w : ι → ℂ) (s : Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ C) : ‖indexedDiagonalTruncation w s‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  calc
    ‖indexedDiagonalTruncation w s x‖ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      by_cases hi : i ∈ s
      · simpa [indexedDiagonalTruncation_apply,hi,norm_mul,abs_of_nonneg hC] using
          mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg (x i))
      · simp only [indexedDiagonalTruncation_apply,hi,ite_false,norm_zero]; exact norm_nonneg _
    _ = C*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,lp.norm_toNorm]

theorem approximationNumber_indexedDiagonalTruncation_le (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (s : Finset ι) (n : ℕ) :
    approximationNumber (indexedDiagonalTruncation w s) n ≤ approximationNumber D n := by
  let P := indexedDiagonalTruncation (fun _ => (1 : ℂ)) s
  have hP : ‖P‖₊ ≤ 1 := by
    exact_mod_cast norm_indexedDiagonalTruncation_le (fun _ : ι => (1 : ℂ)) s 1 (by norm_num) (by simp)
  have heq : indexedDiagonalTruncation w s = P ∘L D := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp only [ContinuousLinearMap.comp_apply,indexedDiagonalTruncation_apply,indexedDiagonal_apply w D hd,P]
    split_ifs <;> simp
  rw [heq]
  exact (approximationNumber_comp_left P D n).trans (by simpa using mul_le_mul_of_nonneg_right hP (by positivity))

theorem tendsto_cofinite_zero_of_indexed_summableValues (w : ι → ℂ) (p : ℝ) (hp : 0 < p)
    (hw : summableValues p w) : Tendsto w cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := Metric.tendsto_nhds.mp hw.tendsto_cofinite_zero (ε^p) (Real.rpow_pos_of_pos hε p)
  filter_upwards [ht] with i hi
  have hh : ‖w i‖^p < ε^p := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (w i)) p)] using hi
  simpa only [dist_zero_right] using (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hp).mp hh

/-- Any finite coefficient power sum is bounded by the full spectral power sum. -/
theorem indexedDiagonal_values_partial_le (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hp : 0 < p)
    (hD : Summable (fun n => (approximationNumber D n : ℝ)^p)) (s : Finset ι) :
    ∑ i ∈ s, ‖w i‖^p ≤ ∑' n, (approximationNumber D n : ℝ)^p := by
  rw [← indexedDiagonalTruncation_power_sum w s p hp]
  apply Summable.tsum_le_tsum _
    (finiteRankSchatten _ ⟨s.card,rank_indexedDiagonalTruncation_le w s⟩ p hp).2.2 hD
  intro n
  exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
    (by exact_mod_cast approximationNumber_indexedDiagonalTruncation_le w D hd s n) hp.le

/-- Finite spectral power sums are controlled by the coefficient sum using the full cut net. -/
theorem indexedDiagonal_spectral_partial_le (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hp : 0 < p)
    (hw : summableValues p w) (M : ℕ) :
    ∑ i ∈ Finset.range M, (approximationNumber D i : ℝ)^p ≤ ∑' i, ‖w i‖^p := by
  have hlim := indexedDiagonalTruncation_tendsto w D hd (tendsto_cofinite_zero_of_indexed_summableValues w p hp hw)
  have ht : Tendsto (fun s : Finset ι => ∑ i ∈ Finset.range M,
      (approximationNumber (indexedDiagonalTruncation w s) i : ℝ)^p)
      atTop (𝓝 (∑ i ∈ Finset.range M, (approximationNumber D i : ℝ)^p)) := by
    apply tendsto_finsetSum
    intro i hi
    exact ((Real.continuous_rpow_const hp.le).comp (continuous_approximationNumber i)).continuousAt.tendsto.comp hlim
  apply le_of_tendsto' ht
  intro s
  calc
    _ ≤ ∑' i, (approximationNumber (indexedDiagonalTruncation w s) i : ℝ)^p :=
      Summable.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
        (finiteRankSchatten _ ⟨s.card,rank_indexedDiagonalTruncation_le w s⟩ p hp).2.2
    _ = ∑ i ∈ s, ‖w i‖^p := indexedDiagonalTruncation_power_sum w s p hp
    _ ≤ ∑' i, ‖w i‖^p := Summable.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hw

theorem indexedDiagonal_summable_iff (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hp : 0 < p) :
    Summable (fun n => (approximationNumber D n : ℝ)^p) ↔ summableValues p w := by
  constructor
  · intro hD
    exact summable_of_sum_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (indexedDiagonal_values_partial_le w D hd p hp hD)
  · intro hw
    exact summable_of_sum_range_le (fun _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (indexedDiagonal_spectral_partial_le w D hd p hp hw)

theorem indexedDiagonal_power_sum_eq (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hp : 0 < p) (hw : summableValues p w) :
    (∑' n, (approximationNumber D n : ℝ)^p) = ∑' i, ‖w i‖^p := by
  apply le_antisymm
  · exact Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (indexedDiagonal_spectral_partial_le w D hd p hp hw)
  · exact Real.tsum_le_of_sum_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (indexedDiagonal_values_partial_le w D hd p hp ((indexedDiagonal_summable_iff w D hd p hp).mpr hw))

/-- The exact all-positive-p Schatten field for any index type, including p<1. -/
theorem indexedDiagonal_schatten_iff (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hp : 0 < p) : Schatten p D ↔ summableValues p w := by
  constructor
  · intro hD
    exact (indexedDiagonal_summable_iff w D hd p hp).mp hD.2.2
  · intro hw
    exact ⟨hp,compact_indexedDiagonal_of_tendsto w D hd (tendsto_cofinite_zero_of_indexed_summableValues w p hp hw),
      (indexedDiagonal_summable_iff w D hd p hp).mpr hw⟩

/-- The actual gauge has its literal coefficient power-sum formula in every positive Schatten class. -/
theorem indexedDiagonal_schattenNorm (w : ι → ℂ) (D : IndexedOperator ι)
    (hd : IndexedDiagonal w D) (p : ℝ) (hD : Schatten p D) : schattenNorm p D = valueNorm p w := by
  unfold schattenNorm valueNorm
  rw [indexedDiagonal_power_sum_eq w D hd p hD.1 ((indexedDiagonal_schatten_iff w D hd p hD.1).mp hD)]

end IndexedDiagonals
end TTO.Paper.Proved
