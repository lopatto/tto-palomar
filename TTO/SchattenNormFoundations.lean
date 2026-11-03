/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto, The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import TTO.FiniteCornerFoundations
public import TTO.FinitePowerFoundations

/-! Finite sorted Gram data for the sharp Schatten norm problem.
The sharp triangle inequality and the frozen norm laws are proved below. -/

@[expose] public section
noncomputable section
open Filter
open scoped NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ E]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Squared Gram column lengths are the actual decreasing Gram eigenvalues. -/
theorem gramBasis_norm_sq (A : E →L[ℂ] F) (i : Fin (Module.finrank ℂ E)) :
    ‖A (gramBasis A i)‖^2 = (gramSymmetric A).eigenvalues rfl i := by
  have h := (gramSymmetric A).apply_eigenvectorBasis rfl i
  change A.adjoint (A (gramBasis A i)) =
    ((gramSymmetric A).eigenvalues rfl i : ℂ) • gramBasis A i at h
  have he := congrArg (fun v : E => (inner ℂ v (gramBasis A i)).re) h
  rw [ContinuousLinearMap.adjoint_inner_left] at he
  rw [inner_smul_left (𝕜 := ℂ) (E := E)] at he
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := F),
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := E)] at he
  simpa [(gramBasis A).norm_eq_one, ← Complex.ofReal_pow] using he

/-- The native eigenbasis has decreasing singular column lengths, including zeros. -/
theorem gramBasis_norm_antitone (A : E →L[ℂ] F) :
    Antitone (fun i : Fin (Module.finrank ℂ E) => ‖A (gramBasis A i)‖) := by
  intro i j hij
  have h := (gramSymmetric A).eigenvalues_antitone rfl hij
  rw [← gramBasis_norm_sq A i, ← gramBasis_norm_sq A j] at h
  exact le_of_sq_le_sq h (norm_nonneg _)

/-- Exact finite-dimensional approximation numbers, without restricting the codomain dimension. -/
theorem approximationNumber_gramBasis (A : E →L[ℂ] F) (k : Fin (Module.finrank ℂ E)) :
    (approximationNumber A k : ℝ) = ‖A (gramBasis A k)‖ := by
  have hd : Diagonal (finiteGramWeights A) (finiteGramDiagonal A) := by
    intro n
    by_cases hn : n < Module.finrank ℂ E
    · simpa [finiteGramWeights,hn] using finiteGramDiagonal_single A ⟨n,hn⟩
    · simp [finiteGramDiagonal_single_outside A n (not_lt.mp hn),finiteGramWeights,hn]
  have he : Antitone (fun i : Fin (Module.finrank ℂ E) =>
      ‖finiteGramWeights A (Fin.valEmbedding i)‖) := by
    simpa using gramBasis_norm_antitone A
  have hz : ∀ n, n ∉ Set.range (Fin.valEmbedding (n := Module.finrank ℂ E)) →
      finiteGramWeights A n = 0 := by
    intro n hn
    have hnot : ¬n < Module.finrank ℂ E := by
      intro hlt
      exact hn ⟨⟨n,hlt⟩,rfl⟩
    simp [finiteGramWeights,hnot]
  rw [approximationNumber_finiteGram]
  have h := approximationNumber_finite_diagonal (finiteGramWeights A) (finiteGramDiagonal A)
    hd Fin.valEmbedding he hz k
  simpa using congrArg (fun x : ℝ≥0 => (x : ℝ)) h

/-- An explicitly given coefficientwise limit remains in the same closed Schatten ball.
This is valid for every p>0, including the quasi-norm range. -/
theorem schatten_ball_weak_closed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (p : ℝ) (hp : 0 < p) (B : ℝ)
    (T : ℕ → H →L[ℂ] H) (Z : H →L[ℂ] H)
    (hT : ∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ B)
    (hLim : ∀ x y : H, Tendsto (fun n => inner ℂ y (T n x)) atTop (𝓝 (inner ℂ y (Z x)))) :
    Schatten p Z ∧ schattenNorm p Z ≤ B := by
  obtain ⟨k,hk,A,hA,hAB,hconv⟩ := schatten_ball_subsequence p hp B T hT
  have he : A = Z := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hl : Tendsto (fun n => inner ℂ y (T (k n) x)) atTop (𝓝 (inner ℂ y (Z x))) := by
      convert (hLim x y).comp hk.tendsto_atTop using 1
      funext n; rfl
    exact tendsto_nhds_unique (hconv x y) hl
  exact he ▸ ⟨hA,hAB⟩

/- The following two real weighted-sum arguments are adapted from Tau Ceti,
Algebra/Order/BigOperators/Sum/ByParts.lean, revision
 d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad (Apache-2.0).
Only this narrow proof is adapted; Tau is not a project dependency. -/

/-- Partial-sum dominance survives nonnegative decreasing weights. -/
theorem weighted_prefix_comparison {f g w : ℕ → ℝ} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range k, g i)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ∑ i ∈ Finset.range N, w i*f i ≤ ∑ i ∈ Finset.range N, w i*g i := by
  let d : ℕ → ℝ := fun i => g i-f i
  have hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ Finset.range k, d i := fun k hk => by
    simpa [d,Finset.sum_sub_distrib] using hfg k hk
  suffices 0 ≤ ∑ i ∈ Finset.range N, w i*d i by
    simpa [d,mul_sub,Finset.sum_sub_distrib] using this
  have hparts := Finset.sum_range_by_parts w d N
  simp only [smul_eq_mul] at hparts
  rw [hparts,sub_nonneg]
  calc
    ∑ i ∈ Finset.range (N-1), (w (i+1)-w i)*∑ j ∈ Finset.range (i+1), d j
      ≤ ∑ _ ∈ Finset.range (N-1), (0 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        rw [← neg_sub (w i) (w (i+1)),neg_mul]
        exact neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr (hw i (by omega)))
          (hD (i+1) (by omega)))
    _ = 0 := Finset.sum_const_zero
    _ ≤ w (N-1)*∑ j ∈ Finset.range N, d j := mul_nonneg hw0 (hD N le_rfl)

/-- At most k units of weights in [0,1] cannot exceed the leading k decreasing terms. -/
theorem weighted_prefix_bound {w c : ℕ → ℝ} {N k : ℕ} (hk : k ≤ N)
    (hc0 : ∀ i < N, 0 ≤ c i) (hc1 : ∀ i < N, c i ≤ 1)
    (hck : ∑ i ∈ Finset.range N, c i ≤ k)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ∑ i ∈ Finset.range N, w i*c i ≤ ∑ i ∈ Finset.range k, w i := by
  have hf (m : ℕ) : {i ∈ Finset.range m | i < k} = Finset.range (min m k) := by
    ext; simp
  have hg : (∑ i ∈ Finset.range N, w i*(if i < k then 1 else 0)) =
      ∑ i ∈ Finset.range k, w i := by
    simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter,hf,min_eq_right hk]
  rw [← hg]
  apply weighted_prefix_comparison (fun m hm => ?_) hw hw0
  simp only [← Finset.sum_filter,hf,Finset.sum_const,Finset.card_range,nsmul_one]
  rcases le_total m k with hmk | hkm
  · rw [min_eq_left hmk]
    calc
      ∑ i ∈ Finset.range m, c i ≤ ∑ _ ∈ Finset.range m, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => hc1 i (by rw [Finset.mem_range] at hi; omega))
      _ = m := by simp
  · rw [min_eq_right hkm]
    calc
      ∑ i ∈ Finset.range m, c i ≤ ∑ i ∈ Finset.range N, c i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm)
          (fun i hi _ => hc0 i (Finset.mem_range.mp hi))
      _ ≤ k := hck


/-- The actual finite Gram expansion, with normalized zero images retained as zero. -/
theorem gramBasis_expansion (A : E →L[ℂ] F) (x : E) :
    A x = ∑ j : Fin (Module.finrank ℂ E),
      (inner ℂ (gramBasis A j) x * (‖A (gramBasis A j)‖ : ℂ)) •
        NormedSpace.normalize (A (gramBasis A j)) := by
  calc
    A x = ∑ j : Fin (Module.finrank ℂ E), inner ℂ (gramBasis A j) x • A (gramBasis A j) := by
      simpa only [map_sum,map_smul] using congrArg A ((gramBasis A).sum_repr' x).symm
    _ = _ := Finset.sum_congr rfl (fun j _ => by rw [mul_smul,complex_norm_smul_normalize])

omit [CompleteSpace F] [FiniteDimensional ℂ E] in
/-- Finite weights in [0,1] of mass at most k are bounded by the first k approximation numbers.
This adapts the weighted step in Tau Ceti InnerProductSpace/KyFan at the recorded revision. -/
theorem approximation_weight_bound (A : E →L[ℂ] F) (k : ℕ)
    (c : Fin (Module.finrank ℂ E) → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hck : ∑ j, c j ≤ k) :
    (∑ j : Fin (Module.finrank ℂ E), (approximationNumber A j : ℝ)*c j) ≤
      ∑ n ∈ Finset.range k, (approximationNumber A n : ℝ) := by
  have hsum (f : ℕ → ℝ) : (∑ j : Fin (Module.finrank ℂ E), f j*c j) =
      ∑ n ∈ Finset.range (Module.finrank ℂ E), f n*(if h : n < Module.finrank ℂ E then c ⟨n,h⟩ else 0) := by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun n => f n*(if h : n < Module.finrank ℂ E then c ⟨n,h⟩ else 0)) (Module.finrank ℂ E))
  have hcard : ∑ j, c j ≤ Module.finrank ℂ E :=
    (Finset.sum_le_sum (fun j _ => hc1 j)).trans (by simp)
  rw [hsum (fun n => (approximationNumber A n : ℝ))]
  apply le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (min_le_left k (Module.finrank ℂ E)))
    (fun n _ _ => (approximationNumber A n).coe_nonneg))
  refine weighted_prefix_bound (N := Module.finrank ℂ E) (k := min k (Module.finrank ℂ E))
    (w := fun n => (approximationNumber A n : ℝ))
    (c := fun n => if h : n < Module.finrank ℂ E then c ⟨n,h⟩ else 0)
    (min_le_right _ _) ?_ ?_ ?_
    (fun i _ => NNReal.coe_le_coe.mpr (approximationNumber_antitone A (Nat.le_succ i)))
    (approximationNumber A _).coe_nonneg
  · intro n hn
    simpa [hn] using hc0 ⟨n,hn⟩
  · intro n hn
    simpa [hn] using hc1 ⟨n,hn⟩
  · have he := hsum (fun _ => 1)
    simp only [one_mul] at he
    rw [← he,Nat.cast_min]
    exact le_min hck hcard

/-- The ordinary finite Ky Fan maximum principle, for arbitrary complete codomain.
The weight argument adapts Tau Ceti InnerProductSpace/KyFan at the recorded revision;
no newer singular-value API or dependency is imported. -/
theorem finite_kyFan_upper {ι : Type*} [Fintype ι] (A : E →L[ℂ] F)
    (u : ι → F) (v : ι → E) (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    ‖∑ i, inner ℂ (u i) (A (v i))‖ ≤
      ∑ n ∈ Finset.range (Fintype.card ι), (approximationNumber A n : ℝ) := by
  classical
  let a : Fin (Module.finrank ℂ E) → ℝ := fun j => ∑ i, ‖inner ℂ (gramBasis A j) (v i)‖^2
  let b : Fin (Module.finrank ℂ E) → ℝ := fun j =>
    ∑ i, ‖inner ℂ (NormedSpace.normalize (A (gramBasis A j))) (u i)‖^2
  have ha1 (j) : a j ≤ 1 := by
    have h := hv.sum_inner_products_le (s := Finset.univ) (gramBasis A j)
    simpa [a,norm_inner_symm,(gramBasis A).norm_eq_one] using h
  have hb1 (j) : b j ≤ 1 := by
    have h := hu.sum_inner_products_le (s := Finset.univ) (NormedSpace.normalize (A (gramBasis A j)))
    have hn : ‖NormedSpace.normalize (A (gramBasis A j))‖ ≤ 1 := by
      by_cases hz : A (gramBasis A j) = 0
      · simp [hz]
      · rw [NormedSpace.norm_normalize hz]
    have hb : b j ≤ ‖NormedSpace.normalize (A (gramBasis A j))‖^2 := by
      simpa [b,norm_inner_symm] using h
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hn)
  have hasum : ∑ j, a j ≤ Fintype.card ι := by
    simp only [a]
    rw [Finset.sum_comm]
    simp [(gramBasis A).sum_sq_norm_inner_right,hv.1]
  have hbsum : ∑ j, b j ≤ Fintype.card ι := by
    simp only [b]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        simpa [hu.1 i] using normalizedFamily_bessel (fun j => A (gramBasis A j))
          (gramBasis_images_orthogonal A) (u i))
      _ = _ := by simp
  apply le_trans ?_ (approximation_weight_bound A (Fintype.card ι) (fun j => (a j+b j)/2)
    (fun j => by dsimp [a,b]; positivity) (fun j => by linarith [ha1 j,hb1 j])
    (by rw [← Finset.sum_div,Finset.sum_add_distrib]; linarith))
  calc
    _ = ‖∑ j : Fin (Module.finrank ℂ E), (‖A (gramBasis A j)‖ : ℂ)*
        ∑ i, inner ℂ (gramBasis A j) (v i)*inner ℂ (u i) (NormedSpace.normalize (A (gramBasis A j)))‖ := by
      congr 1
      have he (i : ι) : inner ℂ (u i) (A (v i)) =
          ∑ j : Fin (Module.finrank ℂ E),
            (inner ℂ (gramBasis A j) (v i)*(‖A (gramBasis A j)‖ : ℂ))*
              inner ℂ (u i) (NormedSpace.normalize (A (gramBasis A j))) := by
        rw [gramBasis_expansion A (v i),inner_sum]
        exact Finset.sum_congr rfl (fun j _ => inner_smul_right _ _ _)
      simp_rw [he,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j : Fin (Module.finrank ℂ E), (approximationNumber A j : ℝ)*((a j+b j)/2) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Complex.norm_real,norm_norm,approximationNumber_gramBasis]
      apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
      simp only [a,b,← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_inner_symm (u i)]
      nlinarith [two_mul_le_add_sq ‖inner ℂ (gramBasis A j) (v i)‖
        ‖inner ℂ (NormedSpace.normalize (A (gramBasis A j))) (u i)‖]


/-- A leading Gram prefix is attained on its nonzero images; no codomain basis completion. -/
theorem finite_kyFan_attainment (A : E →L[ℂ] F) (k : ℕ) (hk : k ≤ Module.finrank ℂ E) :
    ∃ s : Finset (Fin (Module.finrank ℂ E)), s.card ≤ k ∧
      Orthonormal ℂ (fun j : s => NormedSpace.normalize (A (gramBasis A j.val))) ∧
      Orthonormal ℂ (fun j : s => gramBasis A j.val) ∧
      (∑ j : s, inner ℂ (NormedSpace.normalize (A (gramBasis A j.val))) (A (gramBasis A j.val))) =
        (↑(∑ n ∈ Finset.range k, (approximationNumber A n : ℝ)) : ℂ) := by
  classical
  let s : Finset (Fin (Module.finrank ℂ E)) :=
    Finset.univ.filter (fun j => j.val < k ∧ A (gramBasis A j) ≠ 0)
  have hc : s.card ≤ k := by
    let f : s → Fin k := fun j => ⟨j.val.val,(Finset.mem_filter.mp j.property).2.1⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun z : Fin k => z.val) hij
    simpa using Fintype.card_le_of_injective f hf
  have hu : Orthonormal ℂ (fun j : s => NormedSpace.normalize (A (gramBasis A j.val))) := by
    refine ⟨fun j => NormedSpace.norm_normalize (Finset.mem_filter.mp j.property).2.2,?_⟩
    intro i j hij
    have hne : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [NormedSpace.normalize,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
      gramBasis_images_orthogonal A hne,smul_zero]
  have hv : Orthonormal ℂ (fun j : s => gramBasis A j.val) :=
    (gramBasis A).orthonormal.comp (fun j : s => j.val) Subtype.val_injective
  refine ⟨s,hc,hu,hv,?_⟩
  have hp : (∑ j : Fin (Module.finrank ℂ E),
      if j.val < k then (approximationNumber A j : ℝ) else 0) =
      ∑ n ∈ Finset.range k, (approximationNumber A n : ℝ) := by
    calc
      _ = ∑ n ∈ Finset.range (Module.finrank ℂ E),
          if n < k then (approximationNumber A n : ℝ) else 0 :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext n
        simp only [Finset.mem_filter,Finset.mem_range]
        omega
  calc
    _ = ∑ j : Fin (Module.finrank ℂ E),
        if j.val < k then (‖A (gramBasis A j)‖ : ℂ) else 0 := by
      simp_rw [inner_normalize_self]
      rw [Finset.sum_coe_sort s (fun j => (‖A (gramBasis A j)‖ : ℂ))]
      change (∑ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ E) =>
        j.val < k ∧ A (gramBasis A j) ≠ 0), (‖A (gramBasis A j)‖ : ℂ)) = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < k
      · by_cases hz : A (gramBasis A j) = 0
        · simp [hj,hz]
        · simp [hj,hz]
      · simp [hj]
    _ = _ := by
      simp_rw [← approximationNumber_gramBasis]
      have he := congrArg (fun x : ℝ => (x : ℂ)) hp
      simpa only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero] using he

/-- The sharp Ky Fan prefix triangle, before any passage to Schatten powers. -/
theorem finite_kyFan_add (A B : E →L[ℂ] F) (k : ℕ) (hk : k ≤ Module.finrank ℂ E) :
    (∑ n ∈ Finset.range k, (approximationNumber (A+B) n : ℝ)) ≤
      (∑ n ∈ Finset.range k, (approximationNumber A n : ℝ))+
      ∑ n ∈ Finset.range k, (approximationNumber B n : ℝ) := by
  classical
  obtain ⟨s,hc,hu,hv,hs⟩ := finite_kyFan_attainment (A+B) k hk
  let u : s → F := fun j => NormedSpace.normalize ((A+B) (gramBasis (A+B) j.val))
  let v : s → E := fun j => gramBasis (A+B) j.val
  have hmono (T : E →L[ℂ] F) :
      (∑ n ∈ Finset.range s.card, (approximationNumber T n : ℝ)) ≤
        ∑ n ∈ Finset.range k, (approximationNumber T n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hc)
      (fun n _ _ => (approximationNumber T n).coe_nonneg)
  have hA := finite_kyFan_upper A u v hu hv
  have hB := finite_kyFan_upper B u v hu hv
  simp only [Fintype.card_coe] at hA hB
  calc
    _ = ‖∑ j : s, inner ℂ (u j) ((A+B) (v j))‖ := by
      rw [hs,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
      positivity
    _ = ‖(∑ j : s, inner ℂ (u j) (A (v j)))+(∑ j : s, inner ℂ (u j) (B (v j)))‖ := by
      simp only [add_apply,inner_add_right,Finset.sum_add_distrib]
    _ ≤ ‖∑ j : s, inner ℂ (u j) (A (v j))‖+‖∑ j : s, inner ℂ (u j) (B (v j))‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add hA hB).trans (add_le_add (hmono A) (hmono B))


/-- The finite-source sharp inequality used in the reduction, proved below via the scalar power estimate.
This completely defined intermediate Prop is discharged by finiteSchattenTriangle. -/
def FiniteSchattenTriangle : Prop :=
  ∀ (X Y : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (p : ℝ), 1 ≤ p → ∀ A B : X →L[ℂ] Y,
      schattenNorm p (A+B) ≤ schattenNorm p A+schattenNorm p B

section InfiniteSharpTriangle
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite-source sharp estimates give uniformly bounded actual Schatten approximants. -/
theorem exists_schatten_sum_cut (hFin : FiniteSchattenTriangle) (p : ℝ) (hp : 1 ≤ p)
    (A B : H →L[ℂ] H) (hA : Schatten p A) (hB : Schatten p B) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : H →L[ℂ] H, Schatten p C ∧ schattenNorm p C ≤ schattenNorm p A+schattenNorm p B ∧
      ‖(A+B)-C‖ ≤ 2*ε := by
  obtain ⟨M,hM,P,hP,hPJ,hEA,hEB⟩ := simultaneous_compact_source_cut A B hA.2.1 hB.2.1 ε hε
  let : FiniteDimensional ℂ M := hM
  let : CompleteSpace M := FiniteDimensional.complete ℂ M
  have hJ : ‖M.subtypeL‖ ≤ 1 := norm_isometry_clm_le_one M.subtypeₗᵢ
  let C : H →L[ℂ] H := ((A+B) ∘L M.subtypeL) ∘L P
  have hC : Schatten p C := by
    simpa only [C,ContinuousLinearMap.comp_assoc] using
      schatten_comp_right (schatten_add hA hB) (M.subtypeL ∘L P)
  have hbound (T : H →L[ℂ] H) (hT : Schatten p T) :
      schattenNorm p (T ∘L M.subtypeL) ≤ schattenNorm p T := by
    have ht := schattenNorm_le_of_approx_le hT 1 zero_le_one (fun n => by
      simpa only [one_mul] using NNReal.coe_le_coe.mpr
        (approximationNumber_comp_right_contraction T M.subtypeL hJ n))
    simpa only [one_mul] using ht
  refine ⟨C,hC,?_,?_⟩
  · calc
      schattenNorm p C = schattenNorm p ((A+B) ∘L M.subtypeL) :=
        schattenNorm_comp_right_retract P M.subtypeL hP hJ hPJ _ p
      _ = schattenNorm p ((A ∘L M.subtypeL)+(B ∘L M.subtypeL)) := by
        rw [ContinuousLinearMap.add_comp]
      _ ≤ schattenNorm p (A ∘L M.subtypeL)+schattenNorm p (B ∘L M.subtypeL) :=
        hFin M H p hp _ _
      _ ≤ _ := add_le_add (hbound A hA) (hbound B hB)
  · have he : (A+B)-C = (A-A ∘L M.subtypeL ∘L P)+(B-B ∘L M.subtypeL ∘L P) := by
      simp only [C,ContinuousLinearMap.add_comp]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)

/-- Passing the common finite cuts to the actual operator proves the infinite sharp inequality. -/
theorem schattenNorm_add_of_finite (hFin : FiniteSchattenTriangle) (p : ℝ) (hp : 1 ≤ p)
    (A B : H →L[ℂ] H) (hA : Schatten p A) (hB : Schatten p B) :
    schattenNorm p (A+B) ≤ schattenNorm p A+schattenNorm p B := by
  have hex (n : ℕ) := exists_schatten_sum_cut hFin p hp A B hA hB
    (1/((n : ℝ)+1)) (by positivity)
  choose C hCs hCB hCE using hex
  have hz : Tendsto (fun n : ℕ => 2*(1/((n : ℝ)+1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hnorm : Tendsto (fun n => ‖C n-(A+B)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => by simpa only [norm_sub_rev] using hCE n) hz
  have hlim : Tendsto C atTop (𝓝 (A+B)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_eq_norm] using hnorm
  have hcoeff (x y : H) :
      Tendsto (fun n => inner ℂ y (C n x)) atTop (𝓝 (inner ℂ y ((A+B) x))) := by
    have hcont : Continuous (fun T : H →L[ℂ] H => inner ℂ y (T x)) := by fun_prop
    exact (hcont.tendsto (A+B)).comp hlim
  exact (schatten_ball_weak_closed p hA.1 (schattenNorm p A+schattenNorm p B) C (A+B)
    (fun n => ⟨hCs n,hCB n⟩) hcoeff).2

/-- The frozen sub-bound interface follows from a genuine finite-source proof obligation. -/
theorem schattenNormLaws_of_finite (hFin : FiniteSchattenTriangle) : SchattenNormLaws := by
  constructor
  intro H _ _ _ p A B hp hA hB
  have ht := schattenNorm_add_of_finite hFin p hp A (-B) hA (schatten_neg hB)
  simpa only [sub_eq_add_neg,schattenNorm,approximationNumber_neg] using ht

end InfiniteSharpTriangle


/-- For a finite source the literal gauge is the finite approximation-number power sum. -/
theorem schattenNorm_finite_prefix (A : E →L[ℂ] F) (p : ℝ) (hp : 0 < p) :
    schattenNorm p A = (∑ n ∈ Finset.range (Module.finrank ℂ E),
      (approximationNumber A n : ℝ)^p)^(1/p) := by
  unfold schattenNorm
  congr 1
  calc
    _ = ∑ j : Fin (Module.finrank ℂ E), ‖A (gramBasis A j)‖^p := finiteGram_power_sum A p hp
    _ = ∑ j : Fin (Module.finrank ℂ E), (approximationNumber A j : ℝ)^p := by
      simp only [approximationNumber_gramBasis]
    _ = _ := Fin.sum_univ_eq_sum_range (fun n => (approximationNumber A n : ℝ)^p)
      (Module.finrank ℂ E)

/-- The genuine finite-source sharp triangle inequality, now with no proof parameter. -/
theorem finiteSchattenTriangle : FiniteSchattenTriangle := by
  intro X Y _ _ _ _ _ _ p hp A B
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rw [schattenNorm_finite_prefix (A+B) p hp0,schattenNorm_finite_prefix A p hp0,
    schattenNorm_finite_prefix B p hp0]
  exact finite_power_norm_add_of_prefix (fun n => (approximationNumber (A+B) n : ℝ))
    (fun n => (approximationNumber A n : ℝ)) (fun n => (approximationNumber B n : ℝ))
    (Module.finrank ℂ X) p hp
    (fun n _ => (approximationNumber (A+B) n).coe_nonneg)
    (fun n _ => (approximationNumber A n).coe_nonneg)
    (fun n _ => (approximationNumber B n).coe_nonneg)
    (fun n _ => NNReal.coe_le_coe.mpr (approximationNumber_antitone (A+B) (Nat.le_succ n)))
    (fun k hk => finite_kyFan_add A B k hk)

/-- The sharp norm laws required by the atomic proofs, without an open norm obligation. -/
theorem schattenNormLaws : SchattenNormLaws := schattenNormLaws_of_finite finiteSchattenTriangle

/-- The actual sharp triangle on every Schatten p class for p≥1. -/
theorem schattenNorm_add_le_sharp {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (p : ℝ) (hp : 1 ≤ p)
    (A B : H →L[ℂ] H) (hA : Schatten p A) (hB : Schatten p B) :
    schattenNorm p (A+B) ≤ schattenNorm p A+schattenNorm p B :=
  schattenNorm_add_of_finite finiteSchattenTriangle p hp A B hA hB

/-- L8 now has only its triangular-bound and raw regularization obligations left. -/
theorem oneAtomSplitting_of_triangular_regularization (hT : TriangularBoundObligation)
    (hR : AtomicRegularizationObligation) : OneAtomConclusion :=
  oneAtomSplitting_of_regularization_and_triangle hT hR schattenNormLaws

/-- The full finite-atom reduction now supplies the proved sharp Schatten norm laws. -/
theorem finiteAtomClassification_of_corona_oneAtom (hCo : CoronaWitnessObligation)
    (hOne : OneAtomObligation) : FiniteAtomConclusion :=
  finiteAtomClassification_of_witness hCo hOne schattenNormLaws

end TTO.Paper.Proved
