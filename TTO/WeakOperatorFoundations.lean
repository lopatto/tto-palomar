/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BlaschkeFoundations

/-! Actual weak operator subsequence and approximation-number limit infrastructure. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section WeakLimits
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Norm bounds pass to genuine weak limits. -/
theorem weak_limit_norm_le (x : ℕ → H) (y : H) (M : ℝ)
    (hlim : ∀ g : H, Tendsto (fun n => inner ℂ g (x n)) atTop (𝓝 (inner ℂ g y)))
    (hb : ∀ n, ‖x n‖ ≤ M) : ‖y‖ ≤ M := by
  have he := le_of_tendsto (hlim y).norm (Filter.Eventually.of_forall (fun n =>
    (norm_inner_le_norm y (x n)).trans (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg y))))
  have hn : ‖y‖^2 ≤ ‖y‖*M := by
    rw [← inner_self_re_eq_norm,← norm_sq_eq_re_inner] at he
    exact he
  by_cases hy : ‖y‖=0
  · rw [hy]
    exact (norm_nonneg (x 0)).trans (hb 0)
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    nlinarith

variable [CompleteSpace H]

/-- One subsequence simultaneously handles a countable family of bounded Hilbert vectors. -/
theorem weak_countable_subsequence [SeparableSpace H] (x : ℕ → ℕ → H) (R : ℕ → ℝ)
    (hb : ∀ n k, ‖x n k‖ ≤ R k) :
    ∃ y : ℕ → H, (∀ k, ‖y k‖ ≤ R k) ∧ ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ k, ∀ g : H, Tendsto (fun n => inner ℂ g (x (r n) k)) atTop (𝓝 (inner ℂ g (y k))) := by
  let K (k : ℕ) := WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) (R k)
  have hc (k : ℕ) : IsCompact (K k) := WeakDual.isCompact_closedBall 0 (R k)
  let (k : ℕ) : CompactSpace (K k) := isCompact_iff_compactSpace.mp (hc k)
  let (k : ℕ) : MetrizableSpace (K k) := WeakDual.metrizable_of_isCompact ℂ H (K k) (hc k)
  let v (n : ℕ) : ∀ k, K k := fun k => ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (x n k)),by
    rw [Set.mem_preimage,Metric.mem_closedBall]
    change dist (InnerProductSpace.toDual ℂ H (x n k)) (0 : StrongDual ℂ H) ≤ R k
    rw [dist_zero_right,(InnerProductSpace.toDual ℂ H).norm_map]
    exact hb n k⟩
  obtain ⟨l,r,hr,hlim⟩ := CompactSpace.tendsto_subseq v
  let y (k : ℕ) := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual (l k).val)
  refine ⟨y,fun k => ?_,r,hr,fun k g => ?_⟩
  · change ‖(InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual (l k).val)‖ ≤ R k
    rw [(InnerProductSpace.toDual ℂ H).symm.norm_map]
    have hl := (l k).property
    change WeakDual.toStrongDual (l k).val ∈ Metric.closedBall (0 : StrongDual ℂ H) (R k) at hl
    simpa only [Metric.mem_closedBall,dist_zero_right] using hl
  · have ht := (tendsto_pi_nhds.mp hlim k)
    have he := ((WeakDual.eval_continuous (𝕜 := ℂ) g).comp continuous_subtype_val).tendsto (l k)
    have hv := Complex.continuous_conj.continuousAt.tendsto.comp (he.comp ht)
    convert hv using 1
    · funext n
      change inner ℂ g (x (r n) k) = conj (inner ℂ (x (r n) k) g)
      exact (inner_conj_symm _ _).symm
    · congr 1
      change inner ℂ g (y k) = conj ((WeakDual.toStrongDual (l k).val) g)
      rw [← InnerProductSpace.toDual_symm_apply,inner_conj_symm]

/-- A uniformly bounded operator sequence on a separable Hilbert space has a genuine WOT subsequence. -/
theorem bounded_operator_subsequence [SeparableSpace H] (T : ℕ → H →L[ℂ] H) (B : ℝ)
    (hb : ∀ n, ‖T n‖ ≤ B) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ Z : H →L[ℂ] H, ‖Z‖ ≤ B ∧
      ∀ f g : H, Tendsto (fun n => inner ℂ g (T (r n) f)) atTop (𝓝 (inner ℂ g (Z f))) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg (T 0)).trans (hb 0)
  let d := denseSeq H
  obtain ⟨q,_hq,r,hr,hweak⟩ := weak_countable_subsequence (fun n k => T n (d k))
    (fun k => B*‖d k‖) (fun n k => (T n).le_opNorm (d k) |>.trans
      (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg (d k))))
  let e := Finsupp.linearCombination ℂ d
  let f := Finsupp.linearCombination ℂ q
  have hfinite (c : ℕ →₀ ℂ) (g : H) :
      Tendsto (fun n => inner ℂ g (T (r n) (e c))) atTop (𝓝 (inner ℂ g (f c))) := by
    change Tendsto (fun n => inner ℂ g (T (r n) (∑ i ∈ c.support, c i • d i))) atTop
      (𝓝 (inner ℂ g (∑ i ∈ c.support, c i • q i)))
    simp only [map_sum,map_smul,inner_sum,inner_smul_right]
    exact tendsto_finsetSum c.support (fun i _ => (hweak i g).const_mul (c i))
  have hnorm (c : ℕ →₀ ℂ) : ‖f c‖ ≤ B*‖e c‖ :=
    weak_limit_norm_le (fun n => T (r n) (e c)) (f c) (B*‖e c‖) (hfinite c)
      (fun n => (T (r n)).le_opNorm (e c) |>.trans (mul_le_mul_of_nonneg_right (hb (r n)) (norm_nonneg _)))
  have hd : DenseRange e := by
    change Dense (Set.range e)
    change Dense (↑(LinearMap.range e) : Set H)
    rw [show LinearMap.range e = Submodule.span ℂ (Set.range d) from Finsupp.range_linearCombination ℂ]
    exact Dense.mono Submodule.subset_span (denseRange_denseSeq H)
  let Z := f.extendOfNorm e
  have hZ : ‖Z‖ ≤ B := Z.opNorm_le_bound hB (LinearMap.norm_extendOfNorm_apply_le hd B hnorm)
  have hZq (i : ℕ) : Z (d i) = q i := by
    have he := LinearMap.extendOfNorm_eq hd ⟨B,hnorm⟩ (Finsupp.single i (1 : ℂ))
    simpa only [e,f,Finsupp.linearCombination_single,one_smul] using he
  refine ⟨r,hr,Z,hZ,fun x g => ?_⟩
  let D := 1+2*B*‖g‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  let w (n : ℕ) := (D⁻¹ : ℂ) • (T (r n)-Z).adjoint g
  have hw (n : ℕ) : ‖w n‖ ≤ 1 := by
    have hA : ‖(T (r n)-Z).adjoint g‖ ≤ D := by
      have he := (T (r n)-Z).adjoint.le_opNorm g
      rw [ContinuousLinearMap.adjoint.norm_map] at he
      have hs : ‖T (r n)-Z‖ ≤ 2*B := (norm_sub_le _ _).trans (by linarith [hb (r n)])
      have hh := mul_le_mul_of_nonneg_right hs (norm_nonneg g)
      dsimp [D]
      linarith
    change ‖(D⁻¹ : ℂ) • (T (r n)-Z).adjoint g‖ ≤ 1
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hD.le)).trans_eq (inv_mul_cancel₀ (ne_of_gt hD))
  have hwval (n : ℕ) (v : H) : inner ℂ v (w n) =
      (D⁻¹ : ℂ)*conj (inner ℂ g (T (r n) v)-inner ℂ g (Z v)) := by
    rw [show w n = (D⁻¹ : ℂ) • (T (r n)-Z).adjoint g from rfl,inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
    simp only [sub_apply,inner_sub_left,map_sub,inner_conj_symm]
  have hdspan : Dense (Submodule.span ℂ (Set.range d) : Set H) :=
    Dense.mono Submodule.subset_span (denseRange_denseSeq H)
  have htest (i : ℕ) : Tendsto (fun n => inner ℂ (d i) (w n)) atTop (𝓝 0) := by
    have ht := (hweak i g).sub_const (inner ℂ g (q i))
    rw [sub_self] at ht
    have hc := Complex.continuous_conj.continuousAt.tendsto.comp ht
    simpa only [Function.comp_apply,hwval,hZq,map_zero,mul_zero] using hc.const_mul (D⁻¹ : ℂ)
  have hall := tendsto_inner_of_dense_tests atTop w hw d hdspan htest x
  have hscaled := Complex.continuous_conj.continuousAt.tendsto.comp (hall.const_mul (D : ℂ))
  have hc (n : ℕ) : conj ((D : ℂ)*inner ℂ x (w n)) =
      inner ℂ g (T (r n) x)-inner ℂ g (Z x) := by
    rw [hwval,← mul_assoc,mul_inv_cancel₀ hDc,one_mul,Complex.conj_conj]
  have hdiff : Tendsto (fun n => inner ℂ g (T (r n) x)-inner ℂ g (Z x)) atTop (𝓝 0) := by
    convert hscaled using 1
    · funext n; exact (hc n).symm
    · simp
  have ht := hdiff.add_const (inner ℂ g (Z x))
  simpa only [sub_add_cancel,zero_add] using ht

omit [CompleteSpace H] in
/-- Compact images have separable range even when the ambient Hilbert space is not separable. -/
theorem compact_range_isSeparable (A : H →L[ℂ] H) (hA : IsCompactOperator A) : IsSeparable (Set.range A) := by
  have hs : IsSeparable (⋃ n : ℕ, closure (A '' Metric.closedBall 0 (n : ℝ))) :=
    IsSeparable.iUnion (fun n => (hA.isCompact_closure_image_closedBall (n : ℝ)).isSeparable)
  apply hs.mono
  rintro _ ⟨x,rfl⟩
  obtain ⟨n,hn⟩ := exists_nat_ge ‖x‖
  exact Set.mem_iUnion.mpr ⟨n,subset_closure ⟨x,by simpa only [Metric.mem_closedBall,dist_zero_right] using hn,rfl⟩⟩

/-- The actual common support of a sequence and its adjoints. -/
def compactSequenceSupport (T : ℕ → H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ (⋃ n, Set.range (T n) ∪ Set.range (T n).adjoint)).topologicalClosure

instance compactSequenceSupport_complete (T : ℕ → H →L[ℂ] H) : CompleteSpace (compactSequenceSupport T) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem compactSequenceSupport_separable (T : ℕ → H →L[ℂ] H) (hT : ∀ n, IsCompactOperator (T n)) :
    SeparableSpace (compactSequenceSupport T) := by
  have hs : IsSeparable (⋃ n, Set.range (T n) ∪ Set.range (T n).adjoint) :=
    IsSeparable.iUnion (fun n => (compact_range_isSeparable (T n) (hT n)).union
      (compact_range_isSeparable (T n).adjoint (compact_adjoint_of_compact (T n) (hT n))))
  exact (hs.span (R := ℂ)).closure.separableSpace

theorem compactSequenceSupport_mem (T : ℕ → H →L[ℂ] H) (n : ℕ) (x : H) :
    T n x ∈ compactSequenceSupport T :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨n,Or.inl ⟨x,rfl⟩⟩))

theorem compactSequenceSupport_adjoint_mem (T : ℕ → H →L[ℂ] H) (n : ℕ) (x : H) :
    (T n).adjoint x ∈ compactSequenceSupport T :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨n,Or.inr ⟨x,rfl⟩⟩))

def supportRestriction (T : ℕ → H →L[ℂ] H) (n : ℕ) : compactSequenceSupport T →L[ℂ] compactSequenceSupport T :=
  ((T n).comp (compactSequenceSupport T).subtypeL).codRestrict _ (fun x => compactSequenceSupport_mem T n x.val)

theorem supportRestriction_norm_le (T : ℕ → H →L[ℂ] H) (n : ℕ) : ‖supportRestriction T n‖ ≤ ‖T n‖ :=
  (supportRestriction T n).opNorm_le_bound (norm_nonneg _) (fun x => (T n).le_opNorm x.val)

theorem supportProjection_invariant (T : ℕ → H →L[ℂ] H) (n : ℕ) (x : H) :
    T n ((compactSequenceSupport T).orthogonalProjectionOnto x).val = T n x := by
  apply ext_inner_left ℂ
  intro g
  rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left]
  exact (compactSequenceSupport T).inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨(T n).adjoint g,compactSequenceSupport_adjoint_mem T n g⟩ x

/-- Compact sequences admit a bounded WOT subsequence on arbitrary Hilbert spaces.
The extracted limit is not asserted compact or Schatten until the separate closure argument. -/
theorem compact_operator_subsequence (T : ℕ → H →L[ℂ] H) (hT : ∀ n, IsCompactOperator (T n))
    (B : ℝ) (hb : ∀ n, ‖T n‖ ≤ B) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ Z : H →L[ℂ] H, ‖Z‖ ≤ B ∧
      ∀ f g : H, Tendsto (fun n => inner ℂ g (T (r n) f)) atTop (𝓝 (inner ℂ g (Z f))) := by
  let M := compactSequenceSupport T
  let : SeparableSpace M := compactSequenceSupport_separable T hT
  obtain ⟨r,hr,A,hA,hlim⟩ := bounded_operator_subsequence (supportRestriction T) B
    (fun n => (supportRestriction_norm_le T n).trans (hb n))
  let P := M.orthogonalProjectionOnto
  let Z := M.subtypeL ∘L A ∘L P
  have hB : 0 ≤ B := (norm_nonneg (T 0)).trans (hb 0)
  have hZ : ‖Z‖ ≤ B := by
    apply Z.opNorm_le_bound hB
    intro x
    change ‖A (P x)‖ ≤ B*‖x‖
    exact (A.le_opNorm (P x)).trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (M.norm_orthogonalProjectionOnto_apply_le x) hB))
  refine ⟨r,hr,Z,hZ,fun f g => ?_⟩
  have he (n : ℕ) : inner ℂ (P g) (supportRestriction T (r n) (P f)) = inner ℂ g (T (r n) f) := by
    rw [M.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change inner ℂ g (T (r n) (P f).val) = _
    rw [supportProjection_invariant]
  have hz : inner ℂ (P g) (A (P f)) = inner ℂ g (Z f) :=
    M.inner_orthogonalProjectionOnto_eq_of_mem_right (A (P f)) g
  simpa only [he,hz] using hlim (P f) (P g)

omit [CompleteSpace H] in
/-- Uniform finite rank is closed under coefficientwise weak operator limits. -/
theorem rank_le_of_weak_limit {I : Type*} (L : Filter I) [L.NeBot]
    (R : I → H →L[ℂ] H) (A : H →L[ℂ] H) (n : ℕ)
    (hrank : ∀ᶠ j in L, (R j).rank ≤ (n : Cardinal))
    (hlim : ∀ x y : H, Tendsto (fun j => inner ℂ y (R j x)) L (𝓝 (inner ℂ y (A x)))) :
    A.rank ≤ (n : Cardinal) := by
  classical
  by_contra hnot
  have hlt : (n : Cardinal) < A.rank := lt_of_not_ge hnot
  have hsucc : ((n+1 : ℕ) : Cardinal) ≤ A.rank := by
    simpa only [Nat.cast_add,Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨s,hs,hLI⟩ := (LinearMap.le_rank_iff_exists_linearIndependent_finset
    (f := A.toLinearMap) (n := n+1)).mp hsucc
  let V : Submodule ℂ H := Submodule.span ℂ (Set.range (fun x : ↥(s : Set H) => A x))
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let b := stdOrthonormalBasis ℂ V
  let v : ↥(s : Set H) → V := fun x => ⟨A x,Submodule.subset_span (Set.mem_range_self x)⟩
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp V.subtype hLI
  have hp (x : ↥(s : Set H)) : V.orthogonalProjectionOnto (A x) = v x :=
    V.orthogonalProjectionOnto_mem_subspace_eq_self (v x)
  have hproj (x : ↥(s : Set H)) :
      Tendsto (fun j => V.orthogonalProjectionOnto (R j x)) L (𝓝 (v x)) := by
    have ht := tendsto_finsetSum Finset.univ (fun t _ => (hlim x (b t).val).smul_const (b t))
    simpa only [← b.orthogonalProjectionOnto_apply_eq_sum,hp x] using ht
  have hfamily : Tendsto (fun j => fun x : ↥(s : Set H) => V.orthogonalProjectionOnto (R j x))
      L (𝓝 v) := tendsto_pi_nhds.mpr hproj
  have hprojLI := hfamily.eventually hv.eventually
  have hLIevent : ∀ᶠ j in L, LinearIndependent ℂ (fun x : ↥(s : Set H) => R j x) :=
    hprojLI.mono (fun j hj => LinearIndependent.of_comp V.orthogonalProjectionOnto.toLinearMap hj)
  obtain ⟨j,hjLI,hjr⟩ := (hLIevent.and hrank).exists
  have hbig : ((n+1 : ℕ) : Cardinal) ≤ (R j).rank :=
    (LinearMap.le_rank_iff_exists_linearIndependent_finset (f := (R j).toLinearMap) (n := n+1)).mpr ⟨s,hs,hjLI⟩
  have hgt : (n : Cardinal) < (R j).rank :=
    Cardinal.natCast_add_one_le_iff.mp (by simpa only [Nat.cast_add,Nat.cast_one] using hbig)
  exact (not_lt_of_ge hjr) hgt

omit [CompleteSpace H] in
/-- Approximation infima admit genuine finite-rank almost minimizers. -/
theorem exists_rank_approximation (A : H →L[ℂ] H) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : H →L[ℂ] H, R.rank ≤ (k : Cardinal) ∧ ‖A-R‖ < (approximationNumber A k : ℝ)+ε := by
  let : Nonempty {R : H →L[ℂ] H // R.rank ≤ (k : Cardinal)} := ⟨⟨0,by simp⟩⟩
  have hl : approximationNumber A k < approximationNumber A k+⟨ε,hε.le⟩ := by
    exact lt_add_of_pos_right _ hε
  change (⨅ R : {R : H →L[ℂ] H // R.rank ≤ (k : Cardinal)}, ‖A-R.val‖₊) < _ at hl
  obtain ⟨R,hR⟩ := exists_lt_of_ciInf_lt hl
  exact ⟨R.val,R.property,by exact_mod_cast hR⟩

/-- Approximation-number sublevels are closed under bounded WOT sequences. -/
theorem approximationNumber_weak_sublevel (T : ℕ → H →L[ℂ] H) (A : H →L[ℂ] H)
    (B c : ℝ) (hb : ∀ n, ‖T n‖ ≤ B) (k : ℕ)
    (ha : ∀ n, (approximationNumber (T n) k : ℝ) ≤ c)
    (hlim : ∀ x y : H, Tendsto (fun n => inner ℂ y (T n x)) atTop (𝓝 (inner ℂ y (A x)))) :
    (approximationNumber A k : ℝ) ≤ c := by
  have hc : 0 ≤ c := (approximationNumber (T 0) k).coe_nonneg.trans (ha 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hex (n : ℕ) := exists_rank_approximation (T n) k ε hε
  choose R hRank hError using hex
  have hRnorm (n : ℕ) : ‖R n‖ ≤ B+c+ε := by
    have he := norm_sub_le (T n) (T n-R n)
    rw [sub_sub_cancel] at he
    linarith [hError n,ha n,hb n]
  obtain ⟨r,hr,Z,_hZ,hZlim⟩ := compact_operator_subsequence R
    (fun n => finiteRank_compact (R n) ⟨k,hRank n⟩) (B+c+ε) hRnorm
  have hZrank : Z.rank ≤ (k : Cardinal) := rank_le_of_weak_limit atTop (fun n => R (r n)) Z k
    (Filter.Eventually.of_forall (fun n => hRank (r n))) hZlim
  have hdiff (x y : H) : Tendsto (fun n => inner ℂ y ((T (r n)-R (r n)) x)) atTop (𝓝 (inner ℂ y ((A-Z) x))) := by
    simpa only [Function.comp_apply,sub_apply,inner_sub_right] using ((hlim x y).comp hr.tendsto_atTop).sub (hZlim x y)
  have hAZ : ‖A-Z‖ ≤ c+ε := by
    apply (A-Z).opNorm_le_bound (by positivity)
    intro x
    apply weak_limit_norm_le (fun n => (T (r n)-R (r n)) x) ((A-Z) x) ((c+ε)*‖x‖) (fun y => hdiff x y)
    intro n
    exact ((T (r n)-R (r n)).le_opNorm x).trans (mul_le_mul_of_nonneg_right
      (by linarith [hError (r n),ha (r n)]) (norm_nonneg x))
  exact (show (approximationNumber A k : ℝ) ≤ ‖A-Z‖ from
    NNReal.coe_le_coe.mpr (approximationNumber_le_nnnorm_sub A hZrank)).trans hAZ

/-- Actual approximation numbers are lower semicontinuous along bounded WOT sequences. -/
theorem approximationNumber_le_of_weak_limit (T : ℕ → H →L[ℂ] H) (A : H →L[ℂ] H)
    (B : ℝ) (hb : ∀ n, ‖T n‖ ≤ B) (k : ℕ) (c : ℝ)
    (hc : Tendsto (fun n => (approximationNumber (T n) k : ℝ)) atTop (𝓝 c))
    (hlim : ∀ x y : H, Tendsto (fun n => inner ℂ y (T n x)) atTop (𝓝 (inner ℂ y (A x)))) :
    (approximationNumber A k : ℝ) ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in atTop, (approximationNumber (T n) k : ℝ) ≤ c+ε :=
    (hc.eventually (gt_mem_nhds (by linarith : c < c+ε))).mono (fun n hn => hn.le)
  obtain ⟨r,hr,hrb⟩ := extraction_of_frequently_atTop hev.frequently
  apply approximationNumber_weak_sublevel (fun n => T (r n)) A B (c+ε) (fun n => hb (r n)) k hrb
  intro x y
  convert (hlim x y).comp hr.tendsto_atTop using 1
  funext n; rfl

/-- Summable positive approximation powers force genuine compactness, without assuming it. -/
theorem compact_of_summable_approximation (A : H →L[ℂ] H) (p : ℝ) (hp : 0 < p)
    (hs : Summable (fun n => (approximationNumber A n : ℝ)^p)) : IsCompactOperator A := by
  have ht : Tendsto (fun n => (approximationNumber A n : ℝ)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := Metric.tendsto_nhds.mp hs.tendsto_atTop_zero (ε^p) (Real.rpow_pos_of_pos hε p)
    filter_upwards [he] with n hn
    have hh : (approximationNumber A n : ℝ)^p < ε^p := by
      simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (approximationNumber A n).coe_nonneg p)] using hn
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (approximationNumber A n).coe_nonneg] using
      (Real.rpow_lt_rpow_iff (approximationNumber A n).coe_nonneg hε.le hp).mp hh
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := ((Metric.tendsto_nhds.mp ht (ε/2) (by positivity)).exists)
  have hap : (approximationNumber A n : ℝ) < ε/2 := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (approximationNumber A n).coe_nonneg] using hn
  obtain ⟨R,hR,hE⟩ := exists_rank_approximation A n (ε/2) (by positivity)
  refine ⟨R,finiteRank_compact R ⟨n,hR⟩,?_⟩
  rw [dist_eq_norm]
  linarith

omit [CompleteSpace H] in
/-- Rank-zero approximation starts with the actual operator norm. -/
theorem approximationNumber_index_zero (A : H →L[ℂ] H) : approximationNumber A 0 = ‖A‖₊ := by
  apply le_antisymm (approximationNumber_le_nnnorm A 0)
  apply le_approximationNumber_iff.mpr
  intro R hR
  have hrank : R.rank = 0 := le_antisymm hR zero_le
  have hrange : R.range = ⊥ := Submodule.rank_eq_zero.mp hrank
  have hz : R = 0 := by
    have he : R.toLinearMap = 0 := LinearMap.range_eq_bot.mp hrange
    ext x
    exact congrArg (fun F : H →ₗ[ℂ] H => F x) he
  simp only [hz,sub_zero,le_refl]

omit [CompleteSpace H] in
/-- The native Schatten gauge bounds the actual operator norm for every positive exponent. -/
theorem opNorm_le_schattenNorm (p : ℝ) (A : H →L[ℂ] H) (hA : Schatten p A) :
    ‖A‖ ≤ schattenNorm p A := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg A) (schattenNorm_nonneg p A) hA.1).mp
  rw [schattenNorm_rpow hA.1]
  have he := hA.2.2.le_tsum 0 (fun n _ => Real.rpow_nonneg (approximationNumber A n).coe_nonneg p)
  simpa only [approximationNumber_index_zero,coe_nnnorm] using he

/-- Bounded Schatten balls are sequentially WOT compact, with the literal gauge bound.
This helper proves all p>0; the paper's strict-p>1 interface is supplied below. -/
theorem schatten_ball_subsequence (p : ℝ) (hp : 0 < p) (B : ℝ) (T : ℕ → H →L[ℂ] H)
    (hT : ∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ B) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ Z : H →L[ℂ] H, Schatten p Z ∧ schattenNorm p Z ≤ B ∧
      ∀ f g : H, Tendsto (fun n => inner ℂ g (T (k n) f)) atTop (𝓝 (inner ℂ g (Z f))) := by
  have hB : 0 ≤ B := (schattenNorm_nonneg p (T 0)).trans (hT 0).2
  have hop (n : ℕ) : ‖T n‖ ≤ B := (opNorm_le_schattenNorm p (T n) (hT n).1).trans (hT n).2
  obtain ⟨r,hr,Z,_hZ,hlim⟩ := compact_operator_subsequence T (fun n => (hT n).1.2.1) B hop
  let K := Set.Icc (0 : ℝ) B
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let v (j : ℕ) : ℕ → K := fun k => ⟨(approximationNumber (T (r j)) k : ℝ),
    (approximationNumber (T (r j)) k).coe_nonneg,
    (show (approximationNumber (T (r j)) k : ℝ) ≤ ‖T (r j)‖ from
      NNReal.coe_le_coe.mpr (approximationNumber_le_nnnorm _ _)).trans (hop (r j))⟩
  obtain ⟨a,s,hs,hcoord⟩ := CompactSpace.tendsto_subseq v
  have hval (k : ℕ) : Tendsto (fun n => (approximationNumber (T (r (s n))) k : ℝ)) atTop (𝓝 (a k).val) := by
    have he := (continuous_subtype_val.tendsto (a k)).comp (tendsto_pi_nhds.mp hcoord k)
    convert he using 1
    funext n; rfl
  have hap (k : ℕ) : (approximationNumber Z k : ℝ) ≤ (a k).val :=
    approximationNumber_le_of_weak_limit (fun n => T (r (s n))) Z B (fun n => hop (r (s n))) k (a k).val
      (hval k) (fun x y => by
        convert (hlim x y).comp hs.tendsto_atTop using 1
        funext n; rfl)
  have hsum (N : ℕ) : ∑ i ∈ Finset.range N, (approximationNumber Z i : ℝ)^p ≤ B^p := by
    have he := tendsto_finsetSum (Finset.range N) (fun i _ => (hval i).rpow_const (Or.inr hp.le))
    have hlimit : (∑ i ∈ Finset.range N, (a i).val^p) ≤ B^p := by
      apply le_of_tendsto he
      apply Filter.Eventually.of_forall
      intro n
      have hsamp := ((hT (r (s n))).1.2.2).sum_le_tsum (Finset.range N)
        (fun i _ => Real.rpow_nonneg (approximationNumber (T (r (s n))) i).coe_nonneg p)
      rw [← schattenNorm_rpow hp] at hsamp
      exact hsamp.trans (Real.rpow_le_rpow (schattenNorm_nonneg p _) (hT (r (s n))).2 hp.le)
    apply (Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (approximationNumber Z i).coe_nonneg (hap i) hp.le)).trans hlimit
  have hsummable : Summable (fun n => (approximationNumber Z n : ℝ)^p) :=
    summable_of_sum_range_le (fun n => Real.rpow_nonneg (approximationNumber Z n).coe_nonneg p) hsum
  have hSp : Schatten p Z := ⟨hp,compact_of_summable_approximation Z p hp hsummable,hsummable⟩
  have hgauge : schattenNorm p Z ≤ B := by
    apply (Real.rpow_le_rpow_iff (schattenNorm_nonneg p Z) hB hp).mp
    rw [schattenNorm_rpow hp]
    exact Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (approximationNumber Z n).coe_nonneg p) hsum
  refine ⟨r ∘ s,hr.comp hs,Z,hSp,hgauge,fun x y => ?_⟩
  convert (hlim x y).comp hs.tendsto_atTop using 1
  funext n; rfl

/-- The unchanged strict-p>1 interface required by atomic regularization. -/
theorem schattenWeakSubsequence : SchattenWeakSubsequenceObligation := by
  intro H _ _ _ p hp B T hT
  exact schatten_ball_subsequence p (by linarith) B T hT

/-- Working one-atom reduction now supplies the proved arbitrary-Hilbert Schatten subsequence. -/
theorem oneAtomSplitting_of_regularization_and_triangle (hT : TriangularBoundObligation)
    (hR : AtomicRegularizationObligation) (hN : SchattenNormLaws) : OneAtomConclusion :=
  oneAtomSplitting_of_regularization hT schattenWeakSubsequence hR hN

end WeakLimits
end TTO.Paper.Proved
