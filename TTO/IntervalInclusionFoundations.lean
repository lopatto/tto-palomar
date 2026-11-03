/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalAverageFoundations

/-! Actual restriction and zero extension between nested interval L² spaces. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Extend by zero on the line, then restrict to the target interval. -/
def intervalInclusion (L ℓ : ℝ) : IntervalL2 L →L[ℂ] IntervalL2 ℓ :=
  restrictIntervalL ℓ ∘L (zeroExtendIntervalIsometry L).toContinuousLinearMap

theorem intervalInclusion_ae (L ℓ : ℝ) (f : IntervalL2 L) :
    intervalInclusion L ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      (Ioo (0 : ℝ) L).indicator f := by
  filter_upwards [restrictIntervalL_ae ℓ (zeroExtendIntervalIsometry L f),
    ae_restrict_of_ae (zeroExtendIntervalIsometry_ae L f)] with t hr he
  change restrictIntervalL ℓ (zeroExtendIntervalIsometry L f) t = _
  rw [hr,he]

theorem norm_intervalInclusion_le_one (L ℓ : ℝ) : ‖intervalInclusion L ℓ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖restrictIntervalL ℓ (zeroExtendIntervalIsometry L f)‖ ≤ 1*‖f‖
  rw [one_mul]
  exact (norm_restrictIntervalVector_le ℓ _).trans_eq ((zeroExtendIntervalIsometry L).norm_map f)

theorem adjoint_intervalInclusion (L ℓ : ℝ) :
    (intervalInclusion L ℓ).adjoint=intervalInclusion ℓ L := by
  unfold intervalInclusion
  rw [ContinuousLinearMap.adjoint_comp,adjoint_zeroExtendIntervalIsometry,adjoint_restrictIntervalL]

open scoped ContDiff in
/-- The same literal compact smooth function is a test on every larger interval. -/
theorem IntervalSmoothCompact.mono {L ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact L a) (hL : L ≤ ℓ) : IntervalSmoothCompact ℓ a :=
  ⟨ha.1,ha.2.1,fun _ ht => ⟨(ha.2.2 ht).1,(ha.2.2 ht).2.trans_le hL⟩⟩

theorem intervalInclusion_smooth (L ℓ : ℝ) (hL : L ≤ ℓ)
    (a : ℝ → ℂ) (ha : IntervalSmoothCompact L a) :
    intervalInclusion L ℓ (smoothIntervalL2 L a ha)=smoothIntervalL2 ℓ a (ha.mono hL) := by
  apply Lp.ext
  have hA := (ae_restrict_iff' measurableSet_Ioo).mp (smoothIntervalL2_ae L a ha)
  filter_upwards [intervalInclusion_ae L ℓ (smoothIntervalL2 L a ha),
    ae_restrict_of_ae hA,smoothIntervalL2_ae ℓ a (ha.mono hL)] with t hi hs hb
  rw [hi,hb]
  by_cases ht : t ∈ Ioo (0 : ℝ) L
  · rw [indicator_of_mem ht,hs ht]
  · rw [indicator_of_notMem ht,ha.eq_zero_of_not_mem ht]

theorem adjoint_intervalInclusion_smooth (L ℓ : ℝ) (hL : L ≤ ℓ)
    (a : ℝ → ℂ) (ha : IntervalSmoothCompact L a) :
    (intervalInclusion L ℓ).adjoint (smoothIntervalL2 ℓ a (ha.mono hL))=smoothIntervalL2 L a ha := by
  rw [adjoint_intervalInclusion]
  apply Lp.ext
  have hA := (ae_restrict_iff' measurableSet_Ioo).mp (smoothIntervalL2_ae ℓ a (ha.mono hL))
  filter_upwards [intervalInclusion_ae ℓ L (smoothIntervalL2 ℓ a (ha.mono hL)),
    ae_restrict_of_ae hA,smoothIntervalL2_ae L a ha,ae_restrict_mem measurableSet_Ioo] with t hi hs hb ht
  rw [hi,hb,indicator_of_mem (show t ∈ Ioo (0 : ℝ) ℓ from ⟨ht.1,ht.2.trans_le hL⟩)]
  exact hs ⟨ht.1,ht.2.trans_le hL⟩

/-- On a genuinely nested interval the adjoint is a left inverse, with no endpoint convention change. -/
theorem adjoint_intervalInclusion_comp (L ℓ : ℝ) (hL : L ≤ ℓ) :
    (intervalInclusion L ℓ).adjoint ∘L intervalInclusion L ℓ=ContinuousLinearMap.id ℂ (IntervalL2 L) := by
  rw [adjoint_intervalInclusion]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hI := (ae_restrict_iff' measurableSet_Ioo).mp (intervalInclusion_ae L ℓ f)
  filter_upwards [intervalInclusion_ae ℓ L (intervalInclusion L ℓ f),
    ae_restrict_of_ae hI,ae_restrict_mem measurableSet_Ioo] with t hr hi ht
  change intervalInclusion ℓ L (intervalInclusion L ℓ f) t=f t
  have htℓ : t ∈ Ioo (0 : ℝ) ℓ := ⟨ht.1,ht.2.trans_le hL⟩
  rw [hr,indicator_of_mem htℓ,hi htℓ,indicator_of_mem ht]

/-- A genuine short-interval compression of the actual translation average. -/
def shortIntervalTranslatedAverage (L ℓ ε : ℝ) (k : ℝ → ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) : IntervalL2 L →L[ℂ] IntervalL2 L :=
  (intervalInclusion L ℓ).adjoint ∘L intervalTranslatedAverage ℓ ε k A ∘L intervalInclusion L ℓ

theorem schatten_intervalInclusion_sandwich (L ℓ p : ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : Schatten p A) :
    Schatten p ((intervalInclusion L ℓ).adjoint ∘L A ∘L intervalInclusion L ℓ) ∧
      schattenNorm p ((intervalInclusion L ℓ).adjoint ∘L A ∘L intervalInclusion L ℓ) ≤ schattenNorm p A := by
  refine ⟨schatten_comp hA _ _,(schattenNorm_comp_le hA _ _).trans ?_⟩
  have hI := norm_intervalInclusion_le_one L ℓ
  have hJ : ‖(intervalInclusion L ℓ).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hI
  have hProduct : ‖(intervalInclusion L ℓ).adjoint‖*‖intervalInclusion L ℓ‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hJ hI (norm_nonneg _) zero_le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hProduct (Reduction.schattenNorm_nonneg p A)

theorem schatten_shortIntervalTranslatedAverage (L ℓ ε p : ℝ) (hp : 1 ≤ p)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : Schatten p A)
    (k : ℝ → ℝ) (hkCont : Continuous k) (hk : Integrable k)
    (hkNonneg : ∀ r, 0 ≤ k r) (hkOne : ∫ r : ℝ, k r=1) :
    Schatten p (shortIntervalTranslatedAverage L ℓ ε k A) ∧
      schattenNorm p (shortIntervalTranslatedAverage L ℓ ε k A) ≤ schattenNorm p A := by
  obtain ⟨_hi,hS,hN⟩ := schatten_intervalTranslatedAverage ℓ ε p hp A hA k hkCont hk hkNonneg hkOne
  obtain ⟨hC,hCN⟩ := schatten_intervalInclusion_sandwich L ℓ p _ hS
  exact ⟨hC,hCN.trans hN⟩

/-- Compact tests eventually lie in every sufficiently slightly shortened interval. -/
theorem IntervalSmoothCompact.exists_short_margin {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → IntervalSmoothCompact (ℓ-ε) a := by
  by_cases hn : (tsupport a).Nonempty
  · obtain ⟨x,hx,hMax⟩ := ha.2.1.exists_isMaxOn hn continuous_id.continuousOn
    have hxℓ := (ha.2.2 hx).2
    refine ⟨(ℓ-x)/2,by linarith,?_⟩
    intro ε _hε hεδ
    refine ⟨ha.1,ha.2.1,?_⟩
    intro t ht
    exact ⟨(ha.2.2 ht).1,by have htx : t ≤ x := hMax ht; linarith⟩
  · refine ⟨1,zero_lt_one,fun ε _ _ => ⟨ha.1,ha.2.1,?_⟩⟩
    intro t ht
    exact (hn ⟨t,ht⟩).elim

/-- A dense complex test subspace contains a normalized vector whenever the ambient space is nonzero. -/
theorem exists_unit_mem_dense_submodule {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (M : Submodule ℂ H) (hM : Dense (M : Set H))
    (x : H) (hx : x ≠ 0) : ∃ e : M, inner ℂ e.val e.val=1 := by
  classical
  have hy : ∃ y : M, (y : H) ≠ 0 := by
    by_contra h
    have hz : ∀ y ∈ M, y=0 := by
      intro y hy
      exact Classical.not_not.mp (fun hn => h ⟨⟨y,hy⟩,hn⟩)
    apply hx
    apply hM.eq_zero_of_inner_right ℂ
    intro y hy
    rw [hz y hy,inner_zero_left]
  obtain ⟨y,hy⟩ := hy
  have hyM : y ≠ 0 := fun h => hy (congrArg Subtype.val h)
  let e : M := NormedSpace.normalize y
  have he : ‖e‖=1 := NormedSpace.norm_normalize_eq_one_iff.mpr hyM
  refine ⟨e,?_⟩
  rw [inner_self_eq_norm_sq_to_K]
  change (‖e‖ : ℂ)^2=1
  rw [he]
  norm_num

/-- Two actual contractions preserve every positive Schatten gauge without a larger constant. -/
theorem schatten_two_sided_contraction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {p : ℝ} (A : F →L[ℂ] F) (hA : Schatten p A)
    (L : F →L[ℂ] E) (R : E →L[ℂ] F) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    Schatten p (L ∘L A ∘L R) ∧ schattenNorm p (L ∘L A ∘L R) ≤ schattenNorm p A := by
  refine ⟨schatten_comp hA L R,(schattenNorm_comp_le hA L R).trans ?_⟩
  have hProduct : ‖L‖*‖R‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hL hR (norm_nonneg R) zero_le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hProduct (Reduction.schattenNorm_nonneg p A)

/-- Extend an actual operator on the shorter interval by zero on both sides. -/
def intervalOperatorExtension (L ℓ : ℝ) (X : IntervalL2 L →L[ℂ] IntervalL2 L) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  intervalInclusion L ℓ ∘L X ∘L (intervalInclusion L ℓ).adjoint

theorem schatten_intervalOperatorExtension (L ℓ p : ℝ)
    (X : IntervalL2 L →L[ℂ] IntervalL2 L) (hX : Schatten p X) :
    Schatten p (intervalOperatorExtension L ℓ X) ∧
      schattenNorm p (intervalOperatorExtension L ℓ X) ≤ schattenNorm p X := by
  apply schatten_two_sided_contraction X hX _ _ (norm_intervalInclusion_le_one L ℓ)
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_intervalInclusion_le_one L ℓ

theorem inner_intervalOperatorExtension_smooth (L ℓ : ℝ) (hL : L ≤ ℓ)
    (X : IntervalL2 L →L[ℂ] IntervalL2 L) (a b : ℝ → ℂ)
    (ha : IntervalSmoothCompact L a) (hb : IntervalSmoothCompact L b) :
    inner ℂ (smoothIntervalL2 ℓ b (hb.mono hL))
      (intervalOperatorExtension L ℓ X (smoothIntervalL2 ℓ a (ha.mono hL))) =
      inner ℂ (smoothIntervalL2 L b hb) (X (smoothIntervalL2 L a ha)) := by
  change inner ℂ (smoothIntervalL2 ℓ b (hb.mono hL))
    (intervalInclusion L ℓ (X ((intervalInclusion L ℓ).adjoint (smoothIntervalL2 ℓ a (ha.mono hL))))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left,
    adjoint_intervalInclusion_smooth L ℓ hL a ha,adjoint_intervalInclusion_smooth L ℓ hL b hb]

end TTO.Paper.Proved
