/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalTranslationFoundations

/-! Actual adjoint translations, compact-factor norm continuity and Schatten-preserving averages. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem inner_lineTranslateIsometry (r : ℝ) (f g : LineL2) :
    inner ℂ (lineTranslateIsometry r f) g=inner ℂ f (lineTranslateIsometry (-r) g) := by
  rw [lineTranslateIsometry_eq r f,lineTranslateIsometry_eq (-r) g,L2.inner_def,L2.inner_def]
  calc
    _ = ∫ t : ℝ, inner ℂ (f (t-r)) (g t) := by
      apply integral_congr_ae
      filter_upwards [lineTranslate_ae r f] with t ht
      rw [ht]
    _ = ∫ t : ℝ, inner ℂ (f t) (g (t+r)) := by
      calc
        _ = ∫ t : ℝ, (fun x => inner ℂ (f x) (g (x+r))) (t-r) := by
          congr 1
          funext t
          dsimp only
          rw [sub_add_cancel]
        _ = _ := by
          simpa only using! (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
            (fun t : ℝ => inner ℂ (f t) (g (t+r))) r)
    _ = ∫ t : ℝ, inner ℂ (f t) (lineTranslate (-r) g t) := by
      apply integral_congr_ae
      filter_upwards [lineTranslate_ae (-r) g] with t ht
      simpa only [Function.comp_apply,sub_neg_eq_add] using
        congrArg (fun z => inner ℂ (f t) z) ht.symm

theorem adjoint_lineTranslateIsometry (r : ℝ) :
    (lineTranslateIsometry r).toContinuousLinearMap.adjoint=
      (lineTranslateIsometry (-r)).toContinuousLinearMap := by
  have h : (lineTranslateIsometry r).toContinuousLinearMap=
      (lineTranslateIsometry (-r)).toContinuousLinearMap.adjoint :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_lineTranslateIsometry r)
  rw [h,ContinuousLinearMap.adjoint_adjoint]

theorem adjoint_restrictIntervalL (ℓ : ℝ) :
    (restrictIntervalL ℓ).adjoint=(zeroExtendIntervalIsometry ℓ).toContinuousLinearMap := by
  rw [← adjoint_zeroExtendIntervalIsometry,ContinuousLinearMap.adjoint_adjoint]

theorem adjoint_intervalTranslate (ℓ r : ℝ) :
    (intervalTranslate ℓ r).adjoint=intervalTranslate ℓ (-r) := by
  unfold intervalTranslate
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    adjoint_zeroExtendIntervalIsometry,adjoint_restrictIntervalL,adjoint_lineTranslateIsometry]
  rfl

/-- The literal doubly truncated composition, before any sign condition on the shifts. -/
theorem intervalTranslate_comp_ae (ℓ r s : ℝ) (f : IntervalL2 ℓ) :
    (intervalTranslate ℓ r ∘L intervalTranslate ℓ s) f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      fun t => (Ioo (0 : ℝ) ℓ).indicator
        (fun x => (Ioo (0 : ℝ) ℓ).indicator f (x-s)) (t-r) := by
  have hInner := (ae_restrict_iff' measurableSet_Ioo).mp (intervalTranslate_ae ℓ s f)
  have hShift := (measurePreserving_sub_const_line r).quasiMeasurePreserving.ae hInner
  filter_upwards [intervalTranslate_ae ℓ r (intervalTranslate ℓ s f),
    ae_restrict_of_ae hShift] with t hOuter hInner
  change intervalTranslate ℓ r (intervalTranslate ℓ s f) t=_
  rw [hOuter]
  by_cases ht : t-r∈Ioo (0 : ℝ) ℓ
  · rw [indicator_of_mem ht,indicator_of_mem ht]
    exact hInner ht
  · rw [indicator_of_notMem ht,indicator_of_notMem ht]

theorem intervalTranslate_semigroup (ℓ r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    intervalTranslate ℓ r ∘L intervalTranslate ℓ s=intervalTranslate ℓ (r+s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalTranslate_comp_ae ℓ r s f,intervalTranslate_ae ℓ (r+s) f,
    ae_restrict_mem measurableSet_Ioo] with t hComp hSum ht
  rw [hComp,hSum]
  have he : (t-r)-s=t-(r+s) := by ring
  by_cases hTotal : t-(r+s)∈Ioo (0 : ℝ) ℓ
  · have hMid : t-r∈Ioo (0 : ℝ) ℓ := by
      constructor
      · linarith [hTotal.1]
      · linarith [ht.2]
    rw [indicator_of_mem hMid,he]
  · by_cases hMid : t-r∈Ioo (0 : ℝ) ℓ
    · rw [indicator_of_mem hMid,he]
    · rw [indicator_of_notMem hMid,indicator_of_notMem hTotal]

theorem intervalTranslate_zero (ℓ : ℝ) :
    intervalTranslate ℓ 0=ContinuousLinearMap.id ℂ (IntervalL2 ℓ) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.id_apply]
  apply Lp.ext
  filter_upwards [intervalTranslate_ae ℓ 0 f,ae_restrict_mem measurableSet_Ioo] with t hf ht
  simpa only [sub_zero,indicator_of_mem ht] using hf

theorem intervalTranslate_adjoint_self (ℓ r : ℝ) (hr : 0 ≤ r) :
    (intervalTranslate ℓ r).adjoint ∘L intervalTranslate ℓ r=
      intervalMask ℓ (Ioo (0 : ℝ) (ℓ-r)) measurableSet_Ioo := by
  rw [adjoint_intervalTranslate]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalTranslate_comp_ae ℓ (-r) r f,
    intervalMask_ae ℓ (Ioo (0 : ℝ) (ℓ-r)) measurableSet_Ioo f,
    ae_restrict_mem measurableSet_Ioo] with t hComp hMask ht
  rw [hComp,hMask]
  simp only [sub_neg_eq_add]
  by_cases hOut : t+r∈Ioo (0 : ℝ) ℓ
  · rw [indicator_of_mem hOut,show t+r-r=t by ring,indicator_of_mem ht]
    have hShort : t∈Ioo (0 : ℝ) (ℓ-r) := ⟨ht.1,by linarith [hOut.2]⟩
    rw [indicator_of_mem hShort]
  · rw [indicator_of_notMem hOut]
    have hShort : t∉Ioo (0 : ℝ) (ℓ-r) := by
      intro h
      apply hOut
      exact ⟨by linarith [ht.1],by linarith [h.2]⟩
    rw [indicator_of_notMem hShort]

theorem intervalTranslate_self_adjoint (ℓ r : ℝ) (hr : 0 ≤ r) :
    intervalTranslate ℓ r ∘L (intervalTranslate ℓ r).adjoint=
      intervalMask ℓ (Ioo r ℓ) measurableSet_Ioo := by
  rw [adjoint_intervalTranslate]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalTranslate_comp_ae ℓ r (-r) f,
    intervalMask_ae ℓ (Ioo r ℓ) measurableSet_Ioo f,
    ae_restrict_mem measurableSet_Ioo] with t hComp hMask ht
  rw [hComp,hMask]
  simp only [sub_neg_eq_add]
  by_cases hOut : t-r∈Ioo (0 : ℝ) ℓ
  · rw [indicator_of_mem hOut,sub_add_cancel,indicator_of_mem ht]
    have hShort : t∈Ioo r ℓ := ⟨by linarith [hOut.1],ht.2⟩
    rw [indicator_of_mem hShort]
  · rw [indicator_of_notMem hOut]
    have hShort : t∉Ioo r ℓ := by
      intro h
      apply hOut
      exact ⟨by linarith [h.1],by linarith [ht.2]⟩
    rw [indicator_of_notMem hShort]

theorem intervalTranslate_range_mask (ℓ r : ℝ) (_hr : 0 ≤ r) :
    intervalMask ℓ (Ioo r ℓ) measurableSet_Ioo ∘L intervalTranslate ℓ r=
      intervalTranslate ℓ r := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMask_ae ℓ (Ioo r ℓ) measurableSet_Ioo (intervalTranslate ℓ r f),
    intervalTranslate_ae ℓ r f,ae_restrict_mem measurableSet_Ioo] with t hMask hTr ht
  change intervalMask ℓ (Ioo r ℓ) measurableSet_Ioo (intervalTranslate ℓ r f) t=_
  rw [hMask]
  by_cases hOut : t∈Ioo r ℓ
  · rw [indicator_of_mem hOut]
  · rw [indicator_of_notMem hOut,hTr]
    have hMid : t-r∉Ioo (0 : ℝ) ℓ := by
      intro h
      apply hOut
      exact ⟨by linarith [h.1],ht.2⟩
    rw [indicator_of_notMem hMid]

theorem intervalTranslate_source_mask (ℓ r : ℝ) (hr : 0 ≤ r) :
    intervalTranslate ℓ r ∘L intervalMask ℓ (Ioo (0 : ℝ) (ℓ-r)) measurableSet_Ioo=
      intervalTranslate ℓ r := by
  rw [← intervalTranslate_adjoint_self ℓ r hr,← ContinuousLinearMap.comp_assoc,
    intervalTranslate_self_adjoint ℓ r hr]
  exact intervalTranslate_range_mask ℓ r hr

theorem intervalTranslate_adjoint_range_mask (ℓ r : ℝ) (hr : 0 ≤ r) :
    intervalMask ℓ (Ioo (0 : ℝ) (ℓ-r)) measurableSet_Ioo ∘L (intervalTranslate ℓ r).adjoint=
      (intervalTranslate ℓ r).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (intervalTranslate_source_mask ℓ r hr)
  simpa only [ContinuousLinearMap.adjoint_comp,adjoint_intervalMask] using h

section CompactFactorContinuity
variable {α E F G : Type*} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A strongly continuous contraction family becomes operator-norm continuous after a compact factor.
The proof is uniform on the actual compact image of the closed unit ball. -/
theorem continuous_compact_factor (S : α → F →L[ℂ] G)
    (hBound : ∀ a, ‖S a‖ ≤ 1) (hStrong : ∀ x : F, Continuous (fun a => S a x))
    (A : E →L[ℂ] F) (hA : IsCompactOperator A) :
    Continuous (fun a => S a ∘L A) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hAK⟩ := hA.image_closedBall_subset_compact 1
  obtain ⟨t,_htK,ht,hKt⟩ := hK.finite_cover_balls (show 0<ε/8 by positivity)
  have hEvent : ∀ᶠ a' in 𝓝 a, ∀ y∈t, ‖S a' y-S a y‖<ε/2 := by
    apply ht.eventually_all.mpr
    intro y hy
    have h := ((hStrong y).tendsto a).eventually (Metric.ball_mem_nhds (S a y) (half_pos hε))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hContract (a' : α) (x : F) : ‖S a' x‖ ≤ ‖x‖ :=
    (S a').le_opNorm x |>.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hBound a') (norm_nonneg x))
  have hLip (a' : α) (x : F) : ‖S a' x-S a x‖ ≤ 2*‖x‖ := by
    have hn := norm_sub_le (S a' x) (S a x)
    have h₁ := hContract a' x
    have h₂ := hContract a x
    linarith
  filter_upwards [hEvent] with a' hEvent
  have hNorm : ‖S a' ∘L A-S a ∘L A‖ ≤ 3*ε/4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hKt (hAK ⟨x,by simp [hx],rfl⟩))
    have hd : ‖A x-y‖<ε/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using! hxy
    change ‖S a' (A x)-S a (A x)‖ ≤ _
    have he : S a' (A x)-S a (A x)=
        (S a' (A x-y)-S a (A x-y))+(S a' y-S a y) := by
      simp only [map_sub]
      abel
    rw [he]
    have hn := norm_add_le (S a' (A x-y)-S a (A x-y)) (S a' y-S a y)
    have h₁ := hLip a' (A x-y)
    have h₂ := hEvent y hy
    linarith
  rw [dist_eq_norm]
  exact hNorm.trans_lt (by linarith)

end CompactFactorContinuity

section WeightedSchattenAverage
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ordinary Bochner integration of a nonnegative probability density preserves the genuine Schatten ball.
No Schatten carrier or Schatten-topology continuity is assumed. -/
theorem schatten_weighted_integral (p B : ℝ) (hp : 1 ≤ p)
    (T : ℝ → H →L[ℂ] H) (hTCont : Continuous T)
    (hT : ∀ r, Schatten p (T r) ∧ schattenNorm p (T r) ≤ B)
    (k : ℝ → ℝ) (hkCont : Continuous k) (hk : Integrable k)
    (hkNonneg : ∀ r, 0 ≤ k r) (hkOne : ∫ r : ℝ, k r=1) :
    Integrable (fun r : ℝ => k r • T r) ∧
      Schatten p (∫ r : ℝ, k r • T r) ∧ schattenNorm p (∫ r : ℝ, k r • T r) ≤ B := by
  let μ : Measure ℝ := volume.withDensity (fun r => ENNReal.ofReal (k r))
  have hμ : μ Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hk (Eventually.of_forall hkNonneg),hkOne,ENNReal.ofReal_one]
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  have hInt : Integrable T μ :=
    (integrable_const B).mono' hTCont.aestronglyMeasurable
      (Eventually.of_forall fun r => (opNorm_le_schattenNorm p (T r) (hT r).1).trans (hT r).2)
  have hMeas : Measurable (fun r => ENNReal.ofReal (k r)) := hkCont.measurable.ennreal_ofReal
  have hFin : ∀ᵐ r ∂(volume : Measure ℝ), ENNReal.ofReal (k r)<∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hWeighted : Integrable (fun r : ℝ => k r • T r) := by
    have h := (integrable_withDensity_iff_integrable_smul' hMeas hFin).mp hInt
    have he : (fun r => (ENNReal.ofReal (k r)).toReal • T r)=(fun r => k r • T r) := by
      funext r
      rw [ENNReal.toReal_ofReal (hkNonneg r)]
    rw [he] at h
    exact h
  have hEq : (∫ r : ℝ, T r ∂μ)=∫ r : ℝ, k r • T r := by
    rw [integral_withDensity_eq_integral_toReal_smul hMeas hFin]
    congr 1
    funext r
    rw [ENNReal.toReal_ofReal (hkNonneg r)]
  have hBall := schatten_integral_ball μ p hp B T (Eventually.of_forall hT) hInt
  rw [hEq] at hBall
  exact ⟨hWeighted,hBall⟩

end WeightedSchattenAverage

/-- The manuscript's operator inside the Step 1 translation average. -/
def intervalTranslatedSandwich (ℓ ε : ℝ) (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (r : ℝ) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  (intervalTranslate ℓ ε).adjoint ∘L intervalTranslate ℓ r ∘L A ∘L intervalTranslate ℓ ε

theorem continuous_intervalTranslatedSandwich (ℓ ε : ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : IsCompactOperator A) :
    Continuous (intervalTranslatedSandwich ℓ ε A) := by
  unfold intervalTranslatedSandwich
  have h : Continuous (fun r : ℝ => intervalTranslate ℓ r ∘L A) :=
    continuous_compact_factor (intervalTranslate ℓ) (norm_intervalTranslate_le_one ℓ)
      (continuous_intervalTranslate ℓ) A hA
  have hRight : Continuous (fun r : ℝ =>
      (intervalTranslate ℓ r ∘L A) ∘L intervalTranslate ℓ ε) :=
    h.clm_comp_const (intervalTranslate ℓ ε)
  have hBoth : Continuous (fun r : ℝ =>
      (intervalTranslate ℓ ε).adjoint ∘L
        ((intervalTranslate ℓ r ∘L A) ∘L intervalTranslate ℓ ε)) :=
    hRight.const_clm_comp (intervalTranslate ℓ ε).adjoint
  simpa only [ContinuousLinearMap.comp_assoc] using hBoth

theorem schatten_intervalTranslatedSandwich (ℓ ε p : ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : Schatten p A) (r : ℝ) :
    Schatten p (intervalTranslatedSandwich ℓ ε A r) ∧
      schattenNorm p (intervalTranslatedSandwich ℓ ε A r) ≤ schattenNorm p A := by
  let L := (intervalTranslate ℓ ε).adjoint ∘L intervalTranslate ℓ r
  have hε : ‖intervalTranslate ℓ ε‖ ≤ 1 := norm_intervalTranslate_le_one ℓ ε
  have hL : ‖L‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    have h := mul_le_mul hε (norm_intervalTranslate_le_one ℓ r) (norm_nonneg (intervalTranslate ℓ r)) zero_le_one
    simpa only [one_mul] using h
  change Schatten p (L ∘L A ∘L intervalTranslate ℓ ε) ∧ _
  refine ⟨schatten_comp hA L _,?_⟩
  apply (schattenNorm_comp_le hA L (intervalTranslate ℓ ε)).trans
  have hProduct : ‖L‖*‖intervalTranslate ℓ ε‖ ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul hL hε (norm_nonneg (intervalTranslate ℓ ε)) zero_le_one
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hProduct (Reduction.schattenNorm_nonneg p A)

/-- Actual ordinary operator-valued weighted translation average. -/
def intervalTranslatedAverage (ℓ ε : ℝ) (k : ℝ → ℝ) (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  ∫ r : ℝ, k r • intervalTranslatedSandwich ℓ ε A r

theorem schatten_intervalTranslatedAverage (ℓ ε p : ℝ) (hp : 1 ≤ p)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : Schatten p A)
    (k : ℝ → ℝ) (hkCont : Continuous k) (hk : Integrable k)
    (hkNonneg : ∀ r, 0 ≤ k r) (hkOne : ∫ r : ℝ, k r=1) :
    Integrable (fun r : ℝ => k r • intervalTranslatedSandwich ℓ ε A r) ∧
      Schatten p (intervalTranslatedAverage ℓ ε k A) ∧
        schattenNorm p (intervalTranslatedAverage ℓ ε k A) ≤ schattenNorm p A := by
  unfold intervalTranslatedAverage
  exact schatten_weighted_integral p (schattenNorm p A) hp (intervalTranslatedSandwich ℓ ε A)
    (continuous_intervalTranslatedSandwich ℓ ε A hA.2.1)
    (schatten_intervalTranslatedSandwich ℓ ε p A hA) k hkCont hk hkNonneg hkOne

end TTO.Paper.Proved
