/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalKernelCutFoundations
public import TTO.AtomicCausalKernelFoundations

/-! Exact physical convolution-kernel pairings on native interval L².
Only compact-interval continuity is required; no global kernel L¹ hypothesis is introduced. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace TTO.Paper.Proved

theorem intervalSmoothCompact_eq_zero {ℓ : ℝ} {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) ℓ) : a t = 0 := by
  by_contra hn
  exact ht (ha.2.2 (subset_tsupport _ hn))

theorem pwCorrelation_eq_zero_outside {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b)
    {y : ℝ} (hy : y ∉ Ioo (-ℓ) ℓ) : pwCorrelation a b y = 0 := by
  unfold pwCorrelation
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    change a t * conj (b (t+y)) = 0
    by_cases hat : a t = 0
    · rw [hat,zero_mul]
    · have ht := ha.2.2 (subset_tsupport _ hat)
      have hbt : b (t+y) = 0 := by
        by_contra hbn
        have htb := hb.2.2 (subset_tsupport _ hbn)
        apply hy
        constructor <;> linarith [ht.1,ht.2,htb.1,htb.2]
      rw [hbt,map_zero,mul_zero]

def intervalKernelCutoff (ℓ : ℝ) (κ : ℝ → ℂ) : ℝ → ℂ :=
  (Icc (-ℓ) ℓ).indicator κ

theorem integral_intervalKernelCutoff_correlation {ℓ : ℝ} (κ : ℝ → ℂ)
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    (∫ y : ℝ, intervalKernelCutoff ℓ κ y * pwCorrelation a b y) =
      ∫ y : ℝ, κ y * pwCorrelation a b y := by
  congr 1
  funext y
  by_cases hy : y ∈ Icc (-ℓ) ℓ
  · simp only [intervalKernelCutoff,indicator_of_mem hy]
  · have hn : y ∉ Ioo (-ℓ) ℓ := fun h => hy ⟨h.1.le,h.2.le⟩
    simp only [intervalKernelCutoff,indicator_of_notMem hy,pwCorrelation_eq_zero_outside ha hb hn,mul_zero]

theorem integrable_intervalKernelCutoff {ℓ : ℝ} (κ : ℝ → ℂ)
    (hκ : ContinuousOn κ (Icc (-ℓ) ℓ)) : Integrable (intervalKernelCutoff ℓ κ) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (hκ.integrableOn_compact isCompact_Icc)

theorem integral_rawConvolution_correlation {ℓ : ℝ} (κ : ℝ → ℂ) (hκ : Integrable κ)
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    (∫ s : ℝ, (∫ t : ℝ, κ (s-t) * a t) * conj (b s)) =
      ∫ y : ℝ, κ y * pwCorrelation a b y := by
  have hA : MemLp a 2 volume := ha.1.continuous.memLp_of_hasCompactSupport ha.2.1
  have hB : MemLp (fun s => conj (b s)) 2 volume := hb.1.continuous.star.memLp_of_hasCompactSupport
    (hb.2.1.comp_left (g := conj) (map_zero _))
  calc
    _ = ∫ s : ℝ, (∫ t : ℝ, a t * κ (s-t)) * conj (b s) := by
      congr 1
      funext s
      congr 1
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, a t * ∫ r : ℝ, κ r * conj (b (t+r)) :=
      integral_rawConvolution_pairing κ a (fun s => conj (b s)) hκ hA hB
    _ = ∫ r : ℝ, κ r * ∫ t : ℝ, a t * conj (b (t+r)) :=
      integral_rawL1L2_pairing_swap κ a (fun s => conj (b s)) hκ hA hB
    _ = _ := rfl

/-- Native interval operator pairings agree with the physical correlation integral for a genuine
L¹ kernel. The kernel can differ outside the physical interval square. -/
theorem intervalKernelOperator_pairing_L1 (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (κ : ℝ → ℂ) (hκ : Integrable κ)
    (hLiteral : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, K s t = κ (s-t))
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    inner ℂ (smoothIntervalL2 ℓ b hb)
      (intervalKernelOperator ℓ K hK M hM hBound (smoothIntervalL2 ℓ a ha)) =
        ∫ y : ℝ, κ y * pwCorrelation a b y := by
  have hrow (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) :
      (∫ t in Ioo (0 : ℝ) ℓ, K s t * (smoothIntervalL2 ℓ a ha) t) =
        ∫ t : ℝ, κ (s-t) * a t := by
    calc
      _ = ∫ t in Ioo (0 : ℝ) ℓ, κ (s-t) * a t := by
        apply integral_congr_ae
        filter_upwards [smoothIntervalL2_ae ℓ a ha,ae_restrict_mem measurableSet_Ioo] with t hA ht
        rw [hA,hLiteral s hs t ht]
      _ = _ := by
        rw [← integral_indicator measurableSet_Ioo]
        congr 1
        funext t
        by_cases ht : t ∈ Ioo (0 : ℝ) ℓ
        · simp only [indicator_of_mem ht]
        · simp only [indicator_of_notMem ht,intervalSmoothCompact_eq_zero ha ht,mul_zero]
  calc
    _ = ∫ s in Ioo (0 : ℝ) ℓ, (∫ t : ℝ, κ (s-t) * a t) * conj (b s) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [smoothIntervalL2_ae ℓ b hb,
        intervalKernelOperator_ae ℓ K hK M hM hBound (smoothIntervalL2 ℓ a ha),
        ae_restrict_mem measurableSet_Ioo] with s hB hO hs
      rw [hB,hO,RCLike.inner_apply,hrow s hs]
    _ = ∫ s : ℝ, (∫ t : ℝ, κ (s-t) * a t) * conj (b s) := by
      rw [← integral_indicator measurableSet_Ioo]
      congr 1
      funext s
      by_cases hs : s ∈ Ioo (0 : ℝ) ℓ
      · simp only [indicator_of_mem hs]
      · simp only [indicator_of_notMem hs,intervalSmoothCompact_eq_zero hb hs,map_zero,mul_zero]
    _ = _ := integral_rawConvolution_correlation κ hκ ha hb

/-- Only compact-interval continuity is used: a private L¹ cut is removed using actual correlation
support. No global integrability premise appears in the exported physical pairing. -/
theorem intervalKernelOperator_pairing_smooth (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (κ : ℝ → ℂ) (hκ : ContinuousOn κ (Icc (-ℓ) ℓ))
    (hLiteral : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, K s t = κ (s-t))
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    inner ℂ (smoothIntervalL2 ℓ b hb)
      (intervalKernelOperator ℓ K hK M hM hBound (smoothIntervalL2 ℓ a ha)) =
        ∫ y : ℝ, κ y * pwCorrelation a b y := by
  have hLit : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ,
      K s t = intervalKernelCutoff ℓ κ (s-t) := by
    intro s hs t ht
    have hd : s-t ∈ Icc (-ℓ) ℓ := by constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    rw [intervalKernelCutoff,indicator_of_mem hd]
    exact hLiteral s hs t ht
  rw [intervalKernelOperator_pairing_L1 ℓ K hK M hM hBound
    (intervalKernelCutoff ℓ κ) (integrable_intervalKernelCutoff κ hκ) hLit ha hb,
    integral_intervalKernelCutoff_correlation κ ha hb]

theorem intervalKernelCutoff_mul_correlation {ℓ : ℝ} (κ : ℝ → ℂ)
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) (y : ℝ) :
    intervalKernelCutoff ℓ κ y * pwCorrelation a b y = κ y * pwCorrelation a b y := by
  by_cases hy : y ∈ Icc (-ℓ) ℓ
  · simp only [intervalKernelCutoff,indicator_of_mem hy]
  · have hn : y ∉ Ioo (-ℓ) ℓ := fun h => hy ⟨h.1.le,h.2.le⟩
    simp only [intervalKernelCutoff,indicator_of_notMem hy,pwCorrelation_eq_zero_outside ha hb hn,mul_zero]

/-- The native strict lower operator retains exactly positive output-minus-input differences.
No continuity of the truncated kernel across the diagonal is assumed. -/
theorem lowerIntervalKernelOperator_pairing_smooth (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (κ : ℝ → ℂ) (hκ : ContinuousOn κ (Icc (-ℓ) ℓ))
    (hLiteral : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, K s t = κ (s-t))
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    inner ℂ (smoothIntervalL2 ℓ b hb)
      (lowerIntervalKernelOperator ℓ K hK M hM hBound (smoothIntervalL2 ℓ a ha)) =
        ∫ y in Ioi (0 : ℝ), κ y * pwCorrelation a b y := by
  let k : ℝ → ℂ := (Ioi (0 : ℝ)).indicator (intervalKernelCutoff ℓ κ)
  have hk : Integrable k := (integrable_intervalKernelCutoff κ hκ).indicator measurableSet_Ioi
  have hLit : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ,
      lowerIntervalKernel K s t = k (s-t) := by
    intro s hs t ht
    have hd : s-t ∈ Icc (-ℓ) ℓ := by constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    by_cases hst : t<s
    · have hpos : s-t ∈ Ioi (0 : ℝ) := by change 0<s-t; linarith
      rw [lowerIntervalKernel,ite_eq_left hst]
      simp only [k,indicator_of_mem hpos,intervalKernelCutoff,indicator_of_mem hd]
      exact hLiteral s hs t ht
    · have hn : s-t ∉ Ioi (0 : ℝ) := by change ¬0<s-t; linarith
      rw [lowerIntervalKernel,ite_eq_right hst]
      simp only [k,indicator_of_notMem hn]
  calc
    _ = ∫ y : ℝ, k y * pwCorrelation a b y :=
      intervalKernelOperator_pairing_L1 ℓ (lowerIntervalKernel K)
        (stronglyMeasurable_lowerIntervalKernel K hK) M hM
        (lowerIntervalKernel_bound ℓ K M hM hBound) k hk hLit ha hb
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1
      funext y
      by_cases hy : y ∈ Ioi (0 : ℝ)
      · simp only [k,indicator_of_mem hy]
        exact intervalKernelCutoff_mul_correlation κ ha hb y
      · simp only [k,indicator_of_notMem hy,zero_mul]

end TTO.Paper.Proved
