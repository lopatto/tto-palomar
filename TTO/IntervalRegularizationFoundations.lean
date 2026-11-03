/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalInclusionFoundations
public import TTO.IntervalKernelPairingFoundations

/-! Actual bounded convolution kernels identified on the dense compact smooth interval core. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Equality of actual integral pairings on the dense smooth core determines the bounded operator. -/
theorem intervalOperator_eq_of_smooth_pairing (ℓ : ℝ) (hℓ : 0 < ℓ)
    (A B : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ)
    (hPair : ∀ (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      inner ℂ (smoothIntervalL2 ℓ b hb) (A (smoothIntervalL2 ℓ a ha)) =
        inner ℂ (smoothIntervalL2 ℓ b hb) (B (smoothIntervalL2 ℓ a ha))) : A=B := by
  have hd := smoothIntervalCore_dense ℓ hℓ
  have hCore : ∀ f ∈ smoothIntervalCore ℓ, A f=B f := by
    intro f hf
    obtain ⟨a,ha,rfl⟩ := (mem_smoothIntervalCore_iff ℓ f).mp hf
    apply hd.eq_of_inner_right ℂ
    intro g hg
    obtain ⟨b,hb,rfl⟩ := (mem_smoothIntervalCore_iff ℓ g).mp hg
    exact hPair a b ha hb
  have hFun : (fun f => A f)=(fun f => B f) := A.continuous.ext_on hd B.continuous hCore
  apply ContinuousLinearMap.ext
  exact congrFun hFun

/-- A continuous physical convolution kernel already representing a Schatten operator has an
actual strict lower operator with the same prescribed triangular constant. -/
theorem exists_lower_cut_of_smooth_pairing (p τ : ℝ) (hp : 0 < p)
    (hτ : TriangularConstant p τ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (hA : Schatten p A)
    (κ : ℝ → ℂ) (hκ : Continuous κ)
    (hForm : ∀ (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      inner ℂ (smoothIntervalL2 ℓ b hb) (A (smoothIntervalL2 ℓ a ha)) =
        ∫ y : ℝ, κ y*pwCorrelation a b y) :
    ∃ X : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ,
      Schatten p X ∧ schattenNorm p X ≤ τ*schattenNorm p A ∧
      ∀ (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
        inner ℂ (smoothIntervalL2 ℓ b hb) (X (smoothIntervalL2 ℓ a ha)) =
          ∫ y in Ioi (0 : ℝ), κ y*pwCorrelation a b y := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-ℓ) ℓ) hκ.continuousOn
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  let K : ℝ → ℝ → ℂ := fun s t => κ (s-t)
  have hK : StronglyMeasurable (Function.uncurry K) := by
    change StronglyMeasurable (fun x : ℝ × ℝ => κ (x.1-x.2))
    exact (hκ.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable
  have hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M := by
    intro s hs t ht
    apply (hC (s-t) (show s-t ∈ Icc (-ℓ) ℓ by constructor <;> linarith [hs.1,hs.2,ht.1,ht.2])).trans
    exact le_max_left _ _
  let B := intervalKernelOperator ℓ K hK M hM hBound
  have he : A=B := by
    apply intervalOperator_eq_of_smooth_pairing ℓ hℓ
    intro a b ha hb
    rw [hForm a b ha hb]
    exact (intervalKernelOperator_pairing_smooth ℓ K hK M hM hBound κ hκ.continuousOn
      (fun _ _ _ _ => rfl) ha hb).symm
  have hB : Schatten p B := he ▸ hA
  obtain ⟨hX,hXN⟩ := schatten_lowerIntervalKernelOperator p τ hp hτ ℓ hℓ K hK M hM hBound hB
  refine ⟨lowerIntervalKernelOperator ℓ K hK M hM hBound,hX,?_,?_⟩
  · change schattenNorm p (lowerIntervalKernelOperator ℓ K hK M hM hBound) ≤ τ*schattenNorm p B at hXN
    rw [← he] at hXN
    exact hXN
  · intro a b ha hb
    exact lowerIntervalKernelOperator_pairing_smooth ℓ K hK M hM hBound κ hκ.continuousOn
      (fun _ _ _ _ => rfl) ha hb

/-- Uniformly bounded actual kernels on shrinking intervals yield bounded cuts on the original
interval. The physical test pairing is eventually exact; no scalar limit is supplied here. -/
theorem exists_interval_regularization_cuts (p τ : ℝ) (hp : 0 < p) (hτ0 : 0 ≤ τ)
    (hτ : TriangularConstant p τ) (ℓ : ℝ) (B : ℝ)
    (ε : ℕ → ℝ) (hεPos : ∀ n, 0 < ε n) (hεSmall : ∀ n, ε n < ℓ)
    (hεLim : Tendsto ε atTop (𝓝 0))
    (A : ∀ n : ℕ, IntervalL2 (ℓ-ε n) →L[ℂ] IntervalL2 (ℓ-ε n))
    (hA : ∀ n, Schatten p (A n) ∧ schattenNorm p (A n) ≤ B)
    (κ : ℕ → ℝ → ℂ) (hκ : ∀ n, Continuous (κ n))
    (hForm : ∀ (n : ℕ) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε n) a)
      (hb : IntervalSmoothCompact (ℓ-ε n) b),
      inner ℂ (smoothIntervalL2 (ℓ-ε n) b hb) (A n (smoothIntervalL2 (ℓ-ε n) a ha)) =
        ∫ y : ℝ, κ n y*pwCorrelation a b y) :
    ∃ T : ℕ → IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ,
      (∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ τ*B) ∧
      ∀ (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
        (fun n => inner ℂ (smoothIntervalL2 ℓ b hb) (T n (smoothIntervalL2 ℓ a ha))) =ᶠ[atTop]
          (fun n => ∫ y in Ioi (0 : ℝ), κ n y*pwCorrelation a b y) := by
  have hCut (n : ℕ) := exists_lower_cut_of_smooth_pairing p τ hp hτ (ℓ-ε n)
    (sub_pos.mpr (hεSmall n)) (A n) (hA n).1 (κ n) (hκ n) (hForm n)
  choose X hX using hCut
  let T : ℕ → IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
    fun n => intervalOperatorExtension (ℓ-ε n) ℓ (X n)
  refine ⟨T,?_,?_⟩
  · intro n
    obtain ⟨hT,hTN⟩ := schatten_intervalOperatorExtension (ℓ-ε n) ℓ p (X n) (hX n).1
    exact ⟨hT,hTN.trans ((hX n).2.1.trans (mul_le_mul_of_nonneg_left (hA n).2 hτ0))⟩
  · intro a b ha hb
    obtain ⟨δa,hδa,hMarginA⟩ := ha.exists_short_margin
    obtain ⟨δb,hδb,hMarginB⟩ := hb.exists_short_margin
    filter_upwards [Filter.Tendsto.eventually_lt_const hδa hεLim,
      Filter.Tendsto.eventually_lt_const hδb hεLim] with n hna hnb
    have haS := hMarginA (ε n) (hεPos n) hna
    have hbS := hMarginB (ε n) (hεPos n) hnb
    have hL : ℓ-ε n ≤ ℓ := by linarith [hεPos n]
    calc
      _ = inner ℂ (smoothIntervalL2 (ℓ-ε n) b hbS) (X n (smoothIntervalL2 (ℓ-ε n) a haS)) :=
        inner_intervalOperatorExtension_smooth (ℓ-ε n) ℓ hL (X n) a b haS hbS
      _ = _ := (hX n).2.2 a b haS hbS

/-- A concrete positive regularization scale, strictly below half the original length. -/
def atomicRegularizationStep (ℓ : ℝ) (n : ℕ) : ℝ := (ℓ/4)/((n : ℝ)+1)

theorem atomicRegularizationStep_pos (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    0 < atomicRegularizationStep ℓ n := by unfold atomicRegularizationStep; positivity

theorem atomicRegularizationStep_lt_half (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    atomicRegularizationStep ℓ n < ℓ/2 := by
  have hn : (1 : ℝ) ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have he : atomicRegularizationStep ℓ n ≤ ℓ/4 :=
    div_le_self (by positivity : 0 ≤ ℓ/4) hn
  linarith

theorem tendsto_atomicRegularizationStep (ℓ : ℝ) :
    Tendsto (atomicRegularizationStep ℓ) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ℓ/4)
  unfold atomicRegularizationStep
  simpa only [mul_one_div,mul_zero] using h

theorem schatten_unitaryConjugate_le {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (p : ℝ) (A : H →L[ℂ] H) (hA : Schatten p A) :
    Schatten p (unitaryConjugate U A) ∧ schattenNorm p (unitaryConjugate U A) ≤ schattenNorm p A := by
  unfold unitaryConjugate
  exact schatten_two_sided_contraction A hA _ _
    (norm_isometry_clm_le_one U.toLinearIsometry) (norm_isometry_clm_le_one U.symm.toLinearIsometry)

theorem inner_unitaryConjugate_images {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (a b : H) :
    inner ℂ (U b) (unitaryConjugate U A (U a))=inner ℂ b (A a) := by
  change inner ℂ (U b) (U (A (U.symm (U a))))=inner ℂ b (A a)
  rw [U.symm_apply_apply,U.inner_map_map]

/-- The remaining operator identification is an explicit average-kernel pairing, not a splitting
or scalar-limit premise. All bounded cuts, scalar asymptotics and dense-core glue are proved here. -/
theorem atomicRegularization_data_of_average_pairing (p τ : ℝ) (hp : 1 < p)
    (hτPos : 0 < τ) (hτ : TriangularConstant p τ)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u)
    (H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy)
    (hDense : Dense (pwSmoothModelCore U : Set (Model u)))
    (hBound : ∀ f ∈ pwSmoothModelCore U, IsBounded f.val)
    (φ ψ : Hardy) (A : Model u →L[ℂ] Model u) (hA : Schatten p A)
    (hAnalytic : ∀ (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val=
        (Complex.I / (Real.sqrt 2 : ℂ)) * ∫ t in Ioi (0 : ℝ), (H.symm φ) t *
          (-deriv (pwCorrelation a b) t+pwCorrelation a b t))
    (hAverage : ∀ (n : ℕ) (a b : ℝ → ℂ)
      (ha : IntervalSmoothCompact (ℓ-atomicRegularizationStep ℓ n) a)
      (hb : IntervalSmoothCompact (ℓ-atomicRegularizationStep ℓ n) b),
      inner ℂ (smoothIntervalL2 (ℓ-atomicRegularizationStep ℓ n) b hb)
        (shortIntervalTranslatedAverage (ℓ-atomicRegularizationStep ℓ n) ℓ (atomicRegularizationStep ℓ n)
          (scaledAtomicMollifier (atomicRegularizationStep ℓ n)) (unitaryConjugate U.symm A)
          (smoothIntervalL2 (ℓ-atomicRegularizationStep ℓ n) a ha))=
        ∫ y : ℝ, atomicSmoothedKernel (atomicRegularizationStep ℓ n) (H.symm φ) (H.symm ψ) y *
          pwCorrelation a b y) :
    ∃ M : Submodule ℂ (Model u), Dense (M : Set (Model u)) ∧
      (∀ f : M, IsBounded f.val.val) ∧ ∃ e : M, inner ℂ e.val e.val=1 ∧
      ∃ T : ℕ → Model u →L[ℂ] Model u, ∃ μ : ℕ → ℂ,
        (∀ n, Schatten p (T n) ∧ schattenNorm p (T n) ≤ τ*schattenNorm p A) ∧
        ∀ f g : M, Tendsto (fun n => inner ℂ g.val (T n f.val)-
          coreForm φ.val f.val.val g.val.val-μ n*inner ℂ g.val f.val) atTop (𝓝 0) := by
  let ε := atomicRegularizationStep ℓ
  have hεPos (n : ℕ) : 0 < ε n := atomicRegularizationStep_pos ℓ hℓ n
  have hεSmall (n : ℕ) : ε n < ℓ := (atomicRegularizationStep_lt_half ℓ hℓ n).trans (by linarith)
  have hεLim : Tendsto ε atTop (𝓝 0) := tendsto_atomicRegularizationStep ℓ
  let A₀ := unitaryConjugate U.symm A
  have hA₀ := schatten_unitaryConjugate_le U.symm p A hA
  let B : ∀ n : ℕ, IntervalL2 (ℓ-ε n) →L[ℂ] IntervalL2 (ℓ-ε n) := fun n =>
    shortIntervalTranslatedAverage (ℓ-ε n) ℓ (ε n) (scaledAtomicMollifier (ε n)) A₀
  have hB (n : ℕ) : Schatten p (B n) ∧ schattenNorm p (B n) ≤ schattenNorm p A := by
    have h := schatten_shortIntervalTranslatedAverage (ℓ-ε n) ℓ (ε n) p hp.le A₀ hA₀.1
      (scaledAtomicMollifier (ε n)) (scaledAtomicMollifier_contDiff (ε n)).continuous
      (scaledAtomicMollifier_integrable (hεPos n)) (scaledAtomicMollifier_nonneg (hεPos n))
      (scaledAtomicMollifier_integral (hεPos n))
    exact ⟨h.1,h.2.trans hA₀.2⟩
  obtain ⟨T,hT,hPair⟩ := exists_interval_regularization_cuts p τ (by linarith) hτPos.le hτ ℓ
    (schattenNorm p A) ε hεPos hεSmall hεLim B hB
    (fun n => atomicSmoothedKernel (ε n) (H.symm φ) (H.symm ψ))
    (fun n => (atomicSmoothedKernel_contDiff (hεPos n) _ _).continuous) hAverage
  obtain ⟨e,he⟩ := exists_unit_mem_dense_submodule (pwSmoothModelCore U) hDense
    (modelReproducingKernel u hu origin) (modelReproducingKernel_ne_zero u hu hn origin)
  refine ⟨pwSmoothModelCore U,hDense,(fun f => hBound f.val f.property),e,he,
    (fun n => unitaryConjugate U (T n)),(fun n => atomicCrossingScalar (ε n) (H.symm ψ)),?_,?_⟩
  · intro n
    obtain ⟨hS,hN⟩ := schatten_unitaryConjugate_le U p (T n) (hT n).1
    exact ⟨hS,hN.trans (hT n).2⟩
  · intro f g
    obtain ⟨a,ha,hfa⟩ := (mem_pwSmoothModelCore_iff ℓ u U f.val).mp f.property
    obtain ⟨b,hb,hgb⟩ := (mem_pwSmoothModelCore_iff ℓ u U g.val).mp g.property
    have hWithin : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hεLim,Eventually.of_forall hεPos⟩
    have hScalar := atomicSmoothedKernel_positive_test_tendsto (H.symm φ) (H.symm ψ)
      (pwCorrelation a b) ((pwCorrelation_contDiff ha hb).of_le (by simp))
      (pwCorrelation_hasCompactSupport ha hb)
    rw [← hAnalytic a b ha hb,pwCorrelation_zero_eq_inner ha hb,← U.inner_map_map] at hScalar
    have hSeq := hScalar.comp hWithin
    apply hSeq.congr'
    filter_upwards [hPair a b ha hb] with n hPhysical
    rw [hfa,hgb,inner_unitaryConjugate_images,hPhysical]
    rfl

end TTO.Paper.Proved
