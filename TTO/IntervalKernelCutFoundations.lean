/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalKernelFoundations
public import TTO.IntervalTranslationFoundations

/-! Literal lower kernels, local cell estimates and triangular approximation on interval L². -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Output minus input is positive exactly on this strict lower triangle. -/
def lowerIntervalKernel (K : ℝ → ℝ → ℂ) (s t : ℝ) : ℂ := if t<s then K s t else 0

theorem stronglyMeasurable_lowerIntervalKernel (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) :
    StronglyMeasurable (Function.uncurry (lowerIntervalKernel K)) := by
  have h := hK.indicator (measurableSet_lt measurable_snd measurable_fst)
  change StronglyMeasurable (fun p : ℝ × ℝ => if p.2<p.1 then K p.1 p.2 else 0)
  exact h

theorem lowerIntervalKernel_bound (ℓ : ℝ) (K : ℝ → ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖lowerIntervalKernel K s t‖ ≤ M := by
  intro s hs t ht
  by_cases h : t<s
  · rw [lowerIntervalKernel,ite_eq_left h]
    exact hBound s hs t ht
  · rw [lowerIntervalKernel,ite_eq_right h,norm_zero]
    exact hM

def lowerIntervalKernelOperator (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  intervalKernelOperator ℓ (lowerIntervalKernel K) (stronglyMeasurable_lowerIntervalKernel K hK)
    M hM (lowerIntervalKernel_bound ℓ K M hM hBound)

/-- The lower operator has the exact physical integral from 0 to the output point. -/
theorem lowerIntervalKernelOperator_ae (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) (f : IntervalL2 ℓ) :
    lowerIntervalKernelOperator ℓ K hK M hM hBound f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      fun s => ∫ t in Ioo (0 : ℝ) s, K s t*f t := by
  filter_upwards [intervalKernelOperator_ae ℓ (lowerIntervalKernel K)
    (stronglyMeasurable_lowerIntervalKernel K hK) M hM (lowerIntervalKernel_bound ℓ K M hM hBound) f,
    ae_restrict_mem measurableSet_Ioo] with s he hs
  change (lowerIntervalKernelOperator ℓ K hK M hM hBound f) s =
    ∫ t, lowerIntervalKernel K s t*f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) at he
  rw [he]
  have hi : (fun t => lowerIntervalKernel K s t*f t) = (Iio s).indicator (fun t => K s t*f t) := by
    funext t
    by_cases h : t<s <;> simp only [lowerIntervalKernel,Set.indicator_apply,Set.mem_Iio,h,ite_true,ite_false,zero_mul]
  rw [hi,integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio s ∩ Ioo (0 : ℝ) ℓ = Ioo (0 : ℝ) s := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_Iio,Set.mem_Ioo]
    constructor
    · rintro ⟨ht,h0,_⟩
      exact ⟨h0,ht⟩
    · rintro ⟨h0,ht⟩
      exact ⟨ht,h0,ht.trans hs.2⟩
  rw [hset]

theorem inner_intervalMask_both (ℓ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (f g : IntervalL2 ℓ) :
    inner ℂ (intervalMask ℓ s hs f) (intervalMask ℓ s hs g) = inner ℂ f (intervalMask ℓ s hs g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalMask_ae ℓ s hs f,intervalMask_ae ℓ s hs g] with t hf hg
  rw [hf,hg]
  by_cases h : t ∈ s
  · simp only [indicator_of_mem h]
  · simp only [indicator_of_notMem h,inner_zero_right]

theorem norm_mask_intervalKernelRow_le (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (S : Set ℝ) (hS : MeasurableSet S) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) :
    ‖intervalMask ℓ S hS (intervalKernelRow ℓ K hK M hBound s hs)‖ ≤
      M*‖intervalMask ℓ S hS (intervalOne ℓ)‖ := by
  have he := Lp.norm_le_norm_of_ae_le
    (f := intervalMask ℓ S hS (intervalKernelRow ℓ K hK M hBound s hs))
    (g := (M : ℂ) • intervalMask ℓ S hS (intervalOne ℓ)) (by
      filter_upwards [intervalMask_ae ℓ S hS (intervalKernelRow ℓ K hK M hBound s hs),
        intervalKernelRow_ae ℓ K hK M hBound s hs,
        Lp.coeFn_smul (M : ℂ) (intervalMask ℓ S hS (intervalOne ℓ)),
        intervalMask_ae ℓ S hS (intervalOne ℓ),intervalOne_ae ℓ,
        ae_restrict_mem measurableSet_Ioo] with t hm hr hsm ho h1 ht
      rw [hm,hsm]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [ho]
      by_cases h : t ∈ S
      · rw [indicator_of_mem h,indicator_of_mem h,hr,h1,mul_one,Complex.norm_conj,
          Complex.norm_real,Real.norm_of_nonneg hM]
        exact hBound s hs t ht
      · rw [indicator_of_notMem h,indicator_of_notMem h,mul_zero])
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hM] using he

/-- A cell's row norm uses its own measure, rather than the full interval length. -/
theorem norm_intervalKernelRaw_mask_le (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (S : Set ℝ) (hS : MeasurableSet S) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ℓ) (f : IntervalL2 ℓ) :
    ‖intervalKernelRaw ℓ K (intervalMask ℓ S hS f) s‖ ≤
      M*‖intervalMask ℓ S hS (intervalOne ℓ)‖*‖intervalMask ℓ S hS f‖ := by
  rw [intervalKernelRaw_eq_inner ℓ K hK M hBound s hs,
    ← inner_intervalMask_both ℓ S hS (intervalKernelRow ℓ K hK M hBound s hs) f]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_mask_intervalKernelRow_le ℓ K hK M hM hBound S hS s hs) (norm_nonneg _))

/-- Both integration variables are restricted to the same actual cell. -/
theorem norm_intervalMask_kernel_mask_apply_le (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (S : Set ℝ) (hS : MeasurableSet S) (f : IntervalL2 ℓ) :
    ‖intervalMask ℓ S hS (intervalKernelOperator ℓ K hK M hM hBound (intervalMask ℓ S hS f))‖ ≤
      M*‖intervalMask ℓ S hS (intervalOne ℓ)‖^2*‖intervalMask ℓ S hS f‖ := by
  let C := M*‖intervalMask ℓ S hS (intervalOne ℓ)‖*‖intervalMask ℓ S hS f‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have he := Lp.norm_le_norm_of_ae_le
    (f := intervalMask ℓ S hS (intervalKernelOperator ℓ K hK M hM hBound (intervalMask ℓ S hS f)))
    (g := (C : ℂ) • intervalMask ℓ S hS (intervalOne ℓ)) (by
      filter_upwards [intervalMask_ae ℓ S hS
          (intervalKernelOperator ℓ K hK M hM hBound (intervalMask ℓ S hS f)),
        intervalKernelOperator_ae ℓ K hK M hM hBound (intervalMask ℓ S hS f),
        Lp.coeFn_smul (C : ℂ) (intervalMask ℓ S hS (intervalOne ℓ)),
        intervalMask_ae ℓ S hS (intervalOne ℓ),intervalOne_ae ℓ,
        ae_restrict_mem measurableSet_Ioo] with s hy hk hsm ho h1 hs
      rw [hy,hsm]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [ho]
      by_cases h : s ∈ S
      · rw [indicator_of_mem h,indicator_of_mem h,hk,h1,mul_one,
          Complex.norm_real,Real.norm_of_nonneg hC]
        exact norm_intervalKernelRaw_mask_le ℓ K hK M hM hBound S hS s hs f
      · rw [indicator_of_notMem h,indicator_of_notMem h,mul_zero])
  calc
    _ ≤ ‖(C : ℂ) • intervalMask ℓ S hS (intervalOne ℓ)‖ := he
    _ = _ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      dsimp only [C]
      ring

/-- The cell vector records its actual restricted measure, including truncated final cells. -/
theorem norm_intervalMask_one_sq (ℓ : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ‖intervalMask ℓ S hS (intervalOne ℓ)‖^2 =
      (volume.restrict (Ioo (0 : ℝ) ℓ)).real S := by
  have he : inner ℂ (intervalMask ℓ S hS (intervalOne ℓ)) (intervalMask ℓ S hS (intervalOne ℓ)) =
      ((volume.restrict (Ioo (0 : ℝ) ℓ)).real S : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ t, S.indicator (fun _ => (1 : ℂ)) t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) := by
        apply integral_congr_ae
        filter_upwards [intervalMask_ae ℓ S hS (intervalOne ℓ),intervalOne_ae ℓ] with t hq h1
        rw [hq]
        by_cases h : t ∈ S
        · rw [indicator_of_mem h,h1,RCLike.inner_apply,map_one,mul_one,indicator_of_mem h]
        · rw [indicator_of_notMem h,inner_zero_right,indicator_of_notMem h]
      _ = _ := by rw [integral_indicator hS]; simp [Measure.real,Complex.real_smul]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),he]
  exact Complex.ofReal_re _

theorem norm_intervalMask_kernel_mask_apply_le_measure (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (S : Set ℝ) (hS : MeasurableSet S) (f : IntervalL2 ℓ) :
    ‖intervalMask ℓ S hS (intervalKernelOperator ℓ K hK M hM hBound (intervalMask ℓ S hS f))‖ ≤
      M*(volume.restrict (Ioo (0 : ℝ) ℓ)).real S*‖intervalMask ℓ S hS f‖ := by
  simpa only [norm_intervalMask_one_sq] using norm_intervalMask_kernel_mask_apply_le ℓ K hK M hM hBound S hS f

theorem interval_measure_Ioc_le_length (ℓ a b : ℝ) (hab : a ≤ b) :
    (volume.restrict (Ioo (0 : ℝ) ℓ)).real (Ioc a b) ≤ b-a := by
  calc
    _ ≤ volume.real (Ioc a b) := ENNReal.toReal_mono (by simp [Real.volume_Ioc]) (Measure.restrict_le_self _)
    _ = _ := Real.volume_real_Ioc_of_le hab

theorem norm_intervalMask_kernel_mask_apply_le_cell (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (a b : ℝ) (hab : a ≤ b) (f : IntervalL2 ℓ) :
    ‖intervalMask ℓ (Ioc a b) measurableSet_Ioc
      (intervalKernelOperator ℓ K hK M hM hBound (intervalMask ℓ (Ioc a b) measurableSet_Ioc f))‖ ≤
      M*(b-a)*‖intervalMask ℓ (Ioc a b) measurableSet_Ioc f‖ := by
  calc
    _ ≤ M*(volume.restrict (Ioo (0 : ℝ) ℓ)).real (Ioc a b)*
        ‖intervalMask ℓ (Ioc a b) measurableSet_Ioc f‖ :=
      norm_intervalMask_kernel_mask_apply_le_measure ℓ K hK M hM hBound (Ioc a b) measurableSet_Ioc f
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (interval_measure_Ioc_le_length ℓ a b hab) hM) (norm_nonneg _)

def uniformIntervalMesh (ℓ : ℝ) (N : ℕ) : ℝ := ℓ/(N : ℝ)

def uniformIntervalCell (ℓ : ℝ) (N : ℕ) (i : Fin N) : Set ℝ :=
  Ico ((i.val : ℝ)*uniformIntervalMesh ℓ N) (((i.val : ℝ)+1)*uniformIntervalMesh ℓ N)

theorem uniformIntervalMesh_pos (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N) :
    0 < uniformIntervalMesh ℓ N := div_pos hℓ (by exact_mod_cast hN)

theorem uniformIntervalMesh_mul (ℓ : ℝ) (N : ℕ) (hN : 0 < N) :
    (N : ℝ)*uniformIntervalMesh ℓ N = ℓ := by
  rw [uniformIntervalMesh,mul_div_cancel₀]
  exact_mod_cast (Nat.ne_of_gt hN)

theorem uniformIntervalCell_disjoint (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N)
    (i j : Fin N) (hij : i ≠ j) : Disjoint (uniformIntervalCell ℓ N i) (uniformIntervalCell ℓ N j) := by
  have hδ := (uniformIntervalMesh_pos ℓ hℓ N hN).le
  apply Set.disjoint_left.mpr
  intro t hi hj
  change (i.val : ℝ)*uniformIntervalMesh ℓ N ≤ t ∧
    t < ((i.val : ℝ)+1)*uniformIntervalMesh ℓ N at hi
  change (j.val : ℝ)*uniformIntervalMesh ℓ N ≤ t ∧
    t < ((j.val : ℝ)+1)*uniformIntervalMesh ℓ N at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
    have hb := mul_le_mul_of_nonneg_right hh hδ
    exact not_lt_of_ge (hb.trans hj.1) hi.2
  · have hh : (j.val : ℝ)+1 ≤ (i.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
    have hb := mul_le_mul_of_nonneg_right hh hδ
    exact not_lt_of_ge (hb.trans hi.1) hj.2

/-- Uniform half-open cells form a genuine finite partition on the original open interval. -/
theorem existsUnique_uniformIntervalCell (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) ℓ) : ∃! i : Fin N, t ∈ uniformIntervalCell ℓ N i := by
  let δ := uniformIntervalMesh ℓ N
  have hδ : 0 < δ := uniformIntervalMesh_pos ℓ hℓ N hN
  have hq : 0 ≤ t/δ := div_nonneg ht.1.le hδ.le
  have hqN : t/δ < (N : ℝ) := by
    apply (div_lt_iff₀ hδ).mpr
    simpa only [δ,uniformIntervalMesh_mul ℓ N hN] using ht.2
  let j : Fin N := ⟨Nat.floor (t/δ),(Nat.floor_lt hq).mpr hqN⟩
  have hj : t ∈ uniformIntervalCell ℓ N j := by
    change (Nat.floor (t/δ) : ℝ)*δ ≤ t ∧ t < ((Nat.floor (t/δ) : ℝ)+1)*δ
    exact ⟨(le_div_iff₀ hδ).mp (Nat.floor_le hq),
      (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (t/δ))⟩
  refine ⟨j,hj,?_⟩
  intro k hk
  by_contra hkj
  exact Set.disjoint_left.mp (uniformIntervalCell_disjoint ℓ hℓ N hN k j hkj) hk hj

theorem interval_measure_Ico_le_length (ℓ a b : ℝ) (hab : a ≤ b) :
    (volume.restrict (Ioo (0 : ℝ) ℓ)).real (Ico a b) ≤ b-a := by
  calc
    _ ≤ volume.real (Ico a b) := ENNReal.toReal_mono (by simp [Real.volume_Ico]) (Measure.restrict_le_self _)
    _ = _ := Real.volume_real_Ico_of_le hab

def uniformIntervalProjection (ℓ : ℝ) (N : ℕ) (i : Fin N) :
    IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ := intervalMask ℓ (uniformIntervalCell ℓ N i) measurableSet_Ico

theorem uniformIntervalProjection_blocks (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N) :
    TriangularBlocks (uniformIntervalProjection ℓ N) := by
  constructor
  · exact intervalMask_sum_of_partition ℓ (uniformIntervalCell ℓ N) (fun _ => measurableSet_Ico)
      ((ae_restrict_mem measurableSet_Ioo).mono (fun t ht => existsUnique_uniformIntervalCell ℓ hℓ N hN t ht))
  · intro i
    exact adjoint_intervalMask ℓ _ measurableSet_Ico
  · intro i
    exact intervalMask_idempotent ℓ _ measurableSet_Ico
  · intro i j hij
    exact intervalMask_comp_of_disjoint ℓ _ _ measurableSet_Ico measurableSet_Ico
      (uniformIntervalCell_disjoint ℓ hℓ N hN i j hij)

theorem norm_uniformIntervalProjection_kernel_apply_le (ℓ : ℝ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 0 < N) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (i : Fin N) (f : IntervalL2 ℓ) :
    ‖uniformIntervalProjection ℓ N i
      (intervalKernelOperator ℓ K hK M hM hBound (uniformIntervalProjection ℓ N i f))‖ ≤
      M*uniformIntervalMesh ℓ N*‖uniformIntervalProjection ℓ N i f‖ := by
  have hδ := (uniformIntervalMesh_pos ℓ hℓ N hN).le
  have hb : (i.val : ℝ)*uniformIntervalMesh ℓ N ≤ ((i.val : ℝ)+1)*uniformIntervalMesh ℓ N := by nlinarith
  have hm := interval_measure_Ico_le_length ℓ _ _ hb
  have hm' : (volume.restrict (Ioo (0 : ℝ) ℓ)).real (uniformIntervalCell ℓ N i) ≤
      uniformIntervalMesh ℓ N := by
    change (volume.restrict (Ioo (0 : ℝ) ℓ)).real
      (Ico ((i.val : ℝ)*uniformIntervalMesh ℓ N) (((i.val : ℝ)+1)*uniformIntervalMesh ℓ N)) ≤ _
    nlinarith [hm]
  exact (norm_intervalMask_kernel_mask_apply_le_measure ℓ K hK M hM hBound
    (uniformIntervalCell ℓ N i) measurableSet_Ico f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm' hM) (norm_nonneg _))

/-- Equality on the physical output/input rectangle gives equality of the compressed operators. -/
theorem intervalMask_kernel_congr (ℓ : ℝ) (K L : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (hL : StronglyMeasurable (Function.uncurry L))
    (M : ℝ) (hM : 0 ≤ M)
    (hKB : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (hLB : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖L s t‖ ≤ M)
    (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hEq : ∀ s ∈ S, s ∈ Ioo (0 : ℝ) ℓ → ∀ t ∈ T, t ∈ Ioo (0 : ℝ) ℓ → K s t=L s t) :
    intervalMask ℓ S hS ∘L intervalKernelOperator ℓ K hK M hM hKB ∘L intervalMask ℓ T hT =
      intervalMask ℓ S hS ∘L intervalKernelOperator ℓ L hL M hM hLB ∘L intervalMask ℓ T hT := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMask_ae ℓ S hS (intervalKernelOperator ℓ K hK M hM hKB (intervalMask ℓ T hT f)),
    intervalMask_ae ℓ S hS (intervalKernelOperator ℓ L hL M hM hLB (intervalMask ℓ T hT f)),
    intervalKernelOperator_ae ℓ K hK M hM hKB (intervalMask ℓ T hT f),
    intervalKernelOperator_ae ℓ L hL M hM hLB (intervalMask ℓ T hT f),
    ae_restrict_mem measurableSet_Ioo] with s hSK hSL hAK hAL hs
  change intervalMask ℓ S hS (intervalKernelOperator ℓ K hK M hM hKB (intervalMask ℓ T hT f)) s =
    intervalMask ℓ S hS (intervalKernelOperator ℓ L hL M hM hLB (intervalMask ℓ T hT f)) s
  rw [hSK,hSL]
  by_cases hss : s∈S
  · rw [indicator_of_mem hss,indicator_of_mem hss,hAK,hAL]
    apply integral_congr_ae
    filter_upwards [intervalMask_ae ℓ T hT f,ae_restrict_mem measurableSet_Ioo] with t htf ht
    rw [htf]
    by_cases htt : t∈T
    · rw [indicator_of_mem htt,hEq s hss hs t htt ht]
    · rw [indicator_of_notMem htt,mul_zero,mul_zero]
  · rw [indicator_of_notMem hss,indicator_of_notMem hss]

theorem intervalMask_kernel_zero (ℓ : ℝ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hKB : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hEq : ∀ s ∈ S, s ∈ Ioo (0 : ℝ) ℓ → ∀ t ∈ T, t ∈ Ioo (0 : ℝ) ℓ → K s t=0) :
    intervalMask ℓ S hS ∘L intervalKernelOperator ℓ K hK M hM hKB ∘L intervalMask ℓ T hT = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMask_ae ℓ S hS (intervalKernelOperator ℓ K hK M hM hKB (intervalMask ℓ T hT f)),
    intervalKernelOperator_ae ℓ K hK M hM hKB (intervalMask ℓ T hT f),
    Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ)),
    ae_restrict_mem measurableSet_Ioo] with s hSK hAK hz hs
  change intervalMask ℓ S hS (intervalKernelOperator ℓ K hK M hM hKB (intervalMask ℓ T hT f)) s = (0 : IntervalL2 ℓ) s
  simp only [Pi.zero_apply] at hz
  rw [hSK,hz]
  by_cases hss : s∈S
  · rw [indicator_of_mem hss,hAK]
    apply integral_eq_zero_of_ae
    filter_upwards [intervalMask_ae ℓ T hT f,ae_restrict_mem measurableSet_Ioo] with t htf ht
    rw [htf]
    by_cases htt : t∈T
    · rw [hEq s hss hs t htt ht,zero_mul]
      rfl
    · rw [indicator_of_notMem htt,mul_zero]
      rfl
  · rw [indicator_of_notMem hss]

theorem uniformIntervalCell_lt (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (hN : 0 < N)
    (i j : Fin N) (hij : i < j) (s t : ℝ)
    (hs : s ∈ uniformIntervalCell ℓ N i) (ht : t ∈ uniformIntervalCell ℓ N j) : s<t := by
  have hδ := (uniformIntervalMesh_pos ℓ hℓ N hN).le
  have hh : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
  exact hs.2.trans_le ((mul_le_mul_of_nonneg_right hh hδ).trans ht.1)

theorem operatorBlock_lowerIntervalKernel_of_lt (ℓ : ℝ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 0 < N) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (i j : Fin N) (hji : j < i) :
    operatorBlock (uniformIntervalProjection ℓ N) (lowerIntervalKernelOperator ℓ K hK M hM hBound) i j =
      operatorBlock (uniformIntervalProjection ℓ N) (intervalKernelOperator ℓ K hK M hM hBound) i j := by
  apply intervalMask_kernel_congr ℓ (lowerIntervalKernel K) K
    (stronglyMeasurable_lowerIntervalKernel K hK) hK M hM (lowerIntervalKernel_bound ℓ K M hM hBound) hBound
    (uniformIntervalCell ℓ N i) (uniformIntervalCell ℓ N j) measurableSet_Ico measurableSet_Ico
  intro s hs _ t ht _
  exact ite_eq_left (uniformIntervalCell_lt ℓ hℓ N hN j i hji t s ht hs)

theorem operatorBlock_lowerIntervalKernel_of_gt (ℓ : ℝ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 0 < N) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (i j : Fin N) (hij : i < j) :
    operatorBlock (uniformIntervalProjection ℓ N) (lowerIntervalKernelOperator ℓ K hK M hM hBound) i j = 0 := by
  apply intervalMask_kernel_zero ℓ (lowerIntervalKernel K)
    (stronglyMeasurable_lowerIntervalKernel K hK) M hM (lowerIntervalKernel_bound ℓ K M hM hBound)
    (uniformIntervalCell ℓ N i) (uniformIntervalCell ℓ N j) measurableSet_Ico measurableSet_Ico
  intro s hs _ t ht _
  exact ite_eq_right (not_lt_of_ge (uniformIntervalCell_lt ℓ hℓ N hN i j hij s t hs ht).le)

/-- Removing the same-cell blocks from the lower kernel gives the exact strict finite cut. -/
theorem triangularCut_intervalKernel (ℓ : ℝ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 0 < N) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    triangularCut (uniformIntervalProjection ℓ N) (intervalKernelOperator ℓ K hK M hM hBound) =
      lowerIntervalKernelOperator ℓ K hK M hM hBound -
        blockPinching (uniformIntervalProjection ℓ N) (lowerIntervalKernelOperator ℓ K hK M hM hBound) := by
  have hQ := uniformIntervalProjection_blocks ℓ hℓ N hN
  apply operatorBlock_ext _ hQ
  intro i j
  rw [operatorBlock_cut _ hQ,operatorBlock_sub,operatorBlock_pinching _ hQ]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [ite_eq_right (not_lt_of_ge hij.le),diagonalSign,ite_eq_right (ne_of_lt hij),zero_smul,
      operatorBlock_lowerIntervalKernel_of_gt ℓ hℓ N hN K hK M hM hBound i j hij,zero_smul,sub_zero]
  · subst j
    simp only [lt_self_iff_false,ite_false,zero_smul,diagonalSign,ite_true,one_smul,sub_self]
  · rw [ite_eq_left hij,diagonalSign,ite_eq_right (ne_of_gt hij),one_smul,zero_smul,sub_zero,
      operatorBlock_lowerIntervalKernel_of_lt ℓ hℓ N hN K hK M hM hBound i j hij]

theorem norm_triangularCut_intervalKernel_sub_lower_le (ℓ : ℝ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 0 < N) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    ‖triangularCut (uniformIntervalProjection ℓ N) (intervalKernelOperator ℓ K hK M hM hBound) -
      lowerIntervalKernelOperator ℓ K hK M hM hBound‖ ≤ M*uniformIntervalMesh ℓ N := by
  rw [triangularCut_intervalKernel ℓ hℓ N hN K hK M hM hBound,sub_sub_cancel_left,norm_neg]
  exact norm_blockPinching_le_of_local_bound _ (uniformIntervalProjection_blocks ℓ hℓ N hN) _
    (M*uniformIntervalMesh ℓ N) (mul_nonneg hM (uniformIntervalMesh_pos ℓ hℓ N hN).le)
    (fun i f => norm_uniformIntervalProjection_kernel_apply_le ℓ hℓ N hN (lowerIntervalKernel K)
      (stronglyMeasurable_lowerIntervalKernel K hK) M hM (lowerIntervalKernel_bound ℓ K M hM hBound) i f)

theorem tendsto_uniformIntervalMesh (ℓ : ℝ) :
    Tendsto (fun n : ℕ => uniformIntervalMesh ℓ (n+1)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ℓ
  simpa only [uniformIntervalMesh,Nat.cast_add,Nat.cast_one,mul_one_div,mul_zero] using h

/-- Literal strict finite cuts converge in ordinary operator norm to the physical lower kernel. -/
theorem tendsto_triangularCut_intervalKernel (ℓ : ℝ) (hℓ : 0 < ℓ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M) :
    Tendsto (fun n : ℕ => triangularCut (uniformIntervalProjection ℓ (n+1))
      (intervalKernelOperator ℓ K hK M hM hBound)) atTop
      (𝓝 (lowerIntervalKernelOperator ℓ K hK M hM hBound)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    norm_triangularCut_intervalKernel_sub_lower_le ℓ hℓ (n+1) (Nat.succ_pos n) K hK M hM hBound)
    (by simpa only [mul_zero] using (tendsto_uniformIntervalMesh ℓ).const_mul M)

/-- The given finite triangular constant passes unchanged to an actual bounded lower kernel. -/
theorem schatten_lowerIntervalKernelOperator (p τ : ℝ) (hp : 0 < p)
    (hτ : TriangularConstant p τ) (ℓ : ℝ) (hℓ : 0 < ℓ) (K : ℝ → ℝ → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ s ∈ Ioo (0 : ℝ) ℓ, ∀ t ∈ Ioo (0 : ℝ) ℓ, ‖K s t‖ ≤ M)
    (hA : Schatten p (intervalKernelOperator ℓ K hK M hM hBound)) :
    Schatten p (lowerIntervalKernelOperator ℓ K hK M hM hBound) ∧
      schattenNorm p (lowerIntervalKernelOperator ℓ K hK M hM hBound) ≤
        τ*schattenNorm p (intervalKernelOperator ℓ K hK M hM hBound) := by
  apply (isClosed_schattenClosedBall p hp (τ*schattenNorm p (intervalKernelOperator ℓ K hK M hM hBound))).mem_of_tendsto
    (tendsto_triangularCut_intervalKernel ℓ hℓ K hK M hM hBound)
  apply Eventually.of_forall
  intro n
  have hQ := uniformIntervalProjection_blocks ℓ hℓ (n+1) (Nat.succ_pos n)
  exact hτ (IntervalL2 ℓ) (n+1) (uniformIntervalProjection ℓ (n+1)) hQ.sum_eq
    (fun i => ⟨hQ.adjoint_eq i,hQ.idempotent i⟩) hQ.orthogonal _ hA

end TTO.Paper.Proved
