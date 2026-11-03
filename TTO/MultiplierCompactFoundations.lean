/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MultiplicationFoundations
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Finite singleton-null standard-Borel multipliers: actual positive splits and compactness. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section PositiveSplits
variable {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

/-- A positive measurable set admits a genuinely smaller positive measurable subset.
Standard Borel structure is essential to this proof; singleton-null alone is not enough
on arbitrary measurable spaces. -/
theorem exists_positive_measure_subset (s : Set X) (hs : MeasurableSet s) (hpos : 0 < μ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s := by
  classical
  by_contra! hnone
  let ρ : Measure X := (μ s)⁻¹ • μ.restrict s
  have hρ : ρ Set.univ = 1 := by
    change (μ s)⁻¹ * (μ.restrict s) Set.univ = 1
    rw [Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top μ s)
  let : IsZeroOneMeasure ρ := by
    constructor
    intro t ht
    change (μ s)⁻¹ * (μ.restrict s) t = 0 ∨ (μ s)⁻¹ * (μ.restrict s) t = 1
    rw [Measure.restrict_apply ht]
    by_cases hz : μ (t ∩ s) = 0
    · exact Or.inl (by rw [hz,mul_zero])
    · right
      have he : μ (t ∩ s) = μ s := le_antisymm (measure_mono inter_subset_right)
        (hnone (t ∩ s) (ht.inter hs) inter_subset_right (pos_iff_ne_zero.mpr hz))
      rw [he]
      exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top μ s)
  have hne : ρ ≠ 0 := by
    intro he
    simp [he] at hρ
  let : NeZero ρ := ⟨hne⟩
  obtain ⟨x,hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := ρ)
  have hz : ρ {x} = 0 := by simp [ρ]
  simp [hx] at hz


/-- A positive measurable set splits into two disjoint positive measurable pieces. -/
theorem exists_positive_disjoint_split (s : Set X) (hs : MeasurableSet s) (hpos : 0 < μ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ 0 < μ (s \ t) := by
  obtain ⟨t,ht,hts,hpt,hlt⟩ := exists_positive_measure_subset μ s hs hpos
  refine ⟨t,ht,hts,hpt,?_⟩
  rw [measure_sdiff hts ht.nullMeasurableSet (measure_ne_top μ t)]
  exact tsub_pos_iff_lt.mpr hlt

/-- An actual sequence of disjoint positive measurable pieces of any positive measurable set. -/
theorem exists_disjoint_positive_sets (s : Set X) (hs : MeasurableSet s) (hpos : 0 < μ s) :
    ∃ E : ℕ → Set X, (∀ n, MeasurableSet (E n) ∧ E n ⊆ s ∧ 0 < μ (E n)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) := by
  classical
  let P := {t : Set X // MeasurableSet t ∧ 0 < μ t}
  have hex (t : P) := exists_positive_disjoint_split μ t.val t.property.1 t.property.2
  let piece (t : P) : Set X := Classical.choose (hex t)
  have hp (t : P) : MeasurableSet (piece t) ∧ piece t ⊆ t.val ∧
      0 < μ (piece t) ∧ 0 < μ (t.val \ piece t) := Classical.choose_spec (hex t)
  let next (t : P) : P := ⟨t.val \ piece t,t.property.1.diff (hp t).1,(hp t).2.2.2⟩
  let R : ℕ → P := fun n => Nat.rec ⟨s,hs,hpos⟩ (fun _ t => next t) n
  let E : ℕ → Set X := fun n => piece (R n)
  have hRnext (n : ℕ) : (R (n+1)).val = (R n).val \ E n := rfl
  have hanti : Antitone (fun n => (R n).val) := antitone_nat_of_succ_le (fun n => by
    rw [hRnext]
    exact sdiff_subset)
  have hsub (n : ℕ) : E n ⊆ (R n).val := (hp (R n)).2.1
  have hdis (i j : ℕ) (hij : i < j) : Disjoint (E i) (E j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hr : x ∈ (R (i+1)).val := hanti (Nat.succ_le_of_lt hij) (hsub j hxj)
    rw [hRnext] at hr
    exact hr.2 hxi
  refine ⟨E,fun n => ⟨(hp (R n)).1,?_,(hp (R n)).2.2.1⟩,?_⟩
  · exact (hsub n).trans (hanti (Nat.zero_le n))
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdis i j h
    · exact (hdis j i h).symm

end PositiveSplits
section NormalizedIndicators
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The actual L²-normalized indicator, with the native zero normalization convention. -/
def normalizedIndicator (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ :=
  NormedSpace.normalize (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))

/-- Positive measure makes this a genuine unit vector. -/
theorem norm_normalizedIndicator (s : Set X) (hs : MeasurableSet s) (hp : 0 < μ s) :
    ‖normalizedIndicator μ s hs‖ = 1 := by
  have hr : 0 < μ.real s := ENNReal.toReal_pos hp.ne' (measure_ne_top μ s)
  have hn : 0 < ‖indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)‖ := by
    rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simpa only [norm_one,one_mul] using Real.rpow_pos_of_pos hr (1/(2 : ℝ≥0∞).toReal)
  exact NormedSpace.norm_normalize (norm_pos_iff.mp hn)

/-- This vector is supported on the actual measurable set, in the required a.e. sense. -/
theorem normalizedIndicator_ae_notMem (s : Set X) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, x ∉ s → normalizedIndicator μ s hs x = 0 := by
  let a : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)
  have hm := Lp.coeFn_smul (‖a‖⁻¹) a
  have hz := indicatorConstLp_coeFn_notMem (p := (2 : ℝ≥0∞)) (hs := hs)
    (hμs := measure_ne_top μ s) (c := (1 : ℂ))
  filter_upwards [hm,hz] with x hx hz
  intro hxs
  change ((‖a‖⁻¹) • a : Lp ℂ 2 μ) x = 0
  rw [hx]
  change ‖a‖⁻¹ • a x = 0
  have ha : a x = 0 := hz hxs
  rw [ha,smul_zero]

/-- Disjoint positive sets give a genuine orthonormal sequence of normalized indicators. -/
theorem normalizedIndicators_orthonormal (E : ℕ → Set X) (hE : ∀ n, MeasurableSet (E n))
    (hp : ∀ n, 0 < μ (E n)) (hd : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Orthonormal ℂ (fun n => normalizedIndicator μ (E n) (hE n)) := by
  refine ⟨fun n => norm_normalizedIndicator μ (E n) (hE n) (hp n),?_⟩
  intro i j hij
  have he : inner ℂ (indicatorConstLp 2 (hE i) (measure_ne_top μ (E i)) (1 : ℂ))
      (indicatorConstLp 2 (hE j) (measure_ne_top μ (E j)) (1 : ℂ)) = 0 := by
    rw [L2.inner_indicatorConstLp_one_indicatorConstLp_one]
    simp [Set.disjoint_iff_inter_eq_empty.mp (hd hij)]
  simp only [normalizedIndicator,NormedSpace.normalize,inner_smul_left_eq_smul,
    inner_smul_right_eq_smul,he,smul_zero]

end NormalizedIndicators

/-- Native Bessel summability gives weak nullity without a weak-topology wrapper. -/
theorem orthonormal_tendsto_inner_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : ℕ → H) (he : Orthonormal ℂ e) (v : H) :
    Tendsto (fun n => inner ℂ v (e n)) atTop (𝓝 0) := by
  apply tendsto_zero_of_summableValues _ 2 (by norm_num)
  simpa only [summableValues,Real.rpow_two,norm_inner_symm] using he.inner_products_summable v

section MultiplierLowerBound
variable {X : Type} [MeasurableSpace X] (μ : Measure X)

/-- A represented multiplier bounded below on a vector's support bounds its actual L² norm. -/
theorem multiplier_norm_lower_on_support (f : X → ℂ) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hM : RepresentsMultiplier μ f M) (δ : ℝ) (hδ : 0 ≤ δ) (a : Lp ℂ 2 μ)
    (ha : ∀ᵐ x ∂μ, a x ≠ 0 → δ ≤ ‖f x‖) : δ*‖a‖ ≤ ‖M a‖ := by
  have hn : ‖(δ : ℂ) • a‖ ≤ ‖M a‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (δ : ℂ) a,hM a,ha] with x hsm hm hx
    rw [hsm,hm]
    change ‖(δ : ℂ) • a x‖ ≤ ‖f x*a x‖
    rw [norm_smul,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    by_cases hz : a x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hx hz) (norm_nonneg _)
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ] using hn

/-- A symbol not equal to zero a.e. has a positive-norm level set of positive measure. -/
theorem exists_positive_symbol_level (f : X → ℂ) (hf : ¬∀ᵐ x ∂μ, f x = 0) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < μ {x | δ ≤ ‖f x‖} := by
  by_contra! hnone
  have hlevels (n : ℕ) : ∀ᵐ x ∂μ, ‖f x‖ < 1/((n : ℝ)+1) := by
    have hz : μ {x | 1/((n : ℝ)+1) ≤ ‖f x‖} = 0 :=
      nonpos_iff_eq_zero.mp (hnone _ (by positivity))
    apply ae_iff.mpr
    simpa only [not_lt] using hz
  apply hf
  filter_upwards [ae_all_iff.mpr hlevels] with x hx
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  exact ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall (fun n => (hx n).le))

end MultiplierLowerBound

section CompactMultipliers
variable {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

/-- A nonzero represented multiplier on a finite singleton-null standard-Borel space
cannot be compact. Symbol measurability is derived from the actual constant-one vector. -/
theorem compact_representedMultiplier_iff_zero (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hM : RepresentsMultiplier μ f M) :
    IsCompactOperator M ↔ ∀ᵐ x ∂μ, f x = 0 := by
  classical
  constructor
  · intro hcomp
    by_contra hnonzero
    have hmem := representedMultiplier_memLp μ f M hM
    let g := hmem.aestronglyMeasurable.mk f
    have hg : Measurable g := hmem.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have heq : f =ᵐ[μ] g := hmem.aestronglyMeasurable.ae_eq_mk
    have hgM : RepresentsMultiplier μ g M := by
      intro a
      filter_upwards [hM a,heq] with x hm hx
      rw [hm,hx]
    have hgnonzero : ¬∀ᵐ x ∂μ, g x = 0 := fun hz => hnonzero (heq.trans hz)
    obtain ⟨δ,hδ,hpos⟩ := exists_positive_symbol_level μ g hgnonzero
    have hmeas : MeasurableSet {x | δ ≤ ‖g x‖} := measurableSet_le measurable_const hg.norm
    obtain ⟨E,hE,hd⟩ := exists_disjoint_positive_sets μ _ hmeas hpos
    let e : ℕ → Lp ℂ 2 μ := fun n => normalizedIndicator μ (E n) (hE n).1
    have hON : Orthonormal ℂ e := normalizedIndicators_orthonormal μ E
      (fun n => (hE n).1) (fun n => (hE n).2.2) hd
    have hlim := compact_tendsto_zero_of_inner atTop e (fun n => (hON.1 n).le)
      (fun v => orthonormal_tendsto_inner_zero e hON v) M hcomp
    have hlower (n : ℕ) : δ ≤ ‖M (e n)‖ := by
      have hb := multiplier_norm_lower_on_support μ g M hgM δ hδ.le (e n) (by
        filter_upwards [normalizedIndicator_ae_notMem μ (E n) (hE n).1] with x hx
        intro hne
        have hxin : x ∈ E n := by
          by_contra ho
          exact hne (hx ho)
        exact (hE n).2.1 hxin)
      simpa only [hON.1 n,mul_one] using hb
    have hn : Tendsto (fun n => ‖M (e n)‖) atTop (𝓝 0) := by
      have ht := (continuous_norm.tendsto (0 : Lp ℂ 2 μ)).comp hlim
      simp only [norm_zero] at ht
      convert ht using 1
      funext n; rfl
    have hbad : δ ≤ 0 := ge_of_tendsto hn (Filter.Eventually.of_forall hlower)
    exact hδ.not_ge hbad
  · intro hz
    rw [representedMultiplier_zero_of_ae μ f M hM hz]
    exact isCompactOperator_zero

end CompactMultipliers


/-- The exact nonatomic compact-multiplier field, with only the frozen measure hypotheses. -/
theorem nonatomic_multiplier_compact_iff (μ : Measure Boundary) (hμ : μ Set.univ < ∞)
    (hn : NonatomicMeasure μ) (f : Boundary → ℂ) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hM : RepresentsMultiplier μ f M) : IsCompactOperator M ↔ ∀ᵐ x ∂μ, f x = 0 := by
  let : IsFiniteMeasure μ := ⟨hμ⟩
  let : NullSingletonClass μ := ⟨hn⟩
  exact compact_representedMultiplier_iff_zero μ f M hM

/-- The interval factor has mass one, so product-a.e. vanishing is exactly base-a.e. vanishing.
The arbitrary-set product formula avoids an extra measurability premise on the symbol. -/
theorem fiber_ae_zero_iff (μ : Measure Boundary) (f : Boundary → ℂ) :
    (∀ᵐ x ∂fiberMeasure μ, f x.1 = 0) ↔ ∀ᵐ t ∂μ, f t = 0 := by
  rw [ae_iff,ae_iff]
  have hs : {x : Boundary × ℝ | ¬f x.1 = 0} = {t : Boundary | ¬f t = 0} ×ˢ (Set.univ : Set ℝ) := by
    ext x
    simp
  rw [hs,Measure.prod_prod]
  simp

/-- The exact fiber compact-multiplier field, with the actual unit-interval factor. -/
theorem fiber_multiplier_compact_iff (μ : Measure Boundary) (hμ : μ Set.univ < ∞)
    (f : Boundary → ℂ) (M : Lp ℂ 2 (fiberMeasure μ) →L[ℂ] Lp ℂ 2 (fiberMeasure μ))
    (hM : RepresentsMultiplier (fiberMeasure μ) (fun x => f x.1) M) :
    IsCompactOperator M ↔ ∀ᵐ t ∂μ, f t = 0 := by
  let : IsFiniteMeasure μ := ⟨hμ⟩
  let : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  exact (compact_representedMultiplier_iff_zero (fiberMeasure μ) (fun x => f x.1) M hM).trans
    (fiber_ae_zero_iff μ f)

end TTO.Paper.Proved
