/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors; adapted by Patrick Lopatto
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Group.Integral

/-! Adapted from TauCetiProject/TauCeti, commit d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad,
`TauCeti/MeasureTheory/Measure/Lebesgue/DyadicCube.lean`, Apache-2.0.
This standalone prerequisite uses the pinned Mathlib; Tau Ceti is not a dependency. -/

/-!
# Dyadic cubes in `ι → ℝ`

For `k : ℤ` and `m : ι → ℤ`, the **dyadic cube** of level `k` at position `m` is the half-open box

`Q(k, m) = ∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)`

(`TTO.DyadicAnalysis.dyadicCube`). The cubes of a fixed level partition `ι → ℝ`, the cube of level `k`
containing `x` being `Q(k, ⌊x / 2ᵏ⌋)` (`TTO.DyadicAnalysis.dyadicIndex`), and the levels are nested: two
dyadic cubes are either disjoint or one contains the other. Together with the **Lebesgue
differentiation theorem along dyadic cubes**, which says that the averages of an integrable
function over the dyadic cubes containing `x` converge to its value at `x` as the level tends to
`-∞`, this is what the stopping-time arguments of harmonic analysis need, starting with the
Calderón–Zygmund decomposition.

The ambient space carries the sup norm, for which closed balls are closed boxes. A dyadic cube is
therefore a closed ball up to a null set of its boundary
(`TTO.DyadicAnalysis.dyadicCube_ae_eq_closedBall`), and the differentiation theorem along dyadic cubes is
Mathlib's differentiation theorem along closed balls with moving centres.

## Main declarations

* `TTO.DyadicAnalysis.dyadicIndex`, `TTO.DyadicAnalysis.dyadicCube`, `TTO.DyadicAnalysis.dyadicCube_eq_pi`: dyadic cubes and the
  position of the cube of a given level containing a point.
* `TTO.DyadicAnalysis.dyadicIndex_add_one`, `TTO.DyadicAnalysis.dyadicCube_subset_dyadicCube`,
  `TTO.DyadicAnalysis.dyadicCube_subset_or_disjoint`, `TTO.DyadicAnalysis.disjoint_dyadicCube`: the nesting of the
  dyadic levels.
* `TTO.DyadicAnalysis.closure_dyadicCube`: the closure of a dyadic cube is a closed sup-norm ball.
* `TTO.DyadicAnalysis.volume_closedBall_eq_zero_of_nonpos`: a closed ball of nonpositive radius is null.
* `TTO.DyadicAnalysis.volume_dyadicCube`, `TTO.DyadicAnalysis.volume_dyadicCube_add_one`: a cube of level `k` has
  volume `(2ᵏ)ⁿ`, so its parent is `2ⁿ` times larger.
* `TTO.DyadicAnalysis.ae_tendsto_setLAverage_dyadicCube`: the Lebesgue differentiation theorem along dyadic
  cubes.

## References

* E. Stein, *Harmonic Analysis*, Chapter I, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

@[expose] public section

namespace TTO.DyadicAnalysis

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

variable {ι : Type*}

/-- The position of the dyadic cube of level `k` containing `x`: its `i`-th coordinate is
`⌊xᵢ / 2ᵏ⌋`. -/
noncomputable def dyadicIndex (k : ℤ) (x : ι → ℝ) : ι → ℤ :=
  fun i => ⌊x i / 2 ^ k⌋

@[simp]
theorem dyadicIndex_apply (k : ℤ) (x : ι → ℝ) (i : ι) : dyadicIndex k x i = ⌊x i / 2 ^ k⌋ :=
  (rfl)

/-- The **dyadic cube** of level `k` at position `m`: the points whose dyadic index of level `k`
is `m`, that is, the half-open box `∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)` (`TTO.DyadicAnalysis.dyadicCube_eq_pi`). -/
def dyadicCube (k : ℤ) (m : ι → ℤ) : Set (ι → ℝ) :=
  {x | dyadicIndex k x = m}

variable {j k : ℤ} {m m' : ι → ℤ} {x y : ι → ℝ}

@[simp]
theorem mem_dyadicCube : x ∈ dyadicCube k m ↔ dyadicIndex k x = m :=
  Iff.rfl

/-- Every point lies in the dyadic cube of each level indexed by its own dyadic index. -/
theorem mem_dyadicCube_dyadicIndex (k : ℤ) (x : ι → ℝ) : x ∈ dyadicCube k (dyadicIndex k x) :=
  mem_dyadicCube.2 rfl

/-- A dyadic cube is the half-open box `∏ᵢ [mᵢ 2ᵏ, (mᵢ + 1) 2ᵏ)`. -/
theorem dyadicCube_eq_pi (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m = univ.pi fun i => Ico ((m i : ℝ) * 2 ^ k) ((m i + 1) * 2 ^ k) := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  ext x
  simp only [mem_dyadicCube, funext_iff, dyadicIndex_apply, Int.floor_eq_iff, mem_univ_pi, mem_Ico,
    le_div_iff₀ h2, div_lt_iff₀ h2]

/-- Dyadic cubes are measurable. -/
theorem measurableSet_dyadicCube [Countable ι] (k : ℤ) (m : ι → ℤ) :
    MeasurableSet (dyadicCube k m) := by
  rw [dyadicCube_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- The dyadic index of level `k + 1` is obtained from the one of level `k` by halving and rounding
down: the parent of a dyadic cube. -/
theorem dyadicIndex_add_one (k : ℤ) (x : ι → ℝ) :
    dyadicIndex (k + 1) x = fun i => dyadicIndex k x i / 2 := by
  ext i
  rw [dyadicIndex_apply, dyadicIndex_apply, zpow_add_one₀ two_ne_zero, ← div_div]
  exact_mod_cast Int.floor_div_natCast (x i / 2 ^ k) 2

/-- Points in the same dyadic cube of level `j` are in the same dyadic cube of every level
`k ≥ j`. -/
theorem dyadicIndex_eq_of_le (hjk : j ≤ k) (h : dyadicIndex j x = dyadicIndex j y) :
    dyadicIndex k x = dyadicIndex k y := by
  induction k, hjk using Int.leInduction with
  | base => exact h
  | succ k _ ih => rw [dyadicIndex_add_one, dyadicIndex_add_one, ih]

/-- A dyadic cube of level `j` is contained in the dyadic cube of each level `k ≥ j` that meets
it. -/
theorem dyadicCube_subset_dyadicCube (hjk : j ≤ k) (hx : x ∈ dyadicCube j m) :
    dyadicCube j m ⊆ dyadicCube k (dyadicIndex k x) :=
  fun _ hy => dyadicIndex_eq_of_le hjk (hy.trans hx.symm)

/-- Two dyadic cubes of the same level are disjoint unless they are equal. -/
theorem disjoint_dyadicCube (h : m ≠ m') : Disjoint (dyadicCube k m) (dyadicCube k m') :=
  Set.disjoint_left.2 fun _ hx hx' => h (hx.symm.trans hx')

/-- Of two dyadic cubes, either the one of lower level is contained in the other or they are
disjoint. -/
theorem dyadicCube_subset_or_disjoint (hjk : j ≤ k) (m m' : ι → ℤ) :
    dyadicCube j m ⊆ dyadicCube k m' ∨ Disjoint (dyadicCube j m) (dyadicCube k m') := by
  rw [or_iff_not_imp_right, Set.not_disjoint_iff]
  rintro ⟨x, hxj, hxk⟩
  rw [← mem_dyadicCube.1 hxk]
  exact dyadicCube_subset_dyadicCube hjk hxj

section Fintype

variable [Fintype ι]

private theorem closedBall_dyadicCenter (k : ℤ) (m : ι → ℤ) :
    closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) =
      univ.pi fun i => Icc ((m i : ℝ) * 2 ^ k) ((m i + 1) * 2 ^ k) := by
  rw [closedBall_pi _ (by positivity)]
  refine pi_congr rfl fun i _ => ?_
  rw [Real.closedBall_eq_Icc]
  congr 1 <;> ring

/-- A dyadic cube is contained in the closed sup-norm ball around its centre whose radius is half
its side length. -/
theorem dyadicCube_subset_closedBall (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m ⊆ closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi]
  exact pi_mono fun _ _ => Ico_subset_Icc_self

/-- Up to a null set, a dyadic cube is the closed sup-norm ball around its centre whose radius is
half its side length. -/
theorem dyadicCube_ae_eq_closedBall (k : ℤ) (m : ι → ℤ) :
    dyadicCube k m =ᵐ[volume] closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi, volume_pi]
  exact Measure.pi_Ico_ae_eq_pi_Icc

/-- The closure of a dyadic cube is the closed sup-norm ball around its centre whose radius is half
its side length. -/
theorem closure_dyadicCube (k : ℤ) (m : ι → ℤ) :
    closure (dyadicCube k m) = closedBall (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) := by
  have h2 : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  rw [closedBall_dyadicCenter, dyadicCube_eq_pi, closure_pi_set]
  exact pi_congr rfl fun i _ => closure_Ico (by nlinarith)

/-- A closed sup-norm ball of nonpositive radius in `ℝⁿ`, `n ≥ 1`, is Lebesgue-null. -/
theorem volume_closedBall_eq_zero_of_nonpos [Nonempty ι] (c : ι → ℝ) {r : ℝ} (hr : r ≤ 0) :
    volume (closedBall c r) = 0 :=
  measure_mono_null (closedBall_subset_closedBall hr) (by rw [closedBall_zero]; simp)

/-- A dyadic cube of level `k` has volume `(2ᵏ)ⁿ`. -/
theorem volume_dyadicCube (k : ℤ) (m : ι → ℤ) :
    volume (dyadicCube k m) = ENNReal.ofReal ((2 ^ k) ^ Fintype.card ι) := by
  have h (i : ι) : ((m i : ℝ) + 1) * 2 ^ k - m i * 2 ^ k = 2 ^ k := by ring
  rw [dyadicCube_eq_pi, Real.volume_pi_Ico]
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]

/-- Dyadic cubes have positive volume. -/
theorem volume_dyadicCube_pos (k : ℤ) (m : ι → ℤ) : 0 < volume (dyadicCube k m) := by
  rw [volume_dyadicCube]
  exact ENNReal.ofReal_pos.2 (by positivity)

/-- Dyadic cubes have finite volume. -/
theorem volume_dyadicCube_ne_top (k : ℤ) (m : ι → ℤ) : volume (dyadicCube k m) ≠ ∞ := by
  rw [volume_dyadicCube]
  exact ENNReal.ofReal_ne_top

/-- Passing to the next dyadic level multiplies the volume of a cube by `2ⁿ`. -/
theorem volume_dyadicCube_add_one (k : ℤ) (m m' : ι → ℤ) :
    volume (dyadicCube (k + 1) m') = 2 ^ Fintype.card ι * volume (dyadicCube k m) := by
  rw [volume_dyadicCube, volume_dyadicCube, zpow_add_one₀ two_ne_zero, mul_comm _ (2 : ℝ),
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]

/-- In positive dimension, dyadic cubes become arbitrarily large as the level tends to `+∞`. -/
theorem tendsto_volume_dyadicCube_atTop [Nonempty ι] (m : ℤ → ι → ℤ) :
    Tendsto (fun k => volume (dyadicCube k (m k))) atTop (𝓝 ∞) := by
  simp_rw [volume_dyadicCube]
  refine ENNReal.tendsto_ofReal_atTop.comp <|
    (tendsto_pow_atTop Fintype.card_ne_zero).comp <|
      tendsto_atTop_atTop_of_monotone (fun _ _ h => zpow_le_zpow_right₀ one_le_two h) fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt b
  exact ⟨n, hn.le.trans <| by exact_mod_cast (Nat.lt_two_pow_self).le⟩

/-- **Lebesgue's differentiation theorem along dyadic cubes**: for an integrable `g`, at almost
every `x` the averages of `g` over the dyadic cubes containing `x` converge to `g x` as the level
tends to `-∞`. -/
theorem ae_tendsto_setLAverage_dyadicCube {g : (ι → ℝ) → ℝ≥0∞} (hg : AEMeasurable g)
    (hg' : ∫⁻ x, g x ≠ ∞) :
    ∀ᵐ x, Tendsto (fun k => ⨍⁻ y in dyadicCube k (dyadicIndex k x), g y ∂volume) atBot
      (𝓝 (g x)) := by
  let c : ℤ → (ι → ℝ) → ι → ℝ := fun k x i => ((dyadicIndex k x i : ℝ) + 2⁻¹) * 2 ^ k
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_lintegral_div hg hg']
    with x hx
  have hδ : Tendsto (fun k : ℤ => (2 : ℝ) ^ k / 2) atBot (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
    have htwo : Tendsto (fun k : ℤ => (2 : ℝ) ^ k) atBot (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, Real.rpow_intCast] using
        (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
          ((tendsto_intCast_atBot_iff (R := ℝ)).2 tendsto_id)
    simpa using htwo.div_const 2
  have hball := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume (c · x) _ hδ
    (Eventually.of_forall fun k => by
      rw [one_mul]
      exact dyadicCube_subset_closedBall k _ (mem_dyadicCube_dyadicIndex k x))
  refine (hx.comp hball).congr fun k => ?_
  simp only [Function.comp_apply, setLAverage_eq]
  rw [setLIntegral_congr (dyadicCube_ae_eq_closedBall k (dyadicIndex k x)),
    measure_congr (dyadicCube_ae_eq_closedBall k (dyadicIndex k x))]

end Fintype


/-! The stopping cubes and dyadic oscillation-tail proofs below are adapted from the same
Apache-2.0 Tau Ceti revision: `MeasureTheory/Integral/CalderonZygmund/Decomposition.lean`
(Cubes section only) and `MeasureTheory/Integral/JohnNirenberg.lean` (dyadic volume tail).
The full decomposition, exponential-integrability and Euclidean-ball infrastructure is unused. -/

open MeasureTheory

private theorem enorm_average_le_laverage {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) :
    ‖⨍ x, f x ∂μ‖ₑ ≤ ⨍⁻ x, ‖f x‖ₑ ∂μ := by
  rw [average_eq', laverage_eq']
  exact enorm_integral_le_lintegral_enorm _

private theorem enorm_setAverage_le_setLAverage {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (f : α → E) (s : Set α) :
    ‖⨍ x in s, f x ∂μ‖ₑ ≤ ⨍⁻ x in s, ‖f x‖ₑ ∂μ :=
  enorm_average_le_laverage _ _

section Stopping
variable [Fintype ι]
section Cubes

variable {g : (ι → ℝ) → ℝ≥0∞} {t : ℝ≥0∞} {q : ℤ × (ι → ℤ)}

/-- The **Calderón–Zygmund cubes** of `g` at height `t`: the dyadic cubes, recorded by level and
position, on which the average of `g` exceeds `t` while it is at most `t` on every dyadic cube of
higher level containing them. These are the maximal dyadic cubes on which the average of `g`
exceeds `t`. -/
def calderonZygmundCubes (g : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) : Set (ℤ × (ι → ℤ)) :=
  {q | t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ∧
    ∀ j m, q.1 < j → dyadicCube q.1 q.2 ⊆ dyadicCube j m →
      ⨍⁻ x in dyadicCube j m, g x ∂volume ≤ t}

theorem mem_calderonZygmundCubes :
    q ∈ calderonZygmundCubes g t ↔ t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ∧
      ∀ j m, q.1 < j → dyadicCube q.1 q.2 ⊆ dyadicCube j m →
        ⨍⁻ x in dyadicCube j m, g x ∂volume ≤ t :=
  Iff.rfl

/-- The average over a Calderón–Zygmund cube exceeds the height. -/
theorem lt_setLAverage_of_mem_calderonZygmundCubes (hq : q ∈ calderonZygmundCubes g t) :
    t < ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume :=
  hq.1

/-- The integral over a Calderón–Zygmund cube exceeds the height times its volume. -/
theorem mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes
    (hq : q ∈ calderonZygmundCubes g t) :
    t * volume (dyadicCube q.1 q.2) < ∫⁻ x in dyadicCube q.1 q.2, g x := by
  have h := lt_setLAverage_of_mem_calderonZygmundCubes hq
  rwa [setLAverage_eq, ENNReal.lt_div_iff_mul_lt (.inl (volume_dyadicCube_pos _ _).ne')
    (.inl (volume_dyadicCube_ne_top _ _))] at h

/-- The average over a Calderón–Zygmund cube is at most `2ⁿ` times the height: the average over
its parent cube is at most the height, and the parent is `2ⁿ` times larger. -/
theorem setLAverage_le_of_mem_calderonZygmundCubes (hq : q ∈ calderonZygmundCubes g t) :
    ⨍⁻ x in dyadicCube q.1 q.2, g x ∂volume ≤ 2 ^ Fintype.card ι * t := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos q.1 q.2).ne'
  have hsub := dyadicCube_subset_dyadicCube (lt_add_one q.1).le hx
  have hparent := hq.2 _ _ (lt_add_one q.1) hsub
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ y in dyadicCube q.1 q.2, g y
      ≤ ∫⁻ y in dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x), g y := lintegral_mono_set hsub
    _ = volume (dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x)) *
          ⨍⁻ y in dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x), g y ∂volume :=
        (measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)).symm
    _ ≤ volume (dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x)) * t := by gcongr
    _ = 2 ^ Fintype.card ι * t * volume (dyadicCube q.1 q.2) := by
        rw [volume_dyadicCube_add_one q.1 q.2]
        ring

/-- **Localization.** The Calderón–Zygmund cubes of `g` restricted to a dyadic cube `Q₀`, at a
height `t` at least the average of `g` over `Q₀`, lie inside `Q₀`: by the nesting of dyadic cubes,
any other dyadic cube is either disjoint from `Q₀` or contains it, and so has average at most
`t`. -/
theorem dyadicCube_subset_of_mem_calderonZygmundCubes_indicator {q₀ : ℤ × (ι → ℤ)}
    (ht : ⨍⁻ x in dyadicCube q₀.1 q₀.2, g x ∂volume ≤ t)
    (hq : q ∈ calderonZygmundCubes ((dyadicCube q₀.1 q₀.2).indicator g) t) :
    dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 := by
  set Q₀ := dyadicCube q₀.1 q₀.2
  set Q := dyadicCube q.1 q.2
  have hlt := lt_setLAverage_of_mem_calderonZygmundCubes hq
  have hint : ⨍⁻ x in Q, Q₀.indicator g x ∂volume = (∫⁻ x in Q₀ ∩ Q, g x) / volume Q := by
    rw [setLAverage_eq, lintegral_indicator (measurableSet_dyadicCube q₀.1 q₀.2),
      Measure.restrict_restrict (measurableSet_dyadicCube q₀.1 q₀.2)]
  have hcases : Q ⊆ Q₀ ∨ Q₀ ⊆ Q ∨ Disjoint Q₀ Q := by
    rcases le_total q.1 q₀.1 with hle | hle
    · exact (dyadicCube_subset_or_disjoint hle q.2 q₀.2).imp_right fun hd => .inr hd.symm
    · exact .inr (dyadicCube_subset_or_disjoint hle q₀.2 q.2)
  rcases hcases with hsub | hsub | hdisj
  · exact hsub
  · refine absurd hlt (not_lt.2 (hint ▸ ?_))
    rw [inter_eq_left.2 hsub]
    refine le_trans ?_ ht
    rw [setLAverage_eq]
    exact ENNReal.div_le_div_left (measure_mono hsub) _
  · rw [hint, hdisj.inter_eq, Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.zero_div] at hlt
    exact absurd hlt not_lt_zero

/-- Distinct Calderón–Zygmund cubes are disjoint. -/
theorem pairwiseDisjoint_calderonZygmundCubes :
    (calderonZygmundCubes g t).PairwiseDisjoint fun q => dyadicCube q.1 q.2 := by
  have key : ∀ q ∈ calderonZygmundCubes g t, ∀ q' ∈ calderonZygmundCubes g t, q.1 ≤ q'.1 →
      q ≠ q' → Disjoint (dyadicCube q.1 q.2) (dyadicCube q'.1 q'.2) := by
    intro q hq q' hq' hle hne
    refine (dyadicCube_subset_or_disjoint hle q.2 q'.2).resolve_left fun hsub => ?_
    rcases hle.lt_or_eq with hlt | heq
    · exact (hq'.1.trans_le (hq.2 _ _ hlt hsub)).false
    · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos q.1 q.2).ne'
      have hx' := mem_dyadicCube.1 (hsub hx)
      rw [← heq, mem_dyadicCube.1 hx] at hx'
      exact hne (Prod.ext heq hx')
  intro q hq q' hq' hne
  rcases le_total q.1 q'.1 with h | h
  · exact key q hq q' hq' h hne
  · exact (key q' hq' q hq h hne.symm).symm

/-- In positive dimension, every dyadic cube on which the average of an integrable `g` exceeds a
positive height `t` lies in a Calderón–Zygmund cube of `g` at height `t`. -/
theorem exists_mem_calderonZygmundCubes_of_lt_setLAverage [Nonempty ι] (hg : ∫⁻ x, g x ≠ ∞)
    (ht : t ≠ 0) {k : ℤ} {m : ι → ℤ} (h : t < ⨍⁻ x in dyadicCube k m, g x ∂volume) :
    ∃ q ∈ calderonZygmundCubes g t, k ≤ q.1 ∧ dyadicCube k m ⊆ dyadicCube q.1 q.2 := by
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (volume_dyadicCube_pos k m).ne'
  let A : ℤ → ℝ≥0∞ := fun j => ⨍⁻ y in dyadicCube j (dyadicIndex j x), g y ∂volume
  -- The averages over the cubes containing `x` are eventually below `t`, since they are at most
  -- `∫⁻ g` divided by the volume of the cube.
  have hsmall : ∀ᶠ j in atTop, A j < t := by
    have hlim : Tendsto (fun j => (∫⁻ y, g y) / volume (dyadicCube j (dyadicIndex j x)))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_div (tendsto_volume_dyadicCube_atTop _) (.inr hg)
    filter_upwards [(tendsto_order.1 hlim).2 t (pos_iff_ne_zero.2 ht)] with j hj
    refine lt_of_le_of_lt ?_ hj
    simp only [A, setLAverage_eq]
    exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  obtain ⟨j₀, ⟨hkj₀, hj₀⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := fun j => k ≤ j ∧ t < A j)
    ⟨N, fun j hj => le_of_not_gt fun hNj => (hN j hNj.le).not_gt hj.2⟩
    ⟨k, le_rfl, by simpa [A, mem_dyadicCube.1 hx] using h⟩
  refine ⟨(j₀, dyadicIndex j₀ x), ⟨hj₀, fun j m' hj hsub => ?_⟩, hkj₀,
    dyadicCube_subset_dyadicCube hkj₀ hx⟩
  have hm' : dyadicIndex j x = m' := mem_dyadicCube.1 (hsub (mem_dyadicCube_dyadicIndex j₀ x))
  subst hm'
  exact le_of_not_gt fun hlt => (hmax j ⟨hkj₀.trans hj.le, hlt⟩).not_gt hj

/-- In positive dimension, an integrable `g` is at most `t` almost everywhere off its
Calderón–Zygmund cubes at a positive height `t`. -/
theorem ae_le_of_forall_notMem_calderonZygmundCubes [Nonempty ι] (hg : AEMeasurable g)
    (hg' : ∫⁻ x, g x ≠ ∞) (ht : t ≠ 0) :
    ∀ᵐ x, (∀ q ∈ calderonZygmundCubes g t, x ∉ dyadicCube q.1 q.2) → g x ≤ t := by
  filter_upwards [ae_tendsto_setLAverage_dyadicCube hg hg'] with x hx hnot
  refine le_of_tendsto hx (Eventually.of_forall fun k => le_of_not_gt fun hlt => ?_)
  obtain ⟨q, hq, -, hsub⟩ := exists_mem_calderonZygmundCubes_of_lt_setLAverage hg' ht hlt
  exact hnot q hq (hsub (mem_dyadicCube_dyadicIndex k x))

private theorem pairwise_disjoint_calderonZygmundCubes :
    Pairwise (Function.onFun Disjoint fun q : calderonZygmundCubes g t => dyadicCube q.1.1 q.1.2) :=
  fun q q' hne => pairwiseDisjoint_calderonZygmundCubes q.2 q'.2 (Subtype.val_injective.ne hne)

/-- The union of the Calderón–Zygmund cubes is measurable. -/
theorem measurableSet_biUnion_calderonZygmundCubes (g : (ι → ℝ) → ℝ≥0∞) (t : ℝ≥0∞) :
    MeasurableSet (⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2) :=
  MeasurableSet.biUnion (to_countable _) fun q _ => measurableSet_dyadicCube q.1 q.2

/-- The **Calderón–Zygmund measure estimate**: `t` times the measure of the union of the
Calderón–Zygmund cubes of `g` at height `t` is at most the integral of `g` over that union. -/
theorem mul_volume_biUnion_calderonZygmundCubes_le :
    t * volume (⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2) ≤
      ∫⁻ x in ⋃ q ∈ calderonZygmundCubes g t, dyadicCube q.1 q.2, g x := by
  rw [biUnion_eq_iUnion,
    measure_iUnion pairwise_disjoint_calderonZygmundCubes fun q => measurableSet_dyadicCube _ _,
    lintegral_iUnion (fun q => measurableSet_dyadicCube _ _) pairwise_disjoint_calderonZygmundCubes,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun q =>
    (mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes q.2).le

end Cubes
end Stopping

open scoped NNReal

section Oscillation
variable [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : (ι → ℝ) → E} {q₀ : ℤ × (ι → ℤ)} {M : ℝ≥0}
/-- **One Calderón–Zygmund step.** Let `f` be integrable on the dyadic cube `Q₀`, with
`⨍_{Q₀} ‖f - f_{Q₀}‖ ≤ M` for some `M ≠ 0`. Then there are dyadic cubes `Q ⊆ Q₀` of total measure
at most `|Q₀| / 2` such that the measure of the set where `‖f - f_{Q₀}‖ > 2ⁿ⁺¹ (N + 1) M` is at most
the sum over these cubes `Q` of the measures of the sets where `‖f - f_Q‖ > 2ⁿ⁺¹ N M` on `Q`.
The cubes are the Calderón–Zygmund cubes of `‖f - f_{Q₀}‖` on `Q₀` at height `2M`. -/
private theorem exists_volume_lt_enorm_sub_setAverage_le_tsum [Nonempty ι] [CompleteSpace E]
    (hM0 : M ≠ 0) (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hMQ : ⨍⁻ x in dyadicCube q₀.1 q₀.2, ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ
      ∂volume ≤ M) (N : ℕ) :
    ∃ C : Set (ℤ × (ι → ℤ)), (∀ q ∈ C, dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2) ∧
      ∑' q : C, volume (dyadicCube q.1.1 q.1.2) ≤ 2⁻¹ * volume (dyadicCube q₀.1 q₀.2) ∧
      volume {x ∈ dyadicCube q₀.1 q₀.2 | 2 ^ (Fintype.card ι + 1) * ↑(N + 1) * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ} ≤
        ∑' q : C, volume {x ∈ dyadicCube q.1.1 q.1.2 |
          2 ^ (Fintype.card ι + 1) * N * (M : ℝ≥0∞) <
            ‖f x - ⨍ y in dyadicCube q.1.1 q.1.2, f y ∂volume‖ₑ} := by
  set Q := dyadicCube q₀.1 q₀.2
  set c := ⨍ y in Q, f y ∂volume
  set n := Fintype.card ι
  have hQ : MeasurableSet Q := measurableSet_dyadicCube q₀.1 q₀.2
  -- The Calderón–Zygmund cubes of `g = 1_Q ‖f - c‖` at height `t = 2M`.
  set g : (ι → ℝ) → ℝ≥0∞ := Q.indicator fun x => ‖f x - c‖ₑ
  set t : ℝ≥0∞ := 2 * M
  set C := calderonZygmundCubes g t
  have ht0 : t ≠ 0 := mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.2 hM0)
  have hgm : AEMeasurable g :=
    (aemeasurable_indicator_iff hQ).2 (hf.1.sub aestronglyMeasurable_const).enorm
  have hg : ∫⁻ x, g x ≤ M * volume Q := by
    rw [lintegral_indicator hQ, ← measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _),
      mul_comm]
    gcongr
  have hg' : ∫⁻ x, g x ≠ ∞ :=
    (hg.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (volume_dyadicCube_ne_top _ _).lt_top)).ne
  -- The cubes lie in `Q`.
  have hsub : ∀ q ∈ C, dyadicCube q.1 q.2 ⊆ Q := fun q hq =>
    dyadicCube_subset_of_mem_calderonZygmundCubes_indicator
      (hMQ.trans (le_mul_of_one_le_left' one_le_two)) hq
  -- They cover at most half of `Q`.
  have hvol : volume (⋃ q ∈ C, dyadicCube q.1 q.2) ≤ 2⁻¹ * volume Q := by
    set V := volume (⋃ q ∈ C, dyadicCube q.1 q.2)
    have h := (mul_volume_biUnion_calderonZygmundCubes_le (g := g) (t := t)).trans
      ((setLIntegral_le_lintegral _ _).trans hg)
    rw [show t * V = M * (2 * V) by ring] at h
    have h2 := (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.2 hM0) ENNReal.coe_ne_top).1 h
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (.inl two_ne_zero)
      (.inl ENNReal.ofNat_ne_top), mul_comm]
    exact h2
  -- On each cube, the average of `f` is within `2ⁿ⁺¹ M` of `c`.
  have havg : ∀ q ∈ C, ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume - c‖ₑ ≤ 2 ^ (n + 1) * M := by
    intro q hq
    have hfq : IntegrableOn f (dyadicCube q.1 q.2) := hf.mono_set (hsub q hq)
    rw [← setAverage_const (volume_dyadicCube_pos q.1 q.2).ne' (volume_dyadicCube_ne_top _ _) c,
      ← setAverage_sub hfq (integrableOn_const (volume_dyadicCube_ne_top _ _))]
    refine (enorm_setAverage_le_setLAverage _ _ _).trans ?_
    refine le_of_eq_of_le (setLAverage_congr_fun (measurableSet_dyadicCube _ _) ?_)
      ((setLAverage_le_of_mem_calderonZygmundCubes hq).trans_eq ?_)
    · exact fun x hx => by simp only [g, indicator_of_mem (hsub q hq hx), Pi.sub_apply]
    · rw [pow_succ, mul_assoc]
  -- Off the cubes, `‖f - c‖ ≤ 2M` almost everywhere.
  have hae := ae_le_of_forall_notMem_calderonZygmundCubes hgm hg' ht0
  -- Hence, up to a null set, the superlevel set at `2ⁿ⁺¹ (N + 1) M` lies in the union over the
  -- cubes `Q'` of the superlevel sets at `2ⁿ⁺¹ N M` of `‖f - f_{Q'}‖` on `Q'`.
  refine ⟨C, hsub, ?_, ?_⟩
  · rw [← measure_biUnion C.to_countable pairwiseDisjoint_calderonZygmundCubes
      fun q _ => measurableSet_dyadicCube _ _]
    exact hvol
  calc volume {x ∈ Q | 2 ^ (n + 1) * ↑(N + 1) * (M : ℝ≥0∞) < ‖f x - c‖ₑ}
      ≤ volume (⋃ q ∈ C, {x ∈ dyadicCube q.1 q.2 | 2 ^ (n + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ}) := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with x hx hxS
        simp only [mem_iUnion, mem_ofPred_eq]
        by_cases hmem : ∃ q ∈ C, x ∈ dyadicCube q.1 q.2
        · obtain ⟨q, hq, hxq⟩ := hmem
          refine ⟨q, hq, hxq, lt_of_not_ge fun hle => hxS.2.not_ge ?_⟩
          calc ‖f x - c‖ₑ
              ≤ ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ +
                  ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume - c‖ₑ := by
                simpa only [edist_eq_enorm_sub] using edist_triangle (f x) _ c
            _ ≤ 2 ^ (n + 1) * N * M + 2 ^ (n + 1) * M := add_le_add hle (havg q hq)
            _ = 2 ^ (n + 1) * ↑(N + 1) * M := by push_cast; ring
        · push Not at hmem
          have hle := hx hmem
          rw [show g x = ‖f x - c‖ₑ from indicator_of_mem hxS.1 _] at hle
          refine absurd hxS.2 (not_lt.2 (hle.trans ?_))
          calc t = 2 ^ 1 * 1 * M := by ring
            _ ≤ 2 ^ (n + 1) * ↑(N + 1) * M := by
              gcongr
              · exact one_le_two
              · omega
              · exact_mod_cast Nat.succ_pos N
    _ ≤ ∑' q : C, volume {x ∈ dyadicCube q.1.1 q.1.2 | 2 ^ (n + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q.1.1 q.1.2, f y ∂volume‖ₑ} :=
        measure_biUnion_le _ C.to_countable _

/-- **The John–Nirenberg inequality, dyadic form.** Let `f` be integrable on the dyadic cube
`Q₀ ⊆ ℝⁿ`, with mean oscillation `⨍_Q ‖f - f_Q‖ ≤ M` on every dyadic cube `Q ⊆ Q₀`.
Then the set of points of `Q₀` where `‖f - f_{Q₀}‖` exceeds `2ⁿ⁺¹ N M` has measure at most
`2⁻ᴺ |Q₀|`. -/
theorem volume_lt_enorm_sub_setAverage_le_inv_two_pow [CompleteSpace E]
    (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hM : ∀ q : ℤ × (ι → ℤ), dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 →
      ⨍⁻ x in dyadicCube q.1 q.2, ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ ∂volume ≤ M)
    (N : ℕ) :
    volume {x ∈ dyadicCube q₀.1 q₀.2 |
        2 ^ (Fintype.card ι + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ} ≤
      2⁻¹ ^ N * volume (dyadicCube q₀.1 q₀.2) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero every function is constant, so its mean oscillation vanishes.
    have hfconst : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [hfconst]
    simp only [setAverage_const (volume_dyadicCube_pos q₀.1 q₀.2).ne'
      (volume_dyadicCube_ne_top q₀.1 q₀.2), sub_self, enorm_zero, not_lt_zero, and_false,
      ofPred_false, measure_empty, zero_le]
  rcases eq_or_ne M 0 with rfl | hM0
  · -- For `M = 0`, `f` equals its average almost everywhere on `Q₀`.
    have hm : AEMeasurable (fun x => ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ)
        (volume.restrict (dyadicCube q₀.1 q₀.2)) :=
      (hf.1.sub aestronglyMeasurable_const).enorm
    have h := hM q₀ le_rfl
    rw [ENNReal.coe_zero, nonpos_iff_eq_zero, setLAverage_eq, ENNReal.div_eq_zero_iff,
      or_iff_left (volume_dyadicCube_ne_top _ _), lintegral_eq_zero_iff' hm, Filter.EventuallyEq,
      ae_restrict_iff' (measurableSet_dyadicCube q₀.1 q₀.2)] at h
    refine le_trans (le_of_eq (measure_eq_zero_iff_ae_notMem.2 ?_)) zero_le
    exact h.mono fun x hx hxS => hxS.2.ne' (by simpa using hx hxS.1)
  induction N generalizing q₀ with
  | zero =>
    rw [pow_zero, one_mul]
    exact measure_mono (sep_subset _ _)
  | succ N ih =>
    -- One Calderón–Zygmund step, then the induction hypothesis on each of its cubes.
    obtain ⟨C, hsub, hC, hcover⟩ :=
      exists_volume_lt_enorm_sub_setAverage_le_tsum hM0 hf (hM q₀ le_rfl) N
    calc _ ≤ _ := hcover
      _ ≤ ∑' q : C, 2⁻¹ ^ N * volume (dyadicCube q.1.1 q.1.2) :=
        ENNReal.tsum_le_tsum fun q =>
          ih (hf.mono_set (hsub q q.2)) fun q' hq' => hM q' (hq'.trans (hsub q q.2))
      _ = 2⁻¹ ^ N * ∑' q : C, volume (dyadicCube q.1.1 q.1.2) := ENNReal.tsum_mul_left
      _ ≤ 2⁻¹ ^ N * (2⁻¹ * volume (dyadicCube q₀.1 q₀.2)) := by gcongr
      _ = 2⁻¹ ^ (N + 1) * volume (dyadicCube q₀.1 q₀.2) := by rw [pow_succ, mul_assoc]


end Oscillation


/-- The one-dimensional cube is the actual real half-open interval under evaluation. -/
theorem dyadicCube_fin_one (k : ℤ) (m : Fin 1 → ℤ) :
    dyadicCube k m = (fun x : Fin 1 → ℝ => x 0) ⁻¹'
      Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k) := by
  ext x
  simp only [dyadicCube_eq_pi, mem_univ_pi, mem_Ico, mem_preimage, Fin.forall_fin_one]

theorem setIntegral_dyadicCube_fin_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (k : ℤ) (m : Fin 1 → ℤ) :
    (∫ x in dyadicCube k m, F (x 0)) =
      ∫ t in Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k), F t := by
  rw [dyadicCube_fin_one]
  exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding F _

theorem setLIntegral_dyadicCube_fin_one (F : ℝ → ℝ≥0∞) (k : ℤ) (m : Fin 1 → ℤ) :
    (∫⁻ x in dyadicCube k m, F (x 0)) =
      ∫⁻ t in Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k), F t := by
  rw [dyadicCube_fin_one]
  exact ((volume_preserving_funUnique (Fin 1) ℝ).restrict_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding _).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding F


theorem setAverage_dyadicCube_fin_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (k : ℤ) (m : Fin 1 → ℤ) :
    (⨍ x in dyadicCube k m, F (x 0)) =
      ⨍ t in Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k), F t := by
  have hV : volume (dyadicCube k m) =
      volume (Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k)) := by
    rw [volume_dyadicCube,Real.volume_Ico,Fintype.card_fin,pow_one]
    congr 1
    ring
  simp only [setAverage_eq,measureReal_def]
  rw [setIntegral_dyadicCube_fin_one,hV]

theorem setLAverage_dyadicCube_fin_one (F : ℝ → ℝ≥0∞) (k : ℤ) (m : Fin 1 → ℤ) :
    (⨍⁻ x in dyadicCube k m, F (x 0) ∂volume) =
      ⨍⁻ t in Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k), F t ∂volume := by
  have hV : volume (dyadicCube k m) =
      volume (Ico ((m 0 : ℝ)*2^k) ((m 0+1)*2^k)) := by
    rw [volume_dyadicCube,Real.volume_Ico,Fintype.card_fin,pow_one]
    congr 1
    ring
  simp only [setLAverage_eq]
  rw [setLIntegral_dyadicCube_fin_one,hV]

theorem setIntegral_Ico_add_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a l r : ℝ) (F : ℝ → E) :
    (∫ t in Ico l r, F (a+t)) = ∫ t in Ico (a+l) (a+r), F t := by
  have hs : (fun t : ℝ => a+t) ⁻¹' Ico (a+l) (a+r) = Ico l r := by
    ext t
    simp only [mem_preimage,mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [← hs]
  exact (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F _

theorem setLIntegral_Ico_add_left (a l r : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ico l r, F (a+t)) = ∫⁻ t in Ico (a+l) (a+r), F t := by
  have hs : (fun t : ℝ => a+t) ⁻¹' Ico (a+l) (a+r) = Ico l r := by
    ext t
    simp only [mem_preimage,mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [← hs]
  exact ((measurePreserving_add_left volume a).restrict_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding _).lintegral_comp_emb
      (MeasurableEquiv.addLeft a).measurableEmbedding F

end TTO.DyadicAnalysis
