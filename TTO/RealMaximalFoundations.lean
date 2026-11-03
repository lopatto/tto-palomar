/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors; adapted by Patrick Lopatto
-/
module
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The real centered Hardy–Littlewood maximal function. The elementary maximal API,
Vitali covering argument and lower-semicontinuity proof are adapted from
TauCetiProject/TauCeti, commit d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad,
TauCeti/MeasureTheory/Integral/MaximalFunction.lean, Apache-2.0.
Tau Ceti is a source reference, not a project dependency. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology
namespace TTO.RealAnalysis

/-- Actual extended nonnegative averages over every positive-radius real ball. -/
def realMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ r > 0, ⨍⁻ y in ball x r, f y ∂volume

theorem average_le_realMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) {r : ℝ} (hr : 0<r) :
    (⨍⁻ y in ball x r, f y ∂volume)≤realMaximal f x := by
  unfold realMaximal
  exact le_iSup₂ (f:=fun r (_ : 0<r) => ⨍⁻ y in ball x r,f y ∂volume) r hr

theorem realMaximal_le {f : ℝ → ℝ≥0∞} {x : ℝ} {a : ℝ≥0∞}
    (h : ∀ r>0,(⨍⁻ y in ball x r, f y ∂volume)≤a) : realMaximal f x≤a := iSup₂_le h

theorem lt_realMaximal_iff {f : ℝ → ℝ≥0∞} {x : ℝ} {t : ℝ≥0∞} :
    t<realMaximal f x ↔ ∃ r>0,t<(⨍⁻ y in ball x r, f y ∂volume) := by
  simp only [realMaximal,lt_iSup_iff,exists_prop]

theorem realMaximal_mono_ae {f g : ℝ → ℝ≥0∞} (h : f≤ᵐ[volume]g) (x : ℝ) :
    realMaximal f x≤realMaximal g x :=
  realMaximal_le (fun _r hr => (setLAverage_mono_ae _ h).trans (average_le_realMaximal g x hr))

theorem realMaximal_congr_ae {f g : ℝ → ℝ≥0∞} (h : f=ᵐ[volume]g) :
    realMaximal f=realMaximal g := by
  funext x
  exact le_antisymm (realMaximal_mono_ae (h.mono (fun _ h => h.le)) x)
    (realMaximal_mono_ae (h.mono (fun _ h => h.ge)) x)

theorem realMaximal_const (c : ℝ≥0∞) (x : ℝ) : realMaximal (fun _ => c) x=c := by
  apply le_antisymm
  · apply realMaximal_le
    intro r hr
    exact (setLAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne c).le
  · have h := average_le_realMaximal (fun _ => c) x (r:=1) (by norm_num)
    rw [setLAverage_const (measure_ball_pos volume x one_pos).ne' measure_ball_lt_top.ne c] at h
    exact h

theorem realMaximal_add_le {f g : ℝ → ℝ≥0∞} (hf : AEMeasurable f) (x : ℝ) :
    realMaximal (f+g) x≤realMaximal f x+realMaximal g x := by
  apply realMaximal_le
  intro r hr
  rw [setLAverage_eq]
  change (∫⁻ y in ball x r,f y+g y)/volume (ball x r)≤realMaximal f x+realMaximal g x
  rw [lintegral_add_left' hf.restrict,ENNReal.add_div]
  simpa only [setLAverage_eq] using add_le_add (average_le_realMaximal f x hr) (average_le_realMaximal g x hr)

private theorem real_ball_volume (x r : ℝ) (hr : 0<r) :
    volume (ball x r)=ENNReal.ofReal r*volume (ball (0 : ℝ) 1) := by
  simp only [Real.volume_ball,mul_one]
  rw [← ENNReal.ofReal_mul hr.le]
  congr 1
  ring

private theorem real_enlarged_ball_volume (x r : ℝ) :
    volume (closedBall x (4*r))=4*volume (ball x r) := by
  rw [Real.volume_closedBall,Real.volume_ball]
  have h4 : (4 : ℝ≥0∞)=ENNReal.ofReal (4 : ℝ) := by norm_num
  rw [h4,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤4)]
  congr 1
  ring

/-- The genuine Vitali weak estimate, with a uniform bound on selected radii. -/
theorem real_vitali_weak_bound {S : Set ℝ} {R : ℝ} {f : ℝ → ℝ≥0∞} {t : ℝ≥0∞}
    (hS : ∀ x∈S,∃ r∈Ioc 0 R,t*volume (ball x r)≤∫⁻ y in ball x r,f y) :
    t*volume S≤4*∫⁻ y,f y := by
  choose! r hr hle using hS
  obtain ⟨u,hu,hdisj,hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior (fun x hx =>
      ⟨x,ball_subset_interior_closedBall (mem_ball_self (hr x (hu hx)).1)⟩)
  have : Countable u := hcount.to_subtype
  have hsub : S⊆⋃ b∈u,closedBall b (4*r b) := by
    intro x hx
    obtain ⟨b,hb,hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_closedBall_self (hr x hx).1.le))
  have hdisj' : Pairwise (Function.onFun Disjoint (fun b : u => ball (b : ℝ) (r b))) :=
    fun b b' hbb' => (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')).mono
      ball_subset_closedBall ball_subset_closedBall
  calc
    t*volume S≤t*∑' b : u,volume (closedBall (b : ℝ) (4*r b)) := by
      gcongr
      exact (measure_mono hsub).trans (measure_biUnion_le volume hcount _)
    _ = ∑' b : u,t*volume (closedBall (b : ℝ) (4*r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u,4*∫⁻ y in ball (b : ℝ) (r b),f y := by
      apply ENNReal.tsum_le_tsum
      intro b
      rw [real_enlarged_ball_volume,mul_left_comm]
      gcongr
      exact hle b (hu b.2)
    _ = 4*∑' b : u,∫⁻ y in ball (b : ℝ) (r b),f y := ENNReal.tsum_mul_left
    _ = 4*∫⁻ y in ⋃ b : u,ball (b : ℝ) (r b),f y := by
      rw [lintegral_iUnion (fun b => measurableSet_ball) hdisj']
    _ ≤ 4*∫⁻ y,f y := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

theorem lowerSemicontinuous_realMaximal (f : ℝ → ℝ≥0∞) : LowerSemicontinuous (realMaximal f) := by
  intro x t ht
  obtain ⟨r,hr,hlt⟩ := lt_realMaximal_iff.mp ht
  have hc0 : volume (ball (0 : ℝ) 1)≠0 := (measure_ball_pos volume 0 one_pos).ne'
  have hct : volume (ball (0 : ℝ) 1)≠∞ := measure_ball_lt_top.ne
  have hpos : ∀ s : ℝ,0<s → ENNReal.ofReal s*volume (ball (0 : ℝ) 1)≠0 :=
    fun s hs => mul_ne_zero (ENNReal.ofReal_pos.mpr hs).ne' hc0
  have hne : ∀ s : ℝ,ENNReal.ofReal s*volume (ball (0 : ℝ) 1)≠∞ :=
    fun _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  rw [setLAverage_eq] at hlt
  have hmul : t*(ENNReal.ofReal r*volume (ball (0 : ℝ) 1))<∫⁻ y in ball x r,f y := by
    rw [← real_ball_volume x r hr]
    exact ENNReal.mul_lt_of_lt_div hlt
  have hcont : Tendsto (fun s : ℝ => t*(ENNReal.ofReal s*volume (ball (0 : ℝ) 1))) (𝓝 r)
      (𝓝 (t*(ENNReal.ofReal r*volume (ball (0 : ℝ) 1)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto r) (.inr hct)) (.inl (hpos r hr))
  have hev : ∀ᶠ s : ℝ in 𝓝[>] r,t*(ENNReal.ofReal s*volume (ball (0 : ℝ) 1))<∫⁻ y in ball x r,f y :=
    (hcont.mono_left nhdsWithin_le_nhds).eventually_lt_const hmul
  obtain ⟨s,hs,hrs⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrs' : r<s := hrs
  have hsp : 0<s := hr.trans hrs'
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrs')] with y hy
  refine lt_of_lt_of_le ?_ (average_le_realMaximal f y hsp)
  rw [setLAverage_eq,real_ball_volume y s hsp,
    ENNReal.lt_div_iff_mul_lt (.inl (hpos s hsp)) (.inl (hne s))]
  refine hs.trans_le (lintegral_mono_set (ball_subset_ball' ?_))
  rw [dist_comm]
  linarith [mem_ball.mp hy]

@[fun_prop] theorem measurable_realMaximal (f : ℝ → ℝ≥0∞) : Measurable (realMaximal f) :=
  (lowerSemicontinuous_realMaximal f).measurable

/-- Weak type (1,1), without an added integrability hypothesis. Infinite right side is allowed. -/
theorem realMaximal_weak_one (f : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    t*volume {x | t<realMaximal f x}≤4*∫⁻ x,f x := by
  rcases eq_or_ne (∫⁻ x,f x) ∞ with hI|hI
  · simp [hI]
  rcases eq_or_ne t 0 with rfl|ht0
  · simp
  rcases eq_or_ne t ∞ with rfl|httop
  · simp
  have hc0 : volume (ball (0 : ℝ) 1)≠0 := (measure_ball_pos volume 0 one_pos).ne'
  have hct : volume (ball (0 : ℝ) 1)≠∞ := measure_ball_lt_top.ne
  have htc0 : t*volume (ball (0 : ℝ) 1)≠0 := mul_ne_zero ht0 hc0
  have htct : t*volume (ball (0 : ℝ) 1)≠∞ := ENNReal.mul_ne_top httop hct
  have hex : ∀ x∈{x | t<realMaximal f x},∃ r : ℝ,0<r ∧
      t*volume (ball x r)<∫⁻ y in ball x r,f y := by
    intro x hx
    obtain ⟨r,hr,hlt⟩ := lt_realMaximal_iff.mp hx
    rw [setLAverage_eq] at hlt
    exact ⟨r,hr,ENNReal.mul_lt_of_lt_div hlt⟩
  choose! r hr0 hrlt using hex
  let R := max 1 ((∫⁻ x,f x)/(t*volume (ball (0 : ℝ) 1))).toReal
  have hR : ∀ x∈{x | t<realMaximal f x},r x∈Ioc 0 R := by
    intro x hx
    refine ⟨hr0 x hx,?_⟩
    have hlt : ENNReal.ofReal (r x)*(t*volume (ball (0 : ℝ) 1))<∫⁻ y,f y := by
      rw [mul_left_comm,← real_ball_volume x (r x) (hr0 x hx)]
      exact (hrlt x hx).trans_le (setLIntegral_le_lintegral _ _)
    rw [← ENNReal.lt_div_iff_mul_lt (.inl htc0) (.inl htct),
      ENNReal.ofReal_lt_iff_lt_toReal (hr0 x hx).le (ENNReal.div_ne_top hI htc0)] at hlt
    exact hlt.le.trans (le_max_right _ _)
  exact real_vitali_weak_bound (fun x hx => ⟨r x,hR x hx,(hrlt x hx).le⟩)


/-- Only the high tail can create a maximal value above t. No global L¹ premise is used. -/
theorem realMaximal_tail_weak {f : ℝ → ℝ≥0∞} (hf : Measurable f) (t : ℝ) (_ht : 0<t) :
    ENNReal.ofReal t*volume {x | ENNReal.ofReal t<realMaximal f x}≤
      8*∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x := by
  let S := {x | ENNReal.ofReal (t/2)<f x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf
  let hi := S.indicator f
  let lo := Sᶜ.indicator f
  have hsum : f=hi+lo := by
    funext x
    by_cases hx : x∈S <;> simp [hi,lo,hx]
  have hlow : ∀ x,realMaximal lo x≤ENNReal.ofReal (t/2) := by
    intro x
    have hpoint : lo≤fun _ => ENNReal.ofReal (t/2) := by
      intro y
      by_cases hy : y∈S
      · simp [lo,hy]
      · dsimp only [lo]
        rw [Set.indicator_of_mem (show y∈Sᶜ from hy)]
        exact le_of_not_gt hy
    exact (realMaximal_mono_ae (Eventually.of_forall hpoint) x).trans_eq (realMaximal_const _ x)
  have htHalf : ENNReal.ofReal t=2*ENNReal.ofReal (t/2) := by
    rw [← ENNReal.ofReal_ofNat 2,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
    congr 1
    ring
  have hsub : {x | ENNReal.ofReal t<realMaximal f x}⊆
      {x | ENNReal.ofReal (t/2)<realMaximal hi x} := by
    intro x hx
    by_contra hnot
    have hhi : realMaximal hi x≤ENNReal.ofReal (t/2) := le_of_not_gt hnot
    have hm : realMaximal f x≤ENNReal.ofReal t := by
      rw [hsum]
      exact (realMaximal_add_le (hf.indicator hS).aemeasurable x).trans
        ((add_le_add hhi (hlow x)).trans_eq (by rw [htHalf,two_mul]))
    exact (not_lt_of_ge hm) hx
  calc
    _ ≤ ENNReal.ofReal t*volume {x | ENNReal.ofReal (t/2)<realMaximal hi x} := by gcongr
    _ = 2*(ENNReal.ofReal (t/2)*volume {x | ENNReal.ofReal (t/2)<realMaximal hi x}) := by rw [htHalf,mul_assoc]
    _ ≤ 2*(4*∫⁻ x,hi x) := mul_le_mul_right (realMaximal_weak_one hi (ENNReal.ofReal (t/2))) 2
    _ = _ := by dsimp only [hi]; rw [lintegral_indicator hS]; ring


/-- The sole scalar height integral needed for p=2. This includes a=0 and a=∞. -/
theorem lintegral_half_height_indicator (a : ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ),{t : ℝ | ENNReal.ofReal (t/2)<a}.indicator (fun _ => a) t)=2*a^2 := by
  by_cases ha0 : a=0
  · subst a
    simp
  by_cases hat : a=∞
  · subst a
    simp
  have hval : (fun t : ℝ => {t | ENNReal.ofReal (t/2)<a}.indicator (fun _ => a) t)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (Iio (2*a.toReal)).indicator (fun _ => a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := ht
    have he : ENNReal.ofReal (t/2)<a ↔ t<2*a.toReal := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith : 0≤t/2) hat]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,Set.mem_Iio,he]
  rw [lintegral_congr_ae hval,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (2*a.toReal)∩Ioi (0 : ℝ)=Ioo (0 : ℝ) (2*a.toReal) := by ext; simp [and_comm]
  rw [hset,lintegral_const]
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Real.volume_Ioo,sub_zero]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat,ENNReal.ofReal_toReal hat]
  ring


/-- A p=2 layer-cake estimate, specialized to the high-tail bound above. -/
theorem square_lintegral_of_tail_bound {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (u : ℝ → ℝ) (hu : Measurable u) (hu0 : ∀ x,0≤u x)
    (hweak : ∀ t : ℝ,0<t → ENNReal.ofReal t*volume {x | t<u x}≤
      8*∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x) :
    (∫⁻ x,ENNReal.ofReal (u x)^2)≤32*∫⁻ x,(f x)^2 := by
  have hLC : (∫⁻ x,ENNReal.ofReal (u x)^2)=
      ∫⁻ t in Ioi (0 : ℝ),volume {x | t<u x}*ENNReal.ofReal (2*t) := by
    have hbase := lintegral_comp_eq_lintegral_meas_lt_mul (volume : Measure ℝ)
      (Eventually.of_forall hu0) hu.aemeasurable
      (fun t _ => (continuous_const.mul continuous_id : Continuous (fun s : ℝ => (2 : ℝ)*s)).intervalIntegrable 0 t)
      (show ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),0≤(2 : ℝ)*t from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0<t := ht
        positivity)
    simp only [Pi.mul_apply] at hbase
    rw [← hbase]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_pow (hu0 x)]
    congr 1
    rw [intervalIntegral.integral_const_mul,integral_id]
    ring
  let S : Set (ℝ × ℝ) := {q | ENNReal.ofReal (q.1/2)<f q.2}
  let G : ℝ × ℝ → ℝ≥0∞ := S.indicator (fun q => f q.2)
  have hS : MeasurableSet S :=
    measurableSet_lt ((measurable_fst.div_const 2).ennreal_ofReal) (hf.comp measurable_snd)
  have hG : Measurable G := (hf.comp measurable_snd).indicator hS
  have hslice (t : ℝ) : (∫⁻ x,G (t,x))=∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const hf)]
    rfl
  have hTonelli : (∫⁻ t in Ioi (0 : ℝ),∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x)=
      2*∫⁻ x,(f x)^2 := by
    simp_rw [← hslice]
    have hswap : (∫⁻ t in Ioi (0 : ℝ),∫⁻ x,G (t,x))=
        ∫⁻ x,∫⁻ t in Ioi (0 : ℝ),G (t,x) :=
      lintegral_lintegral_swap (μ:=volume.restrict (Ioi (0 : ℝ))) (ν:=volume)
        (f:=fun t x => G (t,x)) hG.aemeasurable
    rw [hswap]
    calc
      _ = ∫⁻ x,(2 : ℝ≥0∞)*(f x)^2 := by
        apply lintegral_congr
        intro x
        change (∫⁻ t in Ioi (0 : ℝ),{t : ℝ | ENNReal.ofReal (t/2)<f x}.indicator (fun _ => f x) t)=_
        exact lintegral_half_height_indicator (f x)
      _ = _ := lintegral_const_mul' _ _ (by norm_num)
  rw [hLC]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),(16 : ℝ≥0∞)*(∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0<t := ht
      calc
        _ = 2*(ENNReal.ofReal t*volume {x | t<u x}) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat]
          ring
        _ ≤ 2*(8*∫⁻ x in {x | ENNReal.ofReal (t/2)<f x},f x) := mul_le_mul_right (hweak t ht0) 2
        _ = _ := by ring
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num),hTonelli]
      ring


/-- Strong type (2,2), first for a measurable extended density; no L¹ hypothesis. -/
theorem realMaximal_strong_two_measurable {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x,(realMaximal f x)^2)≤32*∫⁻ x,(f x)^2 := by
  let u : ℕ → ℝ → ℝ := fun n x => (min (realMaximal f x) (n : ℝ≥0∞)).toReal
  have hcap (n : ℕ) (x : ℝ) : min (realMaximal f x) (n : ℝ≥0∞)≠∞ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hu (n : ℕ) : Measurable (u n) :=
    ((measurable_realMaximal f).min measurable_const).ennreal_toReal
  have hu0 (n : ℕ) (x : ℝ) : 0≤u n x := ENNReal.toReal_nonneg
  have hFinite (n : ℕ) : (∫⁻ x,ENNReal.ofReal (u n x)^2)≤32*∫⁻ x,(f x)^2 := by
    apply square_lintegral_of_tail_bound hf (u n) (hu n) (hu0 n)
    intro t ht
    have hsub : {x | t<u n x}⊆{x | ENNReal.ofReal t<realMaximal f x} := by
      intro x hx
      have hlt : ENNReal.ofReal t<min (realMaximal f x) (n : ℝ≥0∞) :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hcap n x)).mpr hx
      exact hlt.trans_le (min_le_left _ _)
    exact (mul_le_mul_right (measure_mono hsub) (ENNReal.ofReal t)).trans (realMaximal_tail_weak hf t ht)
  have hLim (x : ℝ) : Tendsto (fun n => ENNReal.ofReal (u n x)^2) atTop
      (𝓝 ((realMaximal f x)^2)) := by
    have he : (fun n => ENNReal.ofReal (u n x))= (fun n : ℕ => min (realMaximal f x) (n : ℝ≥0∞)) := by
      funext n
      exact ENNReal.ofReal_toReal (hcap n x)
    simp_rw [← Pi.pow_apply]
    change Tendsto ((fun n => ENNReal.ofReal (u n x))^2) atTop (𝓝 ((realMaximal f x)^2))
    rw [he]
    have hm : Tendsto (fun n : ℕ => min (realMaximal f x) (n : ℝ≥0∞)) atTop (𝓝 (realMaximal f x)) := by
      simpa only [min_top_right] using
        (tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top)
    exact ENNReal.Tendsto.pow hm
  have hMeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (u n x)^2) :=
    ((hu n).ennreal_ofReal.pow_const 2).aemeasurable
  have hFatou := lintegral_liminf_le' (u:=(atTop : Filter ℕ)) hMeas
  have hEq : (fun x => liminf (fun n => ENNReal.ofReal (u n x)^2) atTop)=
      (fun x => (realMaximal f x)^2) := by
    funext x
    exact (hLim x).liminf_eq
  rw [hEq] at hFatou
  exact hFatou.trans (liminf_le_of_frequently_le' (Eventually.of_forall hFinite).frequently)

/-- The actual extended strong L² estimate, with universal squared constant32. -/
theorem realMaximal_strong_two {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f) :
    (∫⁻ x,(realMaximal f x)^2)≤32*∫⁻ x,(f x)^2 := by
  have hM := realMaximal_congr_ae hf.ae_eq_mk
  have hpow : (fun x => (f x)^2)=ᵐ[volume](fun x => (hf.mk f x)^2) :=
    hf.ae_eq_mk.mono (fun _ h => congrArg (fun a : ℝ≥0∞ => a^2) h)
  rw [hM,lintegral_congr_ae hpow]
  exact realMaximal_strong_two_measurable hf.measurable_mk


/-- The same actual maximal estimate for the extended modulus of complex data. -/
theorem realMaximal_complex_two (f : ℝ → ℂ) (hf : AEStronglyMeasurable f) :
    (∫⁻ x,(realMaximal (fun y => ‖f y‖ₑ) x)^2)≤32*∫⁻ x,‖f x‖ₑ^2 :=
  realMaximal_strong_two hf.enorm

/-- Genuine L² complex data have an L² maximal function, hence finite maximal values a.e. -/
theorem memLp_realMaximal_complex_two (f : ℝ → ℂ) (hf : MemLp f 2) :
    MemLp (realMaximal (fun y => ‖f y‖ₑ)) 2 := by
  have hI : (∫⁻ x,‖f x‖ₑ^2)<∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞) hf.aestronglyMeasurable).mp hf
    simpa using h
  have hM : (∫⁻ x,(realMaximal (fun y => ‖f y‖ₑ) x)^2)<∞ :=
    (realMaximal_complex_two f hf.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top (by norm_num) hI)
  have hmeas : AEStronglyMeasurable (realMaximal (fun y => ‖f y‖ₑ)) (volume : Measure ℝ) :=
    (measurable_realMaximal (fun y => ‖f y‖ₑ)).aestronglyMeasurable
  change eLpNorm (realMaximal (fun y => ‖f y‖ₑ)) 2 volume<∞
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞) hmeas).mpr
  simpa using hM

theorem ae_realMaximal_complex_lt_top (f : ℝ → ℂ) (hf : MemLp f 2) :
    ∀ᵐ x ∂volume,realMaximal (fun y => ‖f y‖ₑ) x<∞ := by
  have hM := memLp_realMaximal_complex_two f hf
  have hI : (∫⁻ x,(realMaximal (fun y => ‖f y‖ₑ) x)^2)<∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞) hM
    simpa using h
  have hA := ae_lt_top ((measurable_realMaximal (fun y => ‖f y‖ₑ)).pow_const 2) hI.ne
  filter_upwards [hA] with x hx
  by_contra hnot
  have he : realMaximal (fun y => ‖f y‖ₑ) x=∞ := not_lt_top_iff.mp hnot
  simp only [he,ENNReal.top_pow (by norm_num : (2 : ℕ)≠0),lt_self_iff_false] at hx

end TTO.RealAnalysis
