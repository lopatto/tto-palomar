/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HardyMaximalFoundations
public import TTO.DyadicCubeFoundations

/-! A polar dyadic-box Carleson embedding for the actual Hardy boundary space. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction TTO.DyadicAnalysis

/-- The literal polar parametrization, without choosing a complex argument. -/
def polarMap (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * fourier (T:=1) 1 (p.2 : Boundary)

theorem continuous_polarMap : Continuous polarMap := by
  unfold polarMap
  exact (Complex.continuous_ofReal.comp continuous_fst).mul
    ((fourier (T:=1) 1).continuous.comp ((show Continuous (fun x : ℝ => (x : Boundary)) from continuous_quot_mk).comp continuous_snd))

/-- The actual Hardy function on the disk, honestly extended by zero outside it. -/
def diskHardyValue (g : Hardy) : ℂ → ℂ :=
  Function.extend (Subtype.val : Disk → ℂ) (fun w => analyticValue g.val w.val) (fun _ => 0)

theorem diskHardyValue_on (g : Hardy) (w : Disk) :
    diskHardyValue g w.val = analyticValue g.val w.val :=
  Subtype.val_injective.extend_apply _ _ w

theorem measurable_diskHardyValue (g : Hardy) : Measurable (diskHardyValue g) := by
  apply StronglyMeasurable.measurable
  apply (MeasurableEmbedding.subtype_coe
    (isOpen_lt continuous_norm continuous_const).measurableSet).stronglyMeasurable_extend
  · apply Continuous.stronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (analyticOnNhd_analyticValue g.val w.val w.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  · exact stronglyMeasurable_const

def polarHardyValue (g : Hardy) (p : ℝ × ℝ) : ℂ := diskHardyValue g (polarMap p)

theorem measurable_polarHardyValue (g : Hardy) : Measurable (polarHardyValue g) :=
  (measurable_diskHardyValue g).comp continuous_polarMap.measurable

/-- The polar measure is supported on the actual half-open unit radial rectangle. -/
def PolarSupport (ν : Measure (ℝ × ℝ)) : Prop :=
  ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 < 1

/-- A literal dyadic polar box of angular width and radial depth 2^k. -/
def polarBox (k m : ℤ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Ico ((m : ℝ)*2^k) (((m : ℝ)+1)*2^k) ∧ 1-p.1 ≤ 2^k}

theorem measurableSet_polarBox (k m : ℤ) : MeasurableSet (polarBox k m) := by
  exact (measurable_snd measurableSet_Ico).inter
    (measurableSet_le (measurable_const.sub measurable_fst) measurable_const)

/-- Dyadic box control at all widths at most one. This is an ordinary hypothesis on a measure. -/
def PolarBoxBound (ν : Measure (ℝ × ℝ)) (A : ℝ) : Prop :=
  ∀ k : ℤ, k ≤ 0 → ∀ m : ℤ, ν (polarBox k m) ≤ ENNReal.ofReal (A*2^k)

theorem polar_measure_univ_le {ν : Measure (ℝ × ℝ)} {A : ℝ}
    (hs : PolarSupport ν) (hb : PolarBoxBound ν A) : ν univ ≤ ENNReal.ofReal A := by
  have hmem : ∀ᵐ p ∂ν, p ∈ polarBox 0 0 := by
    filter_upwards [hs] with p hp
    simp only [polarBox,zpow_zero,Int.cast_zero,zero_mul,zero_add,one_mul,mem_ofPred_eq,Set.mem_Ico]
    exact ⟨⟨hp.2.2.1,hp.2.2.2⟩,by linarith [hp.1]⟩
  have hν : ν univ ≤ ν (polarBox 0 0) :=
    measure_mono_ae (hmem.mono fun p hp _ => hp)
  exact hν.trans (by simpa only [zpow_zero,mul_one] using hb 0 le_rfl 0)

theorem polarBox_bound_all {ν : Measure (ℝ × ℝ)} {A : ℝ} (hA : 0 ≤ A)
    (hs : PolarSupport ν) (hb : PolarBoxBound ν A) (k m : ℤ) :
    ν (polarBox k m) ≤ ENNReal.ofReal (A*2^k) := by
  by_cases hk : k ≤ 0
  · exact hb k hk m
  · have hk0 : 0 ≤ k := le_of_lt (lt_of_not_ge hk)
    have hw : (1 : ℝ) ≤ 2^k := one_le_zpow₀ (by norm_num) hk0
    exact (measure_mono (subset_univ _)).trans ((polar_measure_univ_le hs hb).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith)))

theorem polarHardyValue_eq {g : Hardy} {p : ℝ × ℝ} (hr : 0 ≤ p.1) (hr1 : p.1 < 1) :
    polarHardyValue g p = analyticValue g.val (polarMap p) := by
  have h : polarMap p ∈ disk := by
    change ‖polarMap p‖ < 1
    simp only [polarMap,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr]
    simpa using hr1
  exact diskHardyValue_on g ⟨polarMap p,h⟩


/-- The one-coordinate cube model has exactly ordinary Lebesgue measure. -/
theorem lintegral_fin_one (F : ℝ → ℝ≥0∞) :
    (∫⁻ x : Fin 1 → ℝ, F (x 0)) = ∫⁻ t,F t := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding F

/-- A finite-height stopping cover gives a polar-box mass estimate; its input is an ordinary
nonnegative scalar density on the real line. -/
theorem polar_CZ_measure_le {ν : Measure (ℝ × ℝ)} {A : ℝ} (hA : 0 ≤ A)
    (hs : PolarSupport ν) (hb : PolarBoxBound ν A) (G : (Fin 1 → ℝ) → ℝ≥0∞) :
    ν (⋃ q ∈ calderonZygmundCubes G (1/2), polarBox q.1 (q.2 0)) ≤
      (2*ENNReal.ofReal A)*(∫⁻ x,G x) := by
  let C := calderonZygmundCubes G (1/2)
  have hd : Pairwise (Function.onFun Disjoint (fun q : C => dyadicCube q.val.1 q.val.2)) := by
    intro q q' hne
    exact pairwiseDisjoint_calderonZygmundCubes q.property q'.property
      (Subtype.val_injective.ne hne)
  have hv : volume (⋃ q ∈ C,dyadicCube q.1 q.2)=
      ∑' q : C,ENNReal.ofReal ((2 : ℝ)^q.val.1) := by
    rw [biUnion_eq_iUnion,measure_iUnion hd (fun q => measurableSet_dyadicCube _ _)]
    apply tsum_congr
    intro q
    simp only [volume_dyadicCube,Fintype.card_fin,pow_one]
  have htotal : volume (⋃ q ∈ C,dyadicCube q.1 q.2) ≤ 2*(∫⁻ x,G x) := by
    have ht := (mul_volume_biUnion_calderonZygmundCubes_le (g:=G) (t:=1/2)).trans
      (setLIntegral_le_lintegral _ _)
    calc
      _ = 2*((1/2 : ℝ≥0∞)*volume (⋃ q ∈ C,dyadicCube q.1 q.2)) := by
        dsimp [C]
        rw [← mul_assoc]
        simp [ENNReal.mul_inv_cancel]
      _ ≤ 2*(∫⁻ x,G x) := mul_le_mul_right ht 2
  calc
    _ ≤ ∑' q : C,ν (polarBox q.val.1 (q.val.2 0)) := by
      rw [biUnion_eq_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' q : C,ENNReal.ofReal A*ENNReal.ofReal ((2 : ℝ)^q.val.1) := by
      apply ENNReal.tsum_le_tsum
      intro q
      rw [← ENNReal.ofReal_mul hA]
      exact polarBox_bound_all hA hs hb _ _
    _ = ENNReal.ofReal A*volume (⋃ q ∈ C,dyadicCube q.1 q.2) := by
      rw [hv,ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal A*(2*(∫⁻ x,G x)) := mul_le_mul_right htotal _
    _ = _ := by ring

/-- A source depth always has a dyadic width at most one and less than twice that depth. -/
theorem exists_polar_dyadic_width {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ k : ℤ,k ≤ 0 ∧ d ≤ (2 : ℝ)^k ∧ (2 : ℝ)^k < 2*d := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near_of_lt_one hd hd1
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1)
  have he : (2 : ℝ)^(-(n : ℤ))=(1/2 : ℝ)^n := by
    simp only [zpow_neg,zpow_natCast,one_div,inv_pow]
  refine ⟨-(n : ℤ),by omega,?_,?_⟩
  · rw [he]
    exact hn'
  · rw [he]
    rw [pow_succ] at hn
    linarith


/-- Each strict Hardy level point supplies a dyadic angular interval on which the
real centered maximal function is uniformly large, including the origin case. -/
theorem hardy_polar_level_cube (g : Hardy) (p : ℝ × ℝ)
    (hp : 0 ≤ p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 < 1)
    (t : ℝ) (ht : 0 < t) (hpt : t < ‖polarHardyValue g p‖) :
    ∃ (k : ℤ) (m : Fin 1 → ℤ), k ≤ 0 ∧ 1-p.1 ≤ (2 : ℝ)^k ∧
      (fun _ : Fin 1 => p.2) ∈ dyadicCube k m ∧
      ∀ x ∈ dyadicCube k m, x 0 ∈ Ico (0 : ℝ) 1 ∧
        ENNReal.ofReal (t/64) <
          TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) (x 0) := by
  obtain ⟨k,hk,hd,hd'⟩ := exists_polar_dyadic_width
    (by linarith [hp.2.1] : 0<1-p.1) (by linarith [hp.1] : 1-p.1≤1)
  let θ : Fin 1 → ℝ := fun _ => p.2
  let m := dyadicIndex k θ
  have hθ : θ ∈ dyadicCube k m := mem_dyadicCube_dyadicIndex k θ
  have hroot : θ ∈ dyadicCube 0 (fun _ => 0) := by
    rw [dyadicCube_fin_one]
    simpa only [zpow_zero,Int.cast_zero,zero_mul,zero_add,one_mul,mem_preimage,
      θ,Set.mem_Ico] using ⟨hp.2.2.1,hp.2.2.2⟩
  have hrootIndex : dyadicIndex 0 θ = (fun _ => 0) := mem_dyadicCube.mp hroot
  have hsub : dyadicCube k m ⊆ dyadicCube 0 (fun _ => 0) := by
    simpa only [hrootIndex] using dyadicCube_subset_dyadicCube hk hθ
  refine ⟨k,m,hk,hd,hθ,?_⟩
  intro x hx
  have hx01 : x 0 ∈ Ico (0 : ℝ) 1 := by
    have h := hsub hx
    rw [dyadicCube_fin_one] at h
    simpa only [zpow_zero,Int.cast_zero,zero_mul,zero_add,one_mul,mem_preimage] using h
  refine ⟨hx01,?_⟩
  have hθI : p.2 ∈ Ico ((m 0 : ℝ)*2^k) (((m 0 : ℝ)+1)*2^k) := by
    simpa only [dyadicCube_fin_one,mem_preimage,θ] using hθ
  have hxI : x 0 ∈ Ico ((m 0 : ℝ)*2^k) (((m 0 : ℝ)+1)*2^k) := by
    simpa only [dyadicCube_fin_one,mem_preimage] using hx
  have hdist : |x 0-p.2| ≤ 2*(1-p.1) := by
    rw [abs_le]
    constructor <;> nlinarith [hxI.1,hxI.2,hθI.1,hθI.2]
  have hv := hardy_value_le_centered_maximal64 g p.1 p.2 (x 0) hp.1 hp.2.1
    ⟨hp.2.2.1,hp.2.2.2.le⟩ ⟨hx01.1,hx01.2.le⟩ hdist
  change ENNReal.ofReal ‖analyticValue g.val (polarMap p)‖ ≤ _ at hv
  rw [← polarHardyValue_eq (g:=g) hp.1 hp.2.1] at hv
  have hstrict : ENNReal.ofReal t <
      64*TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) (x 0) :=
    ((ENNReal.ofReal_lt_ofReal_iff (ht.trans hpt)).mpr hpt).trans_le hv
  have he : (64 : ℝ≥0∞)*ENNReal.ofReal (t/64)=ENNReal.ofReal t := by
    rw [show (64 : ℝ≥0∞)=ENNReal.ofReal (64 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤64)]
    congr 1
    ring
  by_contra hnot
  have hle := mul_le_mul_right (le_of_not_gt hnot) (64 : ℝ≥0∞)
  rw [he] at hle
  exact hstrict.not_ge hle

/-- Polar box control bounds every Hardy level set by a real maximal-function level set. -/
theorem polar_hardy_level_measure_le {ν : Measure (ℝ × ℝ)} {A : ℝ}
    (hA : 0 ≤ A) (hs : PolarSupport ν) (hb : PolarBoxBound ν A)
    (g : Hardy) (t : ℝ) (ht : 0 < t) :
    ν {p | t < ‖polarHardyValue g p‖} ≤
      (2*ENNReal.ofReal A)*volume
        {x | ENNReal.ofReal (t/64) <
          TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) x} := by
  let E : Set ℝ := {x | ENNReal.ofReal (t/64) <
    TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) x}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const
      (TTO.RealAnalysis.measurable_realMaximal (hardyPeriodicCutoff g.val))
  let G : (Fin 1 → ℝ) → ℝ≥0∞ :=
    fun x => (Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => 1) (x 0)
  have hGfinite : (∫⁻ x,G x) ≠ ∞ := by
    have hh : (∫⁻ x,G x) ≤ (1 : ℝ≥0∞) := by
      rw [show (∫⁻ x,G x)=∫⁻ y,(Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => (1 : ℝ≥0∞)) y
        from by simpa only [G] using lintegral_fin_one ((Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => (1 : ℝ≥0∞)))]
      rw [lintegral_indicator (measurableSet_Ico.inter hE)]
      simpa only [lintegral_one,Measure.restrict_apply_univ,Real.volume_Ico,
        sub_zero,ENNReal.ofReal_one] using
        (show volume (Ico (0 : ℝ) 1 ∩ E)≤volume (Ico (0 : ℝ) 1) from
          measure_mono inter_subset_left)
    exact ne_top_of_le_ne_top (by norm_num) hh
  have hGmass : (∫⁻ x,G x) ≤ volume E := by
    rw [show (∫⁻ x,G x)=∫⁻ y,(Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => (1 : ℝ≥0∞)) y
      from by simpa only [G] using lintegral_fin_one ((Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => (1 : ℝ≥0∞)))]
    rw [lintegral_indicator (measurableSet_Ico.inter hE),lintegral_one,
      Measure.restrict_apply_univ]
    exact measure_mono inter_subset_right
  have hcover : {p | t < ‖polarHardyValue g p‖} ≤ᵐ[ν]
      ⋃ q ∈ calderonZygmundCubes G (1/2),polarBox q.1 (q.2 0) := by
    filter_upwards [hs] with p hp hpt
    obtain ⟨k,m,hk,hd,hθ,hlarge⟩ := hardy_polar_level_cube g p hp t ht hpt
    have hunit : (⨍⁻ x in dyadicCube k m,G x ∂volume)=1 := by
      have he : G =ᵐ[volume.restrict (dyadicCube k m)] fun _ => 1 := by
        filter_upwards [ae_restrict_mem (measurableSet_dyadicCube k m)] with x hx
        change (Ico (0 : ℝ) 1 ∩ E).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) = 1
        exact Set.indicator_of_mem (s:=Ico (0 : ℝ) 1 ∩ E) (a:=x 0)
          ⟨(hlarge x hx).1,(hlarge x hx).2⟩ _
      rw [setLAverage_eq,lintegral_congr_ae he]
      simpa only [setLAverage_eq] using setLAverage_const
        (volume_dyadicCube_pos k m).ne' (volume_dyadicCube_ne_top k m) 1
    obtain ⟨q,hq,hkq,hsub⟩ :=
      exists_mem_calderonZygmundCubes_of_lt_setLAverage hGfinite
        (by norm_num : (1/2 : ℝ≥0∞)≠0) (by rw [hunit]; norm_num)
    apply mem_iUnion.mpr
    refine ⟨q,mem_iUnion.mpr ⟨hq,?_⟩⟩
    have hθq := hsub hθ
    have hangle : p.2 ∈ Ico ((q.2 0 : ℝ)*2^q.1) (((q.2 0 : ℝ)+1)*2^q.1) := by
      simpa only [dyadicCube_fin_one,mem_preimage] using hθq
    exact ⟨hangle,hd.trans (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ)≤2) hkq)⟩
  exact (measure_mono_ae hcover).trans ((polar_CZ_measure_le hA hs hb G).trans
    (mul_le_mul_right hGmass _))


/-- The square case of native layer cake, for an arbitrary measure. -/
theorem square_integral_layercake {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z) (f : Z → ℝ)
    (hf : Measurable f) (hf0 : ∀ z,0≤f z) :
    (∫⁻ z,ENNReal.ofReal ((f z)^2) ∂ρ)=
      ∫⁻ t in Ioi (0 : ℝ),ρ {z | t<f z}*ENNReal.ofReal (2*t) := by
  have hbase := lintegral_comp_eq_lintegral_meas_lt_mul ρ
    (Eventually.of_forall hf0) hf.aemeasurable
    (fun t _ => (continuous_const.mul continuous_id : Continuous (fun s : ℝ => (2 : ℝ)*s)).intervalIntegrable 0 t)
    (show ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),0≤(2 : ℝ)*t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0<t := ht
      positivity)
  simp only [Pi.mul_apply] at hbase
  rw [← hbase]
  apply lintegral_congr
  intro z
  congr 1
  rw [intervalIntegral.integral_const_mul,integral_id]
  ring

/-- Layer cake compares square integrals from ordinary level-measure inequalities. -/
theorem square_integral_le_of_level_measure_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (u : X → ℝ) (v : Y → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hu0 : ∀ x,0≤u x) (hv0 : ∀ y,0≤v y) (K : ℝ≥0∞) (hK : K≠∞)
    (hlevel : ∀ t : ℝ,0<t → μ {x | t<u x} ≤ K*ν {y | t<v y}) :
    (∫⁻ x,ENNReal.ofReal ((u x)^2) ∂μ) ≤
      K*(∫⁻ y,ENNReal.ofReal ((v y)^2) ∂ν) := by
  rw [square_integral_layercake μ u hu hu0,square_integral_layercake ν v hv hv0]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),K*(ν {y | t<v y}*ENNReal.ofReal (2*t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [mul_assoc] using mul_le_mul_left (hlevel t ht) (ENNReal.ofReal (2*t))
    _ = _ := lintegral_const_mul' _ _ hK

/-- The actual polar dyadic-box Carleson embedding. The constant is independent of the
measure, its box constant, and the Hardy vector. -/
theorem polar_carleson_embedding {ν : Measure (ℝ × ℝ)} {A : ℝ} (hA : 0 ≤ A)
    (hs : PolarSupport ν) (hb : PolarBoxBound ν A) (g : Hardy) :
    (∫⁻ p,ENNReal.ofReal (‖polarHardyValue g p‖^2) ∂ν) ≤
      ENNReal.ofReal (1310720*A*‖g‖^2) := by
  let M : ℝ → ℝ≥0∞ := TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val)
  have hM : Measurable M := TTO.RealAnalysis.measurable_realMaximal _
  have henergy : (∫⁻ x,(M x)^2) ≤ 160*ENNReal.ofReal (‖g‖^2) :=
    lintegral_maximal_hardyPeriodicCutoff_sq g.val
  have hfinite : (∫⁻ x,(M x)^2)≠∞ :=
    ne_top_of_le_ne_top (by finiteness) henergy
  have hMfinite : ∀ᵐ x ∂volume,M x≠∞ := by
    filter_upwards [ae_lt_top (hM.pow_const 2) hfinite] with x hx
    intro he
    simp only [he,ENNReal.top_pow (by norm_num : (2 : ℕ)≠0)] at hx
    exact hx.false
  let v : ℝ → ℝ := fun x => 64*(M x).toReal
  have hv : Measurable v := measurable_const.mul hM.ennreal_toReal
  have hv0 : ∀ x,0≤v x := by intro x; exact mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have hvenergy : (∫⁻ x,ENNReal.ofReal ((v x)^2)) ≤
      (655360 : ℝ≥0∞)*ENNReal.ofReal (‖g‖^2) := by
    calc
      _ = (4096 : ℝ≥0∞)*(∫⁻ x,(M x)^2) := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4096 : ℝ≥0∞)≠∞)]
        apply lintegral_congr_ae
        filter_upwards [hMfinite] with x hx
        dsimp [v]
        rw [mul_pow,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hx]
        norm_num
      _ ≤ (4096 : ℝ≥0∞)*(160*ENNReal.ofReal (‖g‖^2)) := mul_le_mul_right henergy _
      _ = _ := by ring
  have hlevel (t : ℝ) (ht : 0<t) :
      ν {p | t<‖polarHardyValue g p‖} ≤ (2*ENNReal.ofReal A)*volume {x | t<v x} := by
    have he : {x | ENNReal.ofReal (t/64)<M x}=ᵐ[volume]{x | t<v x} := by
      filter_upwards [hMfinite] with x hx
      apply propext
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity : 0≤t/64) hx]
      dsimp [v]
      constructor <;> intro h <;> linarith
    have h := polar_hardy_level_measure_le hA hs hb g t ht
    exact h.trans_eq (congrArg (fun a : ℝ≥0∞ => (2*ENNReal.ofReal A)*a) (measure_congr he))
  have hcomp := square_integral_le_of_level_measure_le ν volume
    (fun p => ‖polarHardyValue g p‖) v (measurable_polarHardyValue g).norm hv
    (fun p => norm_nonneg _) hv0 (2*ENNReal.ofReal A) (by finiteness) hlevel
  calc
    _ ≤ (2*ENNReal.ofReal A)*(∫⁻ x,ENNReal.ofReal ((v x)^2)) := hcomp
    _ ≤ (2*ENNReal.ofReal A)*(655360*ENNReal.ofReal (‖g‖^2)) :=
      mul_le_mul_right hvenergy _
    _ = ENNReal.ofReal (1310720*A*‖g‖^2) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤1310720)]
      norm_num
      ring

/-- Uniform quantifier order for use with arbitrary actual polar Carleson measures. -/
theorem exists_polar_carleson_embedding_constant :
    ∃ C : ℝ,0<C ∧ ∀ (ν : Measure (ℝ × ℝ)) (A : ℝ),0≤A →
      PolarSupport ν → PolarBoxBound ν A → ∀ g : Hardy,
        (∫⁻ p,ENNReal.ofReal (‖polarHardyValue g p‖^2) ∂ν) ≤
          ENNReal.ofReal (C*A*‖g‖^2) :=
  ⟨1310720,by norm_num,fun _ _ hA hs hb g => polar_carleson_embedding hA hs hb g⟩


/-- On an actual supported polar measure, the zero-extension statement is exactly the
ordinary disk analytic-value estimate, with no measurability assumption on values off the disk. -/
theorem polar_carleson_embedding_analyticValue {ν : Measure (ℝ × ℝ)} {A : ℝ}
    (hA : 0 ≤ A) (hs : PolarSupport ν) (hb : PolarBoxBound ν A) (g : Hardy) :
    (∫⁻ p,ENNReal.ofReal (‖analyticValue g.val
      ((p.1 : ℂ)*fourier (T:=1) 1 (p.2 : Boundary))‖^2) ∂ν) ≤
        ENNReal.ofReal (1310720*A*‖g‖^2) := by
  have he : (fun p => ENNReal.ofReal (‖analyticValue g.val
      ((p.1 : ℂ)*fourier (T:=1) 1 (p.2 : Boundary))‖^2)) =ᵐ[ν]
      fun p => ENNReal.ofReal (‖polarHardyValue g p‖^2) := by
    filter_upwards [hs] with p hp
    rw [polarHardyValue_eq hp.1 hp.2.1]
    rfl
  rw [lintegral_congr_ae he]
  exact polar_carleson_embedding hA hs hb g

theorem exists_polar_carleson_analyticValue_constant :
    ∃ C : ℝ,0<C ∧ ∀ (ν : Measure (ℝ × ℝ)) (A : ℝ),0≤A →
      PolarSupport ν → PolarBoxBound ν A → ∀ g : Hardy,
        (∫⁻ p,ENNReal.ofReal (‖analyticValue g.val
          ((p.1 : ℂ)*fourier (T:=1) 1 (p.2 : Boundary))‖^2) ∂ν) ≤
            ENNReal.ofReal (C*A*‖g‖^2) :=
  ⟨1310720,by norm_num,fun _ _ hA hs hb g => polar_carleson_embedding_analyticValue hA hs hb g⟩

end TTO.Paper.Proved
