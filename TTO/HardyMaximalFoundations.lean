/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.RealMaximalFoundations
public import TTO.AtomicFoundations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Actual periodic boundary cutoff and centered-maximal control of Hardy values. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

private theorem maximal_circleMeasure_eq_volume : circleMeasure=(volume : Measure Boundary) := by
  simpa only [ENNReal.ofReal_one,one_smul] using
    (AddCircle.volume_eq_smul_haarAddCircle (T:=1)).symm

/-- Every integral over N consecutive real periods has exactly N times the normalized circle mass. -/
theorem lintegral_circle_lift_nat_window (F : Boundary → ℝ≥0∞) (a : ℝ) (N : ℕ) :
    (∫⁻ x in Ioc a (a+(N : ℝ)),F (x : Boundary))=(N : ℝ≥0∞)*∫⁻ t,F t ∂circleMeasure := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hEnd : a+((N+1 : ℕ) : ℝ)=(a+(N : ℝ))+1 := by push_cast; ring
    rw [hEnd]
    have ha : a≤a+(N : ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) N]
    have hd : Disjoint (Ioc a (a+(N : ℝ))) (Ioc (a+(N : ℝ)) ((a+(N : ℝ))+1)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      linarith [hx.2,hy.1]
    rw [← Ioc_union_Ioc_eq_Ioc ha (by linarith : a+(N : ℝ)≤(a+(N : ℝ))+1),
      lintegral_union measurableSet_Ioc hd,ih]
    have hperiod : (∫⁻ x in Ioc (a+(N : ℝ)) ((a+(N : ℝ))+1),F (x : Boundary))=
        ∫⁻ t,F t ∂circleMeasure := by
      rw [maximal_circleMeasure_eq_volume]
      exact AddCircle.lintegral_preimage 1 (a+(N : ℝ)) F
    rw [hperiod,Nat.cast_add,Nat.cast_one,add_mul,one_mul]

/-- Five real periods of the actual native boundary representative; endpoints are immaterial. -/
def hardyPeriodicCutoff (f : BoundaryL2) (x : ℝ) : ℝ≥0∞ :=
  (Ioc (-2 : ℝ) 3).indicator (fun y => ENNReal.ofReal ‖f (y : Boundary)‖) x

theorem measurable_hardyPeriodicCutoff (f : BoundaryL2) : Measurable (hardyPeriodicCutoff f) := by
  exact (((Lp.stronglyMeasurable f).measurable.comp AddCircle.measurable_mk').norm.ennreal_ofReal).indicator measurableSet_Ioc

theorem lintegral_hardyPeriodicCutoff_sq (f : BoundaryL2) :
    (∫⁻ x,(hardyPeriodicCutoff f x)^2)=5*ENNReal.ofReal (‖f‖^2) := by
  have he : (fun x => (hardyPeriodicCutoff f x)^2)=
      (Ioc (-2 : ℝ) 3).indicator (fun x => ENNReal.ofReal (‖f (x : Boundary)‖^2)) := by
    funext x
    by_cases hx : x∈Ioc (-2 : ℝ) 3
    · simp only [hardyPeriodicCutoff,Set.indicator_of_mem hx]
      exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    · simp only [hardyPeriodicCutoff,Set.indicator_of_notMem hx,zero_pow (by norm_num : (2 : ℕ)≠0)]
  rw [he,lintegral_indicator measurableSet_Ioc]
  have hwindow := lintegral_circle_lift_nat_window (fun t => ENNReal.ofReal (‖f t‖^2)) (-2) 5
  norm_num only [Nat.cast_ofNat,neg_add_cancel_left,neg_add_rev] at hwindow
  convert hwindow.trans (congrArg (fun a : ℝ≥0∞ => 5*a) (fourier_lintegral_norm_sq f)) using 1

theorem lintegral_maximal_hardyPeriodicCutoff_sq (f : BoundaryL2) :
    (∫⁻ x,(TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff f) x)^2)≤
      160*ENNReal.ofReal (‖f‖^2) := by
  have h := TTO.RealAnalysis.realMaximal_strong_two (measurable_hardyPeriodicCutoff f).aemeasurable
  rw [lintegral_hardyPeriodicCutoff_sq] at h
  exact h.trans_eq (by ring)


theorem circle_chord_lower_real (x θ : ℝ) (h : |x-θ|≤1/2) :
    4*|x-θ|≤‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖ := by
  have he : fourier (T:=1) 1 ((x-θ : ℝ) : Boundary)*fourier (T:=1) 1 (θ : Boundary)=
      fourier (T:=1) 1 (x : Boundary) := by
    rw [← fourier_position_add]
    congr 1
    change ((x-θ+θ : ℝ) : Boundary)=(x : Boundary)
    rw [sub_add_cancel]
  have hn : ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖=
      ‖fourier (T:=1) 1 ((x-θ : ℝ) : Boundary)-1‖ := by
    calc
      _ = ‖(fourier (T:=1) 1 ((x-θ : ℝ) : Boundary)-1)*fourier (T:=1) 1 (θ : Boundary)‖ := by rw [sub_mul,he,one_mul]
      _ = _ := by rw [norm_mul,show ‖fourier (T:=1) 1 (θ : Boundary)‖=1 by simp,mul_one]
  have hex : fourier (T:=1) 1 ((x-θ : ℝ) : Boundary)=
      Complex.exp (Complex.I*((2*Real.pi*(x-θ) : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hsin : 2*|x-θ|≤|Real.sin (Real.pi*(x-θ))| := by
    have hpi : |Real.pi*(x-θ)|≤Real.pi/2 := by
      rw [abs_mul,abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    have hh := Real.mul_abs_le_abs_sin hpi
    rw [abs_mul,abs_of_pos Real.pi_pos] at hh
    have hc : (2/Real.pi)*(Real.pi*|x-θ|)=2*|x-θ| := by field_simp
    rw [hc] at hh
    exact hh
  rw [hn,hex,Complex.norm_exp_I_mul_ofReal_sub_one]
  have harg : (2*Real.pi*(x-θ))/2=Real.pi*(x-θ) := by ring
  rw [harg,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

theorem norm_radial_unit_difference_sq (z ζ : ℂ) (hz : ‖z‖=1) (hζ : ‖ζ‖=1) (r : ℝ) (hr : 0≤r) :
    ‖z-(r : ℂ)*ζ‖^2=(1-r)^2+r*‖z-ζ‖^2 := by
  change ‖z-(r : ℂ) • ζ‖^2=_
  rw [norm_sub_sq (𝕜:=ℂ),norm_sub_sq (𝕜:=ℂ),norm_smul,inner_smul_right]
  simp only [hz,hζ,mul_one,Complex.norm_real,Real.norm_of_nonneg hr]
  have hre : RCLike.re ((r : ℂ)*inner ℂ z ζ)=r*RCLike.re (inner ℂ z ζ) := by
    change ((r : ℂ)*inner ℂ z ζ).re=r*(inner ℂ z ζ).re
    simp
  rw [hre]
  ring

theorem radialPoisson_bound_near (r θ x : ℝ) (hr : 0≤r) (hr1 : r<1) :
    atomicPoissonKernel ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary)≤2/(1-r) := by
  have ht : 0<1-r := by linarith
  have hden : (1-r)^2≤‖fourier (T:=1) 1 (x : Boundary)-
      (r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖^2 := by
    rw [norm_radial_unit_difference_sq _ _ (by simp) (by simp) r hr]
    exact le_add_of_nonneg_right (mul_nonneg hr (sq_nonneg _))
  unfold atomicPoissonKernel
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,show ‖fourier (T:=1) 1 (θ : Boundary)‖=1 by simp,mul_one]
  calc
    _ ≤ (2*(1-r))/‖fourier (T:=1) 1 (x : Boundary)-
        (r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    _ ≤ (2*(1-r))/(1-r)^2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ht) hden
    _ = _ := by field_simp

theorem radialPoisson_bound_far (r θ s x : ℝ) (hr : 1/2≤r) (hr1 : r<1)
    (hθs : |s-θ|≤2*(1-r)) (hxθ : |x-θ|≤1/2) (hxs : 4*(1-r)≤|x-s|) :
    atomicPoissonKernel ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary)≤
      8*(1-r)/|x-s|^2 := by
  have hr0 : 0≤r := by linarith
  have ht : 0<1-r := by linarith
  have hD : 0< |x-s| := by linarith
  have htri : |x-s|≤|x-θ|+2*(1-r) := by
    have hh := abs_sub_le x θ s
    rw [abs_sub_comm θ s] at hh
    linarith
  have hch := circle_chord_lower_real x θ hxθ
  have hden : |x-s|^2/4≤‖fourier (T:=1) 1 (x : Boundary)-
      (r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖^2 := by
    rw [norm_radial_unit_difference_sq _ _ (by simp) (by simp) r hr0]
    have hm := mul_le_mul_of_nonneg_right hr
      (sq_nonneg ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖)
    nlinarith [abs_nonneg (x-θ),abs_nonneg (x-s),
      norm_nonneg (fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary))]
  unfold atomicPoissonKernel
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr0,show ‖fourier (T:=1) 1 (θ : Boundary)‖=1 by simp,mul_one]
  calc
    _ ≤ (2*(1-r))/‖fourier (T:=1) 1 (x : Boundary)-
        (r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    _ ≤ (2*(1-r))/(|x-s|^2/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp; norm_num


theorem realMaximal_ball_integral_bound (F : ℝ → ℝ≥0∞) (s R : ℝ) (hR : 0<R) :
    (∫⁻ x in ball s R,F x)≤ENNReal.ofReal (2*R)*TTO.RealAnalysis.realMaximal F s := by
  have h := TTO.RealAnalysis.average_le_realMaximal F s hR
  rw [setLAverage_eq] at h
  have hh := (ENNReal.div_le_iff (measure_ball_pos volume s hR).ne' measure_ball_lt_top.ne).mp h
  simpa only [Real.volume_ball,mul_comm] using hh

/-- Actual annular integration of the literal Poisson kernel, with no pointwise finiteness assumption on M. -/
theorem radialPoisson_integral_le_maximal (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (r θ s : ℝ) (hr : 1/2≤r) (hr1 : r<1) (hθs : |s-θ|≤2*(1-r)) :
    (∫⁻ x in Ioc (θ-1/2) (θ+1/2),
      ENNReal.ofReal (atomicPoissonKernel ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary))*F x)≤
      32*TTO.RealAnalysis.realMaximal F s := by
  let t := 1-r
  have ht : 0<t := by dsimp [t]; linarith
  have hr0 : 0≤r := by linarith
  let R : ℕ → ℝ := fun k => 4*t*(2 : ℝ)^k
  have hR (k : ℕ) : 0<R k := by dsimp [R]; positivity
  let J := Ioc (θ-1/2) (θ+1/2)
  let ρ : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (atomicPoissonKernel ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary))
  let A0 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (2/t)*(ball s (4*t)).indicator F x
  let A : ℕ → ℝ → ℝ≥0∞ := fun k x => ENNReal.ofReal (8*t/(R k)^2)*(ball s (2*R k)).indicator F x
  have hpoint (x : ℝ) : J.indicator (fun x => ρ x*F x) x≤A0 x+∑' k,A k x := by
    by_cases hx : x∈J
    · rw [Set.indicator_of_mem hx]
      have hxθ : |x-θ|≤1/2 := by
        exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
      by_cases hD : |x-s|<4*t
      · have hmem : x∈ball s (4*t) := by simpa only [Metric.mem_ball,Real.dist_eq] using hD
        have hp : ρ x≤ENNReal.ofReal (2/t) :=
          ENNReal.ofReal_le_ofReal (radialPoisson_bound_near r θ x hr0 hr1)
        calc
          _ ≤ ENNReal.ofReal (2/t)*F x := mul_le_mul_left hp (F x)
          _ = A0 x := by dsimp only [A0]; rw [Set.indicator_of_mem hmem]
          _ ≤ _ := le_add_of_nonneg_right bot_le
      · have hDle : 4*t≤|x-s| := le_of_not_gt hD
        have hratio : 1≤|x-s|/(4*t) := by
          rw [le_div_iff₀ (by positivity : 0<4*t)]
          simpa only [one_mul] using hDle
        obtain ⟨k,hk0,hk1⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ)<2)
        have hRle : R k≤|x-s| := by
          have hh := (le_div_iff₀ (by positivity : 0<4*t)).mp hk0
          dsimp [R]
          nlinarith
        have hRgt : |x-s|<2*R k := by
          have hh := (div_lt_iff₀ (by positivity : 0<4*t)).mp hk1
          rw [pow_succ] at hh
          dsimp [R]
          nlinarith
        have hmem : x∈ball s (2*R k) := by simpa only [Metric.mem_ball,Real.dist_eq] using hRgt
        have hdSq : (R k)^2≤|x-s|^2 := by nlinarith [hR k,abs_nonneg (x-s)]
        have hp : ρ x≤ENNReal.ofReal (8*t/(R k)^2) := by
          apply ENNReal.ofReal_le_ofReal
          exact (radialPoisson_bound_far r θ s x hr hr1 hθs hxθ hDle).trans
            (div_le_div_of_nonneg_left (by positivity : 0≤8*t) (sq_pos_of_pos (hR k)) hdSq)
        calc
          _ ≤ ENNReal.ofReal (8*t/(R k)^2)*F x := mul_le_mul_left hp (F x)
          _ = A k x := by dsimp only [A]; rw [Set.indicator_of_mem hmem]
          _ ≤ ∑' j,A j x := ENNReal.le_tsum (f:=fun j : ℕ => A j x) k
          _ ≤ _ := le_add_of_nonneg_left bot_le
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hM0 : Measurable A0 :=
    measurable_const.mul (hF.indicator measurableSet_ball)
  have hMA (k : ℕ) : Measurable (A k) :=
    measurable_const.mul (hF.indicator measurableSet_ball)
  have hBound0 : (∫⁻ x,A0 x)≤16*TTO.RealAnalysis.realMaximal F s := by
    dsimp only [A0]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_ball]
    calc
      _ ≤ ENNReal.ofReal (2/t)*(ENNReal.ofReal (2*(4*t))*TTO.RealAnalysis.realMaximal F s) :=
        mul_le_mul_right (realMaximal_ball_integral_bound F s (4*t) (by positivity)) _
      _ = _ := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤2/t)]
        have hc : (2/t)*(2*(4*t))=16 := by field_simp; norm_num
        rw [hc]
        norm_num
  have hBoundA (k : ℕ) : (∫⁻ x,A k x)≤
      ENNReal.ofReal (8*(1/2 : ℝ)^k)*TTO.RealAnalysis.realMaximal F s := by
    dsimp only [A]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_ball]
    calc
      _ ≤ ENNReal.ofReal (8*t/(R k)^2)*(ENNReal.ofReal (2*(2*R k))*TTO.RealAnalysis.realMaximal F s) :=
        mul_le_mul_right (realMaximal_ball_integral_bound F s (2*R k) (by positivity)) _
      _ = _ := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0≤8*t/(R k)^2)]
        have hc : (8*t/(R k)^2)*(2*(2*R k))=8*(1/2 : ℝ)^k := by
          dsimp [R]
          rw [div_pow,one_pow]
          field_simp
          ring
        rw [hc]
  have hgeom : (∑' k : ℕ,ENNReal.ofReal (8*(1/2 : ℝ)^k))=16 := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤8),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2)]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
    norm_num
  rw [← lintegral_indicator measurableSet_Ioc]
  calc
    _ ≤ ∫⁻ x,A0 x+∑' k,A k x := lintegral_mono hpoint
    _ = (∫⁻ x,A0 x)+∑' k,∫⁻ x,A k x := by
      rw [lintegral_add_left' hM0.aemeasurable,lintegral_tsum (fun k => (hMA k).aemeasurable)]
    _ ≤ 16*TTO.RealAnalysis.realMaximal F s+
        ∑' k,ENNReal.ofReal (8*(1/2 : ℝ)^k)*TTO.RealAnalysis.realMaximal F s :=
      add_le_add hBound0 (ENNReal.tsum_le_tsum hBoundA)
    _ = _ := by rw [ENNReal.tsum_mul_right,hgeom]; ring


theorem radialPoisson_integral_le_maximal_all (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (r θ s : ℝ) (hr : 0≤r) (hr1 : r<1) (hθ : θ∈Icc (0 : ℝ) 1) (hs : s∈Icc (0 : ℝ) 1)
    (hθs : |s-θ|≤2*(1-r)) :
    (∫⁻ x in Ioc (θ-1/2) (θ+1/2),
      ENNReal.ofReal (atomicPoissonKernel ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary))*F x)≤
      64*TTO.RealAnalysis.realMaximal F s := by
  by_cases hhalf : 1/2≤r
  · exact (radialPoisson_integral_le_maximal F hF r θ s hhalf hr1 hθs).trans (by gcongr; norm_num)
  · have hrhalf : r≤1/2 := (lt_of_not_ge hhalf).le
    have ht : 0<1-r := by linarith
    have hP (x : ℝ) : atomicPoissonKernel
        ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary)) (x : Boundary)≤4 := by
      apply (radialPoisson_bound_near r θ x hr hr1).trans
      apply (div_le_iff₀ ht).mpr
      linarith
    have hJ : Ioc (θ-1/2) (θ+1/2)⊆ball s 2 := by
      intro x hx
      rw [Metric.mem_ball,Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [hx.1,hx.2,hθ.1,hθ.2,hs.1,hs.2]
    calc
      _ ≤ ∫⁻ x in Ioc (θ-1/2) (θ+1/2),(4 : ℝ≥0∞)*F x := by
        apply lintegral_mono
        intro x
        exact mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal (hP x)) (F x)
      _ = 4*∫⁻ x in Ioc (θ-1/2) (θ+1/2),F x := lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 4*∫⁻ x in ball s 2,F x := mul_le_mul_right (lintegral_mono_set hJ) _
      _ ≤ 4*(ENNReal.ofReal (2*2)*TTO.RealAnalysis.realMaximal F s) :=
        mul_le_mul_right (realMaximal_ball_integral_bound F s 2 (by norm_num)) _
      _ = 16*TTO.RealAnalysis.realMaximal F s := by rw [← mul_assoc]; norm_num
      _ ≤ _ := mul_le_mul_left (by norm_num : (16 : ℝ≥0∞)≤64) _

theorem hardy_value_le_centered_maximal64 (g : Hardy) (r θ s : ℝ)
    (hr : 0≤r) (hr1 : r<1) (hθ : θ∈Icc (0 : ℝ) 1) (hs : s∈Icc (0 : ℝ) 1)
    (hθs : |s-θ|≤2*(1-r)) :
    ENNReal.ofReal ‖analyticValue g.val ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary))‖≤
      64*TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) s := by
  let w : Disk := ⟨(r : ℂ)*fourier (T:=1) 1 (θ : Boundary),by
    change ‖(r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖<1
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_apply,Circle.norm_coe,mul_one] using hr1⟩
  have hpos (u : Boundary) : 0≤atomicPoissonKernel w.val u := by
    unfold atomicPoissonKernel
    apply div_nonneg _ (sq_nonneg _)
    have hw : ‖w.val‖<1 := w.property
    nlinarith [norm_nonneg w.val]
  have hRep : analyticValue g.val w.val=
      ∫ u,g.val u*((atomicPoissonKernel w.val u : ℝ) : ℂ) ∂circleMeasure := by
    rw [← poissonAverage_hardy w g,poissonAverage_integral]
    rfl
  let G : Boundary → ℝ≥0∞ := fun u => ENNReal.ofReal (atomicPoissonKernel w.val u)*ENNReal.ofReal ‖g.val u‖
  have hNorm : ENNReal.ofReal ‖analyticValue g.val w.val‖≤∫⁻ u,G u ∂circleMeasure := by
    rw [hRep,ofReal_norm]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    apply lintegral_congr
    intro u
    dsimp only [G]
    rw [← ofReal_norm,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hpos u),
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_comm _ _
  have hPeriod : (∫⁻ u,G u ∂circleMeasure)=
      ∫⁻ x in Ioc (θ-1/2) (θ+1/2),
        ENNReal.ofReal (atomicPoissonKernel w.val (x : Boundary))*hardyPeriodicCutoff g.val x := by
    have hEnd : θ-1/2+(1 : ℝ)=θ+1/2 := by ring
    have hwindow := lintegral_circle_lift_nat_window G (θ-1/2) 1
    have hw : (∫⁻ u,G u ∂circleMeasure)=∫⁻ x in Ioc (θ-1/2) (θ+1/2),G (x : Boundary) := by
      simpa only [Nat.cast_one,one_mul,hEnd] using hwindow.symm
    rw [hw]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hcut : x∈Ioc (-2 : ℝ) 3 := by constructor <;> linarith [hx.1,hx.2,hθ.1,hθ.2]
    dsimp only [G,hardyPeriodicCutoff]
    rw [Set.indicator_of_mem hcut]
  change ENNReal.ofReal ‖analyticValue g.val w.val‖≤_
  rw [hPeriod] at hNorm
  exact hNorm.trans (radialPoisson_integral_le_maximal_all (hardyPeriodicCutoff g.val)
    (measurable_hardyPeriodicCutoff g.val) r θ s hr hr1 hθ hs hθs)

/-- The positive constant is fixed uniformly before every Hardy vector and disk point. -/
theorem exists_hardy_value_centered_maximal_bound :
    ∃ C : ℝ,0<C ∧ ∀ g : Hardy,∀ r θ s : ℝ,0≤r → r<1 →
      θ∈Icc (0 : ℝ) 1 → s∈Icc (0 : ℝ) 1 → |s-θ|≤2*(1-r) →
      ENNReal.ofReal ‖analyticValue g.val ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary))‖≤
        ENNReal.ofReal C*TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff g.val) s := by
  refine ⟨64,by norm_num,?_⟩
  intro g r θ s hr hr1 hθ hs hθs
  simpa using hardy_value_le_centered_maximal64 g r θ s hr hr1 hθ hs hθs

end TTO.Paper.Proved
