/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedPolarFoundations
public import TTO.ArcLocalizationPairingFoundations
public import TTO.CappedArcIntegralFoundations
public import TTO.CauchyFarGeometryFoundations

/-! Literal polar-box volume and near/large-box kernel estimates. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem diskRadialMeasure_Ici_one_sub_le (h : ℝ) :
    diskRadialMeasure (Ici (1-h))≤ENNReal.ofReal (2*h) := by
  have hVol : (volume.restrict (Ioo (0 : ℝ) 1)) (Ici (1-h))≤ENNReal.ofReal h := by
    rw [Measure.restrict_apply measurableSet_Ici]
    calc
      volume (Ici (1-h)∩Ioo (0 : ℝ) 1) ≤ volume (Icc (1-h) 1) :=
        measure_mono (fun x hx => ⟨hx.1,hx.2.2.le⟩)
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  rw [diskRadialMeasure,withDensity_apply _ measurableSet_Ici]
  calc
    _ ≤ ∫⁻ r in Ici (1-h),(2 : ℝ≥0∞) ∂volume.restrict (Ioo (0 : ℝ) 1) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with r hr
      exact (ENNReal.ofReal_le_ofReal (by linarith [hr.2] : 2*r≤2)).trans_eq (by norm_num)
    _ = 2*(volume.restrict (Ioo (0 : ℝ) 1)) (Ici (1-h)) := by
      rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ 2*ENNReal.ofReal h := mul_le_mul_right hVol 2
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]; norm_num

theorem polarBox_eq_rectangle (k m : ℤ) :
    polarBox k m=Ici (1-(2 : ℝ)^k) ×ˢ
      Ico ((m : ℝ)*2^k) (((m : ℝ)+1)*2^k) := by
  ext p
  simp only [polarBox,mem_ofPred_eq,mem_prod,mem_Ici]
  constructor
  · intro hp
    exact ⟨by linarith [hp.2],hp.1⟩
  · intro hp
    exact ⟨hp.2,by linarith [hp.1]⟩

theorem realPolarBase_polarBox_le (k m : ℤ) :
    realPolarBase (polarBox k m)≤ENNReal.ofReal (2*((2 : ℝ)^k)^2) := by
  have hAng : (volume.restrict (Ico (0 : ℝ) 1))
      (Ico ((m : ℝ)*2^k) (((m : ℝ)+1)*2^k))≤ENNReal.ofReal ((2 : ℝ)^k) := by
    calc
      _ ≤ volume (Ico ((m : ℝ)*2^k) (((m : ℝ)+1)*2^k)) := Measure.restrict_apply_le _ _
      _ = _ := by rw [Real.volume_Ico]; congr 1; ring
  rw [polarBox_eq_rectangle,realPolarBase,Measure.prod_prod]
  calc
    _ ≤ ENNReal.ofReal (2*(2 : ℝ)^k)*ENNReal.ofReal ((2 : ℝ)^k) :=
      mul_le_mul' (diskRadialMeasure_Ici_one_sub_le _) hAng
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

theorem weighted_realPolarBase_polarBox_le (k m : ℤ) :
    (∫⁻ p in polarBox k m,ENNReal.ofReal (1-p.1^2) ∂realPolarBase)≤
      ENNReal.ofReal (4*((2 : ℝ)^k)^3) := by
  have hDensity : ∀ᵐ p ∂realPolarBase.restrict (polarBox k m),
      ENNReal.ofReal (1-p.1^2)≤ENNReal.ofReal (2*(2 : ℝ)^k) := by
    filter_upwards [ae_restrict_mem (measurableSet_polarBox k m)] with p hp
    apply ENNReal.ofReal_le_ofReal
    have hDepth : 1-p.1≤(2 : ℝ)^k := hp.2
    nlinarith [sq_nonneg (1-p.1)]
  calc
    _ ≤ ∫⁻ _p in polarBox k m,ENNReal.ofReal (2*(2 : ℝ)^k) ∂realPolarBase :=
      lintegral_mono_ae hDensity
    _ = ENNReal.ofReal (2*(2 : ℝ)^k)*realPolarBase (polarBox k m) := by
      rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (2*(2 : ℝ)^k)*ENNReal.ofReal (2*((2 : ℝ)^k)^2) :=
      mul_le_mul_right (realPolarBase_polarBox_le k m) _
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- Actual localized near datum on a full centered real-period window. -/
def nearArcDatum (f : BoundaryL2) (a h : ℝ) : BoundaryL2 :=
  arcWindowL2 (a-1/2) (a-2*h) (a+2*h)
    (f-constL2 (arcMean f (a-2*h) (a+2*h)))

theorem nearArcDatum_norm_sq_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hSmall : h≤1/4) :
    ‖nearArcDatum f a h‖^2≤1536*B^2*h := by
  have hNear := norm_arcWindowL2_sub_arcMean_sq_le (a-1/2) (a-2*h) (a+2*h)
    (by linarith) (by linarith) (by linarith) f B hB hMO
  change ‖nearArcDatum f a h‖^2≤384*B^2*(a+2*h-(a-2*h)) at hNear
  convert hNear using 1
  ring

theorem weightedPolarMeasure_nearArc_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hSmall : h≤1/4) (S : Set (ℝ×ℝ)) :
    weightedPolarMeasure (nearArcDatum f a h) S≤ENNReal.ofReal (3072*B^2*h) := by
  calc
    _ ≤ weightedPolarMeasure (nearArcDatum f a h) univ := measure_mono (subset_univ _)
    _ ≤ ENNReal.ofReal (2*‖nearArcDatum f a h‖^2) := by
      rw [weightedPolarMeasure_univ]
      exact cauchyWeightedHardyKernel_weighted_energy_le _
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      nlinarith [nearArcDatum_norm_sq_le f B hB hMO a h hh hSmall])

theorem weightedPolarMeasure_largeBox_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (k m : ℤ) (hLarge : (1 : ℝ)/4≤(2 : ℝ)^k) :
    weightedPolarMeasure f (polarBox k m)≤ENNReal.ofReal (3072*B^2*(2 : ℝ)^k) := by
  calc
    _ ≤ weightedPolarMeasure f univ := measure_mono (subset_univ _)
    _ ≤ ENNReal.ofReal (768*B^2) := weightedPolarMeasure_univ_le_oscillation f B hB hMO
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      nlinarith [mul_le_mul_of_nonneg_left hLarge (sq_nonneg B)])


/-- The far datum is the actual remainder after constant cancellation and localization. -/
def farArcDatum (f : BoundaryL2) (a h : ℝ) : BoundaryL2 :=
  f-constL2 (arcMean f (a-2*h) (a+2*h))-nearArcDatum f a h

theorem cauchyWeightedHardyKernel_period_integral (f : BoundaryL2) (w : Disk) (a : ℝ) :
    cauchyWeightedHardyKernel f w.val=
      ∫ x in Ioc (a-1/2) (a+1/2),f (x : Boundary)*
        cauchyWeightedBoundaryKernel w (x : Boundary) := by
  let F : Boundary → ℂ := fun ζ => f ζ*cauchyWeightedBoundaryKernel w ζ
  have hEnd : a-1/2+1=a+1/2 := by ring
  calc
    _ = ∫ ζ,F ζ ∂circleMeasure := (cauchyWeightedHardyKernel_integral f w).2
    _ = ∫ ζ : Boundary,F ζ := by rw [circleMeasure_eq_volume]
    _ = _ := by
      have he := (AddCircle.integral_preimage 1 (a-1/2) F).symm
      simpa only [hEnd,F] using he

theorem cauchyWeightedHardyKernel_farArcDatum_integral (f : BoundaryL2) (w : Disk)
    (a h : ℝ) (_hh : 0<h) (hSmall : h≤1/4) :
    cauchyWeightedHardyKernel (farArcDatum f a h) w.val=
      ∫ x in Ioc (a-1/2) (a+1/2)\Ioc (a-2*h) (a+2*h),
        (f-constL2 (arcMean f (a-2*h) (a+2*h))) (x : Boundary)*
          cauchyWeightedBoundaryKernel w (x : Boundary) := by
  let g := f-constL2 (arcMean f (a-2*h) (a+2*h))
  have hI := integrableOn_cauchyWeightedBoundaryKernel g w (a-1/2) (a+1/2) (by linarith)
  have hSub : Ioc (a-2*h) (a+2*h) ⊆ Ioc (a-1/2) (a+1/2) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [farArcDatum,cauchyWeightedHardyKernel_sub,
    cauchyWeightedHardyKernel_period_integral g w a]
  change _-cauchyWeightedHardyKernel
    (arcWindowL2 (a-1/2) (a-2*h) (a+2*h) g) w.val=_
  rw [(cauchyWeightedHardyKernel_arcWindow_integral (a-1/2) (a-2*h) (a+2*h)
    (by linarith) (by linarith) g w).2]
  exact (setIntegral_sdiff measurableSet_Ioc hI hSub).symm

theorem norm_cauchyWeightedHardyKernel_farArcDatum_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (w : Disk) (r a θ h : ℝ) (hr : 1/2≤r)
    (hw : w.val=(r : ℂ)*fourier (T:=1) 1 (θ : Boundary))
    (hh : 0<h) (hSmall : h≤1/4) (hθ : |θ-a|≤h/2) :
    ‖cauchyWeightedHardyKernel (farArcDatum f a h) w.val‖≤40*B/h := by
  let c := arcMean f (a-2*h) (a+2*h)
  let g := f-constL2 c
  let G : ℝ → ℝ := fun x => ‖f (x : Boundary)-c‖/|x-a|^2
  let S := Ioc (a-1/2) (a+1/2)\Ioc (a-2*h) (a+2*h)
  let T := Ioc (a-1/2) (a+1/2)∩{x : ℝ | (4*h)/2≤|x-a|}
  have hSub : S ⊆ T := by
    intro x hx
    refine ⟨hx.1,?_⟩
    change (4*h)/2≤|x-a|
    have hNot : ¬(a-2*h<x ∧ x≤a+2*h) := hx.2
    by_cases hLeft : x≤a-2*h
    · have hd := neg_le_abs (x-a)
      linarith
    · have hRight : a+2*h<x := by
        by_contra hn
        exact hNot ⟨lt_of_not_ge hLeft,le_of_not_gt hn⟩
      have hd := le_abs_self (x-a)
      linarith
  have hScalar := integrable_far_arc_norm_div_sq f B hB hMO a (4*h) (by positivity) (by linarith)
  have hMean : arcMean f (a-(4*h)/2) (a+(4*h)/2)=c := by
    change arcMean f (a-(4*h)/2) (a+(4*h)/2)=arcMean f (a-2*h) (a+2*h)
    congr 1 <;> ring
  rw [hMean] at hScalar
  have hI : IntegrableOn G T := hScalar.1
  have hIBound : (∫ x in T,G x)≤80*B/(4*h) := hScalar.2
  have hGNonneg (x : ℝ) : 0≤G x := by dsimp [G]; positivity
  have hMono : (∫ x in S,G x)≤∫ x in T,G x :=
    setIntegral_mono_set hI (Eventually.of_forall hGNonneg)
      (Eventually.of_forall fun x hx => hSub hx)
  have hAE : (fun ζ => g ζ)=ᵐ[circleMeasure] fun ζ => f ζ-c := by
    filter_upwards [Lp.coeFn_sub f (constL2 c),
      (memLp_const c (μ:=circleMeasure) (p:=2)).coeFn_toLp] with ζ hs hc
    change (f-constL2 c) ζ=f ζ-(constL2 c) ζ at hs
    change (constL2 c) ζ=c at hc
    change (f-constL2 c) ζ=f ζ-c
    rw [hs,hc]
  have hLift := circle_ae_lift_Ioc hAE (a-1/2) (a+1/2) (by linarith)
  have hS : MeasurableSet S := measurableSet_Ioc.diff measurableSet_Ioc
  have hPoint : ∀ᵐ (x : ℝ) ∂volume.restrict S,
      ‖g (x : Boundary)*cauchyWeightedBoundaryKernel w (x : Boundary)‖≤2*G x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hLift,
      ae_restrict_mem hS] with x hx hMem
    have hxAbs : |x-a|≤1/2 := abs_le.mpr
      ⟨by linarith [hMem.1.1],by linarith [hMem.1.2]⟩
    have hFar : 2*h≤|x-a| := by
      have hd : (4*h)/2≤|x-a| := (hSub hMem).2
      linarith
    rw [hx,norm_mul]
    calc
      _ ≤ ‖f (x : Boundary)-c‖*(2/|x-a|^2) :=
        mul_le_mul_of_nonneg_left
          (norm_cauchyWeightedBoundaryKernel_le_far_arc w r a θ h x hr hw hh hθ hxAbs hFar)
          (norm_nonneg _)
      _ = _ := by dsimp [G]; ring
  rw [cauchyWeightedHardyKernel_farArcDatum_integral f w a h hh hSmall]
  change ‖∫ x in S,g (x : Boundary)*cauchyWeightedBoundaryKernel w (x : Boundary)‖≤_
  calc
    _ ≤ ∫ x in S,2*G x := norm_integral_le_of_norm_le ((hI.mono_set hSub).const_mul 2) hPoint
    _ = 2*(∫ x in S,G x) := integral_const_mul _ _
    _ ≤ 2*(80*B/(4*h)) := mul_le_mul_of_nonneg_left (hMono.trans hIBound) (by norm_num)
    _ = _ := by ring

theorem cauchyWeightedHardyKernel_near_add_far (f : BoundaryL2) (a h : ℝ) (w : Disk) :
    cauchyWeightedHardyKernel f w.val=
      cauchyWeightedHardyKernel (nearArcDatum f a h) w.val+
        cauchyWeightedHardyKernel (farArcDatum f a h) w.val := by
  rw [farArcDatum,cauchyWeightedHardyKernel_sub,cauchyWeightedHardyKernel_sub_const]
  ring


/-- The real center of the literal dyadic angular interval. -/
def polarBoxCenter (k m : ℤ) : ℝ := ((m : ℝ)+1/2)*(2 : ℝ)^k

theorem polarBox_angle_distance_le (k m : ℤ) (p : ℝ×ℝ) (hp : p∈polarBox k m) :
    |p.2-polarBoxCenter k m|≤(2 : ℝ)^k/2 := by
  have hθ : (m : ℝ)*2^k≤p.2 ∧ p.2<((m : ℝ)+1)*2^k := hp.1
  dsimp [polarBoxCenter]
  apply abs_le.mpr
  constructor <;> nlinarith [hθ.1,hθ.2]

theorem weightedPolarMeasure_farArc_polarBox_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (k m : ℤ) (hSmall : (2 : ℝ)^k≤1/4) :
    weightedPolarMeasure (farArcDatum f (polarBoxCenter k m) ((2 : ℝ)^k))
      (polarBox k m)≤ENNReal.ofReal (6400*B^2*(2 : ℝ)^k) := by
  let h : ℝ := (2 : ℝ)^k
  let a := polarBoxCenter k m
  let g := farArcDatum f a h
  have hh : 0<h := by dsimp [h]; positivity
  have hPoint : ∀ᵐ p ∂realPolarBase.restrict (polarBox k m),
      ENNReal.ofReal ((1-p.1^2)*‖cauchyWeightedHardyKernel g (polarMap p)‖^2)≤
        ENNReal.ofReal ((40*B/h)^2)*ENNReal.ofReal (1-p.1^2) := by
    filter_upwards [ae_restrict_of_ae realPolarBase_support,
      ae_restrict_mem (measurableSet_polarBox k m)] with p hp hMem
    have hDisk : polarMap p∈disk := by
      change ‖polarMap p‖<1
      simp only [polarMap,norm_mul,Complex.norm_real,Real.norm_of_nonneg hp.1,
        show ‖fourier (T:=1) 1 (p.2 : Boundary)‖=1 by simp,mul_one]
      exact hp.2.1
    have hr : 1/2≤p.1 := by
      have hd : 1-p.1≤h := hMem.2
      change h≤1/4 at hSmall
      linarith
    have hθ : |p.2-a|≤h/2 := polarBox_angle_distance_le k m p hMem
    have hK := norm_cauchyWeightedHardyKernel_farArcDatum_le f B hB hMO
      ⟨polarMap p,hDisk⟩ p.1 a p.2 h hr rfl hh hSmall hθ
    have hSq : ‖cauchyWeightedHardyKernel g (polarMap p)‖^2≤(40*B/h)^2 := by
      have hNN : 0≤40*B/h := by positivity
      nlinarith [norm_nonneg (cauchyWeightedHardyKernel g (polarMap p))]
    have hWeight : 0≤1-p.1^2 := by nlinarith [hp.1,hp.2.1]
    rw [← ENNReal.ofReal_mul (sq_nonneg (40*B/h))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hSq hWeight]
  rw [weightedPolarMeasure_apply _ _ (measurableSet_polarBox k m)]
  calc
    _ ≤ ∫⁻ p in polarBox k m,ENNReal.ofReal ((40*B/h)^2)*
        ENNReal.ofReal (1-p.1^2) ∂realPolarBase := lintegral_mono_ae hPoint
    _ = ENNReal.ofReal ((40*B/h)^2)*
        (∫⁻ p in polarBox k m,ENNReal.ofReal (1-p.1^2) ∂realPolarBase) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((40*B/h)^2)*ENNReal.ofReal (4*h^3) :=
      mul_le_mul_right (weighted_realPolarBase_polarBox_le k m) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg (40*B/h))]
      congr 1
      dsimp [h]
      field_simp
      ring

/-- The actual kernel measure obeys the square-triangle estimate after constant cancellation. -/
theorem weightedPolarMeasure_near_add_far_le (f : BoundaryL2) (a h : ℝ)
    (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) :
    weightedPolarMeasure f S≤2*weightedPolarMeasure (nearArcDatum f a h) S+
      2*weightedPolarMeasure (farArcDatum f a h) S := by
  let n := nearArcDatum f a h
  let q := farArcDatum f a h
  have hPoint : ∀ᵐ p ∂realPolarBase.restrict S,
      polarKernelDensity f p≤2*polarKernelDensity n p+2*polarKernelDensity q p := by
    filter_upwards [ae_restrict_of_ae realPolarBase_support,
      ae_restrict_of_ae (polarKernelDensity_ae f),
      ae_restrict_of_ae (polarKernelDensity_ae n),
      ae_restrict_of_ae (polarKernelDensity_ae q)] with p hp hf hn hq
    rw [hf,hn,hq]
    have hDisk : polarMap p∈disk := by
      change ‖polarMap p‖<1
      simp only [polarMap,norm_mul,Complex.norm_real,Real.norm_of_nonneg hp.1,
        show ‖fourier (T:=1) 1 (p.2 : Boundary)‖=1 by simp,mul_one]
      exact hp.2.1
    have hTri : ‖cauchyWeightedHardyKernel f (polarMap p)‖≤
        ‖cauchyWeightedHardyKernel n (polarMap p)‖+
          ‖cauchyWeightedHardyKernel q (polarMap p)‖ := by
      rw [cauchyWeightedHardyKernel_near_add_far f a h ⟨polarMap p,hDisk⟩]
      exact norm_add_le _ _
    have hSq : ‖cauchyWeightedHardyKernel f (polarMap p)‖^2≤
        2*‖cauchyWeightedHardyKernel n (polarMap p)‖^2+
          2*‖cauchyWeightedHardyKernel q (polarMap p)‖^2 := by
      nlinarith [norm_nonneg (cauchyWeightedHardyKernel f (polarMap p)),
        norm_nonneg (cauchyWeightedHardyKernel n (polarMap p)),
        norm_nonneg (cauchyWeightedHardyKernel q (polarMap p)),
        sq_nonneg (‖cauchyWeightedHardyKernel n (polarMap p)‖-
          ‖cauchyWeightedHardyKernel q (polarMap p)‖)]
    have hW : 0≤1-p.1^2 := by nlinarith [hp.1,hp.2.1]
    calc
      _ ≤ ENNReal.ofReal (2*((1-p.1^2)*‖cauchyWeightedHardyKernel n (polarMap p)‖^2)+
          2*((1-p.1^2)*‖cauchyWeightedHardyKernel q (polarMap p)‖^2)) :=
        ENNReal.ofReal_le_ofReal (by
          nlinarith [mul_le_mul_of_nonneg_left hSq hW])
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat]
  simp only [weightedPolarMeasure]
  rw [withDensity_apply (polarKernelDensity f) hS,
    withDensity_apply (polarKernelDensity (nearArcDatum f a h)) hS,
    withDensity_apply (polarKernelDensity (farArcDatum f a h)) hS]
  calc
    _ ≤ ∫⁻ p in S,2*polarKernelDensity n p+2*polarKernelDensity q p ∂realPolarBase :=
      lintegral_mono_ae hPoint
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun p : ℝ×ℝ => (2 : ℝ≥0∞)*polarKernelDensity n p) from
          measurable_const.mul (measurable_polarKernelDensity n)) (fun p => 2*polarKernelDensity q p),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞)≠∞),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞)≠∞)]

/-- Uniform actual symbol boxes, with the constant fixed before every symbol and BMO bound. -/
theorem weightedPolarMeasure_polarBoxBound_oscillation (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B) :
    PolarBoxBound (weightedPolarMeasure f) (32768*B^2) := by
  intro k _hk m
  have hh : 0<(2 : ℝ)^k := by positivity
  by_cases hSmall : (2 : ℝ)^k≤1/4
  · calc
      _ ≤ 2*weightedPolarMeasure (nearArcDatum f (polarBoxCenter k m) ((2 : ℝ)^k))
            (polarBox k m)+
          2*weightedPolarMeasure (farArcDatum f (polarBoxCenter k m) ((2 : ℝ)^k))
            (polarBox k m) :=
        weightedPolarMeasure_near_add_far_le f _ _ _ (measurableSet_polarBox k m)
      _ ≤ 2*ENNReal.ofReal (3072*B^2*(2 : ℝ)^k)+
          2*ENNReal.ofReal (6400*B^2*(2 : ℝ)^k) :=
        add_le_add
          (mul_le_mul_right (weightedPolarMeasure_nearArc_le f B hB hMO _ _ hh hSmall _) 2)
          (mul_le_mul_right (weightedPolarMeasure_farArc_polarBox_le f B hB hMO k m hSmall) 2)
      _ = ENNReal.ofReal (18944*B^2*(2 : ℝ)^k) := by
        rw [← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (sq_nonneg B) hh.le])
  · exact (weightedPolarMeasure_largeBox_le f B hB hMO k m (le_of_not_ge hSmall)).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg (sq_nonneg B) hh.le]))


/-- The actual symbol box bound discharges the homogeneous Hardy embedding. -/
theorem hardyWeightedOscillationEmbedding : HardyWeightedOscillationEmbedding :=
  hardyWeightedOscillationEmbedding_of_polar_boxes 32768 (by norm_num)
    (fun f B hB hMO => weightedPolarMeasure_polarBoxBound_oscillation f B hB hMO)

/-- Genuine finite Hardy L¹ pairing estimate, with no remaining analytic proof parameter. -/
theorem finiteHardyL1OscillationEstimate : FiniteHardyL1OscillationEstimate :=
  finiteHardyL1OscillationEstimate_of_weighted_embedding hardyWeightedOscillationEmbedding

/-- Compact Hankel/VMOA and continuous-symbol characterization.
Reference: V. V. Peller, *An Excursion into the Theory of Hankel Operators*,
MSRI Publications 33 (1998), Theorems 5.5 and 5.8, pp. 79–80;
https://library.slmath.org/books/Book33/files/peller.pdf.
The bounded-symbol lift and analytic estimates are proved in the imported source closure. -/
theorem hartman : Reduction.HartmanObligation :=
  hartmanObligation_of_weighted_oscillation_embedding hardyWeightedOscillationEmbedding

/-- The full reviewed principal compactness theorem, without external hypotheses. -/
theorem compactClassificationTheorem : CompactConclusion := compactClassification hartman

end TTO.Paper.Proved
