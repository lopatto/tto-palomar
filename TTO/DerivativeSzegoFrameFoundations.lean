/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedBergmanFoundations
public import TTO.SzegoRankOneFoundations

/-! Literal derivative Szegő vectors and their normalized weighted-area Bessel bound.
The full frame operator is not claimed to be Bochner integrable. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem summable_nat_succ_geometric (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ)+1)*r^n) := by
  have h1 := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (show ‖r‖ < 1 by simpa only [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
  have h0 := summable_geometric_of_lt_one hr hr1
  have hs := h1.add h0
  have hpow (n : ℕ) : |r^n|=r^n := abs_of_nonneg (pow_nonneg hr n)
  simpa only [pow_one,norm_mul,Real.norm_natCast,Real.norm_eq_abs,hpow,
    Nat.abs_cast,add_mul,one_mul] using hs

def derivativeSzegoCoeff (w : Disk) (n : ℕ) : ℂ :=
  ((n : ℂ)+1)*conj w.val^n

theorem summable_norm_derivativeSzegoCoeff (w : Disk) :
    Summable (fun n : ℕ => ‖derivativeSzegoCoeff w n‖) := by
  have he (n : ℕ) : ‖derivativeSzegoCoeff w n‖ = ((n : ℝ)+1)*‖w.val‖^n := by
    rw [derivativeSzegoCoeff,norm_mul,show (n : ℂ)+1=((n+1 : ℕ) : ℂ) from by push_cast; rfl,
      Complex.norm_natCast,norm_pow,Complex.norm_conj]
    push_cast
    rfl
  simpa only [he] using
      summable_nat_succ_geometric ‖w.val‖ (norm_nonneg _) w.property

theorem summable_derivativeSzegoKernel (w : Disk) :
    Summable (fun n : ℕ => derivativeSzegoCoeff w n • hardyBasis n) := by
  refine Summable.of_norm_bounded (summable_norm_derivativeSzegoCoeff w) fun n => ?_
  rw [norm_smul,hardyBasis.orthonormal.norm_eq_one,mul_one]

def derivativeSzegoKernel (w : Disk) : Hardy :=
  ∑' n : ℕ, derivativeSzegoCoeff w n • hardyBasis n

theorem hardyBasis_repr_derivativeSzegoKernel (w : Disk) (n : ℕ) :
    hardyBasis.repr (derivativeSzegoKernel w) n = ((n : ℂ)+1)*conj w.val^n := by
  rw [HilbertBasis.repr_apply_apply,derivativeSzegoKernel,← innerSL_apply_apply ℂ,
    ContinuousLinearMap.map_tsum _ (summable_derivativeSzegoKernel w),
    tsum_eq_single n fun m hm => by
      rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
        (orthonormal_iff_ite.mp hardyBasis.orthonormal n m).trans (ite_eq_right (Ne.symm hm)),
        mul_zero]]
  rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
    inner_self_eq_one_of_norm_eq_one (hardyBasis.orthonormal.norm_eq_one n),mul_one]
  rfl

def derivativeSzegoSeries (f : BoundaryL2) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : ℕ => ((n : ℂ)+1)*fourierCoeff f (n : ℤ))

def derivativeSzegoValue (f : BoundaryL2) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (((n : ℂ)+1)*fourierCoeff f (n : ℤ))*z^n

theorem summable_derivativeSzegoSeries (f : BoundaryL2) (r : ℝ≥0) (hr : r < 1) :
    Summable (fun n : ℕ => ‖derivativeSzegoSeries f n‖*(r : ℝ)^n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))
    (fun n => ?_) ((summable_nat_succ_geometric r r.coe_nonneg hr).mul_left ‖f‖)
  rw [derivativeSzegoSeries,FormalMultilinearSeries.ofScalars_norm,norm_mul,
    ← Nat.cast_add_one,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ (((n : ℝ)+1)*‖f‖)*(r : ℝ)^n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_fourierCoeff_le f n) (by positivity))
        (pow_nonneg r.coe_nonneg n)
    _ = _ := by ring

theorem derivativeSzegoSeries_sum (f : BoundaryL2) :
    (derivativeSzegoSeries f).sum = derivativeSzegoValue f := by
  funext z
  rw [FormalMultilinearSeries.sum,derivativeSzegoValue]
  simp only [derivativeSzegoSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]

theorem analyticOnNhd_derivativeSzegoValue (f : BoundaryL2) :
    AnalyticOnNhd ℂ (derivativeSzegoValue f) disk := by
  intro z hz
  obtain ⟨r,hzr,hr1⟩ := exists_between (show ‖z‖ < 1 from hz)
  let R : ℝ≥0 := ⟨r,(norm_nonneg z).trans hzr.le⟩
  have hR : (R : ℝ≥0∞) ≤ (derivativeSzegoSeries f).radius :=
    (derivativeSzegoSeries f).le_radius_of_summable (summable_derivativeSzegoSeries f R hr1)
  have hpos : 0 < (derivativeSzegoSeries f).radius :=
    (ENNReal.coe_pos.mpr (show 0 < R from (norm_nonneg z).trans_lt hzr)).trans_le hR
  have hs := (derivativeSzegoSeries f).hasFPowerSeriesOnBall hpos
  rw [derivativeSzegoSeries_sum] at hs
  exact hs.analyticAt_of_mem (by
    change edist z 0 < (derivativeSzegoSeries f).radius
    rw [edist_zero_right]
    exact (ENNReal.coe_lt_coe.mpr (show ‖z‖₊ < R from hzr)).trans_le hR)

theorem diskTaylorCoeff_derivativeSzegoValue (f : BoundaryL2) (n : ℕ) :
    diskTaylorCoeff (derivativeSzegoValue f) n =
      ((n : ℂ)+1)*fourierCoeff f (n : ℤ) := by
  have hR : ((1/2 : ℝ≥0) : ℝ≥0∞) ≤ (derivativeSzegoSeries f).radius :=
    (derivativeSzegoSeries f).le_radius_of_summable
      (summable_derivativeSzegoSeries f (1/2) (by norm_num))
  have hs := (derivativeSzegoSeries f).hasFPowerSeriesOnBall
    ((by norm_num : (0 : ℝ≥0∞) < (1/2 : ℝ≥0)).trans_le hR)
  rw [derivativeSzegoSeries_sum] at hs
  have ht := (analyticOnNhd_derivativeSzegoValue f 0 (by norm_num [disk])).hasFPowerSeriesAt
  have he := hs.hasFPowerSeriesAt.eq_formalMultilinearSeries ht
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [derivativeSzegoSeries,FormalMultilinearSeries.coeff_ofScalars,diskTaylorCoeff] using hc.symm

theorem inner_derivativeSzegoKernel (w : Disk) (f : Hardy) :
    inner ℂ (derivativeSzegoKernel w) f = derivativeSzegoValue f.val w.val := by
  rw [← inner_conj_symm,derivativeSzegoKernel,← innerSL_apply_apply ℂ,
    ContinuousLinearMap.map_tsum _ (summable_derivativeSzegoKernel w),Complex.conj_tsum]
  unfold derivativeSzegoValue
  apply tsum_congr
  intro n
  change conj (inner ℂ f (derivativeSzegoCoeff w n • hardyBasis n)) = _
  rw [inner_smul_right (𝕜 := ℂ) (E := Hardy),map_mul,← inner_conj_symm,
    ← HilbertBasis.repr_apply_apply,hardyBasis_repr_eq_fourierCoeff]
  simp only [derivativeSzegoCoeff,map_mul,map_add,map_natCast,map_one,map_pow,Complex.conj_conj]
  ring

theorem lintegral_weighted_radial_monomial (n : ℕ) :
    (∫⁻ r : ℝ, ENNReal.ofReal ((1-r^2)*r^(2*n)) ∂diskRadialMeasure) =
      ENNReal.ofReal (1/(((n : ℝ)+1)*((n : ℝ)+2))) := by
  have hI : Integrable (fun r : ℝ => (1-r^2)*r^(2*n)) diskRadialMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
      (by fun_prop : Continuous (fun r : ℝ => (1-r^2)*r^(2*n))).aestronglyMeasurable
    filter_upwards [ae_mem_diskRadialMeasure] with r hr
    have h0 : 0 ≤ 1-r^2 := by nlinarith [hr.1,hr.2]
    rw [norm_mul,Real.norm_of_nonneg h0,Real.norm_of_nonneg (pow_nonneg hr.1.le _)]
    calc
      _ ≤ 1*1 := mul_le_mul (by nlinarith [sq_nonneg r])
        (pow_le_one₀ hr.1.le hr.2.le) (pow_nonneg hr.1.le _) zero_le_one
      _ = 1 := by ring
  rw [← ofReal_integral_eq_lintegral_ofReal hI (by
    filter_upwards [ae_mem_diskRadialMeasure] with r hr
    exact mul_nonneg (by nlinarith [hr.1,hr.2]) (pow_nonneg hr.1.le _)),
    integral_weighted_radial_monomial]

/-- Weighted Bergman Parseval retains infinity and assumes only disk analyticity. -/
theorem analytic_weighted_disk_area_parseval (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) :
    (∫⁻ z, ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) ∂diskArea) =
      ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2 /
        (((n : ℝ)+1)*((n : ℝ)+2))) := by
  have hM : Measurable (disk.indicator
      (fun z => ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2))) := by
    classical
    change Measurable (disk.piecewise
      (fun z => ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2)) (fun _ => 0))
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.sub (continuous_norm.continuousOn.pow 2)).mul
        (hF.continuousOn.norm.pow 2))).measurable_piecewise continuousOn_const
          (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [lintegral_diskArea_polar _ hM]
  calc
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2*r)*
        (ENNReal.ofReal (1-r^2)*
          ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have he (t : Boundary) :
          ENNReal.ofReal ((1-‖(r : ℂ)*fourier (T := 1) 1 t‖^2)*
            ‖F ((r : ℂ)*fourier (T := 1) 1 t)‖^2) =
          ENNReal.ofReal (1-r^2)*ENNReal.ofReal
            (‖F ((r : ℂ)*fourier (T := 1) 1 t)‖^2) := by
        simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1.le,
          fourier_one,Circle.norm_coe,mul_one]
        exact ENNReal.ofReal_mul (by nlinarith [hr.1,hr.2])
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        analytic_radial_circle_parseval F hF r hr.1.le hr.2]
    _ = ∫⁻ r : ℝ, ENNReal.ofReal (1-r^2)*
          ∑' n : ℕ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2*r^(2*n))
        ∂diskRadialMeasure := by
      rw [diskRadialMeasure,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)]
      · rfl
      · exact (by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal (1-r^2))).mul
          (Measurable.tsum (fun n : ℕ => by fun_prop))
    _ = ∫⁻ r : ℝ, ∑' n : ℕ,
          ENNReal.ofReal (‖diskTaylorCoeff F n‖^2)*
            ENNReal.ofReal ((1-r^2)*r^(2*n)) ∂diskRadialMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_diskRadialMeasure] with r hr
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_mul (by nlinarith [hr.1,hr.2])]
      ring
    _ = ∑' n : ℕ, ∫⁻ r : ℝ, ENNReal.ofReal (‖diskTaylorCoeff F n‖^2)*
          ENNReal.ofReal ((1-r^2)*r^(2*n)) ∂diskRadialMeasure := by
      apply lintegral_tsum
      intro n
      exact (by fun_prop : Measurable (fun r : ℝ =>
        ENNReal.ofReal (‖diskTaylorCoeff F n‖^2)*
          ENNReal.ofReal ((1-r^2)*r^(2*n)))).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_weighted_radial_monomial,← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring

theorem derivativeSzegoValue_weighted_area_le (f : Hardy) :
    (∫⁻ z, ENNReal.ofReal ((1-‖z‖^2)*‖derivativeSzegoValue f.val z‖^2) ∂diskArea) ≤
      ENNReal.ofReal (‖f‖^2) := by
  rw [analytic_weighted_disk_area_parseval _ (analyticOnNhd_derivativeSzegoValue f.val)]
  have hs := hasSum_basis_inner_norm_sq hardyBasis f
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg
    (fun n => sq_nonneg ‖inner ℂ (hardyBasis n) f‖) hs.summable]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [diskTaylorCoeff_derivativeSzegoValue,norm_mul,
    show (n : ℂ)+1=((n+1 : ℕ) : ℂ) from by push_cast; rfl,Complex.norm_natCast,
    Nat.cast_add,Nat.cast_one,← hardyBasis_repr_eq_fourierCoeff,HilbertBasis.repr_apply_apply]
  apply ENNReal.ofReal_le_ofReal
  have hpos : 0 < ((n : ℝ)+1)*((n : ℝ)+2) := by positivity
  apply (div_le_iff₀ hpos).mpr
  nlinarith [sq_nonneg ‖inner ℂ (hardyBasis n) f‖]


theorem stronglyMeasurable_derivativeSzegoKernel :
    StronglyMeasurable derivativeSzegoKernel := by
  exact StronglyMeasurable.tsum (fun n : ℕ =>
    (by unfold derivativeSzegoCoeff; fun_prop : Continuous (fun w : Disk =>
      derivativeSzegoCoeff w n • hardyBasis n)).stronglyMeasurable)

def derivativeSzegoZero : ℂ → Hardy :=
  Function.extend (Subtype.val : Disk → ℂ) derivativeSzegoKernel (fun _ => 0)

theorem derivativeSzegoZero_on (w : Disk) :
    derivativeSzegoZero w.val = derivativeSzegoKernel w :=
  Subtype.val_injective.extend_apply _ _ w

theorem derivativeSzegoZero_off (z : ℂ) (hz : z ∉ disk) :
    derivativeSzegoZero z = 0 := by
  apply Function.extend_apply'
  rintro ⟨w,he⟩
  exact hz (he ▸ w.property)

theorem stronglyMeasurable_derivativeSzegoZero :
    StronglyMeasurable derivativeSzegoZero :=
  (MeasurableEmbedding.subtype_coe
    (isOpen_lt continuous_norm continuous_const).measurableSet).stronglyMeasurable_extend
      stronglyMeasurable_derivativeSzegoKernel stronglyMeasurable_const

/-- This measure absorbs the frame weight; its normalization is the actual π⁻¹ disk area. -/
def szegoFrameMeasure : Measure ℂ :=
  diskArea.withDensity (fun z => ENNReal.ofReal (1-‖z‖^2))

theorem derivativeSzegoZero_frame_lintegral (f : Hardy) :
    (∫⁻ z, ENNReal.ofReal (‖inner ℂ (derivativeSzegoZero z) f‖^2) ∂szegoFrameMeasure) ≤
      ENNReal.ofReal (‖f‖^2) := by
  have hM : StronglyMeasurable (fun z => inner ℂ (derivativeSzegoZero z) f) :=
    stronglyMeasurable_derivativeSzegoZero.inner stronglyMeasurable_const
  have hQ : Measurable (fun z => ENNReal.ofReal (‖inner ℂ (derivativeSzegoZero z) f‖^2)) := by
    simpa only [Pi.pow_apply] using ((hM.norm.pow 2).measurable.ennreal_ofReal)
  rw [szegoFrameMeasure,lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hQ]
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((1-‖z‖^2)*‖derivativeSzegoValue f.val z‖^2) ∂diskArea := by
      apply lintegral_congr_ae
      filter_upwards [ae_mem_diskArea] with z hz
      change ENNReal.ofReal (1-‖z‖^2)*ENNReal.ofReal (‖inner ℂ (derivativeSzegoZero z) f‖^2)=_
      rw [derivativeSzegoZero_on ⟨z,hz⟩,inner_derivativeSzegoKernel,
        ← ENNReal.ofReal_mul (by have hz1 : ‖z‖ < 1 := hz; nlinarith [norm_nonneg z])]
    _ ≤ _ := derivativeSzegoValue_weighted_area_le f


theorem derivativeSzegoZero_frame (f : Hardy) :
    MemLp (fun z => inner ℂ (derivativeSzegoZero z) f) 2 szegoFrameMeasure ∧
      (∫ z, ‖inner ℂ (derivativeSzegoZero z) f‖^2 ∂szegoFrameMeasure) ≤ ‖f‖^2 := by
  have hM : StronglyMeasurable (fun z => inner ℂ (derivativeSzegoZero z) f) :=
    stronglyMeasurable_derivativeSzegoZero.inner stronglyMeasurable_const
  have hI : Integrable (fun z => ‖inner ℂ (derivativeSzegoZero z) f‖^2) szegoFrameMeasure := by
    refine ⟨?_,?_⟩
    · simpa only [Pi.pow_apply] using! (hM.norm.pow 2).aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_norm]
      simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using
        (derivativeSzegoZero_frame_lintegral f).trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mpr hI,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖f‖)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun z => sq_nonneg ‖inner ℂ (derivativeSzegoZero z) f‖)]
  exact derivativeSzegoZero_frame_lintegral f

theorem measurePreserving_conj_diskArea :
    MeasurePreserving (conj : ℂ → ℂ) diskArea diskArea := by
  have hvol : MeasurePreserving (conj : ℂ → ℂ) volume volume := by
    simpa only using! Complex.conjLIE.measurePreserving
  have hp := hvol.restrict_preimage (s := disk)
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hs : (conj : ℂ → ℂ) ⁻¹' disk = disk := by
    ext z
    simp only [Set.mem_preimage,disk,Set.mem_ofPred_eq,Complex.norm_conj]
  rw [hs] at hp
  exact hp.smul_measure ((ENNReal.ofReal Real.pi)⁻¹)

theorem measurePreserving_conj_szegoFrameMeasure :
    MeasurePreserving (conj : ℂ → ℂ) szegoFrameMeasure szegoFrameMeasure := by
  refine ⟨Complex.continuous_conj.measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map' hf.aemeasurable Complex.continuous_conj.measurable.aemeasurable]
  have hfc : Measurable (fun z : ℂ => f (conj z)) := hf.comp Complex.continuous_conj.measurable
  rw [szegoFrameMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hfc,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  have he := measurePreserving_conj_diskArea.lintegral_comp
    (by fun_prop : Measurable (fun z : ℂ => ENNReal.ofReal (1-‖z‖^2)*f z))
  simpa only [Function.comp_def,Pi.mul_apply,Complex.norm_conj] using he

theorem derivativeSzegoZero_conj_frame (f : Hardy) :
    MemLp (fun z => inner ℂ (derivativeSzegoZero (conj z)) f) 2 szegoFrameMeasure ∧
      (∫ z, ‖inner ℂ (derivativeSzegoZero (conj z)) f‖^2 ∂szegoFrameMeasure) ≤ ‖f‖^2 := by
  obtain ⟨hLp,hB⟩ := derivativeSzegoZero_frame f
  refine ⟨hLp.comp_measurePreserving measurePreserving_conj_szegoFrameMeasure,?_⟩
  have hEmb : MeasurableEmbedding (conj : ℂ → ℂ) := by
    simpa only using! Complex.conjLIE.toHomeomorph.measurableEmbedding
  rw [measurePreserving_conj_szegoFrameMeasure.integral_comp hEmb
    (fun z => ‖inner ℂ (derivativeSzegoZero z) f‖^2)]
  exact hB


theorem stronglyMeasurable_derivativeSzegoZero_conj :
    StronglyMeasurable (fun z : ℂ => derivativeSzegoZero (conj z)) :=
  stronglyMeasurable_derivativeSzegoZero.comp_measurable Complex.continuous_conj.measurable


end TTO.Paper.Proved
