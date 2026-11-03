/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Portions of the radial convergence proof: Copyright (c) 2026 The Tau Ceti contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialMeaningFoundations
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Constructing native Hardy boundary representatives of bounded disk-analytic functions.
The intended final theorem uses AnalyticOnNhd on the OPEN disk and a uniform disk bound;
no boundary representative, Fatou theorem or pointwise boundary limit is assumed.
-/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The genuine Taylor coefficients, rather than a chosen boundary function. -/
def diskTaylorCoeff (F : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n F 0 / (n.factorial : ℂ)

theorem hasSum_diskTaylorCoeff (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    {z : ℂ} (hz : z ∈ disk) :
    HasSum (fun n : ℕ => diskTaylorCoeff F n * z ^ n) (F z) := by
  have hd : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1) :=
    hF.differentiableOn.mono (by
      intro w hw
      simpa only [disk, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using hw)
  have hs := Complex.hasSum_taylorSeries_on_ball hd
    (show z ∈ Metric.ball (0 : ℂ) 1 by simpa only [disk, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using hz)
  convert hs using 1
  funext n
  simp only [diskTaylorCoeff, sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Cauchy's estimate on any smaller positive radius gives a concrete coefficient bound. -/
theorem norm_diskTaylorCoeff_le_radius (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (R : ℝ) (hR : 0 < R) (hR1 : R < 1) (n : ℕ) :
    ‖diskTaylorCoeff F n‖ ≤ M / R ^ n := by
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ disk := by
    intro z hz
    exact lt_of_le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) hR1
  have hd := hF.differentiableOn.diffContOnCl_ball hsub
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hd
    (fun z hz => hM z (hsub (Metric.sphere_subset_closedBall hz)))
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  calc
    ‖diskTaylorCoeff F n‖ = ‖iteratedDeriv n F 0‖ / (n.factorial : ℝ) := by
      simp only [diskTaylorCoeff, norm_div, Complex.norm_natCast]
    _ ≤ ((n.factorial : ℝ) * M / R ^ n) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_right hc hn.le
    _ = M / R ^ n := by field_simp

/-- Taylor coefficients damped on a strictly smaller radius. -/
def diskRadialCoeff (F : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  diskTaylorCoeff F n * (r : ℂ) ^ n

theorem summable_norm_diskRadialCoeff (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖diskRadialCoeff F r n‖) := by
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hgeom : Summable (fun n : ℕ => M * (r / R) ^ n) :=
    (summable_geometric_of_lt_one (div_nonneg hr hR.le) ((div_lt_one hR).mpr hrR)).mul_left M
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hgeom
  calc
    ‖diskRadialCoeff F r n‖ = ‖diskTaylorCoeff F n‖ * r ^ n := by
      simp only [diskRadialCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]
    _ ≤ (M / R ^ n) * r ^ n :=
      mul_le_mul_of_nonneg_right (norm_diskTaylorCoeff_le_radius F hF M hM R hR hR1 n)
        (pow_nonneg hr n)
    _ = M * (r / R) ^ n := by rw [div_pow]; ring

/-- The actual H² radial Taylor series. -/
def diskRadialHardy (F : ℂ → ℂ) (r : ℝ) : Hardy :=
  ∑' n : ℕ, diskRadialCoeff F r n • hardyBasis n

theorem summable_diskRadialHardy (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => diskRadialCoeff F r n • hardyBasis n) := by
  refine Summable.of_norm_bounded (summable_norm_diskRadialCoeff F hF M hM r hr hr1) fun n => ?_
  rw [norm_smul, hardyBasis.orthonormal.norm_eq_one, mul_one]

theorem hardyBasis_repr_diskRadialHardy (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    hardyBasis.repr (diskRadialHardy F r) n = diskRadialCoeff F r n := by
  rw [HilbertBasis.repr_apply_apply, diskRadialHardy,
    ← innerSL_apply_apply ℂ, ContinuousLinearMap.map_tsum _ (summable_diskRadialHardy F hF M hM r hr hr1),
    tsum_eq_single n fun m hm => by
      rw [innerSL_apply_apply, inner_smul_right (𝕜 := ℂ) (E := Hardy),
        (orthonormal_iff_ite.mp hardyBasis.orthonormal n m).trans (ite_eq_right (Ne.symm hm)),
        mul_zero]]
  rw [innerSL_apply_apply, inner_smul_right (𝕜 := ℂ) (E := Hardy),
    inner_self_eq_one_of_norm_eq_one (hardyBasis.orthonormal.norm_eq_one n), mul_one]

/-- The radial Taylor vector has its literal continuous circle representative. -/
theorem diskRadialHardy_ae (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (diskRadialHardy F r).val =ᵐ[circleMeasure] fun t => F ((r : ℂ) * fourier (T := 1) 1 t) := by
  let g : ℕ → C(Boundary, ℂ) := fun n => diskRadialCoeff F r n • fourier (T := 1) (n : ℤ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_norm_diskRadialCoeff F hF M hM r hr hr1) fun n => ?_
    rw [norm_smul, fourier_norm, mul_one]
  have hcoe : (diskRadialHardy F r).val =
      ContinuousMap.toLp 2 circleMeasure ℂ (∑' n, g n) := by
    rw [diskRadialHardy, ← hardy.subtypeL_apply,
      ContinuousLinearMap.map_tsum _ (summable_diskRadialHardy F hF M hM r hr hr1),
      ContinuousLinearMap.map_tsum _ hg]
    congr 1
    funext n
    simp [g, coe_fourierBasis, hardyMode]
  rw [hcoe]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure (∑' n, g n)] with t ht
  rw [ht]
  refine (ContinuousMap.tsum_apply hg t).symm.trans ?_
  have hz : (r : ℂ) * fourier (T := 1) 1 t ∈ disk := by
    simpa only [disk, Set.mem_ofPred_eq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr, fourier_one, Circle.norm_coe, mul_one] using hr1
  have hs := hasSum_diskTaylorCoeff F hF hz
  rw [← hs.tsum_eq]
  congr 1
  funext n
  simp only [g, diskRadialCoeff, ContinuousMap.smul_apply, smul_eq_mul, fourier_apply,
    natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow, one_zsmul, mul_pow]
  ring

/-- Disk boundedness bounds every radial H² vector with the same constant. -/
theorem norm_diskRadialHardy_le (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖diskRadialHardy F r‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hM 0 (by norm_num [disk]))
  have hb : ∀ᵐ t ∂circleMeasure, ‖(diskRadialHardy F r).val t‖ ≤ M := by
    filter_upwards [diskRadialHardy_ae F hF M hM r hr hr1] with t ht
    rw [ht]
    apply hM
    simpa only [disk, Set.mem_ofPred_eq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr, fourier_one, Circle.norm_coe, mul_one] using hr1
  have hn := Lp.norm_le_of_ae_bound hM0 hb
  simpa [measureUnivNNReal] using hn

/-- Finite Bessel bounds survive the approach to the boundary, without assuming a boundary limit. -/
theorem sum_norm_sq_diskTaylorCoeff_le (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (s : Finset ℕ) :
    ∑ n ∈ s, ‖diskTaylorCoeff F n‖ ^ 2 ≤ M ^ 2 := by
  have hb (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
      ∑ n ∈ s, ‖diskRadialCoeff F r n‖ ^ 2 ≤ M ^ 2 := by
    have h := Orthonormal.sum_inner_products_le (diskRadialHardy F r)
      (s := s) hardyBasis.orthonormal
    simp_rw [← HilbertBasis.repr_apply_apply,
      hardyBasis_repr_diskRadialHardy F hF M hM r hr hr1] at h
    refine h.trans ?_
    have hn := norm_diskRadialHardy_le F hF M hM r hr hr1
    nlinarith [norm_nonneg (diskRadialHardy F r)]
  have hc : Continuous (fun r : ℝ => ∑ n ∈ s, ‖diskRadialCoeff F r n‖ ^ 2) := by
    unfold diskRadialCoeff
    fun_prop
  have hl : Tendsto (fun r : ℝ => ∑ n ∈ s, ‖diskRadialCoeff F r n‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (∑ n ∈ s, ‖diskTaylorCoeff F n‖ ^ 2)) := by
    simpa only [diskRadialCoeff, Complex.ofReal_one, one_pow, mul_one] using
      (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact hb r hr.1.le hr.2

/-- The native square-summable Taylor coefficient vector obtained by Bessel's inequality. -/
def diskTaylorLp (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨diskTaylorCoeff F, memℓp_gen' (C := M ^ 2) (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      sum_norm_sq_diskTaylorCoeff_le F hF M hM)⟩

/-- The H² vector reconstructed from the actual Taylor coefficients. -/
def boundedAnalyticHardy (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) : Hardy :=
  hardyBasis.repr.symm (diskTaylorLp F hF M hM)

@[simp] theorem hardyBasis_repr_boundedAnalyticHardy (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) (n : ℕ) :
    hardyBasis.repr (boundedAnalyticHardy F hF M hM) n = diskTaylorCoeff F n := by
  simp only [boundedAnalyticHardy, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The native Hardy basis coordinates are precisely the nonnegative Fourier coefficients. -/
theorem hardyBasis_repr_eq_fourierCoeff (f : Hardy) (n : ℕ) :
    hardyBasis.repr f n = fourierCoeff f.val (n : ℤ) := by
  rw [HilbertBasis.repr_apply_apply, hardyBasis_apply]
  change inner ℂ (fourierBasis (T := 1) (n : ℤ)) f.val = _
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- The reconstructed Hardy vector has exactly the original analytic disk function. -/
theorem analyticValue_boundedAnalyticHardy (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) {z : ℂ} (hz : z ∈ disk) :
    analyticValue (boundedAnalyticHardy F hF M hM).val z = F z := by
  unfold analyticValue
  simp_rw [← hardyBasis_repr_eq_fourierCoeff, hardyBasis_repr_boundedAnalyticHardy]
  exact (hasSum_diskTaylorCoeff F hF hz).tsum_eq

/-- Radial Taylor vectors converge strongly to the reconstructed Hardy boundary vector.
The dominated-coordinate argument follows the native Hilbert-basis proof pattern in
TauCeti's `Hardy/DiskFunction.lean` (Apache-2.0, revision d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad, inspected),
adapted to Taylor coefficients reconstructed above rather than an assumed boundary function. -/
theorem tendsto_diskRadialHardy (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) :
    Tendsto (diskRadialHardy F) (𝓝[<] (1 : ℝ)) (𝓝 (boundedAnalyticHardy F hF M hM)) := by
  let x := boundedAnalyticHardy F hF M hM
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) fun r hr => ⟨hr.1.le, hr.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun r => ‖diskRadialHardy F r - x‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[<] (1 : ℝ))
      (f := fun r (n : ℕ) => ‖((r : ℂ) ^ n - 1) * diskTaylorCoeff F n‖ ^ 2)
      (g := fun _ => 0) (bound := fun n : ℕ => ‖diskTaylorCoeff F n‖ ^ 2) ?_ ?_ ?_
    · rw [tsum_zero] at hdom
      refine hdom.congr' ?_
      filter_upwards [hev] with r hr
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hardyBasis.repr (diskRadialHardy F r - x))
      rw [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at h
      rw [h]
      congr 1
      funext n
      rw [Real.rpow_two, map_sub, lp.coeFn_sub, Pi.sub_apply,
        hardyBasis_repr_diskRadialHardy F hF M hM r hr.1 hr.2]
      simp only [x, hardyBasis_repr_boundedAnalyticHardy, diskRadialCoeff]
      ring_nf
    · simpa [diskTaylorLp, ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp (diskTaylorLp F hF M hM)).summable (by norm_num)
    · intro n
      have hc : Continuous fun r : ℝ => ‖((r : ℂ) ^ n - 1) * diskTaylorCoeff F n‖ ^ 2 := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [hev] with r hr n
      rw [norm_pow, norm_norm, norm_mul]
      have h1 : ‖(r : ℂ) ^ n - 1‖ ≤ 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [pow_le_one₀ hr.1 hr.2.le (n := n), pow_nonneg hr.1 n]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hroot := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using hroot

/-- The uniform disk bound passes to the actual reconstructed boundary vector.
Convergence in measure and the native essential-supremum lower-semicontinuity theorem
provide the L∞ bound; no pointwise boundary-value theorem is assumed. -/
theorem boundedAnalyticHardy_ae_bound (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) :
    ∀ᵐ t ∂circleMeasure, ‖(boundedAnalyticHardy F hF M hM).val t‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hM 0 (by norm_num [disk]))
  have ht : Tendsto (fun r : ℝ => (diskRadialHardy F r).val)
      (𝓝[<] (1 : ℝ)) (𝓝 (boundedAnalyticHardy F hF M hM).val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_diskRadialHardy F hF M hM)
  have hb : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      eLpNorm (diskRadialHardy F r).val ∞ circleMeasure ≤ ENNReal.ofReal M := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [diskRadialHardy_ae F hF M hM r hr.1.le hr.2] with t ht
    rw [ht]
    apply hM
    simpa only [disk, Set.mem_ofPred_eq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.1.le, fourier_one, Circle.norm_coe, mul_one] using hr.2
  have hnorm := eLpNorm_le_of_tendstoInMeasure hb
    (tendstoInMeasure_of_tendsto_Lp ht) (fun r => Lp.aestronglyMeasurable (diskRadialHardy F r).val)
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)] at hnorm
  filter_upwards [ae_le_eLpNormEssSup (f := (boundedAnalyticHardy F hF M hM).val)] with t ht
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ht.trans hnorm)
  simpa only [ENNReal.toReal_ofReal hM0, toReal_enorm] using h

/-- Every uniformly bounded analytic function on the open disk has an actual native L∞
Hardy boundary representative with the original point evaluations and the same bound. -/
theorem exists_boundedAnalyticBoundary (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) :
    ∃ φ : BoundaryLInf, toL2 φ ∈ hardy ∧
      (∀ z ∈ disk, innerValue φ z = F z) ∧
      (∀ᵐ t ∂circleMeasure, ‖φ t‖ ≤ M) ∧ ‖φ‖ ≤ M := by
  let x := boundedAnalyticHardy F hF M hM
  have hb := boundedAnalyticHardy_ae_bound F hF M hM
  have htop : MemLp x.val ∞ circleMeasure := memLp_top_of_bound (Lp.aestronglyMeasurable _) M hb
  let φ : BoundaryLInf := htop.toLp x.val
  have he : toL2 φ = x.val := Lp.ext ((toL2_ae φ).trans htop.coeFn_toLp)
  have hφ : ∀ᵐ t ∂circleMeasure, ‖φ t‖ ≤ M := by
    filter_upwards [htop.coeFn_toLp, hb] with t ht hbt
    rw [ht]
    exact hbt
  refine ⟨φ, he ▸ x.property, ?_, hφ, ?_⟩
  · intro z hz
    change analyticValue (toL2 φ) z = F z
    rw [he]
    exact analyticValue_boundedAnalyticHardy F hF M hM hz
  · have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hM 0 (by norm_num [disk]))
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hM0 hφ

end TTO.Paper.Proved
