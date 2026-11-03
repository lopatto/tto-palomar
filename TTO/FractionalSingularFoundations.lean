/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SingleAtomConstruction
public import TTO.AtomicPolynomialFoundations
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual fractional singular-inner boundary functions, reconstructed in the native Hardy space. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal finite-measure Herglotz integral occurring in the manuscript's singular factor. -/
def singularHerglotzIntegral (μ : Measure Boundary) (z : ℂ) : ℂ :=
  ∫ t, (fourier (T := 1) 1 t + z) / (fourier (T := 1) 1 t - z) ∂μ

/-- Differentiation under this finite-measure integral uses a uniform smaller-disk bound. -/
theorem hasDerivAt_singularHerglotzIntegral (μ : Measure Boundary) [IsFiniteMeasure μ]
    (z : Disk) : HasDerivAt (singularHerglotzIntegral μ)
      (∫ t, 2 * fourier (T := 1) 1 t / (fourier (T := 1) 1 t - z.val) ^ 2 ∂μ) z.val := by
  let R : ℝ := (‖z.val‖ + 1) / 2
  have hz : ‖z.val‖ < 1 := z.property
  have hR : ‖z.val‖ < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hd : 0 < 1 - R := sub_pos.mpr hR1
  have hden (t : Boundary) (x : ℂ) (hx : x ∈ Metric.ball (0 : ℂ) R) :
      1 - R ≤ ‖fourier (T := 1) 1 t - x‖ := by
    have h := norm_sub_norm_le (fourier (T := 1) 1 t) x
    have hx' : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    have he : ‖fourier (T := 1) 1 t‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
    rw [he] at h
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => (fourier (T := 1) 1 t + x) / (fourier (T := 1) 1 t - x))
    (F' := fun x t => 2 * fourier (T := 1) 1 t / (fourier (T := 1) 1 t - x) ^ 2)
    (bound := fun _ => 2 / (1 - R) ^ 2)
    (Metric.isOpen_ball.mem_nhds (show z.val ∈ Metric.ball (0 : ℂ) R by
      simpa only [Metric.mem_ball, dist_zero_right] using hR))
    ?_ (herglotz_integrable μ z) ?_ ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall fun x => (show Measurable (fun t : Boundary =>
      (fourier (T := 1) 1 t + x) / (fourier (T := 1) 1 t - x)) by fun_prop).aestronglyMeasurable
  · exact (show Measurable (fun t : Boundary =>
      2 * fourier (T := 1) 1 t / (fourier (T := 1) 1 t - z.val) ^ 2) by fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun t x hx => by
      rw [norm_div, norm_mul, norm_pow]
      simp only [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
        show ‖fourier (T := 1) 1 t‖ = 1 by simp only [fourier_apply, Circle.norm_coe], mul_one]
      exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hd)
        (pow_le_pow_left₀ hd.le (hden t x hx) 2)
  · exact Eventually.of_forall fun t x hx => by
      have hne : fourier (T := 1) 1 t - x ≠ 0 :=
        norm_pos_iff.mp (hd.trans_le (hden t x hx))
      have h := ((hasDerivAt_id' x).const_add (fourier (T := 1) 1 t)).div
        ((hasDerivAt_id' x).const_sub (fourier (T := 1) 1 t)) hne
      convert h using 1; simp only [one_mul, mul_neg, mul_one, sub_neg_eq_add]
      congr 1
      ring

/-- The explicit singular-inner disk formula is analytic for every real exponent. -/
theorem analyticOnNhd_singularInnerValue (μ : Measure Boundary) [IsFiniteMeasure μ] (r : ℝ) :
    AnalyticOnNhd ℂ (singularInnerValue μ r) disk := by
  have ha : AnalyticOnNhd ℂ (singularHerglotzIntegral μ) disk := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      exact (hasDerivAt_singularHerglotzIntegral μ ⟨z, hz⟩).differentiableAt.differentiableWithinAt
    · exact isOpen_lt continuous_norm continuous_const
  intro z hz
  exact (analyticAt_const.mul (ha z hz)).cexp'

/-- The modulus of the actual exponential scales by the real power, without a branch choice. -/
theorem norm_singularInnerValue_rpow (μ : Measure Boundary) (r : ℝ) (z : ℂ) :
    ‖singularInnerValue μ r z‖ = ‖singularInnerValue μ 1 z‖ ^ r := by
  unfold singularInnerValue
  simp only [Complex.ofReal_one, neg_one_mul, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]
  rw [← Real.exp_mul]
  congr 1
  ring

/-- The given singular representation determines the modulus of every positive fractional factor. -/
theorem norm_fractionalSingular_eq_rpow (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasSingularRepresentation u μ) (r : ℝ) {z : ℂ} (hz : z ∈ disk) :
    ‖singularInnerValue μ r z‖ = ‖innerValue u z‖ ^ r := by
  obtain ⟨α, hα, hval⟩ := hμ.2
  rw [norm_singularInnerValue_rpow, hval z hz, norm_mul, hα, one_mul]

/-- The existing Taylor reconstruction is literally the boundary vector, with no replacement definition. -/
theorem analyticBoundary_eq_boundedAnalyticHardy (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M) :
    analyticBoundary F = (boundedAnalyticHardy F hF M hM).val := by
  let x := boundedAnalyticHardy F hF M hM
  have hs := hardyBasis.hasSum_repr x
  have hsum := hs.mapL hardy.subtypeL
  have he : (fun n : ℕ => hardy.subtypeL (hardyBasis.repr x n • hardyBasis n)) =
      (fun n : ℕ => diskTaylorCoeff F n • fourierBasis (T := 1) (n : ℤ)) := by
    funext n
    simp only [map_smul, x, hardyBasis_repr_boundedAnalyticHardy, hardyBasis_apply]
    rfl
  rw [he] at hsum
  exact hsum.tsum_eq

/-- Simultaneous a.e. radial subsequences transfer the given inner boundary modulus to a
bounded analytic function whose disk modulus is a real power of that inner function. -/
theorem boundedAnalyticHardy_unimodular_of_norm_rpow
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (hM : ∀ z ∈ disk, ‖F z‖ ≤ 1) (u : BoundaryLInf) (hu : IsInner u) (r : ℝ)
    (hrel : ∀ z ∈ disk, ‖F z‖ = ‖innerValue u z‖ ^ r) :
    ∀ᵐ t ∂circleMeasure, ‖(boundedAnalyticHardy F hF 1 hM).val t‖ = 1 := by
  let uh : Hardy := ⟨toL2 u, hu.1⟩
  have htu : Tendsto (fun a : ℝ => (hardyRadialBoundary uh a).val)
      (𝓝[<] (1 : ℝ)) (𝓝 uh.val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_hardyRadialBoundary uh)
  obtain ⟨s, hs, hsu⟩ := (tendstoInMeasure_of_tendsto_Lp htu).exists_seq_tendsto_ae'
  have htx : Tendsto (fun a : ℝ => (diskRadialHardy F a).val)
      (𝓝[<] (1 : ℝ)) (𝓝 (boundedAnalyticHardy F hF 1 hM).val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_diskRadialHardy F hF 1 hM)
  obtain ⟨k, hk, hkx⟩ := (tendstoInMeasure_of_tendsto_Lp (htx.comp hs)).exists_seq_tendsto_ae
  have heq (a : ℝ) : ∀ᵐ t ∂circleMeasure, 0 ≤ a ∧ a < 1 →
      ‖(diskRadialHardy F a).val t‖ = ‖(hardyRadialBoundary uh a).val t‖ ^ r := by
    by_cases ha : 0 ≤ a ∧ a < 1
    · filter_upwards [diskRadialHardy_ae F hF 1 hM a ha.1 ha.2,
        hardyRadialBoundary_ae uh a ha.1 ha.2] with t hft hut _
      rw [hft, hut]
      change ‖F ((a : ℂ) * fourier (T := 1) 1 t)‖ =
        ‖innerValue u ((a : ℂ) * fourier (T := 1) 1 t)‖ ^ r
      apply hrel
      simpa only [disk, Set.mem_ofPred_eq, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ha.1, fourier_one, Circle.norm_coe, mul_one] using ha.2
    · exact Eventually.of_forall fun _ ha' => (ha ha').elim
  have heqa : ∀ᵐ t ∂circleMeasure, ∀ n : ℕ, 0 ≤ s (k n) ∧ s (k n) < 1 →
      ‖(diskRadialHardy F (s (k n))).val t‖ =
        ‖(hardyRadialBoundary uh (s (k n))).val t‖ ^ r :=
    ae_all_iff.mpr fun n => heq (s (k n))
  have hgood := (hs.comp hk.tendsto_atTop).eventually
    (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsu, hkx, heqa, toL2_ae u, hu.2] with t hut hxt het hto hunit
  have hulim : Tendsto (fun n => ‖(hardyRadialBoundary uh (s (k n))).val t‖)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_apply, uh, hto, hunit] using (hut.comp hk.tendsto_atTop).norm
  have hp : Tendsto (fun n => ‖(hardyRadialBoundary uh (s (k n))).val t‖ ^ r)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.one_rpow] using hulim.rpow_const (p := r) (Or.inl one_ne_zero)
  have hxlim : Tendsto (fun n => ‖(diskRadialHardy F (s (k n))).val t‖)
      atTop (𝓝 (1 : ℝ)) := by
    apply hp.congr'
    filter_upwards [hgood] with n hn
    exact (het n ⟨hn.1.le, hn.2⟩).symm
  exact tendsto_nhds_unique hxt.norm hxlim

/-- An actual positive fractional singular-inner boundary factor with the Taylor-L² meaning.
The only mathematical premises are the given inner function and its manuscript representation. -/
theorem exists_fractionalSingularBoundary (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (r : ℝ) (hr : 0 < r) :
    ∃ v : BoundaryLInf, IsInner v ∧
      (∀ z ∈ disk, innerValue v z = singularInnerValue μ r z) ∧
      toL2 v = analyticBoundary (singularInnerValue μ r) := by
  let : IsFiniteMeasure μ := ⟨hμ.1.1⟩
  let F := singularInnerValue μ r
  have hF : AnalyticOnNhd ℂ F disk := analyticOnNhd_singularInnerValue μ r
  have hrel : ∀ z ∈ disk, ‖F z‖ = ‖innerValue u z‖ ^ r :=
    fun z hz => norm_fractionalSingular_eq_rpow u μ hμ r hz
  have hM : ∀ z ∈ disk, ‖F z‖ ≤ 1 := by
    intro z hz
    rw [hrel z hz]
    exact Real.rpow_le_one (norm_nonneg _) (norm_innerValue_le_one u hu ⟨z, hz⟩) hr.le
  let x := boundedAnalyticHardy F hF 1 hM
  have hbound := boundedAnalyticHardy_ae_bound F hF 1 hM
  have htop : MemLp x.val ∞ circleMeasure :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) 1 hbound
  let v : BoundaryLInf := htop.toLp x.val
  have he : toL2 v = x.val := Lp.ext ((toL2_ae v).trans htop.coeFn_toLp)
  have hunit := boundedAnalyticHardy_unimodular_of_norm_rpow F hF hM u hu r hrel
  refine ⟨v, ⟨he ▸ x.property, ?_⟩, ?_, ?_⟩
  · filter_upwards [htop.coeFn_toLp, hunit] with t ht hnorm
    rw [ht]
    exact hnorm
  · intro z hz
    change analyticValue (toL2 v) z = F z
    rw [he]
    exact analyticValue_boundedAnalyticHardy F hF 1 hM hz
  · exact he.trans (analyticBoundary_eq_boundedAnalyticHardy F hF 1 hM).symm

/-- The literal singular exponential obeys addition of exponents, including exponent zero. -/
theorem singularInnerValue_add (μ : Measure Boundary) (r s : ℝ) (z : ℂ) :
    singularInnerValue μ (r + s) z = singularInnerValue μ r z * singularInnerValue μ s z := by
  unfold singularInnerValue
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem singularInnerValue_zero (μ : Measure Boundary) (z : ℂ) :
    singularInnerValue μ 0 z = 1 := by simp only [singularInnerValue, Complex.ofReal_zero, neg_zero,
      zero_mul, Complex.exp_zero]

/-- Natural powers are exact, including the constant-one base case. -/
theorem singularInnerValue_nat_mul (μ : Measure Boundary) (r : ℝ) (n : ℕ) (z : ℂ) :
    singularInnerValue μ ((n : ℝ) * r) z = singularInnerValue μ r z ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, singularInnerValue_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, singularInnerValue_add, ih, pow_succ]

/-- Native bounded Hardy boundary symbols are determined by their actual disk evaluations. -/
theorem hardyBoundary_ext (a b : BoundaryLInf) (ha : toL2 a ∈ hardy) (hb : toL2 b ∈ hardy)
    (heval : ∀ z ∈ disk, innerValue a z = innerValue b z) : a = b := by
  have he : toL2 a = toL2 b := congrArg Subtype.val
    (hardy_analyticValue_injective ⟨toL2 a, ha⟩ ⟨toL2 b, hb⟩ heval)
  apply Lp.ext
  filter_upwards [toL2_ae a, toL2_ae b] with t hat hbt
  rw [← hat, ← hbt, he]

/-- Any actual fractional boundary representatives multiply according to exponent addition. -/
theorem fractionalSingularBoundary_product (μ : Measure Boundary) (r s : ℝ)
    (v w x : BoundaryLInf) (hv : IsInner v) (hw : IsInner w) (hx : IsInner x)
    (hvalv : ∀ z ∈ disk, innerValue v z = singularInnerValue μ r z)
    (hvalw : ∀ z ∈ disk, innerValue w z = singularInnerValue μ s z)
    (hvalx : ∀ z ∈ disk, innerValue x z = singularInnerValue μ (r + s) z) :
    multiplyInf v w = x := by
  apply hardyBoundary_ext _ _ (isInner_multiplyInf v w hv hw).1 hx.1
  intro z hz
  rw [innerValue_multiplyInf v w hv.1 hw.1 ⟨z, hz⟩,
    hvalv z hz, hvalw z hz, hvalx z hz, singularInnerValue_add]

end TTO.Paper.Proved
