/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticAreaSubmeanFoundations

/-! Infinity-preserving weighted analytic derivative raising from actual local Lp smoothing.
No reverse derivative-order or Besov characterization is asserted here. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric Real
open scoped ENNReal NNReal Topology
namespace TTO.Paper.Proved

/-- Literal Euclidean distance to the unit circle, positive precisely inside the disk. -/
def diskBoundaryDistance (z : ℂ) : ℝ := 1 - ‖z‖

@[fun_prop] theorem continuous_diskBoundaryDistance : Continuous diskBoundaryDistance := by
  unfold diskBoundaryDistance
  fun_prop

/-- The actual power weight is extended by zero outside the open disk. -/
def diskBoundaryWeight (α : ℝ) (z : ℂ) : ℝ≥0∞ := by
  classical
  exact if z ∈ disk then ENNReal.ofReal (diskBoundaryDistance z ^ α) else 0

/-- The local averaging kernel is supported at half the actual boundary distance. -/
def diskLocalAreaKernel (α : ℝ) (z x : ℂ) : ℝ≥0∞ :=
  if dist x z < diskBoundaryDistance z / 2 then diskBoundaryWeight (α - 2) z else 0

theorem diskBoundaryDistance_pos {z : ℂ} (hz : z ∈ disk) : 0 < diskBoundaryDistance z := by
  have hz1 : ‖z‖ < 1 := hz
  dsimp [diskBoundaryDistance]
  linarith

theorem measurable_diskBoundaryWeight (α : ℝ) : Measurable (diskBoundaryWeight α) := by
  classical
  have hC : ContinuousOn (fun z : ℂ => ENNReal.ofReal (diskBoundaryDistance z ^ α)) disk :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((by fun_prop : Continuous (diskBoundaryDistance)).continuousOn.rpow_const
        (fun z hz => Or.inl (diskBoundaryDistance_pos hz).ne'))
  exact hC.measurable_piecewise continuousOn_const
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem measurable_diskLocalAreaKernel (α : ℝ) :
    Measurable (fun q : ℂ × ℂ => diskLocalAreaKernel α q.1 q.2) := by
  have hs : MeasurableSet {q : ℂ × ℂ | dist q.2 q.1 < diskBoundaryDistance q.1 / 2} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  exact ((measurable_diskBoundaryWeight (α - 2)).comp measurable_fst).piecewise hs measurable_const

/-- Comparable positive bases have comparable arbitrary real powers. -/
theorem rpow_le_two_abs_mul {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hl : s / 2 ≤ r) (hu : r ≤ 2 * s) (α : ℝ) :
    r ^ α ≤ (2 : ℝ) ^ |α| * s ^ α := by
  by_cases hα : 0 ≤ α
  · calc
      _ ≤ (2*s) ^ α := Real.rpow_le_rpow hr.le hu hα
      _ = _ := by rw [Real.mul_rpow (by norm_num) hs.le, abs_of_nonneg hα]
  · have hα0 : α < 0 := lt_of_not_ge hα
    calc
      _ ≤ (s/2) ^ α := Real.rpow_le_rpow_of_nonpos (by positivity) hl hα0.le
      _ = _ := by
        rw [Real.div_rpow hs.le (by norm_num), abs_of_neg hα0,
          Real.rpow_neg (by norm_num)]
        ring

/-- Actual incidence implies disk membership, comparable boundary distances, and reverse support. -/
theorem diskLocalArea_incidence {z x : ℂ} (hz : z ∈ disk)
    (h : dist x z < diskBoundaryDistance z / 2) :
    x ∈ disk ∧ diskBoundaryDistance x / 2 ≤ diskBoundaryDistance z ∧
      diskBoundaryDistance z ≤ 2 * diskBoundaryDistance x ∧
        z ∈ ball x (diskBoundaryDistance x) := by
  have hz1 : ‖z‖ < 1 := hz
  have hnx : ‖x‖ ≤ dist x z + ‖z‖ := by
    simpa only [dist_zero_right] using dist_triangle x z (0 : ℂ)
  have hnz : ‖z‖ ≤ dist x z + ‖x‖ := by
    simpa only [dist_zero_right, dist_comm z x] using dist_triangle z x (0 : ℂ)
  dsimp [diskBoundaryDistance] at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖x‖ < 1
    linarith
  · linarith
  · linarith
  · rw [mem_ball, dist_comm]
    linarith

/-- The explicit unit-ball volume is finite; no formula involving Γ is needed. -/
theorem volume_unitDisk_ne_top : volume (ball (0 : ℂ) 1) ≠ ∞ :=
  measure_ball_lt_top.ne

/-- The reverse local-area kernel has a uniform weighted integral, including all real exponents. -/
theorem lintegral_diskLocalAreaKernel_le (α : ℝ) (x : ℂ) :
    (∫⁻ z, diskLocalAreaKernel α z x) ≤
      volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
        diskBoundaryWeight α x := by
  classical
  by_cases hx : x ∈ disk
  · have hxD := diskBoundaryDistance_pos hx
    have hp (z : ℂ) : diskLocalAreaKernel α z x ≤
        (ball x (diskBoundaryDistance x)).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ |α - 2| * diskBoundaryDistance x ^ (α - 2))) z := by
      by_cases hz : z ∈ disk
      · by_cases h : dist x z < diskBoundaryDistance z / 2
        · obtain ⟨_, hl, hu, hrev⟩ := diskLocalArea_incidence hz h
          simp only [diskLocalAreaKernel, ite_eq_left h, diskBoundaryWeight, ite_eq_left hz,
            indicator_of_mem hrev]
          exact ENNReal.ofReal_le_ofReal
            (rpow_le_two_abs_mul (diskBoundaryDistance_pos hz) hxD hl hu (α - 2))
        · simp only [diskLocalAreaKernel, ite_eq_right h, zero_le]
      · simp only [diskLocalAreaKernel, diskBoundaryWeight, ite_eq_right hz, ite_self, zero_le]
    calc
      _ ≤ ∫⁻ z, (ball x (diskBoundaryDistance x)).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ |α - 2| * diskBoundaryDistance x ^ (α - 2))) z :=
        lintegral_mono hp
      _ = ENNReal.ofReal ((2 : ℝ) ^ |α - 2| * diskBoundaryDistance x ^ (α - 2)) *
          volume (ball x (diskBoundaryDistance x)) := by
        rw [lintegral_indicator measurableSet_ball, lintegral_const, Measure.restrict_apply_univ]
      _ = _ := by
        rw [Measure.addHaar_ball_of_pos volume x hxD, Complex.finrank_real_complex,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hxD.le,
          diskBoundaryWeight, ite_eq_left hx]
        have hpw : diskBoundaryDistance x ^ (α - 2) * diskBoundaryDistance x ^ (2 : ℝ) =
            diskBoundaryDistance x ^ α := by
          rw [← Real.rpow_add hxD]
          congr 1
          ring
        have he : ENNReal.ofReal (diskBoundaryDistance x ^ (α - 2)) *
            ENNReal.ofReal (diskBoundaryDistance x) ^ 2 =
              ENNReal.ofReal (diskBoundaryDistance x ^ α) := by
          rw [← ENNReal.ofReal_pow hxD.le, ← ENNReal.ofReal_mul (by positivity),
            ← Real.rpow_natCast]
          norm_num only [Nat.cast_ofNat]
          rw [hpw]
        calc
          _ = volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
              (ENNReal.ofReal (diskBoundaryDistance x ^ (α - 2)) *
                ENNReal.ofReal (diskBoundaryDistance x) ^ 2) := by ring
          _ = _ := by rw [he]
  · have hzero (z : ℂ) : diskLocalAreaKernel α z x = 0 := by
      by_cases hz : z ∈ disk
      · by_cases h : dist x z < diskBoundaryDistance z / 2
        · exact (hx (diskLocalArea_incidence hz h).1).elim
        · simp only [diskLocalAreaKernel, ite_eq_right h]
      · simp only [diskLocalAreaKernel, diskBoundaryWeight, ite_eq_right hz, ite_self]
    simp only [hzero, lintegral_zero, diskBoundaryWeight, ite_eq_right hx, mul_zero, le_refl]

/-- Tonelli converts the proved reverse-kernel integral into a genuine weighted area bound.
The nonnegative input may have infinite integral. -/
theorem lintegral_disk_local_area_weighted_le (U : ℂ → ℝ≥0∞) (hU : Measurable U) (α : ℝ) :
    (∫⁻ z, diskBoundaryWeight (α - 2) z *
      ∫⁻ x in ball z (diskBoundaryDistance z / 2), U x) ≤
        volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
          ∫⁻ x, U x * diskBoundaryWeight α x := by
  classical
  have hK (z : ℂ) : (∫⁻ x, U x * diskLocalAreaKernel α z x) =
      diskBoundaryWeight (α - 2) z *
        ∫⁻ x in ball z (diskBoundaryDistance z / 2), U x := by
    have he : (fun x => U x * diskLocalAreaKernel α z x) =
        (ball z (diskBoundaryDistance z / 2)).indicator
          (fun x => U x * diskBoundaryWeight (α - 2) z) := by
      funext x
      by_cases hx : dist x z < diskBoundaryDistance z / 2
      · simp only [diskLocalAreaKernel, ite_eq_left hx,
          indicator_of_mem (show x ∈ ball z (diskBoundaryDistance z / 2) from hx)]
      · simp only [diskLocalAreaKernel, ite_eq_right hx, mul_zero,
          indicator_of_notMem (show x ∉ ball z (diskBoundaryDistance z / 2) from hx)]
    rw [he, lintegral_indicator measurableSet_ball]
    have hW : diskBoundaryWeight (α - 2) z ≠ ∞ := by
      unfold diskBoundaryWeight
      split_ifs <;> simp
    rw [lintegral_mul_const' (diskBoundaryWeight (α - 2) z) U hW, mul_comm]
  calc
    _ = ∫⁻ z, ∫⁻ x, U x * diskLocalAreaKernel α z x :=
      lintegral_congr fun z => (hK z).symm
    _ = ∫⁻ x, ∫⁻ z, U x * diskLocalAreaKernel α z x := by
      apply lintegral_lintegral_swap
      exact ((hU.comp measurable_snd).mul (measurable_diskLocalAreaKernel α)).aemeasurable
    _ = ∫⁻ x, U x * ∫⁻ z, diskLocalAreaKernel α z x := by
      apply lintegral_congr
      intro x
      exact lintegral_const_mul (U x) ((measurable_diskLocalAreaKernel α).comp
        (measurable_id.prodMk measurable_const))
    _ ≤ ∫⁻ x, U x * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
          diskBoundaryWeight α x) :=
      lintegral_mono fun x => mul_le_mul_right (lintegral_diskLocalAreaKernel_le α x) (U x)
    _ = _ := by
      simp_rw [show ∀ x, U x * (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
          diskBoundaryWeight α x) =
          (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|)) *
            (U x * diskBoundaryWeight α x) from fun x => by ring]
      exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top volume_unitDisk_ne_top ENNReal.ofReal_ne_top)

/-- The literal local Cauchy constant, before weighted area integration. -/
def analyticDerivativeLocalConstant (p : ℝ) (n : ℕ) : ℝ :=
  (16 / Real.pi) * (((n.factorial : ℝ) * 4^n) ^ p)

theorem analyticDerivativeLocalConstant_pos (p : ℝ) (n : ℕ) :
    0 < analyticDerivativeLocalConstant p n := by
  unfold analyticDerivativeLocalConstant
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  positivity

/-- All boundary-distance factors cancel exactly before any finite-energy conversion. -/
theorem analyticDerivativeLocalConstant_identity {d : ℝ} (hd : 0 < d)
    (p α : ℝ) (n : ℕ) :
    (((n.factorial : ℝ) / (d/4)^n) ^ p * (Real.pi * (d/4)^2)⁻¹) *
        d ^ (α + (n : ℝ)*p) =
      analyticDerivativeLocalConstant p n * d ^ (α - 2) := by
  have hn : 0 ≤ (n.factorial : ℝ) := by positivity
  have hfrac : (n.factorial : ℝ) / (d/4)^n = ((n.factorial : ℝ)*4^n) / d^n := by
    rw [div_pow]
    field_simp
  have hpower : (((n.factorial : ℝ)*4^n) / d^n)^p =
      (((n.factorial : ℝ)*4^n)^p) / d^((n : ℝ)*p) := by
    rw [Real.div_rpow (by positivity) (pow_nonneg hd.le n),
      ← Real.rpow_natCast d n, ← Real.rpow_mul hd.le]
  have hw : d^(α + (n : ℝ)*p) = d^(α - 2) * d^((n : ℝ)*p) * d^2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  rw [hfrac, hpower, hw]
  unfold analyticDerivativeLocalConstant
  have hdp : d ^ ((n : ℝ)*p) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-- The analytic norm power is literally zero-extended; no global measurability is assumed. -/
def analyticPowerZero (F : ℂ → ℂ) (p : ℝ) (z : ℂ) : ℝ≥0∞ := by
  classical
  exact if z ∈ disk then ENNReal.ofReal (‖F z‖ ^ p) else 0

theorem measurable_analyticPowerZero (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (p : ℝ) (hp : 0 ≤ p) : Measurable (analyticPowerZero F p) := by
  classical
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (hF.continuousOn.norm.rpow_const (fun _ _ => Or.inr hp))).measurable_piecewise
      continuousOn_const (isOpen_lt continuous_norm continuous_const).measurableSet

/-- The actual local derivative estimate is transferred to nonnegative lower integrals
using only proved ordinary integrability on the strictly interior local ball. -/
theorem analytic_derivative_weighted_pointwise (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (p : ℝ) (hp : 0 < p) (n : ℕ) (α : ℝ) (z : ℂ) :
    analyticPowerZero (iteratedDeriv n F) p z * diskBoundaryWeight (α + (n : ℝ)*p) z ≤
      ENNReal.ofReal (analyticDerivativeLocalConstant p n) * diskBoundaryWeight (α - 2) z *
        ∫⁻ x in ball z (diskBoundaryDistance z / 2), analyticPowerZero F p x := by
  classical
  by_cases hz : z ∈ disk
  · have hd := diskBoundaryDistance_pos hz
    have hR : 2 * analyticLocalRadius (⟨z, hz⟩ : Disk) = diskBoundaryDistance z / 2 := by
      dsimp [analyticLocalRadius, diskBoundaryDistance]
      ring
    have hclosed := closedBall_twice_analyticLocalRadius_subset_disk (⟨z, hz⟩ : Disk)
    rw [hR] at hclosed
    have hI := (integrableOn_analytic_norm_rpow_closedBall F z (diskBoundaryDistance z / 2) p
      (hF.mono hclosed) hp.le).mono_set ball_subset_closedBall
    have hUI : ENNReal.ofReal (∫ x in ball z (diskBoundaryDistance z / 2), ‖F x‖ ^ p) =
        ∫⁻ x in ball z (diskBoundaryDistance z / 2), analyticPowerZero F p x := by
      rw [ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      simp only [analyticPowerZero, ite_eq_left (hclosed (ball_subset_closedBall hx))]
    have hlocal := analytic_iteratedDeriv_rpow_le_disk_local_area F hF (⟨z, hz⟩ : Disk) p n hp
    rw [hR] at hlocal
    change ‖iteratedDeriv n F z‖ ^ p ≤
      ((n.factorial : ℝ) / (diskBoundaryDistance z / 4)^n)^p *
        ((Real.pi * (diskBoundaryDistance z / 4)^2)⁻¹ *
          ∫ x in ball z (diskBoundaryDistance z / 2), ‖F x‖ ^ p) at hlocal
    have hreal : ‖iteratedDeriv n F z‖ ^ p * diskBoundaryDistance z ^ (α + (n : ℝ)*p) ≤
        (analyticDerivativeLocalConstant p n * diskBoundaryDistance z ^ (α - 2)) *
          ∫ x in ball z (diskBoundaryDistance z / 2), ‖F x‖ ^ p := by
      calc
        _ ≤ (((n.factorial : ℝ) / (diskBoundaryDistance z / 4)^n)^p *
            ((Real.pi * (diskBoundaryDistance z / 4)^2)⁻¹ *
              ∫ x in ball z (diskBoundaryDistance z / 2), ‖F x‖ ^ p)) *
            diskBoundaryDistance z ^ (α + (n : ℝ)*p) :=
          mul_le_mul_of_nonneg_right hlocal (Real.rpow_nonneg hd.le _)
        _ = ((((n.factorial : ℝ) / (diskBoundaryDistance z / 4)^n)^p *
            (Real.pi * (diskBoundaryDistance z / 4)^2)⁻¹) *
              diskBoundaryDistance z ^ (α + (n : ℝ)*p)) *
            ∫ x in ball z (diskBoundaryDistance z / 2), ‖F x‖ ^ p := by ring
        _ = _ := by rw [analyticDerivativeLocalConstant_identity hd p α n]
    simp only [analyticPowerZero, diskBoundaryWeight, ite_eq_left hz]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (analyticDerivativeLocalConstant_pos p n).le
      (Real.rpow_nonneg hd.le _)), ENNReal.ofReal_mul (analyticDerivativeLocalConstant_pos p n).le,
      hUI]
    rfl
  · simp only [analyticPowerZero, diskBoundaryWeight, ite_eq_right hz, zero_mul,
      mul_zero, zero_le]

/-- Explicit finite real constants are chosen before the analytic function. -/
def analyticDerivativeWeightConstant (p : ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  analyticDerivativeLocalConstant p n * (2 : ℝ)^|α - 2| *
    ((volume (ball (0 : ℂ) 1)).toReal + 1)

theorem analyticDerivativeWeightConstant_pos (p : ℝ) (n : ℕ) (α : ℝ) :
    0 < analyticDerivativeWeightConstant p n α := by
  unfold analyticDerivativeWeightConstant
  exact mul_pos (mul_pos (analyticDerivativeLocalConstant_pos p n) (by positivity)) (by positivity)

/-- Derivative raising for arbitrary real weights, in lower-integral form preserving infinity. -/
theorem analytic_derivative_weighted_volume_le (p : ℝ) (hp : 0 < p) (n : ℕ) (α : ℝ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk) :
    (∫⁻ z, analyticPowerZero (iteratedDeriv n F) p z * diskBoundaryWeight (α + (n : ℝ)*p) z) ≤
      ENNReal.ofReal (analyticDerivativeWeightConstant p n α) *
        ∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z := by
  have hT := lintegral_disk_local_area_weighted_le (analyticPowerZero F p)
    (measurable_analyticPowerZero F hF p hp.le) α
  have hV : volume (ball (0 : ℂ) 1) ≤
      ENNReal.ofReal ((volume (ball (0 : ℂ) 1)).toReal + 1) := by
    calc
      _ = ENNReal.ofReal ((volume (ball (0 : ℂ) 1)).toReal) :=
        (ENNReal.ofReal_toReal volume_unitDisk_ne_top).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (analyticDerivativeLocalConstant p n) *
        (diskBoundaryWeight (α - 2) z *
          ∫⁻ x in ball z (diskBoundaryDistance z / 2), analyticPowerZero F p x) := by
      apply lintegral_mono
      intro z
      simpa only [mul_assoc] using analytic_derivative_weighted_pointwise F hF p hp n α z
    _ = ENNReal.ofReal (analyticDerivativeLocalConstant p n) *
        ∫⁻ z, diskBoundaryWeight (α - 2) z *
          ∫⁻ x in ball z (diskBoundaryDistance z / 2), analyticPowerZero F p x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (analyticDerivativeLocalConstant p n) *
        (volume (ball (0 : ℂ) 1) * ENNReal.ofReal ((2 : ℝ) ^ |α - 2|) *
          ∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z) :=
      mul_le_mul_right hT _
    _ ≤ ENNReal.ofReal (analyticDerivativeWeightConstant p n α) *
        ∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z := by
      calc
        _ = ((ENNReal.ofReal (analyticDerivativeLocalConstant p n) *
            ENNReal.ofReal ((2 : ℝ)^|α - 2|)) * volume (ball (0 : ℂ) 1)) *
              ∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z := by ring
        _ ≤ ((ENNReal.ofReal (analyticDerivativeLocalConstant p n) *
            ENNReal.ofReal ((2 : ℝ)^|α - 2|)) *
              ENNReal.ofReal ((volume (ball (0 : ℂ) 1)).toReal + 1)) *
                ∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z :=
          mul_le_mul_left (mul_le_mul_right hV _) _
        _ = _ := by
          unfold analyticDerivativeWeightConstant
          rw [ENNReal.ofReal_mul (mul_nonneg (analyticDerivativeLocalConstant_pos p n).le (by positivity)),
            ENNReal.ofReal_mul (analyticDerivativeLocalConstant_pos p n).le]

/-- The zero-extended functions have exactly the literal restricted-disk energy meaning. -/
theorem lintegral_analyticPowerZero_mul_weight (F : ℂ → ℂ) (p α : ℝ) :
    (∫⁻ z, analyticPowerZero F p z * diskBoundaryWeight α z) =
      ∫⁻ z in disk, ENNReal.ofReal (‖F z‖ ^ p * (1 - ‖z‖) ^ α) := by
  classical
  have hs : MeasurableSet disk := (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ disk
  · simp only [analyticPowerZero, diskBoundaryWeight, ite_eq_left hz, indicator_of_mem hz,
      diskBoundaryDistance, ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg (F z)) p)]
  · simp only [analyticPowerZero, diskBoundaryWeight, ite_eq_right hz, zero_mul,
      indicator_of_notMem hz]

/-- Actual normalized-area derivative raising; both lower integrals may be infinite.
The power weight is literal (1 − norm z), with arbitrary real exponent. -/
theorem analytic_derivative_weighted_diskArea_le (p : ℝ) (hp : 0 < p) (n : ℕ) (α : ℝ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk) :
    (∫⁻ z, ENNReal.ofReal (‖iteratedDeriv n F z‖ ^ p *
        (1 - ‖z‖) ^ (α + (n : ℝ)*p)) ∂diskArea) ≤
      ENNReal.ofReal (analyticDerivativeWeightConstant p n α) *
        ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ p * (1 - ‖z‖) ^ α) ∂diskArea := by
  have h := analytic_derivative_weighted_volume_le p hp n α F hF
  rw [lintegral_analyticPowerZero_mul_weight, lintegral_analyticPowerZero_mul_weight] at h
  rw [diskArea, lintegral_smul_measure, lintegral_smul_measure]
  change (ENNReal.ofReal Real.pi)⁻¹ * _ ≤
    ENNReal.ofReal (analyticDerivativeWeightConstant p n α) * ((ENNReal.ofReal Real.pi)⁻¹ * _)
  calc
    _ ≤ (ENNReal.ofReal Real.pi)⁻¹ *
        (ENNReal.ofReal (analyticDerivativeWeightConstant p n α) *
          ∫⁻ z in disk, ENNReal.ofReal (‖F z‖ ^ p * (1 - ‖z‖) ^ α)) :=
      mul_le_mul_right h _
    _ = _ := by ring

/-- Uniform constants precede every analytic function, including functions with infinite energy. -/
theorem exists_analytic_derivative_weighted_diskArea_bound (p : ℝ) (hp : 0 < p)
    (n : ℕ) (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℂ → ℂ, AnalyticOnNhd ℂ F disk →
      (∫⁻ z, ENNReal.ofReal (‖iteratedDeriv n F z‖ ^ p *
          (1 - ‖z‖) ^ (α + (n : ℝ)*p)) ∂diskArea) ≤
        ENNReal.ofReal C *
          ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ p * (1 - ‖z‖) ^ α) ∂diskArea :=
  ⟨analyticDerivativeWeightConstant p n α, analyticDerivativeWeightConstant_pos p n α,
    fun F hF => analytic_derivative_weighted_diskArea_le p hp n α F hF⟩

end TTO.Paper.Proved
