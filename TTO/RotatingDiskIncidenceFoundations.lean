/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PositiveBandConvolutionFoundations

/-! Actual probability-Haar incidence bounds for rotating analytic disks. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The actual quotient norm is controlled by the period-one complex chord. -/
theorem circle_character_chord_lower_norm (t ζ : Boundary) :
    4*‖t-ζ‖ ≤ ‖fourier (T := 1) 1 t-fourier (T := 1) 1 ζ‖ := by
  let x : ℝ := (AddCircle.equivIoc (1 : ℝ) (-1/2) (t-ζ)).val
  have hx : (x : Boundary)=t-ζ := AddCircle.coe_equivIoc
  have hI := (AddCircle.equivIoc (1 : ℝ) (-1/2) (t-ζ)).property
  have hAbs : |x| ≤ 1/2 := abs_le.mpr ⟨by linarith [hI.1],by linarith [hI.2]⟩
  have hNorm : ‖t-ζ‖ ≤ |x| := by
    rw [← hx]
    exact (QuotientAddGroup.norm_mk_le_norm (m := x)).trans_eq (Real.norm_eq_abs x)
  have hChord := circle_chord_lower_real x 0 (by simpa only [sub_zero] using hAbs)
  have hMul : fourier (T := 1) 1 (t-ζ)*fourier (T := 1) 1 ζ = fourier (T := 1) 1 t := by
    rw [← fourier_position_add,sub_add_cancel]
  have hEq : ‖fourier (T := 1) 1 t-fourier (T := 1) 1 ζ‖ =
      ‖fourier (T := 1) 1 (t-ζ)-1‖ := by
    calc
      _ = ‖(fourier (T := 1) 1 (t-ζ)-1)*fourier (T := 1) 1 ζ‖ := by rw [sub_mul,hMul,one_mul]
      _ = _ := by rw [norm_mul,show ‖fourier (T := 1) 1 ζ‖=1 by simp,mul_one]
  have hChord' : 4*|x| ≤ ‖fourier (T := 1) 1 (x : Boundary)-1‖ := by simpa using hChord
  calc
    _ ≤ 4*|x| := by linarith
    _ ≤ _ := hChord'
    _ = _ := by rw [hEq,← hx]

/-- Centers whose literal complex disks contain z. -/
def rotatingDiskIncidence (N : ℕ) (z : ℂ) : Set Boundary :=
  {θ | ‖z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ‖ < 2/(N : ℝ)}

theorem measurableSet_rotatingDiskIncidence (N : ℕ) (z : ℂ) :
    MeasurableSet (rotatingDiskIncidence N z) := by
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- Every nonempty incidence set lies in a genuine quotient-metric ball of radius 2/N. -/
theorem rotatingDiskIncidence_subset_closedBall (N : ℕ) (hN : 10 ≤ N) (z : ℂ) (ζ : Boundary)
    (hζ : ζ ∈ rotatingDiskIncidence N z) :
    rotatingDiskIncidence N z ⊆ closedBall ζ (2/(N : ℝ)) := by
  intro t ht
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 ≤ positiveKernelRadius N := by linarith [hBounds.1]
  change ‖z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 t‖ < 2/(N : ℝ) at ht
  change ‖z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 ζ‖ < 2/(N : ℝ) at hζ
  have hTri := norm_add_le ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 t-z)
    (z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 ζ)
  rw [show (positiveKernelRadius N : ℂ)*fourier (T := 1) 1 t-z+
      (z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 ζ) =
      (positiveKernelRadius N : ℂ)*(fourier (T := 1) 1 t-fourier (T := 1) 1 ζ) by ring,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,
    norm_sub_rev ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 t) z] at hTri
  have hLower := mul_le_mul_of_nonneg_left (circle_character_chord_lower_norm t ζ) hr
  have h2 : 2*‖t-ζ‖ ≤ positiveKernelRadius N*(4*‖t-ζ‖) := by
    nlinarith [mul_nonneg (show 0 ≤ positiveKernelRadius N-1/2 by linarith [hBounds.1]) (norm_nonneg (t-ζ))]
  rw [mem_closedBall,dist_eq_norm]
  nlinarith

/-- Actual normalized Haar incidence costs at most 4/N, uniformly in every planar point. -/
theorem measure_rotatingDiskIncidence_le (N : ℕ) (hN : 10 ≤ N) (z : ℂ) :
    circleMeasure (rotatingDiskIncidence N z) ≤ ENNReal.ofReal (4/(N : ℝ)) := by
  by_cases hS : (rotatingDiskIncidence N z).Nonempty
  · obtain ⟨ζ,hζ⟩ := hS
    apply (measure_mono (rotatingDiskIncidence_subset_closedBall N hN z ζ hζ)).trans
    have hMeasure : circleMeasure=(volume : Measure Boundary) := by
      simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
    rw [hMeasure,AddCircle.volume_closedBall]
    apply ENNReal.ofReal_le_ofReal
    calc
      min 1 (2*(2/(N : ℝ))) ≤ 2*(2/(N : ℝ)) := min_le_right _ _
      _ = _ := by ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hS,measure_empty]
    exact bot_le

/-- A closed radial annulus containing every rotating disk; its distance endpoints are literal. -/
def rotatingDiskAnnulus (N : ℕ) : Set ℂ :=
  {z | 2/(N : ℝ) ≤ 1-‖z‖ ∧ 1-‖z‖ ≤ 6/(N : ℝ)}

theorem measurableSet_rotatingDiskAnnulus (N : ℕ) : MeasurableSet (rotatingDiskAnnulus N) := by
  have h1 : IsClosed {z : ℂ | 2/(N : ℝ) ≤ 1-‖z‖} := isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {z : ℂ | 1-‖z‖ ≤ 6/(N : ℝ)} := isClosed_le (by fun_prop) continuous_const
  exact (h1.inter h2).measurableSet

theorem rotating_disk_subset_annulus (N : ℕ) (hN : 10 ≤ N) (θ : Boundary) :
    ball ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ) (2/(N : ℝ)) ⊆ rotatingDiskAnnulus N := by
  intro z hz
  have hBounds := positiveKernelRadius_bounds N hN
  have hr : 0 ≤ positiveKernelRadius N := by linarith [hBounds.1]
  have hc : ‖(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ‖ = positiveKernelRadius N := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,fourier_apply,Circle.norm_coe,mul_one]
  have hRev := abs_norm_sub_norm_le z ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ)
  rw [hc] at hRev
  have hDist := mem_ball.mp hz
  rw [dist_eq_norm] at hDist
  have hAbs := abs_lt.mp (hRev.trans_lt hDist)
  change 2/(N : ℝ) ≤ 1-‖z‖ ∧ 1-‖z‖ ≤ 6/(N : ℝ)
  dsimp only [positiveKernelRadius] at hAbs
  have hFour : 4/(N : ℝ)=2*(2/(N : ℝ)) := by ring
  have hSix : 6/(N : ℝ)=3*(2/(N : ℝ)) := by ring
  constructor <;> linarith [hAbs.1,hAbs.2]

/-- Genuine Tonelli incidence bound; U and either energy may be infinite. -/
theorem lintegral_rotating_disk_le (N : ℕ) (hN : 10 ≤ N) (U : ℂ → ℝ≥0∞) (hU : Measurable U) :
    (∫⁻ θ : Boundary,∫⁻ z in ball ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ)
      (2/(N : ℝ)),U z ∂volume ∂circleMeasure) ≤
      ENNReal.ofReal (4/(N : ℝ))*(∫⁻ z in rotatingDiskAnnulus N,U z ∂volume) := by
  classical
  let F : Boundary → ℂ → ℝ≥0∞ := fun θ z =>
    if ‖z-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ‖ < 2/(N : ℝ) then U z else 0
  have hSet : MeasurableSet {q : Boundary × ℂ |
      ‖q.2-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 q.1‖ < 2/(N : ℝ)} := by
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hJoint : Measurable (Function.uncurry F) := by
    exact (hU.comp measurable_snd).indicator hSet
  have hSlice (z : ℂ) : (∫⁻ θ : Boundary,F θ z ∂circleMeasure) = U z*circleMeasure (rotatingDiskIncidence N z) := by
    change (∫⁻ θ : Boundary,(rotatingDiskIncidence N z).indicator (fun _ => U z) θ ∂circleMeasure)=_
    rw [lintegral_indicator (measurableSet_rotatingDiskIncidence N z),lintegral_const,Measure.restrict_apply_univ]
  calc
    _ = ∫⁻ θ : Boundary,∫⁻ z,F θ z ∂volume ∂circleMeasure := by
      apply lintegral_congr
      intro θ
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro z
      simp only [F,Set.indicator,mem_ball,dist_eq_norm]
    _ = ∫⁻ z,∫⁻ θ : Boundary,F θ z ∂circleMeasure ∂volume := lintegral_lintegral_swap hJoint.aemeasurable
    _ = ∫⁻ z,U z*circleMeasure (rotatingDiskIncidence N z) ∂volume := lintegral_congr hSlice
    _ ≤ ∫⁻ z,ENNReal.ofReal (4/(N : ℝ))*(rotatingDiskAnnulus N).indicator U z ∂volume := by
      apply lintegral_mono
      intro z
      change U z*circleMeasure (rotatingDiskIncidence N z) ≤
        ENNReal.ofReal (4/(N : ℝ))*(rotatingDiskAnnulus N).indicator U z
      by_cases hz : z ∈ rotatingDiskAnnulus N
      · rw [Set.indicator_of_mem hz,mul_comm]
        exact mul_le_mul_left (measure_rotatingDiskIncidence_le N hN z) (U z)
      · have hEmpty : rotatingDiskIncidence N z=∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro θ hθ
          apply hz
          apply rotating_disk_subset_annulus N hN θ
          rw [mem_ball,dist_eq_norm]
          exact hθ
        rw [hEmpty,measure_empty,mul_zero,Set.indicator_of_notMem hz,mul_zero]
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator (measurableSet_rotatingDiskAnnulus N)]

end TTO.Paper.Proved
