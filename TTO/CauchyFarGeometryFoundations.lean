/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CauchyDerivativeFoundations
public import TTO.HardyMaximalFoundations
public import TTO.SingularBoundaryFoundations
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Actual far-arc geometry for the weighted Cauchy kernel.
All centers and angular representatives are real; wrapping arcs are retained. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The literal period-one circle character has the standard angular chord bound. -/
theorem circle_chord_upper_real (x y : ℝ) :
    ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (y : Boundary)‖≤
      2*Real.pi*|x-y| := by
  rw [circleCharacter_chord_eq]
  have hSub : (x : Boundary)-(y : Boundary)=((x-y : ℝ) : Boundary) := rfl
  rw [hSub]
  simpa only [Real.norm_eq_abs] using norm_circleCharacter_coe_sub_one_le (x-y)

/-- A perturbation by at most h/2 preserves a quantitative far-arc chord separation. -/
theorem circle_chord_lower_far_arc (a θ h x : ℝ) (hh : 0<h)
    (hθ : |θ-a|≤h/2) (hx : |x-a|≤1/2) (hFar : 2*h≤|x-a|) :
    2*|x-a|≤‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖ := by
  have hOld := circle_chord_lower_real x a hx
  have hPert : ‖fourier (T:=1) 1 (θ : Boundary)-fourier (T:=1) 1 (a : Boundary)‖≤
      2*|x-a| := by
    calc
      _ ≤ 2*Real.pi*|θ-a| := circle_chord_upper_real θ a
      _ ≤ 2*Real.pi*(h/2) := mul_le_mul_of_nonneg_left hθ (by positivity)
      _ = Real.pi*h := by ring
      _ ≤ 4*h := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hh.le
      _ ≤ _ := by linarith
  have hTri : ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (a : Boundary)‖≤
      ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖+
        ‖fourier (T:=1) 1 (θ : Boundary)-fourier (T:=1) 1 (a : Boundary)‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (fourier (T:=1) 1 (x : Boundary)) (fourier (T:=1) 1 (θ : Boundary))
      (fourier (T:=1) 1 (a : Boundary))
  linarith

/-- The actual radial disk denominator has quadratic far-arc separation. -/
theorem cauchy_denominator_sq_lower_far_arc (w : Disk) (r a θ h x : ℝ)
    (hr : 1/2≤r) (hw : w.val=(r : ℂ)*fourier (T:=1) 1 (θ : Boundary))
    (hh : 0<h) (hθ : |θ-a|≤h/2) (hx : |x-a|≤1/2) (hFar : 2*h≤|x-a|) :
    2*|x-a|^2≤‖fourier (T:=1) 1 (x : Boundary)-w.val‖^2 := by
  have hCh := circle_chord_lower_far_arc a θ h x hh hθ hx hFar
  have hSq : 4*|x-a|^2≤
      ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖^2 := by
    nlinarith [abs_nonneg (x-a),
      norm_nonneg (fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary))]
  rw [hw,norm_radial_unit_difference_sq _ _ (by simp) (by simp) r (by linarith)]
  have hMul := mul_le_mul_of_nonneg_right hr
    (sq_nonneg ‖fourier (T:=1) 1 (x : Boundary)-fourier (T:=1) 1 (θ : Boundary)‖)
  nlinarith [sq_nonneg (1-r)]

/-- Actual pointwise weighted Cauchy-kernel decay with one uniform numerical constant. -/
theorem norm_cauchyWeightedBoundaryKernel_le_far_arc (w : Disk) (r a θ h x : ℝ)
    (hr : 1/2≤r) (hw : w.val=(r : ℂ)*fourier (T:=1) 1 (θ : Boundary))
    (hh : 0<h) (hθ : |θ-a|≤h/2) (hx : |x-a|≤1/2) (hFar : 2*h≤|x-a|) :
    ‖cauchyWeightedBoundaryKernel w (x : Boundary)‖≤2/|x-a|^2 := by
  have hD : 0 < |x-a| := by linarith
  have hDen := cauchy_denominator_sq_lower_far_arc w r a θ h x hr hw hh hθ hx hFar
  have hDenPos : 0<‖fourier (T:=1) 1 (x : Boundary)-w.val‖^2 := by
    nlinarith [sq_pos_of_pos hD]
  apply (norm_cauchyWeightedBoundaryKernel_le w (x : Boundary)).trans
  apply (div_le_div_iff₀ hDenPos (sq_pos_of_pos hD)).mpr
  nlinarith [sq_nonneg |x-a|]

end TTO.Paper.Proved
