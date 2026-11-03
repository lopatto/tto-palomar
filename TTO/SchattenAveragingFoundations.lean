/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.SchattenNormFoundations
public import Mathlib.Analysis.Convex.Integral

/-! Closed Schatten balls and ordinary operator-norm Bochner averaging.
No normed-space structure on a Schatten carrier is used. -/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved

section ScalarGauge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Scalar multiplication has the expected upper gauge estimate for every p>0. -/
theorem schattenNorm_smul_le {p : ℝ} {A : E →L[ℂ] F}
    (hA : Schatten p A) (c : ℂ) :
    schattenNorm p (c • A) ≤ ‖c‖ * schattenNorm p A := by
  apply schattenNorm_le_of_approx_le hA ‖c‖ (norm_nonneg c)
  intro n
  simp only [approximationNumber_smul, NNReal.coe_mul, coe_nnnorm]
  exact le_rfl

/-- Nonnegative real scalar multiplication is compatible with the complex ideal. -/
theorem schatten_nonneg_real_smul {p : ℝ} {A : E →L[ℂ] F}
    (hA : Schatten p A) (r : ℝ) (hr : 0 ≤ r) :
    Schatten p (r • A) ∧ schattenNorm p (r • A) ≤ r * schattenNorm p A := by
  have hs : (r : ℂ) • A = r • A := algebraMap_smul ℂ r A
  refine ⟨hs ▸ schatten_smul hA (r : ℂ), ?_⟩
  simpa only [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    using schattenNorm_smul_le hA (r : ℂ)

end ScalarGauge

section HilbertBall
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ball is defined by actual compactness, summable approximation numbers and their gauge. -/
def schattenClosedBall (p B : ℝ) : Set (H →L[ℂ] H) :=
  {T | Schatten p T ∧ schattenNorm p T ≤ B}

/-- These balls are closed in ordinary operator norm, even for 0<p<1. -/
theorem isClosed_schattenClosedBall (p : ℝ) (hp : 0 < p) (B : ℝ) :
    IsClosed (schattenClosedBall (H := H) p B) := by
  apply IsSeqClosed.isClosed
  intro T Z hT hLim
  apply schatten_ball_weak_closed p hp B T Z hT
  intro x y
  have hc : Continuous (fun A : H →L[ℂ] H => inner ℂ y (A x)) := by fun_prop
  exact (hc.tendsto Z).comp hLim

/-- The sharp p≥1 triangle makes the literal Schatten ball convex over the reals. -/
theorem convex_schattenClosedBall (p : ℝ) (hp : 1 ≤ p) (B : ℝ) :
    Convex ℝ (schattenClosedBall (H := H) p B) := by
  intro A hA C hC a b ha hb hab
  change Schatten p A ∧ schattenNorm p A ≤ B at hA
  change Schatten p C ∧ schattenNorm p C ≤ B at hC
  change Schatten p (a • A + b • C) ∧ schattenNorm p (a • A + b • C) ≤ B
  obtain ⟨hAS, hAN⟩ := schatten_nonneg_real_smul hA.1 a ha
  obtain ⟨hCS, hCN⟩ := schatten_nonneg_real_smul hC.1 b hb
  refine ⟨schatten_add hAS hCS, ?_⟩
  calc
    schattenNorm p (a • A + b • C) ≤
        schattenNorm p (a • A) + schattenNorm p (b • C) :=
      schattenNorm_add_le_sharp p hp _ _ hAS hCS
    _ ≤ a * schattenNorm p A + b * schattenNorm p C := add_le_add hAN hCN
    _ ≤ a * B + b * B :=
      add_le_add (mul_le_mul_of_nonneg_left hA.2 ha) (mul_le_mul_of_nonneg_left hC.2 hb)
    _ = B := by rw [← add_mul, hab, one_mul]

/-- Probability Bochner averaging in the ordinary CLM Banach space preserves the p≥1 ball.
Only ordinary operator-norm integrability is required. -/
theorem schatten_integral_ball {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 ≤ p) (B : ℝ) (T : α → H →L[ℂ] H)
    (hT : ∀ᵐ a ∂μ, Schatten p (T a) ∧ schattenNorm p (T a) ≤ B)
    (hInt : Integrable T μ) :
    Schatten p (∫ a, T a ∂μ) ∧ schattenNorm p (∫ a, T a ∂μ) ≤ B :=
  (convex_schattenClosedBall (H := H) p hp B).integral_mem
    (isClosed_schattenClosedBall (H := H) p (by linarith) B) hT hInt

/-- A finite nonzero measure can equivalently be normalized by native Bochner averaging. -/
theorem schatten_average_ball {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (p : ℝ) (hp : 1 ≤ p) (B : ℝ) (T : α → H →L[ℂ] H)
    (hT : ∀ᵐ a ∂μ, Schatten p (T a) ∧ schattenNorm p (T a) ≤ B)
    (hInt : Integrable T μ) :
    Schatten p (⨍ a, T a ∂μ) ∧ schattenNorm p (⨍ a, T a ∂μ) ≤ B :=
  (convex_schattenClosedBall (H := H) p hp B).average_mem
    (isClosed_schattenClosedBall (H := H) p (by linarith) B) hT hInt

/-- Averaging left and right contractions of one Schatten operator cannot increase its gauge.
This is the generic smoothing estimate; no translation or symbol regularization is asserted. -/
theorem schatten_integral_contractions {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 ≤ p) (A : H →L[ℂ] H) (hA : Schatten p A)
    (L R : α → H →L[ℂ] H)
    (hLR : ∀ᵐ a ∂μ, ‖L a‖ ≤ 1 ∧ ‖R a‖ ≤ 1)
    (hInt : Integrable (fun a => L a ∘L A ∘L R a) μ) :
    Schatten p (∫ a, L a ∘L A ∘L R a ∂μ) ∧
      schattenNorm p (∫ a, L a ∘L A ∘L R a ∂μ) ≤ schattenNorm p A := by
  apply schatten_integral_ball μ p hp (schattenNorm p A) _ _ hInt
  filter_upwards [hLR] with a ha
  refine ⟨schatten_comp hA (L a) (R a), ?_⟩
  apply (schattenNorm_comp_le hA (L a) (R a)).trans
  have hn : ‖L a‖ * ‖R a‖ ≤ 1 := by
    calc
      ‖L a‖ * ‖R a‖ ≤ 1 * 1 :=
        mul_le_mul ha.1 ha.2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hn (Reduction.schattenNorm_nonneg p A)

end HilbertBall
end TTO.Paper.Proved
