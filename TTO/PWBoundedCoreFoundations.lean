/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PaleyWienerKernelFoundations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual bounded PW images of endpoint-zero differentiable functions.
The compact smooth interval core is used by the atomic regularization constructions. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace TTO.Paper.Proved
open Reduction

/-- Integration by parts with the manuscript's literal positive Fourier--Laplace sign. -/
theorem interval_laplace_integration_by_parts (ℓ : ℝ) (hℓ : 0 < ℓ)
    (f f' : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) ℓ))
    (hf' : ContinuousOn f' (Icc (0 : ℝ) ℓ))
    (hd : ∀ t ∈ Ioo (0 : ℝ) ℓ, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hEnd : f ℓ = 0) (w : ℂ) :
    (w * Complex.I) * (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t) =
      -(∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f' t) := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * w * Complex.I)
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hEd (t : ℝ) : HasDerivAt E ((w * Complex.I) * E t) t := by
    have ht : HasDerivAt (fun s : ℝ => (s : ℂ) * w * Complex.I) (w * Complex.I) t := by
      simpa only [one_mul] using!
        ((((hasDerivAt_id (t : ℂ)).mul_const w).mul_const Complex.I).comp_ofReal)
    simpa only [E, mul_comm] using ht.cexp
  have hfi : IntervalIntegrable f' volume 0 ℓ :=
    hf'.intervalIntegrable_of_Icc hℓ.le
  have hEi : IntervalIntegrable (fun t => (w * Complex.I) * E t) volume 0 ℓ :=
    (by fun_prop : Continuous (fun t => (w * Complex.I) * E t)).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (u' := f') (v := E) (v' := fun t => (w * Complex.I) * E t)
    (by simpa only [uIcc_of_le hℓ.le] using hf) hE.continuousOn
    (by simpa only [min_eq_left hℓ.le, max_eq_right hℓ.le] using hd)
    (fun t _ => hEd t) hfi hEi
  simp only [h0, hEnd, zero_mul, sub_zero, zero_sub] at hi
  simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ.le]
  simpa only [E, ← intervalIntegral.integral_const_mul, mul_assoc, mul_left_comm, mul_comm] using hi

/-- A uniform disk evaluation bound gives an actual essentially bounded Hardy vector. -/
theorem bounded_hardy_of_analyticValue_bound (f : Hardy) (M : ℝ)
    (hM : ∀ z ∈ disk, ‖analyticValue f.val z‖ ≤ M) : IsBounded f.val := by
  obtain ⟨b,hb,hval,_hae,_hnorm⟩ :=
    exists_boundedAnalyticBoundary (analyticValue f.val) (analyticOnNhd_analyticValue f.val) M hM
  have he : (⟨toL2 b,hb⟩ : Hardy) = f := by
    apply hardy_analyticValue_injective
    intro z hz
    exact hval z hz
  have hvaleq : toL2 b = f.val := congrArg Subtype.val he
  exact hvaleq ▸ bounded_toL2 b

/-- The derivative correction has the literal factor i/sqrt(2), as in the manuscript. -/
theorem paleyWiener_eval_C1 (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f f' : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) ℓ))
    (hf' : ContinuousOn f' (Icc (0 : ℝ) ℓ))
    (hd : ∀ t ∈ Ioo (0 : ℝ) ℓ, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hEnd : f ℓ = 0)
    (a : IntervalL2 ℓ) (ha : a =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f)
    (w : ℂ) (hw : 0 < w.im) :
    analyticValue (U a).val (upperCayley w) =
      Complex.I / (Real.sqrt 2 : ℂ) *
        ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * (f' t + f t) := by
  have hfa : (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * a t) =
      ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
    apply integral_congr_ae
    filter_upwards [ha] with t ht
    rw [ht]
  have hc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * w * Complex.I)) := by fun_prop
  have hfi : Integrable (fun t : ℝ => Complex.exp ((t : ℂ) * w * Complex.I) * f t)
      (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    (hc.continuousOn.mul hf).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hf'i : Integrable (fun t : ℝ => Complex.exp ((t : ℂ) * w * Complex.I) * f' t)
      (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    (hc.continuousOn.mul hf').integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi := interval_laplace_integration_by_parts ℓ hℓ f f' hf hf' hd h0 hEnd w
  have hwi := congrArg (fun z : ℂ => -Complex.I * z) hi
  simp only [neg_mul, mul_neg, neg_neg] at hwi
  have hwi' :
      w * (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t) =
      Complex.I * (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f' t) := by
    have hcanc (x : ℂ) : -(Complex.I * (w * Complex.I * x)) = w * x := by
      calc
        _ = -(Complex.I * Complex.I) * (w * x) := by ring
        _ = w * x := by rw [Complex.I_mul_I]; ring
    rwa [hcanc] at hwi
  rw [paleyWienerUnitary_eval ℓ u U hU a w hw, inner_intervalEvalKernel, hfa]
  have hsum : (∫ t in Ioo (0 : ℝ) ℓ,
      Complex.exp ((t : ℂ) * w * Complex.I) * (f' t + f t)) =
      (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f' t) +
      ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t := by
    simp_rw [mul_add]
    exact integral_add hf'i hfi
  rw [hsum]
  calc
    _ = (Real.sqrt 2 : ℂ)⁻¹ *
        (w * (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t) +
          Complex.I * (∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t)) := by ring
    _ = _ := by rw [hwi']; ring

/-- C¹ endpoint-zero data have a uniform analytic bound after the actual normalized PW map. -/
theorem norm_paleyWiener_C1_le (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f f' : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) ℓ))
    (hf' : ContinuousOn f' (Icc (0 : ℝ) ℓ))
    (hd : ∀ t ∈ Ioo (0 : ℝ) ℓ, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hEnd : f ℓ = 0)
    (a : IntervalL2 ℓ) (ha : a =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f) :
    ∀ z ∈ disk, ‖analyticValue (U a).val z‖ ≤
      ((∫ t in Ioo (0 : ℝ) ℓ, ‖f' t‖) + ∫ t in Ioo (0 : ℝ) ℓ, ‖f t‖) / Real.sqrt 2 := by
  intro z hz
  obtain ⟨w,hw⟩ := upperCayleyDisk_surjective ⟨z,hz⟩
  have hw' : upperCayley w.val = z := congrArg Subtype.val hw
  rw [← hw', paleyWiener_eval_C1 ℓ hℓ u U hU f f' hf hf' hd h0 hEnd a ha w.val w.property]
  have hc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * w.val * Complex.I)) := by fun_prop
  have hInt : Integrable (fun t : ℝ => Complex.exp ((t : ℂ) * w.val * Complex.I) * (f' t + f t))
      (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    (hc.continuousOn.mul (hf'.add hf)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hNf : Integrable (fun t => ‖f t‖) (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    hf.norm.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hNf' : Integrable (fun t => ‖f' t‖) (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
    hf'.norm.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hBound : ‖∫ t in Ioo (0 : ℝ) ℓ,
      Complex.exp ((t : ℂ) * w.val * Complex.I) * (f' t + f t)‖ ≤
      (∫ t in Ioo (0 : ℝ) ℓ, ‖f' t‖) + ∫ t in Ioo (0 : ℝ) ℓ, ‖f t‖ := by
    calc
      _ ≤ ∫ t in Ioo (0 : ℝ) ℓ,
          ‖Complex.exp ((t : ℂ) * w.val * Complex.I) * (f' t + f t)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioo (0 : ℝ) ℓ, ‖f' t‖ + ‖f t‖ := by
        apply integral_mono_ae hInt.norm (hNf'.add hNf)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (norm_upper_exponential_le_one t ht.1.le w.val w.property)).trans (norm_add_le _ _)
      _ = _ := integral_add hNf' hNf
  rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2), one_div]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (Real.sqrt_nonneg 2))

/-- Actual bounded boundary membership, with no pointwise boundary definition substituted. -/
theorem bounded_paleyWiener_C1 (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f f' : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) ℓ))
    (hf' : ContinuousOn f' (Icc (0 : ℝ) ℓ))
    (hd : ∀ t ∈ Ioo (0 : ℝ) ℓ, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hEnd : f ℓ = 0)
    (a : IntervalL2 ℓ) (ha : a =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f) :
    IsBounded (U a).val :=
  bounded_hardy_of_analyticValue_bound ⟨(U a).val,(U a).property.1⟩ _
    (norm_paleyWiener_C1_le ℓ hℓ u U hU f f' hf hf' hd h0 hEnd a ha)

/-- Literal compactly supported smooth test functions in the open interval. -/
def IntervalSmoothCompact (ℓ : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (0 : ℝ) ℓ

theorem memLp_intervalSmoothCompact {ℓ : ℝ} {f : ℝ → ℂ}
    (hf : IntervalSmoothCompact ℓ f) :
    MemLp f 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2.1

/-- The native L² equivalence class of an actual smooth interval test function. -/
def smoothIntervalL2 (ℓ : ℝ) (f : ℝ → ℂ) (hf : IntervalSmoothCompact ℓ f) : IntervalL2 ℓ :=
  (memLp_intervalSmoothCompact hf).toLp f

theorem smoothIntervalL2_ae (ℓ : ℝ) (f : ℝ → ℂ) (hf : IntervalSmoothCompact ℓ f) :
    smoothIntervalL2 ℓ f hf =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] f :=
  (memLp_intervalSmoothCompact hf).coeFn_toLp

/-- Source Lemma 7(a)'s bounded-image assertion, for literal C_c^∞(0,ℓ) functions. -/
theorem bounded_paleyWiener_smoothCompact (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f : ℝ → ℂ) (hf : IntervalSmoothCompact ℓ f) :
    IsBounded (U (smoothIntervalL2 ℓ f hf)).val := by
  have h0 : f 0 = 0 := by
    by_contra hn
    exact (lt_irrefl (0 : ℝ)) (hf.2.2 (subset_tsupport f hn)).1
  have hEnd : f ℓ = 0 := by
    by_contra hn
    exact (lt_irrefl ℓ) (hf.2.2 (subset_tsupport f hn)).2
  exact bounded_paleyWiener_C1 ℓ hℓ u U hU f (deriv f) hf.1.continuous.continuousOn
    (hf.1.continuous_deriv (by simp)).continuousOn
    (fun t _ => ((hf.1.differentiable (by simp)) t).hasDerivAt) h0 hEnd _
    (smoothIntervalL2_ae ℓ f hf)

/-- Compact smooth cutoffs whose inner radii exhaust the interval. -/
def intervalSmoothCutoff (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) : ContDiffBump (ℓ / 2) where
  rIn := ℓ / 2 * (1 - 1 / ((n : ℝ) + 2))
  rOut := ℓ / 2 * (1 - 1 / ((n : ℝ) + 3))
  rIn_pos := by
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hi : 1 / ((n : ℝ) + 2) < 1 :=
      by simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hn
    exact mul_pos (half_pos hℓ) (sub_pos.mpr hi)
  rIn_lt_rOut := by
    have hi : 1 / ((n : ℝ) + 3) < 1 / ((n : ℝ) + 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    exact mul_lt_mul_of_pos_left (by linarith) (half_pos hℓ)

theorem intervalSmoothCutoff_rOut_lt (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    (intervalSmoothCutoff ℓ hℓ n).rOut < ℓ / 2 := by
  have hn : 0 < 1 / ((n : ℝ) + 3) := by positivity
  change ℓ / 2 * (1 - 1 / ((n : ℝ) + 3)) < ℓ / 2
  nlinarith

theorem intervalSmoothCutoff_tsupport (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    tsupport (intervalSmoothCutoff ℓ hℓ n) ⊆ Ioo (0 : ℝ) ℓ := by
  intro t ht
  rw [(intervalSmoothCutoff ℓ hℓ n).tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at ht
  have hh := abs_le.mp ht
  have hr := intervalSmoothCutoff_rOut_lt ℓ hℓ n
  constructor <;> linarith

theorem intervalSmoothCutoff_eventually_one (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) ℓ) :
    ∀ᶠ n : ℕ in atTop, intervalSmoothCutoff ℓ hℓ n t = 1 := by
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hr : Tendsto (fun n : ℕ => (intervalSmoothCutoff ℓ hℓ n).rIn) atTop (𝓝 (ℓ / 2)) := by
    simpa only [intervalSmoothCutoff, sub_zero, mul_one] using
      (tendsto_const_nhds (x := ℓ / 2)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hi)
  have hd : dist t (ℓ / 2) < ℓ / 2 := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  filter_upwards [hr.eventually (Ioi_mem_nhds hd)] with n hn
  exact (intervalSmoothCutoff ℓ hℓ n).one_of_mem_closedBall (le_of_lt hn)

/-- These approximants really are smooth and compactly supported strictly inside the interval. -/
def cutoffIntervalEvalFunction (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  (intervalSmoothCutoff ℓ hℓ n t) • intervalEvalFunction w t

theorem cutoffIntervalEvalFunction_smooth (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) (w : ℂ) :
    IntervalSmoothCompact ℓ (cutoffIntervalEvalFunction ℓ hℓ n w) := by
  refine ⟨?_, ?_, ?_⟩
  · have hco : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := by
      simpa only [Complex.ofRealCLM_apply] using! (Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ Complex.ofRealCLM)
    exact (intervalSmoothCutoff ℓ hℓ n).contDiff.smul (by unfold intervalEvalFunction; fun_prop)
  · exact (intervalSmoothCutoff ℓ hℓ n).hasCompactSupport.smul_right
  · exact (tsupport_smul_subset_left _ _).trans (intervalSmoothCutoff_tsupport ℓ hℓ n)

/-- The genuine compact smooth interval test functions generate a native linear core. -/
def smoothIntervalCore (ℓ : ℝ) : Submodule ℂ (IntervalL2 ℓ) :=
  Submodule.span ℂ (Set.range (fun f : {f : ℝ → ℂ // IntervalSmoothCompact ℓ f} =>
    smoothIntervalL2 ℓ f.val f.property))

/-- Compact smooth interval tests are total. The proof uses actual smooth cutoffs,
dominated convergence of pairings, and the already proved interval kernel density. -/
theorem smoothIntervalCore_dense (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Dense (smoothIntervalCore ℓ : Set (IntervalL2 ℓ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro g hg
  have hpair (w : ℂ) (hw : 0 < w.im) : inner ℂ (intervalEvalKernel ℓ w hw) g = 0 := by
    let a : ℕ → IntervalL2 ℓ := fun n =>
      smoothIntervalL2 ℓ (cutoffIntervalEvalFunction ℓ hℓ n w)
        (cutoffIntervalEvalFunction_smooth ℓ hℓ n w)
    have ha (n : ℕ) : a n =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
        cutoffIntervalEvalFunction ℓ hℓ n w :=
      smoothIntervalL2_ae ℓ _ _
    have hzero (n : ℕ) : inner ℂ (a n) g = 0 := by
      apply (Submodule.mem_orthogonal _ _).mp hg
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      exact ⟨⟨cutoffIntervalEvalFunction ℓ hℓ n w,
        cutoffIntervalEvalFunction_smooth ℓ hℓ n w⟩,rfl⟩
    have hD := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) ℓ))
      (F := fun n t => inner ℂ ((a n) t) (g t))
      (f := fun t => inner ℂ ((intervalEvalKernel ℓ w hw) t) (g t))
      (fun t => ‖inner ℂ ((intervalEvalKernel ℓ w hw) t) (g t)‖)
      (fun n => (L2.integrable_inner (a n) g).aestronglyMeasurable)
      (L2.integrable_inner (intervalEvalKernel ℓ w hw) g).norm
      (fun n => by
        filter_upwards [ha n, intervalEvalKernel_ae ℓ w hw] with t hat hkt
        rw [hat, hkt, cutoffIntervalEvalFunction, RCLike.real_smul_eq_coe_smul (K := ℂ),
          inner_smul_real_left, norm_smul, Real.norm_of_nonneg (intervalSmoothCutoff ℓ hℓ n).nonneg]
        exact mul_le_of_le_one_left (norm_nonneg _) (intervalSmoothCutoff ℓ hℓ n).le_one)
      (by
        filter_upwards [ae_all_iff.mpr ha, intervalEvalKernel_ae ℓ w hw,
          ae_restrict_mem measurableSet_Ioo] with t hat hkt ht
        apply tendsto_const_nhds.congr'
        filter_upwards [intervalSmoothCutoff_eventually_one ℓ hℓ t ht] with n hn
        rw [hat n, cutoffIntervalEvalFunction, hn, one_smul, hkt])
    have hconst : Tendsto (fun n : ℕ => inner ℂ (a n) g) atTop (𝓝 (0 : ℂ)) := by
      simpa only [hzero] using (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
    have hlim : Tendsto (fun n : ℕ => inner ℂ (a n) g) atTop
        (𝓝 (inner ℂ (intervalEvalKernel ℓ w hw) g)) := by
      simpa only [L2.inner_def] using hD
    exact tendsto_nhds_unique hlim hconst
  let K : Submodule ℂ (IntervalL2 ℓ) := Submodule.span ℂ
    (Set.range (fun w : {w : ℂ // 0 < w.im} => intervalEvalKernel ℓ w.val w.property))
  have horth : g ∈ K.orthogonal := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨w,rfl⟩ := hf
      exact hpair w.val w.property
    | zero => simp
    | add x y hx hy hx0 hy0 => simp only [inner_add_left,hx0,hy0,add_zero]
    | smul c x hx hx0 => simp only [inner_smul_left,hx0,mul_zero]
  have hd : K.topologicalClosure = ⊤ :=
    (Submodule.dense_iff_topologicalClosure_eq_top).mp (intervalEvalKernels_dense ℓ hℓ)
  rw [← Submodule.orthogonal_closure K, hd, Submodule.top_orthogonal_eq_bot] at horth
  exact horth

/-- Every vector in the actual compact smooth core has a bounded model image. -/
theorem bounded_paleyWiener_smoothIntervalCore (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (a : IntervalL2 ℓ) (ha : a ∈ smoothIntervalCore ℓ) : IsBounded (U a).val := by
  change (U a).val ∈ boundedL2
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f,rfl⟩ := ha
    exact bounded_paleyWiener_smoothCompact ℓ hℓ u U hU f.val f.property
  | zero =>
    rw [map_zero]
    exact boundedL2.zero_mem
  | add a b ha hb hab hbb =>
    simpa only [map_add, Submodule.coe_add] using boundedL2.add_mem hab hbb
  | smul c a ha hab =>
    simpa only [map_smul, Submodule.coe_smul] using boundedL2.smul_mem c hab

/-- The span definition introduces no extra tests: each core element has one literal C_c^∞ representative. -/
theorem mem_smoothIntervalCore_iff (ℓ : ℝ) (a : IntervalL2 ℓ) :
    a ∈ smoothIntervalCore ℓ ↔
      ∃ f : ℝ → ℂ, ∃ hf : IntervalSmoothCompact ℓ f, a = smoothIntervalL2 ℓ f hf := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f,rfl⟩ := ha
      exact ⟨f.val,f.property,rfl⟩
    | zero =>
      have hz : IntervalSmoothCompact ℓ (0 : ℝ → ℂ) := by
        exact ⟨contDiff_const,by simp [HasCompactSupport],by simp⟩
      refine ⟨0,hz,?_⟩
      apply Lp.ext
      exact (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ))).trans
        (smoothIntervalL2_ae ℓ 0 hz).symm
    | add a b ha hb hfa hfb =>
      obtain ⟨f,hf,rfl⟩ := hfa
      obtain ⟨g,hg,rfl⟩ := hfb
      have hfg : IntervalSmoothCompact ℓ (f + g) :=
        ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,
          (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
      refine ⟨f + g,hfg,?_⟩
      apply Lp.ext
      filter_upwards [Lp.coeFn_add (smoothIntervalL2 ℓ f hf) (smoothIntervalL2 ℓ g hg),
        smoothIntervalL2_ae ℓ f hf, smoothIntervalL2_ae ℓ g hg,
        smoothIntervalL2_ae ℓ (f + g) hfg] with t hab hft hgt hsum
      rw [hab,hsum,Pi.add_apply,Pi.add_apply,hft,hgt]
    | smul c a ha hfa =>
      obtain ⟨f,hf,rfl⟩ := hfa
      have hcf : IntervalSmoothCompact ℓ (c • f) :=
        ⟨hf.1.const_smul c,hf.2.1.smul_left,
          (tsupport_smul_subset_right (fun _ : ℝ => c) f).trans hf.2.2⟩
      refine ⟨c • f,hcf,?_⟩
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul c (smoothIntervalL2 ℓ f hf),
        smoothIntervalL2_ae ℓ f hf, smoothIntervalL2_ae ℓ (c • f) hcf] with t hsm hft hcf'
      rw [hsm,hcf',Pi.smul_apply,Pi.smul_apply,hft]
  · rintro ⟨f,hf,rfl⟩
    exact Submodule.subset_span ⟨⟨f,hf⟩,rfl⟩

/-- The actual PW image of the compact smooth interval core. -/
def pwSmoothModelCore {ℓ : ℝ} {u : BoundaryLInf}
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) : Submodule ℂ (Model u) :=
  (smoothIntervalCore ℓ).map U.toLinearEquiv.toLinearMap

theorem pwSmoothModelCore_dense (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) :
    Dense (pwSmoothModelCore U : Set (Model u)) := by
  have he : (pwSmoothModelCore U : Set (Model u)) =
      U '' (smoothIntervalCore ℓ : Set (IntervalL2 ℓ)) := by
    ext f
    exact Iff.rfl
  rw [he]
  exact U.surjective.denseRange.dense_image U.continuous (smoothIntervalCore_dense ℓ hℓ)

theorem pwSmoothModelCore_bounded (ℓ : ℝ) (hℓ : 0 < ℓ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (hU : PaleyWienerUnitary u ℓ U)
    (f : Model u) (hf : f ∈ pwSmoothModelCore U) : IsBounded f.val := by
  obtain ⟨a,ha,rfl⟩ := hf
  exact bounded_paleyWiener_smoothIntervalCore ℓ hℓ u U hU a ha

/-- Every element of the model core is literally the PW image of one compact smooth interval function. -/
theorem mem_pwSmoothModelCore_iff (ℓ : ℝ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (f : Model u) :
    f ∈ pwSmoothModelCore U ↔
      ∃ a : ℝ → ℂ, ∃ ha : IntervalSmoothCompact ℓ a, f = U (smoothIntervalL2 ℓ a ha) := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨b,hb,rfl⟩ := (mem_smoothIntervalCore_iff ℓ a).mp ha
    exact ⟨b,hb,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨smoothIntervalL2 ℓ a ha,(mem_smoothIntervalCore_iff ℓ _).mpr ⟨a,ha,rfl⟩,rfl⟩

/-- The concrete phase-one single-atom model has the dense compact smooth PW core. -/
theorem normalizedPW_smoothCore_dense (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Dense (pwSmoothModelCore (normalizedVolterraModelData ℓ hℓ).piModel :
      Set (Model (normalizedVolterraModelData ℓ hℓ).u)) :=
  pwSmoothModelCore_dense ℓ hℓ _ _

/-- Boundedness of every vector in that concrete core uses no model or Fourier hypothesis. -/
theorem normalizedPW_smoothCore_bounded (ℓ : ℝ) (hℓ : 0 < ℓ)
    (f : Model (normalizedAtomBoundary ℓ))
    (hf : f ∈ pwSmoothModelCore (normalizedVolterraModelData ℓ hℓ).piModel) :
    IsBounded f.val :=
  pwSmoothModelCore_bounded ℓ hℓ _ _ (normalizedVolterraModelData ℓ hℓ).piModel_formula f hf

end TTO.Paper.Proved
