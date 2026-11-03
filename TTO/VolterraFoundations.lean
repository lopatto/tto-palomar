/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.Proofs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The actual Volterra integral operator on the manuscript's interval L² space. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The constant-one interval L² vector, also defined for empty intervals. -/
def intervalOne (ℓ : ℝ) : IntervalL2 ℓ := (memLp_const (1 : ℂ)).toLp (fun _ => 1)

theorem intervalOne_ae (ℓ : ℝ) :
    intervalOne ℓ =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] (fun _ => (1 : ℂ)) :=
  (memLp_const (1 : ℂ)).coeFn_toLp

/-- The literal characteristic vector of the interval below t, inside (0,ℓ). -/
def intervalLowerRow (ℓ t : ℝ) : IntervalL2 ℓ :=
  ((memLp_const (1 : ℂ) : MemLp (fun _ : ℝ => (1 : ℂ)) 2
    (volume.restrict (Ioo (0 : ℝ) ℓ))).indicator (s := Iio t) measurableSet_Iio.nullMeasurableSet).toLp ((Iio t).indicator (fun _ => 1))

theorem intervalLowerRow_ae (ℓ t : ℝ) :
    intervalLowerRow ℓ t =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] (Iio t).indicator (fun _ => (1 : ℂ)) :=
  ((memLp_const (1 : ℂ) : MemLp (fun _ : ℝ => (1 : ℂ)) 2
    (volume.restrict (Ioo (0 : ℝ) ℓ))).indicator (s := Iio t) measurableSet_Iio.nullMeasurableSet).coeFn_toLp

theorem norm_intervalLowerRow_le (ℓ t : ℝ) : ‖intervalLowerRow ℓ t‖ ≤ ‖intervalOne ℓ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [intervalLowerRow_ae ℓ t, intervalOne_ae ℓ] with s hs ho
  rw [hs, ho]
  by_cases h : s ∈ Iio t <;> simp [Set.indicator, h]

/-- The actual lower-triangular integral, temporarily written using the restricted interval measure. -/
def volterraRaw (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) : ℂ :=
  ∫ s, (Iio t).indicator f s ∂(volume.restrict (Ioo (0 : ℝ) ℓ))

theorem volterraRaw_eq_inner (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) :
    volterraRaw ℓ f t = inner ℂ (intervalLowerRow ℓ t) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalLowerRow_ae ℓ t] with s hs
  rw [hs]
  by_cases h : s ∈ Iio t <;> simp [Set.indicator, h, RCLike.inner_apply]

theorem norm_volterraRaw_le (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) :
    ‖volterraRaw ℓ f t‖ ≤ ‖intervalOne ℓ‖ * ‖f‖ := by
  rw [volterraRaw_eq_inner]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right (norm_intervalLowerRow_le ℓ t) (norm_nonneg f))

/-- Joint measurability of the literal triangular kernel gives a measurable integral function. -/
theorem stronglyMeasurable_volterraRaw (ℓ : ℝ) (f : IntervalL2 ℓ) :
    StronglyMeasurable (volterraRaw ℓ f) := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hf : StronglyMeasurable (fun p : ℝ × ℝ =>
      ({q : ℝ × ℝ | q.2 < q.1}).indicator (fun q => f q.2) p) :=
    ((Lp.stronglyMeasurable f).comp_measurable measurable_snd).indicator hm
  change StronglyMeasurable (fun t => ∫ s, (Iio t).indicator f s
    ∂(volume.restrict (Ioo (0 : ℝ) ℓ)))
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio] using
    hf.integral_prod_right' (ν := volume.restrict (Ioo (0 : ℝ) ℓ))

theorem memLp_volterraRaw (ℓ : ℝ) (f : IntervalL2 ℓ) :
    MemLp (volterraRaw ℓ f) 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) :=
  MemLp.of_bound (stronglyMeasurable_volterraRaw ℓ f).aestronglyMeasurable
    (‖intervalOne ℓ‖ * ‖f‖) (Eventually.of_forall (norm_volterraRaw_le ℓ f))

/-- The interval L² vector of the literal Volterra integral. -/
def volterraVector (ℓ : ℝ) (f : IntervalL2 ℓ) : IntervalL2 ℓ :=
  (memLp_volterraRaw ℓ f).toLp (volterraRaw ℓ f)

theorem volterraVector_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    volterraVector ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] volterraRaw ℓ f :=
  (memLp_volterraRaw ℓ f).coeFn_toLp

theorem volterraVector_add (ℓ : ℝ) (f g : IntervalL2 ℓ) :
    volterraVector ℓ (f + g) = volterraVector ℓ f + volterraVector ℓ g := by
  apply Lp.ext
  filter_upwards [volterraVector_ae ℓ (f + g), volterraVector_ae ℓ f, volterraVector_ae ℓ g,
    Lp.coeFn_add (volterraVector ℓ f) (volterraVector ℓ g)] with t hfg hf hg ha
  rw [hfg, ha]
  simp only [Pi.add_apply]
  rw [hf, hg]
  unfold volterraRaw
  rw [← integral_add (((Lp.memLp f).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))).indicator measurableSet_Iio)
    (((Lp.memLp g).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))).indicator measurableSet_Iio)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with s hs
  by_cases h : s ∈ Iio t
  · simp only [Set.indicator_of_mem h]
    exact hs
  · simp only [Set.indicator_of_notMem h, add_zero]

theorem volterraVector_smul (ℓ : ℝ) (f : IntervalL2 ℓ) (c : ℂ) :
    volterraVector ℓ (c • f) = c • volterraVector ℓ f := by
  apply Lp.ext
  filter_upwards [volterraVector_ae ℓ (c • f), volterraVector_ae ℓ f,
    Lp.coeFn_smul c (volterraVector ℓ f)] with t hcf hf hc
  rw [hcf, hc]
  simp only [Pi.smul_apply]
  rw [hf]
  unfold volterraRaw
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with s hs
  by_cases h : s ∈ Iio t
  · simp only [Set.indicator_of_mem h]
    exact hs
  · simp only [Set.indicator_of_notMem h, smul_zero]

/-- The actual algebraic Volterra map. -/
def volterraLinearMap (ℓ : ℝ) : IntervalL2 ℓ →ₗ[ℂ] IntervalL2 ℓ where
  toFun := volterraVector ℓ
  map_add' := volterraVector_add ℓ
  map_smul' c f := volterraVector_smul ℓ f c

/-- The literal integral map, made continuous by finite-measure Cauchy–Schwarz. -/
def volterraOperator (ℓ : ℝ) : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  (volterraLinearMap ℓ).mkContinuous
    ((measureUnivNNReal (volume.restrict (Ioo (0 : ℝ) ℓ)) : ℝ) ^
      ((2 : ℝ≥0∞).toReal⁻¹) * ‖intervalOne ℓ‖) (fun f => by
    have hb : ‖volterraVector ℓ f‖ ≤
        (measureUnivNNReal (volume.restrict (Ioo (0 : ℝ) ℓ)) : ℝ) ^
          ((2 : ℝ≥0∞).toReal⁻¹) * (‖intervalOne ℓ‖ * ‖f‖) := by
      apply Lp.norm_le_of_ae_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      filter_upwards [volterraVector_ae ℓ f] with t ht
      rw [ht]
      exact norm_volterraRaw_le ℓ f t
    simpa only [volterraLinearMap, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using hb)

theorem volterraOperator_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    volterraOperator ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] volterraRaw ℓ f :=
  volterraVector_ae ℓ f

/-- The restricted-measure integral is exactly the manuscript's lower interval integral. -/
theorem volterraRaw_interval (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) (ht : t < ℓ) :
    volterraRaw ℓ f t = ∫ s in Ioo (0 : ℝ) t, f s := by
  unfold volterraRaw
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio t ∩ Ioo (0 : ℝ) ℓ = Ioo (0 : ℝ) t := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans ht⟩
  rw [hset]

/-- The bounded linear map has precisely the frozen Volterra meaning. -/
theorem volterraOperator_represents (ℓ : ℝ) : RepresentsVolterra ℓ (volterraOperator ℓ) := by
  intro f
  filter_upwards [volterraOperator_ae ℓ f, ae_restrict_mem measurableSet_Ioo] with t ht hm
  exact ht.trans (volterraRaw_interval ℓ f t hm.2)

/-- Weighted triangular Fubini, with both integrability hypotheses explicit. -/
theorem integral_mul_lower_swap {μ : Measure ℝ} [SFinite μ] {f g : ℝ → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ t, g t * (∫ s, (Iio t).indicator f s ∂μ) ∂μ) =
      ∫ s, f s * (∫ t, (Ioi s).indicator g t ∂μ) ∂μ := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} := measurableSet_lt measurable_snd measurable_fst
  have hh : Integrable (Function.uncurry (fun t s => if s < t then g t * f s else 0)) (μ.prod μ) := by
    convert (hg.mul_prod hf).indicator hm using 1
    funext p
    rfl
  calc
    _ = ∫ t, ∫ s, if s < t then g t * f s else 0 ∂μ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by
          simp only [Set.indicator_apply, Set.mem_Iio, mul_ite, mul_zero]
    _ = ∫ s, ∫ t, if s < t then g t * f s else 0 ∂μ ∂μ := integral_integral_swap hh
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun t => by
          simp only [Set.indicator_apply, Set.mem_Ioi, mul_ite, mul_zero, mul_comm]

theorem inner_intervalOne (ℓ : ℝ) (f : IntervalL2 ℓ) :
    inner ℂ (intervalOne ℓ) f = ∫ t, f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalOne_ae ℓ] with t ht
  rw [ht]
  simp only [RCLike.inner_apply, map_one, mul_one]

/-- The genuine constant-integral rank-one map. -/
def intervalIntegralOperator (ℓ : ℝ) : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  (innerSL ℂ (intervalOne ℓ)).smulRight (intervalOne ℓ)

theorem intervalIntegralOperator_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    intervalIntegralOperator ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      (fun _ => ∫ t, f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ))) := by
  change (inner ℂ (intervalOne ℓ) f) • intervalOne ℓ =ᵐ[_] _
  filter_upwards [Lp.coeFn_smul (inner ℂ (intervalOne ℓ) f) (intervalOne ℓ),
    intervalOne_ae ℓ] with t hs ht
  rw [hs]
  simp only [Pi.smul_apply, ht, smul_eq_mul, mul_one, inner_intervalOne]

/-- The upper-triangular integral on the same interval measure. -/
def volterraUpperRaw (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) : ℂ :=
  ∫ s, (Ioi t).indicator f s ∂(volume.restrict (Ioo (0 : ℝ) ℓ))

theorem volterraRaw_add_upper (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) :
    volterraRaw ℓ f t + volterraUpperRaw ℓ f t =
      ∫ s, f s ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  rw [volterraRaw, volterraUpperRaw, integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Ioi, ← integral_Ici_eq_integral_Ioi]
  exact intervalIntegral.integral_Iio_add_Ici
    (((Lp.memLp f).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))).integrableOn)
    (((Lp.memLp f).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))).integrableOn)

/-- The upper integral map, constructed without assuming an adjoint formula. -/
def volterraUpperOperator (ℓ : ℝ) : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ :=
  intervalIntegralOperator ℓ - volterraOperator ℓ

theorem volterraUpperOperator_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    volterraUpperOperator ℓ f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] volterraUpperRaw ℓ f := by
  filter_upwards [Lp.coeFn_sub (intervalIntegralOperator ℓ f) (volterraOperator ℓ f),
    intervalIntegralOperator_ae ℓ f, volterraOperator_ae ℓ f] with t hs hJ hV
  change (intervalIntegralOperator ℓ f - volterraOperator ℓ f) t = _
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hJ, hV, ← volterraRaw_add_upper ℓ f t]
  abel

/-- The explicit adjoint pairing follows from integrable triangular Fubini. -/
theorem inner_volterraOperator (ℓ : ℝ) (f g : IntervalL2 ℓ) :
    inner ℂ g (volterraOperator ℓ f) = inner ℂ (volterraUpperOperator ℓ g) f := by
  have hf := (Lp.memLp f).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hg := ((Lp.memLp g).star).integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hconj (s : ℝ) :
      (∫ t, (Ioi s).indicator (fun t => conj (g t)) t
        ∂(volume.restrict (Ioo (0 : ℝ) ℓ))) = conj (volterraUpperRaw ℓ g s) := by
    rw [volterraUpperRaw, ← integral_conj]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      by_cases h : t ∈ Ioi s <;> simp [Set.indicator, h]
  calc
    _ = ∫ t, conj (g t) * volterraRaw ℓ f t ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [volterraOperator_ae ℓ f] with t ht
      rw [ht, RCLike.inner_apply, mul_comm]
    _ = ∫ s, f s * (∫ t, (Ioi s).indicator (fun t => conj (g t)) t
        ∂(volume.restrict (Ioo (0 : ℝ) ℓ))) ∂(volume.restrict (Ioo (0 : ℝ) ℓ)) :=
      integral_mul_lower_swap hf hg
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [volterraUpperOperator_ae ℓ g] with s hs
      rw [hs, RCLike.inner_apply, hconj]

/-- The actual Hilbert adjoint is the upper-triangular integral operator. -/
theorem adjoint_volterraOperator (ℓ : ℝ) :
    (volterraOperator ℓ).adjoint = volterraUpperOperator ℓ := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact inner_volterraOperator ℓ f g

/-- Exact symmetrization, before taking any rank or ideal conclusion. -/
theorem volterraOperator_add_adjoint (ℓ : ℝ) :
    volterraOperator ℓ + (volterraOperator ℓ).adjoint = intervalIntegralOperator ℓ := by
  rw [adjoint_volterraOperator, volterraUpperOperator]
  abel

/-- The manuscript's literal rank-one formula. -/
theorem volterraOperator_add_adjoint_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    (volterraOperator ℓ + (volterraOperator ℓ).adjoint) f
      =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] (fun _ => ∫ s in Ioo (0 : ℝ) ℓ, f s) := by
  rw [volterraOperator_add_adjoint]
  exact intervalIntegralOperator_ae ℓ f

theorem volterraUpperRaw_interval (ℓ : ℝ) (f : IntervalL2 ℓ) (t : ℝ) (ht : 0 < t) :
    volterraUpperRaw ℓ f t = ∫ s in Ioo t ℓ, f s := by
  rw [volterraUpperRaw, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi t ∩ Ioo (0 : ℝ) ℓ = Ioo t ℓ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, ht.trans h.1, h.2⟩
  rw [hset]

/-- Literal upper-interval formula for the actual Hilbert adjoint. -/
theorem adjoint_volterraOperator_ae (ℓ : ℝ) (f : IntervalL2 ℓ) :
    (volterraOperator ℓ).adjoint f =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)]
      (fun t => ∫ s in Ioo t ℓ, f s) := by
  rw [adjoint_volterraOperator]
  filter_upwards [volterraUpperOperator_ae ℓ f, ae_restrict_mem measurableSet_Ioo] with t ht hm
  exact ht.trans (volterraUpperRaw_interval ℓ f t hm.1)

theorem integral_intervalOne (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (∫ t, intervalOne ℓ t ∂(volume.restrict (Ioo (0 : ℝ) ℓ))) = (ℓ : ℂ) := by
  rw [integral_congr_ae (intervalOne_ae ℓ)]
  simp [Measure.real, Real.volume_Ioo, hℓ.le]

theorem inner_intervalOne_self (ℓ : ℝ) (hℓ : 0 < ℓ) :
    inner ℂ (intervalOne ℓ) (intervalOne ℓ) = (ℓ : ℂ) := by
  rw [inner_intervalOne, integral_intervalOne ℓ hℓ]

theorem intervalOne_ne_zero (ℓ : ℝ) (hℓ : 0 < ℓ) : intervalOne ℓ ≠ 0 := by
  intro hz
  have hh := inner_intervalOne_self ℓ hℓ
  rw [hz, inner_zero_left] at hh
  exact (Complex.ofReal_ne_zero.mpr hℓ.ne') hh.symm

/-- Exact rank one, using the genuinely nonzero interval vector when ℓ>0. -/
theorem intervalIntegralOperator_rank (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (intervalIntegralOperator ℓ).rank = 1 := by
  change Module.rank ℂ (intervalIntegralOperator ℓ).toLinearMap.range = 1
  apply (rank_submodule_eq_one_iff _).mpr
  refine ⟨intervalOne ℓ, ?_, intervalOne_ne_zero ℓ hℓ, ?_⟩
  · refine ⟨(ℓ : ℂ)⁻¹ • intervalOne ℓ, ?_⟩
    change inner ℂ (intervalOne ℓ) ((ℓ : ℂ)⁻¹ • intervalOne ℓ) • intervalOne ℓ = intervalOne ℓ
    rw [inner_smul_right, inner_intervalOne_self ℓ hℓ,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hℓ.ne'), one_smul]
  · rintro x ⟨f, rfl⟩
    change inner ℂ (intervalOne ℓ) f • intervalOne ℓ ∈ ℂ ∙ intervalOne ℓ
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The rank statement in the manuscript's actual Volterra model. -/
theorem volterraOperator_rank_one (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (volterraOperator ℓ + (volterraOperator ℓ).adjoint).rank = 1 := by
  rw [volterraOperator_add_adjoint]
  exact intervalIntegralOperator_rank ℓ hℓ

end TTO.Paper.Proved
