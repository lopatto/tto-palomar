/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Portions of the reflection/Parseval argument: Copyright (c) 2026 The Tau Ceti contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.VolterraFoundations
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The half-integer interval systems for the exact Volterra singular values. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal positive half-integer frequency on an interval of length ℓ. -/
def halfFrequency (ℓ : ℝ) (n : ℕ) : ℝ := Real.pi * ((n : ℝ) + 1 / 2) / ℓ

def halfCosineFunction (ℓ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.sqrt (2 / ℓ) : ℂ) * Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ))

def halfSineFunction (ℓ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.sqrt (2 / ℓ) : ℂ) * Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ))

theorem memLp_halfCosineFunction (ℓ : ℝ) (n : ℕ) :
    MemLp (halfCosineFunction ℓ n) 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  apply MemLp.of_bound (by unfold halfCosineFunction; fun_prop) ‖(Real.sqrt (2 / ℓ) : ℂ)‖
  exact Eventually.of_forall fun t => by
    rw [halfCosineFunction, norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

theorem memLp_halfSineFunction (ℓ : ℝ) (n : ℕ) :
    MemLp (halfSineFunction ℓ n) 2 (volume.restrict (Ioo (0 : ℝ) ℓ)) := by
  apply MemLp.of_bound (by unfold halfSineFunction; fun_prop) ‖(Real.sqrt (2 / ℓ) : ℂ)‖
  exact Eventually.of_forall fun t => by
    rw [halfSineFunction, norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _

def halfCosineVector (ℓ : ℝ) (n : ℕ) : IntervalL2 ℓ :=
  (memLp_halfCosineFunction ℓ n).toLp (halfCosineFunction ℓ n)

def halfSineVector (ℓ : ℝ) (n : ℕ) : IntervalL2 ℓ :=
  (memLp_halfSineFunction ℓ n).toLp (halfSineFunction ℓ n)

theorem halfCosineVector_ae (ℓ : ℝ) (n : ℕ) :
    halfCosineVector ℓ n =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] halfCosineFunction ℓ n :=
  (memLp_halfCosineFunction ℓ n).coeFn_toLp

theorem halfSineVector_ae (ℓ : ℝ) (n : ℕ) :
    halfSineVector ℓ n =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] halfSineFunction ℓ n :=
  (memLp_halfSineFunction ℓ n).coeFn_toLp

/-- The elementary integer-frequency cosine integral, with the zero mode retained. -/
theorem integral_integer_cosine (ℓ : ℝ) (hℓ : 0 < ℓ) (k : ℤ) :
    (∫ t in (0 : ℝ)..ℓ, Complex.cos (((k : ℂ) * (Real.pi : ℂ) / (ℓ : ℂ)) * (t : ℂ))) =
      if k = 0 then (ℓ : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [ite_eq_right hk]
    have hl : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
    have hz : (k : ℂ) * (Real.pi : ℂ) / (ℓ : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hk)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hl
    rw [integral_cos_mul_complex hz, div_mul_cancel₀ _ hl]
    simp only [Complex.sin_int_mul_pi, Complex.ofReal_zero, mul_zero, Complex.sin_zero,
      zero_div, sub_zero]

theorem halfFrequency_pos (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) : 0 < halfFrequency ℓ n := by
  unfold halfFrequency
  positivity

theorem halfFrequency_length (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    halfFrequency ℓ n * ℓ = Real.pi * ((n : ℝ) + 1 / 2) := by
  rw [halfFrequency, div_mul_cancel₀ _ hℓ.ne']

/-- Product-to-sum identities used with the exact integer-frequency integral. -/
theorem complex_cosine_product (x y : ℂ) :
    Complex.cos x * Complex.cos y = (Complex.cos (x - y) + Complex.cos (x + y)) / 2 := by
  rw [Complex.cos_sub, Complex.cos_add]
  ring

theorem complex_sine_product (x y : ℂ) :
    Complex.sin x * Complex.sin y = (Complex.cos (x - y) - Complex.cos (x + y)) / 2 := by
  rw [Complex.cos_sub, Complex.cos_add]
  ring

theorem halfFrequency_sub (ℓ : ℝ) (m n : ℕ) :
    (halfFrequency ℓ m : ℂ) - (halfFrequency ℓ n : ℂ) =
      (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (Real.pi : ℂ) / (ℓ : ℂ) := by
  simp only [halfFrequency]
  push_cast
  ring

theorem halfFrequency_add (ℓ : ℝ) (m n : ℕ) :
    (halfFrequency ℓ m : ℂ) + (halfFrequency ℓ n : ℂ) =
      (((m + n + 1 : ℕ) : ℤ) : ℂ) * (Real.pi : ℂ) / (ℓ : ℂ) := by
  simp only [halfFrequency]
  push_cast
  ring

theorem integral_half_cosine_product (ℓ : ℝ) (hℓ : 0 < ℓ) (m n : ℕ) :
    (∫ t in (0 : ℝ)..ℓ, Complex.cos ((halfFrequency ℓ m : ℂ) * (t : ℂ)) *
      Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ))) =
      if m = n then (ℓ : ℂ) / 2 else 0 := by
  simp_rw [complex_cosine_product, ← sub_mul, ← add_mul]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [halfFrequency_sub, halfFrequency_add, integral_integer_cosine ℓ hℓ]
  have hs : (m : ℤ) + (n : ℤ) + 1 ≠ 0 := by omega
  by_cases h : m = n
  · subst n
    simp [hs]
  · simp [sub_eq_zero, h, hs]

theorem integral_half_sine_product (ℓ : ℝ) (hℓ : 0 < ℓ) (m n : ℕ) :
    (∫ t in (0 : ℝ)..ℓ, Complex.sin ((halfFrequency ℓ m : ℂ) * (t : ℂ)) *
      Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ))) =
      if m = n then (ℓ : ℂ) / 2 else 0 := by
  simp_rw [complex_sine_product, ← sub_mul, ← add_mul]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [halfFrequency_sub, halfFrequency_add, integral_integer_cosine ℓ hℓ]
  have hs : (m : ℤ) + (n : ℤ) + 1 ≠ 0 := by omega
  by_cases h : m = n
  · subst n
    simp [hs]
  · simp [sub_eq_zero, h, hs]

/-- Exact normalized interval pairing, including the diagonal constant. -/
theorem inner_halfCosineVector (ℓ : ℝ) (hℓ : 0 < ℓ) (m n : ℕ) :
    inner ℂ (halfCosineVector ℓ m) (halfCosineVector ℓ n) = if m = n then 1 else 0 := by
  have hk : (Real.sqrt (2 / ℓ) : ℂ) ^ 2 = ((2 / ℓ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  have hconj (t : ℝ) :
      conj (Complex.cos ((halfFrequency ℓ m : ℂ) * (t : ℂ))) =
        Complex.cos ((halfFrequency ℓ m : ℂ) * (t : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.conj_ofReal]
  calc
    _ = ((2 / ℓ : ℝ) : ℂ) * ∫ t in Ioo (0 : ℝ) ℓ,
        Complex.cos ((halfFrequency ℓ m : ℂ) * (t : ℂ)) *
          Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [halfCosineVector_ae ℓ m, halfCosineVector_ae ℓ n] with t hm hn
      rw [RCLike.inner_apply, hm, hn, halfCosineFunction, halfCosineFunction,
        map_mul, Complex.conj_ofReal, hconj]
      rw [← hk]
      ring
    _ = _ := by
      rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hℓ.le,
        integral_half_cosine_product ℓ hℓ]
      by_cases h : m = n
      · simp only [ite_eq_left h]
        push_cast
        field_simp [hℓ.ne']
      · simp only [ite_eq_right h, mul_zero]

theorem halfCosineVector_orthonormal (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Orthonormal ℂ (halfCosineVector ℓ) :=
  orthonormal_iff_ite.mpr (inner_halfCosineVector ℓ hℓ)

/-- Exact normalized interval pairing, including the diagonal constant. -/
theorem inner_halfSineVector (ℓ : ℝ) (hℓ : 0 < ℓ) (m n : ℕ) :
    inner ℂ (halfSineVector ℓ m) (halfSineVector ℓ n) = if m = n then 1 else 0 := by
  have hk : (Real.sqrt (2 / ℓ) : ℂ) ^ 2 = ((2 / ℓ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  have hconj (t : ℝ) :
      conj (Complex.sin ((halfFrequency ℓ m : ℂ) * (t : ℂ))) =
        Complex.sin ((halfFrequency ℓ m : ℂ) * (t : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.conj_ofReal]
  calc
    _ = ((2 / ℓ : ℝ) : ℂ) * ∫ t in Ioo (0 : ℝ) ℓ,
        Complex.sin ((halfFrequency ℓ m : ℂ) * (t : ℂ)) *
          Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [halfSineVector_ae ℓ m, halfSineVector_ae ℓ n] with t hm hn
      rw [RCLike.inner_apply, hm, hn, halfSineFunction, halfSineFunction,
        map_mul, Complex.conj_ofReal, hconj]
      rw [← hk]
      ring
    _ = _ := by
      rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hℓ.le,
        integral_half_sine_product ℓ hℓ]
      by_cases h : m = n
      · simp only [ite_eq_left h]
        push_cast
        field_simp [hℓ.ne']
      · simp only [ite_eq_right h, mul_zero]

theorem halfSineVector_orthonormal (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Orthonormal ℂ (halfSineVector ℓ) :=
  orthonormal_iff_ite.mpr (inner_halfSineVector ℓ hℓ)

/-- Complex even/odd reflection; ε=1 gives the cosine and ε=-1 the sine extension. -/
def intervalReflection (ε : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).piecewise f (fun t => ε * f (-t))

theorem intervalReflection_of_pos (ε : ℂ) (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    intervalReflection ε f t = f t := by
  exact Set.piecewise_eq_of_mem _ _ _ ht

theorem intervalReflection_of_nonpos (ε : ℂ) (f : ℝ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    intervalReflection ε f t = ε * f (-t) := by
  exact Set.piecewise_eq_of_notMem _ _ _ (not_lt.mpr ht)

/-- Complex reflection preserves interval L² integrability. Adapted from the Apache-2.0
TauCeti SineSeries reflection argument at revision d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad. -/
theorem memLp_intervalReflection (ℓ : ℝ) (hℓ : 0 < ℓ) (ε : ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ))) :
    MemLp (intervalReflection ε f) 2 (volume.restrict (Ioc (-ℓ) ℓ)) := by
  have hset1 : Ioi (0 : ℝ) ∩ Ioc (-ℓ) ℓ = Ioc (0 : ℝ) ℓ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, by linarith [h.1], h.2⟩
  have hset2 : (Ioi (0 : ℝ))ᶜ ∩ Ioc (-ℓ) ℓ = Ioc (-ℓ) (0 : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ioi, not_lt, Set.mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, by linarith [h.2]⟩
  apply MemLp.piecewise measurableSet_Ioi.nullMeasurableSet
  · rw [Measure.restrict_restrict measurableSet_Ioi, hset1]
    exact hf
  · rw [Measure.restrict_restrict measurableSet_Ioi.compl, hset2]
    have hmp : MeasurePreserving (fun t : ℝ => -t)
        (volume.restrict (Ioc (-ℓ) (0 : ℝ))) (volume.restrict (Ico (0 : ℝ) ℓ)) := by
      have h := ((volume : Measure ℝ).measurePreserving_sub_left 0).restrict_preimage
        (measurableSet_Ico (a := (0 : ℝ)) (b := ℓ))
      rw [preimage_const_sub_Ico, sub_zero, zero_sub] at h
      simpa only [zero_sub] using h
    have hf' : MemLp f 2 (volume.restrict (Ico (0 : ℝ) ℓ)) := by
      rwa [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact (hf'.comp_measurePreserving hmp).const_mul ε

/-- Integrating against the reflected function folds the negative interval onto the positive one. -/
theorem integral_mul_intervalReflection (ℓ : ℝ) (hℓ : 0 < ℓ) (ε : ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ))) {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in (-ℓ)..ℓ, F t * intervalReflection ε f t) =
      ∫ t in (0 : ℝ)..ℓ, (F t + ε * F (-t)) * f t := by
  have hfi : IntervalIntegrable f volume (0 : ℝ) ℓ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hℓ.le).mpr (hf.integrable (by norm_num))
  have hfi' : IntervalIntegrable (fun t => f (-t)) volume (-ℓ) (0 : ℝ) := by
    simpa only [sub_zero, zero_sub] using (hfi.comp_sub_left 0).symm
  have hleft : (∫ t in (-ℓ)..(0 : ℝ), F t * intervalReflection ε f t) =
      ∫ t in (0 : ℝ)..ℓ, F (-t) * (ε * f t) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun t => F t * (ε * f (-t))) (a := (0 : ℝ)) (b := ℓ) 0
    simp only [sub_zero, zero_sub, neg_neg] at hsub
    rw [hsub]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    dsimp only
    rw [intervalReflection_of_nonpos ε f ht.2]
  have hright : (∫ t in (0 : ℝ)..ℓ, F t * intervalReflection ε f t) =
      ∫ t in (0 : ℝ)..ℓ, F t * f t := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hℓ.le] at ht
      rw [intervalReflection_of_pos ε f ht.1]
  have hint1 : IntervalIntegrable (fun t => F t * f t) volume (0 : ℝ) ℓ :=
    hfi.continuousOn_mul hF.continuousOn
  have hint2 : IntervalIntegrable (fun t => F (-t) * (ε * f t)) volume (0 : ℝ) ℓ :=
    (hfi.const_mul ε).continuousOn_mul (hF.comp continuous_neg).continuousOn
  have hintL : IntervalIntegrable (fun t => F t * intervalReflection ε f t) volume (-ℓ) (0 : ℝ) := by
    apply ((hfi'.const_mul ε).continuousOn_mul hF.continuousOn).congr_ae
    rw [uIoc_of_le (by linarith)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [intervalReflection_of_nonpos ε f ht.2]
  have hintR : IntervalIntegrable (fun t => F t * intervalReflection ε f t) volume (0 : ℝ) ℓ := by
    apply hint1.congr_ae
    rw [uIoc_of_le hℓ.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [intervalReflection_of_pos ε f ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hintL hintR, hleft, hright,
    ← intervalIntegral.integral_add hint2 hint1]
  congr 1 with t
  ring

/-- The unit-modulus phase shifting the integer Fourier grid by one half. -/
def halfFourierPhase (ℓ t : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t / (2 * ℓ) : ℝ) : ℂ) * Complex.I)

theorem norm_halfFourierPhase (ℓ t : ℝ) : ‖halfFourierPhase ℓ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem memLp_phaseReflection (ℓ : ℝ) (hℓ : 0 < ℓ) (ε : ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ))) :
    MemLp (fun t => halfFourierPhase ℓ t * intervalReflection ε f t) 2
      (volume.restrict (Ioc (-ℓ) ℓ)) := by
  have hE := memLp_intervalReflection ℓ hℓ ε hf
  have hc : Continuous (halfFourierPhase ℓ) := by unfold halfFourierPhase; fun_prop
  apply hE.of_le (hc.aestronglyMeasurable.mul hE.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by rw [Pi.mul_apply, norm_mul, norm_halfFourierPhase, one_mul]

/-- The actual Fourier character and the phase give precisely the half-integer exponential. -/
theorem fourier_mul_halfFourierPhase (ℓ : ℝ) (_hℓ : 0 < ℓ) (n : ℤ) (t : ℝ) :
    fourier (T := ℓ - (-ℓ)) (-n) (t : AddCircle (ℓ - (-ℓ))) * halfFourierPhase ℓ t =
      Complex.exp (-(((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) * Complex.I) := by
  rw [fourier_coe_apply, halfFourierPhase, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Native interval Parseval uniqueness with arbitrary endpoints. -/
theorem interval_fourier_unique {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hc : ∀ n : ℤ, fourierCoeffOn hab f n = 0) : f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hs := hasSum_sq_fourierCoeffOn hab hf
  simp only [hc, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
  have hzero := hasSum_zero.unique hs
  rw [eq_comm, smul_eq_mul, mul_eq_zero, intervalIntegral.integral_of_le hab.le] at hzero
  have hint : ∫ t in Ioc a b, ‖f t‖ ^ 2 = 0 :=
    hzero.resolve_left (inv_ne_zero (sub_pos.mpr hab).ne')
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun t => by positivity)
    (hf.integrable_norm_pow' (p := 2))).mp hint] with t ht
  simpa using ht

/-- The shifted Fourier exponential, with an integer index before even/odd folding. -/
def halfIntegerExponential (ℓ : ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-(((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) * Complex.I)

/-- Reflection plus the half phase reduces interval totality to ordinary native Parseval. -/
theorem ae_zero_of_half_fold (ℓ : ℝ) (hℓ : 0 < ℓ) (ε : ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ)))
    (hfold : ∀ n : ℤ, (∫ t in (0 : ℝ)..ℓ,
      (halfIntegerExponential ℓ n t + ε * halfIntegerExponential ℓ n (-t)) * f t) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) ℓ)] 0 := by
  let g := fun t => halfFourierPhase ℓ t * intervalReflection ε f t
  have hg : MemLp g 2 (volume.restrict (Ioc (-ℓ) ℓ)) := memLp_phaseReflection ℓ hℓ ε hf
  have hc : ∀ n : ℤ, fourierCoeffOn (by linarith : -ℓ < ℓ) g n = 0 := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    simp only [smul_eq_mul]
    dsimp only [g]
    simp_rw [← mul_assoc, fourier_mul_halfFourierPhase ℓ hℓ]
    change (1 / (ℓ - (-ℓ)) : ℝ) • (∫ t in (-ℓ)..ℓ,
      halfIntegerExponential ℓ n t * intervalReflection ε f t) = 0
    rw [integral_mul_intervalReflection ℓ hℓ ε hf (by unfold halfIntegerExponential; fun_prop),
      hfold n, smul_zero]
  have hz := interval_fourier_unique (by linarith : -ℓ < ℓ) hg hc
  have hz' : g =ᵐ[volume.restrict (Ioc (0 : ℝ) ℓ)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc (by linarith) le_rfl) hz
  filter_upwards [hz', ae_restrict_mem measurableSet_Ioc] with t ht hm
  change halfFourierPhase ℓ t * intervalReflection ε f t = 0 at ht
  rw [intervalReflection_of_pos ε f hm.1] at ht
  exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)

/-- Even folding of the literal shifted exponential. -/
theorem halfIntegerExponential_cos_fold (ℓ : ℝ) (n : ℤ) (t : ℝ) :
    halfIntegerExponential ℓ n t + (1 : ℂ) * halfIntegerExponential ℓ n (-t) =
      2 * Complex.cos (((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) := by
  unfold halfIntegerExponential
  rw [Complex.ofReal_neg, mul_neg, neg_neg, Complex.cos]
  ring

/-- Odd folding of the literal shifted exponential. -/
theorem halfIntegerExponential_sin_fold (ℓ : ℝ) (n : ℤ) (t : ℝ) :
    halfIntegerExponential ℓ n t + (-1 : ℂ) * halfIntegerExponential ℓ n (-t) =
      -2 * Complex.I * Complex.sin (((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) := by
  unfold halfIntegerExponential
  rw [Complex.ofReal_neg, mul_neg, neg_neg, Complex.sin]
  simp only [neg_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The negative integer half frequencies are indexed by -k-1, not by -k. -/
theorem half_cosine_integral_int_zero (ℓ : ℝ) (f : ℝ → ℂ)
    (h : ∀ n : ℕ, (∫ t in (0 : ℝ)..ℓ,
      Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0) (n : ℤ) :
    (∫ t in (0 : ℝ)..ℓ,
      Complex.cos (((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) * f t) = 0 := by
  rcases n with k | k
  · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, halfFrequency] using h k
  · have he : ((Real.pi * (((Int.negSucc k : ℤ) : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) =
        -(halfFrequency ℓ k : ℂ) := by
      simp only [Int.cast_negSucc, halfFrequency]
      push_cast
      ring
    simp_rw [he, neg_mul, Complex.cos_neg]
    exact h k

/-- The exact half-integer cosine system is total for arbitrary complex interval L² functions. -/
theorem ae_zero_of_half_cosine_integrals (ℓ : ℝ) (hℓ : 0 < ℓ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ)))
    (h : ∀ n : ℕ, (∫ t in (0 : ℝ)..ℓ,
      Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) ℓ)] 0 := by
  apply ae_zero_of_half_fold ℓ hℓ 1 hf
  intro n
  simp_rw [halfIntegerExponential_cos_fold, mul_assoc]
  rw [intervalIntegral.integral_const_mul, half_cosine_integral_int_zero ℓ f h n, mul_zero]

/-- The negative integer half frequencies are indexed by -k-1, not by -k. -/
theorem half_sine_integral_int_zero (ℓ : ℝ) (f : ℝ → ℂ)
    (h : ∀ n : ℕ, (∫ t in (0 : ℝ)..ℓ,
      Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0) (n : ℤ) :
    (∫ t in (0 : ℝ)..ℓ,
      Complex.sin (((Real.pi * ((n : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) * (t : ℂ)) * f t) = 0 := by
  rcases n with k | k
  · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, halfFrequency] using h k
  · have he : ((Real.pi * (((Int.negSucc k : ℤ) : ℝ) + 1 / 2) / ℓ : ℝ) : ℂ) =
        -(halfFrequency ℓ k : ℂ) := by
      simp only [Int.cast_negSucc, halfFrequency]
      push_cast
      ring
    simp_rw [he, neg_mul, Complex.sin_neg]
    simp_rw [neg_mul, intervalIntegral.integral_neg, h k, neg_zero]

/-- The exact half-integer sine system is total for arbitrary complex interval L² functions. -/
theorem ae_zero_of_half_sine_integrals (ℓ : ℝ) (hℓ : 0 < ℓ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ℓ)))
    (h : ∀ n : ℕ, (∫ t in (0 : ℝ)..ℓ,
      Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) ℓ)] 0 := by
  apply ae_zero_of_half_fold ℓ hℓ (-1) hf
  intro n
  simp_rw [halfIntegerExponential_sin_fold, mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    half_sine_integral_int_zero ℓ f h n, mul_zero, mul_zero]

theorem inner_halfCosineVector_test (ℓ : ℝ) (n : ℕ) (f : IntervalL2 ℓ) :
    inner ℂ (halfCosineVector ℓ n) f = (Real.sqrt (2 / ℓ) : ℂ) *
      ∫ t in Ioo (0 : ℝ) ℓ, Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [halfCosineVector_ae ℓ n] with t ht
  have hc : conj (Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ))) =
      Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.conj_ofReal]
  rw [RCLike.inner_apply, ht, halfCosineFunction, map_mul, Complex.conj_ofReal, hc]
  ring

theorem halfCosineVectors_total (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (Submodule.span ℂ (Set.range (halfCosineVector ℓ)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hk : (Real.sqrt (2 / ℓ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos (by norm_num : (0 : ℝ) < 2) hℓ)).ne'
  have hi (n : ℕ) : (∫ t in (0 : ℝ)..ℓ,
      Complex.cos ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0 := by
    have hm : halfCosineVector ℓ n ∈ Submodule.span ℂ (Set.range (halfCosineVector ℓ)) :=
      Submodule.subset_span ⟨n, rfl⟩
    have hp : inner ℂ (halfCosineVector ℓ n) f = 0 :=
      (Submodule.mem_orthogonal _ _).mp hf _ hm
    rw [inner_halfCosineVector_test] at hp
    rw [intervalIntegral.integral_of_le hℓ.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (mul_eq_zero.mp hp).resolve_left hk
  have hm : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact Lp.memLp f
  have hz := ae_zero_of_half_cosine_integrals ℓ hℓ hm hi
  have hz' : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] 0 := by
    simpa only [← restrict_Ioo_eq_restrict_Ioc] using hz
  apply Lp.ext
  exact hz'.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ))).symm

/-- The actual normalized half-integer cosine Hilbert basis on the whole complex interval L² space. -/
def halfCosineBasis (ℓ : ℝ) (hℓ : 0 < ℓ) : HilbertBasis ℕ ℂ (IntervalL2 ℓ) :=
  HilbertBasis.mkOfOrthogonalEqBot (halfCosineVector_orthonormal ℓ hℓ) (halfCosineVectors_total ℓ hℓ)

theorem inner_halfSineVector_test (ℓ : ℝ) (n : ℕ) (f : IntervalL2 ℓ) :
    inner ℂ (halfSineVector ℓ n) f = (Real.sqrt (2 / ℓ) : ℂ) *
      ∫ t in Ioo (0 : ℝ) ℓ, Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [halfSineVector_ae ℓ n] with t ht
  have hc : conj (Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ))) =
      Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.conj_ofReal]
  rw [RCLike.inner_apply, ht, halfSineFunction, map_mul, Complex.conj_ofReal, hc]
  ring

theorem halfSineVectors_total (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (Submodule.span ℂ (Set.range (halfSineVector ℓ)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hk : (Real.sqrt (2 / ℓ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos (by norm_num : (0 : ℝ) < 2) hℓ)).ne'
  have hi (n : ℕ) : (∫ t in (0 : ℝ)..ℓ,
      Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) * f t) = 0 := by
    have hm : halfSineVector ℓ n ∈ Submodule.span ℂ (Set.range (halfSineVector ℓ)) :=
      Submodule.subset_span ⟨n, rfl⟩
    have hp : inner ℂ (halfSineVector ℓ n) f = 0 :=
      (Submodule.mem_orthogonal _ _).mp hf _ hm
    rw [inner_halfSineVector_test] at hp
    rw [intervalIntegral.integral_of_le hℓ.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (mul_eq_zero.mp hp).resolve_left hk
  have hm : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact Lp.memLp f
  have hz := ae_zero_of_half_sine_integrals ℓ hℓ hm hi
  have hz' : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioo (0 : ℝ) ℓ)] 0 := by
    simpa only [← restrict_Ioo_eq_restrict_Ioc] using hz
  apply Lp.ext
  exact hz'.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo (0 : ℝ) ℓ))).symm

/-- The actual normalized half-integer sine Hilbert basis on the whole complex interval L² space. -/
def halfSineBasis (ℓ : ℝ) (hℓ : 0 < ℓ) : HilbertBasis ℕ ℂ (IntervalL2 ℓ) :=
  HilbertBasis.mkOfOrthogonalEqBot (halfSineVector_orthonormal ℓ hℓ) (halfSineVectors_total ℓ hℓ)

@[simp] theorem halfCosineBasis_apply (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    halfCosineBasis ℓ hℓ n = halfCosineVector ℓ n := by
  simp only [halfCosineBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

@[simp] theorem halfSineBasis_apply (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    halfSineBasis ℓ hℓ n = halfSineVector ℓ n := by
  simp only [halfSineBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The actual Volterra operator maps each normalized cosine to the corresponding sine
with precisely the reciprocal half-integer frequency. -/
theorem volterraOperator_halfCosineVector (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    volterraOperator ℓ (halfCosineVector ℓ n) =
      (halfFrequency ℓ n : ℂ)⁻¹ • halfSineVector ℓ n := by
  apply Lp.ext
  filter_upwards [volterraOperator_represents ℓ (halfCosineVector ℓ n),
    Lp.coeFn_smul (halfFrequency ℓ n : ℂ)⁻¹ (halfSineVector ℓ n),
    halfSineVector_ae ℓ n, ae_restrict_mem measurableSet_Ioo] with t hV hs hsin ht
  rw [hV, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsin]
  have hc := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo le_rfl ht.2.le) (halfCosineVector_ae ℓ n)
  calc
    (∫ s in Ioo (0 : ℝ) t, halfCosineVector ℓ n s) =
        ∫ s in Ioo (0 : ℝ) t, halfCosineFunction ℓ n s := integral_congr_ae hc
    _ = (Real.sqrt (2 / ℓ) : ℂ) *
        (Complex.sin ((halfFrequency ℓ n : ℂ) * (t : ℂ)) / (halfFrequency ℓ n : ℂ)) := by
      simp only [halfCosineFunction]
      rw [integral_const_mul, restrict_Ioo_eq_restrict_Ioc,
        ← intervalIntegral.integral_of_le ht.1.le,
        integral_cos_mul_complex (Complex.ofReal_ne_zero.mpr (halfFrequency_pos ℓ hℓ n).ne'),
        Complex.ofReal_zero, mul_zero, Complex.sin_zero, zero_div, sub_zero]
    _ = _ := by rw [halfSineFunction]; ring

end TTO.Paper.Proved
