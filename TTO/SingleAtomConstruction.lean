/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBoundaryFoundations
public import TTO.AngularFoundations
public import TTO.MalmquistFoundations
public import TTO.TrigonometricFoundations

/-! Constructing an actual single-atom singular inner boundary symbol. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal analytic function with a positive point mass and phase one. -/
def atomDiskFunction (ℓ : ℝ) (ζ : Boundary) (z : ℂ) : ℂ :=
  Complex.exp (-(ℓ : ℂ) * (fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z))

/-- The boundary formula is totalized at the single pole, a null singleton. -/
def atomBoundaryFunction (ℓ : ℝ) (ζ t : Boundary) : ℂ :=
  atomDiskFunction ℓ ζ (fourier (T := 1) 1 t)

theorem norm_atomDiskFunction (ℓ : ℝ) (ζ : Boundary) (z : ℂ) :
    ‖atomDiskFunction ℓ ζ z‖ = Real.exp (-ℓ * atomicPoissonKernel z ζ) := by
  unfold atomDiskFunction
  rw [Complex.norm_exp]
  have he : -(ℓ : ℂ) * (fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z) =
      -(ℓ : ℂ) * ((fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z)) := by ring
  rw [he]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  rw [herglotz_re z _ (by simp only [fourier_apply, Circle.norm_coe])]
  rfl

theorem analyticOnNhd_atomDiskFunction (ℓ : ℝ) (ζ : Boundary) :
    AnalyticOnNhd ℂ (atomDiskFunction ℓ ζ) disk := by
  intro z hz
  have hne : fourier (T := 1) 1 ζ - z ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    have hz' : ‖z‖ < 1 := hz
    simp only [fourier_apply, Circle.norm_coe] at hn
    linarith
  exact (((analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hne).cexp')

theorem norm_atomDiskFunction_le_one (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (ζ : Boundary)
    {z : ℂ} (hz : z ∈ disk) : ‖atomDiskFunction ℓ ζ z‖ ≤ 1 := by
  rw [norm_atomDiskFunction, Real.exp_le_one_iff]
  have hp : 0 ≤ atomicPoissonKernel z ζ := by
    unfold atomicPoissonKernel
    apply div_nonneg _ (sq_nonneg _)
    have hz' : ‖z‖ < 1 := hz
    nlinarith [norm_nonneg z]
  nlinarith

theorem norm_atomBoundaryFunction (ℓ : ℝ) (ζ t : Boundary) :
    ‖atomBoundaryFunction ℓ ζ t‖ = 1 := by
  rw [atomBoundaryFunction, norm_atomDiskFunction]
  simp only [atomicPoissonKernel, fourier_apply, Circle.norm_coe, one_pow, sub_self,
    zero_div, mul_zero, Real.exp_zero]

/-- The explicit boundary formula is the actual radial limit away from its one pole. -/
theorem tendsto_atomDiskFunction_radial (ℓ : ℝ) (ζ t : Boundary) (ht : t ≠ ζ) :
    Tendsto (fun r : ℝ => atomDiskFunction ℓ ζ ((r : ℂ) * fourier (T := 1) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (atomBoundaryFunction ℓ ζ t)) := by
  have hne : fourier (T := 1) 1 ζ - fourier (T := 1) 1 t ≠ 0 := by
    intro h
    apply ht
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    apply Subtype.ext
    simpa only [fourier_one] using (sub_eq_zero.mp h).symm
  have hc : ContinuousAt (atomDiskFunction ℓ ζ) (fourier (T := 1) 1 t) := by
    unfold atomDiskFunction
    fun_prop (disch := assumption)
  have hr : Tendsto (fun r : ℝ => (r : ℂ) * fourier (T := 1) 1 t)
      (𝓝[<] (1 : ℝ)) (𝓝 (fourier (T := 1) 1 t)) := by
    have hm : Continuous (fun r : ℝ => (r : ℂ) * fourier (T := 1) 1 t) := by fun_prop
    simpa only [Complex.ofReal_one, one_mul] using
      (hm.tendsto 1).mono_left nhdsWithin_le_nhds
  exact hc.tendsto.comp hr

/-- A verified a.e. radial limit identifies the boundary vector constructed from Taylor coefficients. -/
theorem boundedAnalyticHardy_ae_of_radialLimit (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (M : ℝ) (hM : ∀ z ∈ disk, ‖F z‖ ≤ M)
    (B : Boundary → ℂ)
    (hlim : ∀ᵐ t ∂circleMeasure, Tendsto
      (fun r : ℝ => F ((r : ℂ) * fourier (T := 1) 1 t)) (𝓝[<] (1 : ℝ)) (𝓝 (B t))) :
    (boundedAnalyticHardy F hF M hM).val =ᵐ[circleMeasure] B := by
  have ht : Tendsto (fun r : ℝ => (diskRadialHardy F r).val)
      (𝓝[<] (1 : ℝ)) (𝓝 (boundedAnalyticHardy F hF M hM).val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_diskRadialHardy F hF M hM)
  obtain ⟨s, hs, hseq⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae'
  have heq (r : ℝ) : ∀ᵐ t ∂circleMeasure, 0 ≤ r ∧ r < 1 →
      (diskRadialHardy F r).val t = F ((r : ℂ) * fourier (T := 1) 1 t) := by
    by_cases hr : 0 ≤ r ∧ r < 1
    · exact (diskRadialHardy_ae F hF M hM r hr.1 hr.2).mono fun _ ht _ => ht
    · exact Eventually.of_forall fun _ hr' => (hr hr').elim
  have heqa : ∀ᵐ t ∂circleMeasure, ∀ n : ℕ, 0 ≤ s n ∧ s n < 1 →
      (diskRadialHardy F (s n)).val t = F ((s n : ℂ) * fourier (T := 1) 1 t) :=
    ae_all_iff.mpr fun n => heq (s n)
  have hgood := hs.eventually (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hseq, heqa, hlim] with t hst het hlt
  apply tendsto_nhds_unique hst
  apply (hlt.comp hs).congr'
  filter_upwards [hgood] with n hn
  exact (het n ⟨hn.1.le, hn.2⟩).symm

/-- A positive point mass gives an actual nonconstant inner L∞ symbol, with its literal
analytic exponential. No boundary-value hypothesis is needed. -/
theorem exists_singleAtom_inner (ℓ : ℝ) (hℓ : 0 < ℓ) (ζ : Boundary) :
    ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ SingleAtom u ζ := by
  let F := atomDiskFunction ℓ ζ
  have hF : AnalyticOnNhd ℂ F disk := analyticOnNhd_atomDiskFunction ℓ ζ
  have hM : ∀ z ∈ disk, ‖F z‖ ≤ 1 := fun _ hz =>
    norm_atomDiskFunction_le_one ℓ hℓ.le ζ hz
  let x := boundedAnalyticHardy F hF 1 hM
  have hb := boundedAnalyticHardy_ae_bound F hF 1 hM
  have htop : MemLp x.val ∞ circleMeasure :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) 1 hb
  let u : BoundaryLInf := htop.toLp x.val
  have he : toL2 u = x.val := Lp.ext ((toL2_ae u).trans htop.coeFn_toLp)
  have hlim : ∀ᵐ t ∂circleMeasure, Tendsto
      (fun r : ℝ => F ((r : ℂ) * fourier (T := 1) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (atomBoundaryFunction ℓ ζ t)) := by
    have hn : ∀ᵐ t ∂circleMeasure, t ≠ ζ := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using
        (measure_singleton ζ : circleMeasure {ζ} = 0)
    exact hn.mono fun t ht => tendsto_atomDiskFunction_radial ℓ ζ t ht
  have hx := boundedAnalyticHardy_ae_of_radialLimit F hF 1 hM
    (atomBoundaryFunction ℓ ζ) hlim
  have hu : IsInner u := by
    refine ⟨he ▸ x.property, ?_⟩
    filter_upwards [htop.coeFn_toLp, hx] with t ht hxt
    rw [ht, hxt]
    exact norm_atomBoundaryFunction ℓ ζ t
  have hv : ∀ z ∈ disk, innerValue u z = F z := by
    intro z hz
    change analyticValue (toL2 u) z = F z
    rw [he]
    exact analyticValue_boundedAnalyticHardy F hF 1 hM hz
  refine ⟨u, hu, ?_, ℓ, hℓ, 1, norm_one, ?_⟩
  · have hstrict : ‖innerValue u 0‖ < 1 := by
      rw [hv 0 (by norm_num [disk])]
      change ‖atomDiskFunction ℓ ζ 0‖ < 1
      rw [norm_atomDiskFunction]
      simp only [atomicPoissonKernel, norm_zero, zero_pow (by decide : 2 ≠ 0),
        sub_zero, fourier_apply, Circle.norm_coe, one_pow, div_one, mul_one]
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hℓ)
    rintro ⟨c, hc⟩
    have hn := hu.2
    rw [hc] at hn
    have hcae : constLInf c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
    obtain ⟨t, ht, hct⟩ := (hn.and hcae).exists
    have hnc : ‖c‖ = 1 := by rw [hct] at ht; exact ht
    have hcval : innerValue u 0 = c := by
      rw [hc]
      change analyticValue (toL2 (constLInf c)) 0 = c
      rw [toL2_constLInf, analyticValue_at_zero, fourierCoeff_constL2]
      simp
    rw [hcval, hnc] at hstrict
    exact (lt_irrefl 1) hstrict
  · intro z hz
    simpa only [F, atomDiskFunction, one_mul] using hv z hz

/-- The literal single-atom formula has its actual finite singular point measure.
The last clause identifies all its positive atoms, rather than just supplying abstract atomicity. -/
theorem singleAtom_singularRepresentation (u : BoundaryLInf) (ζ : Boundary)
    (hs : SingleAtom u ζ) :
    ∃ μ : Measure Boundary, HasSingularRepresentation u μ ∧ AtomicMeasure μ ∧
      ∀ t : Boundary, 0 < μ {t} → t = ζ := by
  obtain ⟨ℓ, hℓ, α, hα, hval⟩ := hs
  let μ : Measure Boundary := ENNReal.ofReal ℓ • Measure.dirac ζ
  have hfinite : finiteSingular μ := by
    refine ⟨?_, ?_⟩
    · simp only [μ, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ ζ)]
      change ENNReal.ofReal ℓ * 1 < ∞
      rw [mul_one]
      exact ENNReal.ofReal_lt_top
    · exact Measure.MutuallySingular.smul (ENNReal.ofReal ℓ)
        (mutuallySingular_dirac ζ circleMeasure)
  refine ⟨μ, ⟨hfinite, α, hα, ?_⟩, ?_, ?_⟩
  · intro z hz
    rw [hval z hz]
    congr 1
    unfold singularInnerValue
    rw [integral_smul_measure, integral_dirac]
    simp only [ENNReal.toReal_ofReal hℓ.le, Complex.ofReal_one]
    rw [← Complex.coe_smul]
    congr 1
    change -(ℓ : ℂ) * (fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z) =
      -(1 : ℂ) * ((ℓ : ℂ) * ((fourier (T := 1) 1 ζ + z) / (fourier (T := 1) 1 ζ - z)))
    ring
  · refine ⟨{ζ}, Set.countable_singleton ζ, ?_⟩
    simp [μ, Measure.smul_apply, Measure.dirac_apply' ζ ((measurableSet_singleton ζ).compl)]
  · intro t ht
    by_contra hne
    have hz : μ {t} = 0 := by
      simp [μ, Measure.smul_apply, Measure.dirac_apply' ζ (measurableSet_singleton t), Ne.symm hne]
    rw [hz] at ht
    exact (lt_irrefl 0) ht

/-- The literal bi-polynomial used in the nonzero atomic example. -/
def atomicQuadraticPolynomial : BiPolynomial :=
  Finsupp.single (0, 0) 2 + Finsupp.single (1, 0) (-1) + Finsupp.single (0, 1) (-1)

theorem atomicQuadraticPolynomial_value (z : ℂ) :
    polynomialValue atomicQuadraticPolynomial z = 2 - z - conj z := by
  have hadd (a b : BiPolynomial) : polynomialValue (a + b) z =
      polynomialValue a z + polynomialValue b z :=
    Finsupp.sum_add_index' (h := fun (jk : ℕ × ℕ) (c : ℂ) =>
      c * z ^ jk.1 * conj z ^ jk.2) (fun _ => by simp only [zero_mul])
      (fun _ _ _ => by ring)
  have hsingle (jk : ℕ × ℕ) (c : ℂ) : polynomialValue (Finsupp.single jk c) z =
      c * z ^ jk.1 * conj z ^ jk.2 :=
    Finsupp.sum_single_index (by simp only [zero_mul])
  unfold atomicQuadraticPolynomial
  rw [hadd, hadd, hsingle, hsingle, hsingle]
  simp only [pow_zero, pow_one, mul_one]
  ring

/-- Multiplication by 1-z cannot annihilate a nonzero native L² vector. The sole boundary
zero of its literal symbol is a Haar-null singleton. -/
theorem multiply_one_sub_coordinate_ne_zero (f : BoundaryL2) (hf : f ≠ 0) :
    multiply (constLInf 1 - coordinate) f ≠ 0 := by
  intro hz
  apply hf
  apply Lp.ext
  have hne : ∀ᵐ t ∂circleMeasure, t ≠ (0 : Boundary) := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (0 : Boundary) : circleMeasure {0} = 0)
  have hzero : multiply (constLInf 1 - coordinate) f =ᵐ[circleMeasure]
      (0 : BoundaryL2) := by rw [hz]
  have hconst : constLInf 1 =ᵐ[circleMeasure] fun _ => (1 : ℂ) :=
    (memLp_const (1 : ℂ)).coeFn_toLp
  filter_upwards [multiply_ae (constLInf 1 - coordinate) f,
    Lp.coeFn_sub (constLInf 1) coordinate, hconst, coordinate_ae,
    hzero, Lp.coeFn_zero ℂ 2 circleMeasure, hne] with t hm hs hc he hh h0 ht
  have hchar : 1 - fourier (T := 1) 1 t ≠ 0 := by
    intro heq
    apply ht
    apply circleCharacter_injective
    simpa only [fourier_eval_zero] using (sub_eq_zero.mp heq).symm
  rw [hm, hs] at hh
  change (constLInf 1 t - coordinate t) * f t = (0 : BoundaryL2) t at hh
  rw [hc, he, h0] at hh
  rw [h0]
  exact (mul_eq_zero.mp hh).resolve_left hchar

/-- The compressed literal quadratic has exactly the ambient squared-norm form. -/
theorem atomicQuadratic_form (u : BoundaryLInf) (f : Model u) :
    inner ℂ f (boundedSymbolOperator u (biPolynomialBoundary atomicQuadraticPolynomial) f) =
      inner ℂ (multiply (constLInf 1 - coordinate) f.val)
        (multiply (constLInf 1 - coordinate) f.val) := by
  have hi : inner ℂ f (boundedSymbolOperator u (biPolynomialBoundary atomicQuadraticPolynomial) f) =
      inner ℂ f.val (multiply (biPolynomialBoundary atomicQuadraticPolynomial) f.val) := by
    simp [boundedSymbolOperator]
  rw [hi, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hconst : constLInf 1 =ᵐ[circleMeasure] fun _ => (1 : ℂ) :=
    (memLp_const (1 : ℂ)).coeFn_toLp
  filter_upwards [multiply_ae (biPolynomialBoundary atomicQuadraticPolynomial) f.val,
    biPolynomialBoundary_ae atomicQuadraticPolynomial,
    multiply_ae (constLInf 1 - coordinate) f.val,
    Lp.coeFn_sub (constLInf 1) coordinate, hconst, coordinate_ae]
    with t hmq hq hm hs hc he
  rw [hmq, hq, atomicQuadraticPolynomial_value]
  rw [hm, hs]
  change inner ℂ (f.val t) ((2 - fourier (T := 1) 1 t - conj (fourier (T := 1) 1 t)) * f.val t) =
    inner ℂ ((constLInf 1 t - coordinate t) * f.val t)
      ((constLInf 1 t - coordinate t) * f.val t)
  rw [hc, he]
  simp only [RCLike.inner_apply, map_mul, map_sub, map_one]
  have hz := circleCharacter_mul_conj t
  linear_combination -(f.val t * conj (f.val t)) * hz

/-- The literal quadratic has a strictly positive matrix coefficient on every nonconstant model. -/
theorem atomicQuadratic_positive (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) :
    ∃ f : Model u, 0 < (inner ℂ f
      (boundedSymbolOperator u (biPolynomialBoundary atomicQuadraticPolynomial) f)).re := by
  let f := modelReproducingKernel u hu origin
  have hf : f.val ≠ 0 := by
    intro h
    apply modelReproducingKernel_ne_zero u hu hn origin
    exact Subtype.ext h
  have hv := multiply_one_sub_coordinate_ne_zero f.val hf
  refine ⟨f, ?_⟩
  rw [atomicQuadratic_form]
  change 0 < RCLike.re (inner ℂ (multiply (constLInf 1 - coordinate) f.val)
    (multiply (constLInf 1 - coordinate) f.val))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

/-- The fully explicit intermediate witness for T7's atomic example. This assertion deliberately
contains no compactness or Schatten claim; those come from the polynomial sufficiency proof. -/
theorem atomicQuadraticWitness : AtomicQuadraticWitness := by
  obtain ⟨u, hu, hn, hs⟩ := exists_singleAtom_inner 1 (by norm_num) 0
  obtain ⟨μ, hμ, ha, hatom⟩ := singleAtom_singularRepresentation u 0 hs
  refine ⟨u, hu, hn, hs, μ, hμ, ha, atomicQuadraticPolynomial,
    atomicQuadraticPolynomial_value, ?_,
    boundedSymbolOperator u (biPolynomialBoundary atomicQuadraticPolynomial),
    boundedSymbolOperator_represents u (biPolynomialBoundary atomicQuadraticPolynomial),
    atomicQuadratic_positive u hu hn⟩
  intro t ht
  rw [hatom t ht, fourier_eval_zero, atomicQuadraticPolynomial_value]
  norm_num

end TTO.Paper.Proved
