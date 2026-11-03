/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations
public import TTO.AnalyticBoundaryFoundations
public import TTO.AtomicFoundations

/-! Direct polynomial Hilbert–Schmidt estimates for singular model spaces. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The actual Fourier coefficients of a Hardy vector damped at radius r. -/
def hardyRadialCoeff (f : Hardy) (r : ℝ) (n : ℕ) : ℂ :=
  (r : ℂ)^n*fourierCoeff f.val (n : ℤ)

/-- The actual radial H² vector, without a bounded analytic-symbol premise. -/
def hardyRadialBoundary (f : Hardy) (r : ℝ) : Hardy :=
  ∑' n : ℕ, hardyRadialCoeff f r n • hardyBasis n

theorem summable_norm_hardyRadialCoeff (f : Hardy) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖hardyRadialCoeff f r n‖) := by
  apply ((summable_geometric_of_lt_one hr hr1).mul_left ‖f.val‖).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  rw [hardyRadialCoeff,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr]
  nlinarith [norm_fourierCoeff_le f.val n,pow_nonneg hr n]

theorem summable_hardyRadialBoundary (f : Hardy) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => hardyRadialCoeff f r n • hardyBasis n) := by
  refine Summable.of_norm_bounded (summable_norm_hardyRadialCoeff f r hr hr1) fun n => ?_
  rw [norm_smul,hardyBasis.orthonormal.norm_eq_one,mul_one]

theorem hardyBasis_repr_hardyRadialBoundary (f : Hardy) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    hardyBasis.repr (hardyRadialBoundary f r) n = hardyRadialCoeff f r n := by
  rw [HilbertBasis.repr_apply_apply,hardyRadialBoundary,← innerSL_apply_apply ℂ,
    ContinuousLinearMap.map_tsum _ (summable_hardyRadialBoundary f r hr hr1),
    tsum_eq_single n fun m hm => by
      rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
        (orthonormal_iff_ite.mp hardyBasis.orthonormal n m).trans (ite_eq_right (Ne.symm hm)),mul_zero]]
  rw [innerSL_apply_apply,inner_smul_right (𝕜 := ℂ) (E := Hardy),
    inner_self_eq_one_of_norm_eq_one (hardyBasis.orthonormal.norm_eq_one n),mul_one]

/-- The radial vector has the literal analytic-value circle representative a.e. -/
theorem hardyRadialBoundary_ae (f : Hardy) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (hardyRadialBoundary f r).val =ᵐ[circleMeasure]
      fun t => analyticValue f.val ((r : ℂ)*fourier (T := 1) 1 t) := by
  let g : ℕ → C(Boundary,ℂ) := fun n => hardyRadialCoeff f r n • fourier (T := 1) (n : ℤ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_norm_hardyRadialCoeff f r hr hr1) fun n => ?_
    rw [norm_smul,fourier_norm,mul_one]
  have hcoe : (hardyRadialBoundary f r).val = ContinuousMap.toLp 2 circleMeasure ℂ (∑' n,g n) := by
    rw [hardyRadialBoundary,← hardy.subtypeL_apply,
      ContinuousLinearMap.map_tsum _ (summable_hardyRadialBoundary f r hr hr1),
      ContinuousLinearMap.map_tsum _ hg]
    congr 1
    funext n
    simp [g,coe_fourierBasis,hardyMode]
  rw [hcoe]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure (∑' n,g n)] with t ht
  rw [ht]
  refine (ContinuousMap.tsum_apply hg t).symm.trans ?_
  have hz : ‖(r : ℂ)*fourier (T := 1) 1 t‖ < 1 := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,fourier_one,Circle.norm_coe,mul_one] using hr1
  rw [← (hasSum_analyticValue f.val hz).tsum_eq]
  congr 1
  funext n
  simp only [g,hardyRadialCoeff,ContinuousMap.smul_apply,smul_eq_mul,fourier_apply,
    natCast_zsmul,AddCircle.toCircle_nsmul,Circle.coe_pow,one_zsmul,mul_pow]
  ring

/-- Actual radial convergence in the unchanged native Hardy/L² norm. -/
theorem tendsto_hardyRadialBoundary (f : Hardy) :
    Tendsto (hardyRadialBoundary f) (𝓝[<] (1 : ℝ)) (𝓝 f) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) fun r hr => ⟨hr.1.le,hr.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun r => ‖hardyRadialBoundary f r-f‖^2) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[<] (1 : ℝ))
      (f := fun r (n : ℕ) => ‖((r : ℂ)^n-1)*fourierCoeff f.val (n : ℤ)‖^2)
      (g := fun _ => 0) (bound := fun n : ℕ => ‖fourierCoeff f.val (n : ℤ)‖^2) ?_ ?_ ?_
    · rw [tsum_zero] at hdom
      refine hdom.congr' ?_
      filter_upwards [hev] with r hr
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hardyBasis.repr (hardyRadialBoundary f r-f))
      rw [ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] at h
      rw [h]
      congr 1
      funext n
      rw [Real.rpow_two,map_sub,lp.coeFn_sub,Pi.sub_apply,
        hardyBasis_repr_hardyRadialBoundary f r hr.1 hr.2,hardyBasis_repr_eq_fourierCoeff]
      simp only [hardyRadialCoeff]
      ring_nf
    · have h := (lp.memℓp (hardyBasis.repr f)).summable (by norm_num)
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hardyBasis_repr_eq_fourierCoeff] using h
    · intro n
      have hc : Continuous fun r : ℝ => ‖((r : ℂ)^n-1)*fourierCoeff f.val (n : ℤ)‖^2 := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [hev] with r hr n
      rw [norm_pow,norm_norm,norm_mul]
      have h1 : ‖(r : ℂ)^n-1‖ ≤ 1 := by
        rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs,abs_le]
        constructor <;> nlinarith [pow_le_one₀ hr.1 hr.2.le (n := n),pow_nonneg hr.1 n]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hroot := hsq.sqrt
  simpa only [Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using hroot

/-- Bessel's inequality for actual model evaluations on an arbitrary finite orthonormal family. -/
theorem model_finite_eval_energy_le {I : Type*} (u : BoundaryLInf) (hu : IsInner u)
    (v : I → Model u) (hv : Orthonormal ℂ v) (s : Finset I) (w : Disk) :
    ∑ i ∈ s, ‖analyticValue (v i).val w.val‖^2 ≤
      (1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2) := by
  have h := hv.sum_inner_products_le (s := s) (x := modelReproducingKernel u hu w)
  have ht (i : I) : ‖inner ℂ (v i) (modelReproducingKernel u hu w)‖ =
      ‖analyticValue (v i).val w.val‖ := by
    rw [norm_inner_symm,inner_modelReproducingKernel]
  simpa only [ht,norm_modelReproducingKernel_sq] using h

/-- The literal inverse squared distance in the model-kernel energy estimate. -/
def singularInverseWeight (z : ℂ) (t : Boundary) : ℝ :=
  (‖fourier (T := 1) 1 t-z‖^2)⁻¹

theorem circlePoint_sub_disk_ne_zero (t : Boundary) (w : Disk) :
    fourier (T := 1) 1 t-w.val ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  have hw : ‖w.val‖ < 1 := w.property
  simp only [fourier_apply,Circle.norm_coe] at hn
  linarith

theorem singularInverseWeight_continuous (w : Disk) : Continuous (singularInverseWeight w.val) := by
  apply (((fourier (T := 1) 1).continuous.sub continuous_const).norm.pow 2).inv₀
  intro t
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (circlePoint_sub_disk_ne_zero t w))

theorem singularInverseWeight_integrable (μ : Measure Boundary) [IsFiniteMeasure μ] (w : Disk) :
    Integrable (singularInverseWeight w.val) μ :=
  (singularInverseWeight_continuous w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Exact modulus of the literal exponential singular-inner formula. -/
theorem norm_singularInnerValue_poisson (μ : Measure Boundary) [IsFiniteMeasure μ] (w : Disk) :
    ‖singularInnerValue μ 1 w.val‖ = Real.exp (-∫ t,atomicPoissonKernel w.val t ∂μ) := by
  have hi := herglotz_integrable μ w
  have hr : (∫ t,(fourier (T := 1) 1 t+w.val)/(fourier (T := 1) 1 t-w.val) ∂μ).re =
      ∫ t,atomicPoissonKernel w.val t ∂μ := by
    change RCLike.re (∫ t,(fourier (T := 1) 1 t+w.val)/(fourier (T := 1) 1 t-w.val) ∂μ) = _
    rw [← integral_re hi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => herglotz_re w.val _ (by simp only [fourier_apply,Circle.norm_coe]))
  unfold singularInnerValue
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_one,neg_one_mul,Complex.neg_re]
  rw [hr]

/-- The model-kernel energy is controlled by the actual singular measure, with no atomicity
assumption. The elementary inequality 1-exp(-x)≤x supplies the constant 2. -/
theorem singular_model_kernel_energy_le (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (w : Disk) :
    ‖modelReproducingKernel u hu w‖^2 ≤ 2*∫ t,singularInverseWeight w.val t ∂μ := by
  let : IsFiniteMeasure μ := ⟨hμ.1.1⟩
  obtain ⟨α,hα,huval⟩ := hμ.2
  have hnorm : ‖innerValue u w.val‖ = Real.exp (-∫ t,atomicPoissonKernel w.val t ∂μ) := by
    rw [huval _ w.property,norm_mul,hα,one_mul,norm_singularInnerValue_poisson μ w]
  have hpow : ‖innerValue u w.val‖^2 = Real.exp (-2*∫ t,atomicPoissonKernel w.val t ∂μ) := by
    rw [hnorm,pow_two,← Real.exp_add]
    congr 1
    ring
  have hgap : 1-‖innerValue u w.val‖^2 ≤ 2*∫ t,atomicPoissonKernel w.val t ∂μ := by
    rw [hpow]
    have h := Real.add_one_le_exp (-2*∫ t,atomicPoissonKernel w.val t ∂μ)
    linarith
  have hweight : (∫ t,atomicPoissonKernel w.val t ∂μ) =
      (1-‖w.val‖^2)*∫ t,singularInverseWeight w.val t ∂μ := by
    simp only [atomicPoissonKernel,singularInverseWeight,div_eq_mul_inv]
    rw [integral_const_mul]
  have hw : ‖w.val‖ < 1 := w.property
  have hden : 0 < 1-‖w.val‖^2 := by nlinarith [norm_nonneg w.val]
  rw [norm_modelReproducingKernel_sq]
  apply (div_le_iff₀ hden).mpr
  rw [hweight] at hgap
  nlinarith [hgap]

/-- A coarse radial chord estimate avoids any boundary-limit or differentiation premise. -/
theorem circle_chord_le_two_radial_chord {e z : ℂ} (he : ‖e‖ = 1) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : ‖z-e‖ ≤ 2*‖e-(r : ℂ)*z‖ := by
  have hrad : ‖z-(r : ℂ)*z‖ = 1-r := by
    rw [show z-(r : ℂ)*z = ((1-r : ℝ) : ℂ)*z by push_cast; ring]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hr1),hz,mul_one]
  have hlo : 1-r ≤ ‖e-(r : ℂ)*z‖ := by
    have h := norm_sub_norm_le e ((r : ℂ)*z)
    simpa only [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,hz,mul_one] using h
  have ht := dist_triangle z ((r : ℂ)*z) e
  simp only [dist_eq_norm] at ht
  rw [hrad,norm_sub_rev ((r : ℂ)*z) e] at ht
  linarith

/-- A polynomial vanishing on the singular measure controls the weighted inverse kernel.
Only finite-measure integration at a fixed circle point is used. -/
theorem polynomial_singular_weight_integral_le (μ : Measure Boundary) [IsFiniteMeasure μ]
    (q : BiPolynomial) (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (t : Boundary) :
    ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 *
      (∫ s,singularInverseWeight ((r : ℂ)*fourier (T := 1) 1 t) s ∂μ) ≤
      4*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
  let w : Disk := ⟨(r : ℂ)*fourier (T := 1) 1 t,by
    simpa only [disk,Set.mem_ofPred_eq,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_one,Circle.norm_coe,mul_one] using hr1⟩
  change ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 * (∫ s,singularInverseWeight w.val s ∂μ) ≤ _
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ _ : Boundary,4*biPolynomialLipschitzBound q^2 ∂μ := by
      apply integral_mono_ae ((singularInverseWeight_integrable μ w).const_mul _)
        (integrable_const _)
      filter_upwards [hq] with s hs
      have hLip := norm_polynomialValue_sub_le_on_unit q
        (z := fourier (T := 1) 1 t) (w := fourier (T := 1) 1 s) (by simp) (by simp)
      rw [hs,sub_zero] at hLip
      have hchord := circle_chord_le_two_radial_chord
        (e := fourier (T := 1) 1 s) (z := fourier (T := 1) 1 t) (by simp) (by simp) r hr hr1.le
      have hnorm : ‖polynomialValue q (fourier (T := 1) 1 t)‖ ≤
          2*biPolynomialLipschitzBound q*‖fourier (T := 1) 1 s-w.val‖ := by
        apply hLip.trans
        simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hchord
          (biPolynomialLipschitzBound_nonneg q)
      have hd : 0 < ‖fourier (T := 1) 1 s-w.val‖^2 :=
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (circlePoint_sub_disk_ne_zero s w))
      change ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 *
        (‖fourier (T := 1) 1 s-w.val‖^2)⁻¹ ≤ _
      rw [← div_eq_mul_inv,div_le_iff₀ hd]
      calc
        _ ≤ (2*biPolynomialLipschitzBound q*‖fourier (T := 1) 1 s-w.val‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = _ := by ring
    _ = _ := by rw [integral_const,smul_eq_mul]; ring

/-- The complete finite orthonormal radial-energy bound is uniform in the radius and family.
It works for all singular measures, and hence for the atomic case in Theorem7. -/
theorem model_finite_polynomial_radial_energy_le {I : Type*} (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (q : BiPolynomial)
    (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0)
    (v : I → Model u) (hv : Orthonormal ℂ v) (s : Finset I)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (t : Boundary) :
    ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 *
      (∑ i ∈ s,‖analyticValue (v i).val ((r : ℂ)*fourier (T := 1) 1 t)‖^2) ≤
      8*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
  let : IsFiniteMeasure μ := ⟨hμ.1.1⟩
  let w : Disk := ⟨(r : ℂ)*fourier (T := 1) 1 t,by
    simpa only [disk,Set.mem_ofPred_eq,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_one,Circle.norm_coe,mul_one] using hr1⟩
  have hb : (∑ i ∈ s,‖analyticValue (v i).val w.val‖^2) ≤ ‖modelReproducingKernel u hu w‖^2 := by
    rw [norm_modelReproducingKernel_sq]
    exact model_finite_eval_energy_le u hu v hv s w
  have hk := singular_model_kernel_energy_le u hu μ hμ w
  have hi := polynomial_singular_weight_integral_le μ q hq r hr hr1 t
  calc
    _ ≤ ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 * (2*∫ s,singularInverseWeight w.val s ∂μ) :=
      mul_le_mul_of_nonneg_left (hb.trans hk) (sq_nonneg _)
    _ = 2*(‖polynomialValue q (fourier (T := 1) 1 t)‖^2*(∫ s,singularInverseWeight w.val s ∂μ)) := by ring
    _ ≤ 2*(4*biPolynomialLipschitzBound q^2*μ.real Set.univ) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

/-- Literal Bochner integral of the square norm of a native boundary L² vector. -/
theorem boundaryL2_norm_sq_integral (f : BoundaryL2) :
    ‖f‖^2 = ∫ t,‖f t‖^2 ∂circleMeasure := by
  calc
    ‖f‖^2 = RCLike.re (inner ℂ f f) := (inner_self_eq_norm_sq f).symm
    _ = RCLike.re (∫ t,inner ℂ (f t) (f t) ∂circleMeasure) := by rw [L2.inner_def]
    _ = ∫ t,RCLike.re (inner ℂ (f t) (f t)) ∂circleMeasure := (integral_re (L2.integrable_inner f f)).symm
    _ = ∫ t,‖f t‖^2 ∂circleMeasure := by simp only [inner_self_eq_norm_sq]

theorem boundaryL2_integrable_norm_sq (f : BoundaryL2) : Integrable (fun t => ‖f t‖^2) circleMeasure :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

/-- A uniform L² estimate for a finite family of the actual radial Hardy vectors. -/
theorem model_finite_polynomial_radial_L2_le {I : Type*} (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (q : BiPolynomial)
    (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0)
    (v : I → Model u) (hv : Orthonormal ℂ v) (s : Finset I)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∑ i ∈ s,‖multiply (biPolynomialBoundary q)
      (hardyRadialBoundary (modelHardyIsometry u (v i)) r).val‖^2 ≤
      8*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
  classical
  let W (i : I) : BoundaryL2 := multiply (biPolynomialBoundary q)
    (hardyRadialBoundary (modelHardyIsometry u (v i)) r).val
  have hW (i : I) : W i =ᵐ[circleMeasure] fun t => polynomialValue q (fourier (T := 1) 1 t)*
      analyticValue (v i).val ((r : ℂ)*fourier (T := 1) 1 t) := by
    filter_upwards [multiply_ae (biPolynomialBoundary q)
        (hardyRadialBoundary (modelHardyIsometry u (v i)) r).val,
      hardyRadialBoundary_ae (modelHardyIsometry u (v i)) r hr hr1,biPolynomialBoundary_ae q] with t hm hf hq
    change multiply (biPolynomialBoundary q) (hardyRadialBoundary (modelHardyIsometry u (v i)) r).val t = _
    rw [hm,hf,hq]
    rfl
  have hi (i : I) := boundaryL2_integrable_norm_sq (W i)
  have hbound : ∀ᵐ t ∂circleMeasure, (∑ i ∈ s,‖W i t‖^2) ≤
      8*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
    filter_upwards [(ae_ball_iff s.countable_toSet).mpr (fun i _ => hW i)] with t ht
    calc
      _ = ‖polynomialValue q (fourier (T := 1) 1 t)‖^2 *
          (∑ i ∈ s,‖analyticValue (v i).val ((r : ℂ)*fourier (T := 1) 1 t)‖^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i his
        rw [ht i his,norm_mul,mul_pow]
      _ ≤ _ := model_finite_polynomial_radial_energy_le u hu μ hμ q hq v hv s r hr hr1 t
  calc
    _ = ∫ t,∑ i ∈ s,‖W i t‖^2 ∂circleMeasure := by
      simp_rw [boundaryL2_norm_sq_integral]
      exact (integral_finsetSum s (fun i _ => hi i)).symm
    _ ≤ ∫ _ : Boundary,8*biPolynomialLipschitzBound q^2*μ.real Set.univ ∂circleMeasure :=
      integral_mono_ae (integrable_finsetSum s (fun i _ => hi i)) (integrable_const _) hbound
    _ = _ := by simp

/-- The radial estimate passes to the actual boundary vectors in native L² norm. -/
theorem model_finite_polynomial_boundary_L2_le {I : Type*} (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (q : BiPolynomial)
    (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0)
    (v : I → Model u) (hv : Orthonormal ℂ v) (s : Finset I) :
    ∑ i ∈ s,‖multiply (biPolynomialBoundary q) (v i).val‖^2 ≤
      8*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
  have ht : Tendsto (fun r => ∑ i ∈ s,‖multiply (biPolynomialBoundary q)
      (hardyRadialBoundary (modelHardyIsometry u (v i)) r).val‖^2)
      (𝓝[<] (1 : ℝ)) (𝓝 (∑ i ∈ s,‖multiply (biPolynomialBoundary q) (v i).val‖^2)) := by
    apply tendsto_finsetSum
    intro i _
    have hrad := tendsto_hardyRadialBoundary (modelHardyIsometry u (v i))
    have hval := (hardy.subtypeL.continuous.tendsto (modelHardyIsometry u (v i))).comp hrad
    have hmul := ((multiply (biPolynomialBoundary q)).continuous.tendsto
      (modelHardyIsometry u (v i)).val).comp hval
    exact hmul.norm.pow 2
  apply le_of_tendsto ht
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) fun r hr => ⟨hr.1.le,hr.2⟩
  filter_upwards [hev] with r hr
  exact model_finite_polynomial_radial_L2_le u hu μ hμ q hq v hv s r hr.1 hr.2

/-- A polynomial vanishing a.e. on the literal singular measure defines a genuine S₂ TTO.
No atomicity or pure-type representation theorem is assumed. -/
theorem singularPolynomial_schatten_two (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (q : BiPolynomial)
    (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0) :
    Schatten 2 (boundedSymbolOperator u (biPolynomialBoundary q)) := by
  let A := boundedSymbolOperator u (biPolynomialBoundary q)
  obtain ⟨I,b,_⟩ := exists_hilbertBasis ℂ (Model u)
  have hsum (s : Finset I) : (∑ i ∈ s,‖A (b i)‖^2) ≤
      8*biPolynomialLipschitzBound q^2*μ.real Set.univ := by
    calc
      _ ≤ ∑ i ∈ s,‖multiply (biPolynomialBoundary q) (b i).val‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        change ‖(model u).orthogonalProjectionOnto (multiply (biPolynomialBoundary q) (b i).val)‖^2 ≤ _
        exact pow_le_pow_left₀ (norm_nonneg _) ((model u).norm_orthogonalProjectionOnto_apply_le _) 2
      _ ≤ _ := model_finite_polynomial_boundary_L2_le u hu μ hμ q hq b b.orthonormal s
  have hs : Summable (fun i => ‖A (b i)‖^2) := summable_of_sum_le (fun i => sq_nonneg _) hsum
  apply (schatten_two_iff_columnEnergy A b).mpr
  unfold columnEnergy
  have he : (∑' i,‖A (b i)‖ₑ^2) = ENNReal.ofReal (∑' i,‖A (b i)‖^2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖A (b i)‖) hs]
    apply tsum_congr
    intro i
    rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (A (b i)))]
  rw [he]
  exact ENNReal.ofReal_lt_top

/-- Operator-existence formulation of the direct singular polynomial S₂ sufficiency. -/
theorem singularPolynomial_hasSchatten_two (u : BoundaryLInf) (hu : IsInner u)
    (μ : Measure Boundary) (hμ : HasSingularRepresentation u μ) (q : BiPolynomial)
    (hq : ∀ᵐ s ∂μ, polynomialValue q (fourier (T := 1) 1 s) = 0) :
    HasSchattenTTO 2 u (polynomialSymbol q) :=
  ⟨boundedSymbolOperator u (biPolynomialBoundary q),boundedSymbolOperator_represents _ _,
    singularPolynomial_schatten_two u hu μ hμ q hq⟩

end TTO.Paper.Proved
