/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicPolynomialFoundations
public import TTO.TrigonometricFoundations
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Singular-measure radial zero sequences from actual measure differentiation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Push the actual circle measure into the native complex plane. -/
def embeddedCircleMeasure (μ : Measure Boundary) : Measure ℂ :=
  μ.map (fun t : Boundary => fourier (T := 1) 1 t)

theorem circleCharacter_measurableEmbedding :
    MeasurableEmbedding (fun t : Boundary => fourier (T := 1) 1 t) :=
  ((fourier (T := 1) 1).continuous.isClosedEmbedding circleCharacter_injective).measurableEmbedding

instance embeddedCircleMeasure_finite (μ : Measure Boundary) [IsFiniteMeasure μ] :
    IsFiniteMeasure (embeddedCircleMeasure μ) := by
  constructor
  change μ.map (fun t : Boundary => fourier (T := 1) 1 t) Set.univ < ∞
  rw [circleCharacter_measurableEmbedding.map_apply]
  simpa only [Set.preimage_univ] using (measure_lt_top μ Set.univ)

/-- Native Besicovitch differentiation of the mutually singular pushed measures. -/
theorem singular_circle_ratio_zero (μ : Measure Boundary) (hμ : finiteSingular μ) :
    ∀ᵐ ζ ∂μ, Tendsto (fun δ : ℝ =>
      embeddedCircleMeasure circleMeasure (closedBall (fourier (T := 1) 1 ζ) δ) /
        embeddedCircleMeasure μ (closedBall (fourier (T := 1) 1 ζ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let : IsFiniteMeasure μ := ⟨hμ.1⟩
  have hsing : embeddedCircleMeasure circleMeasure ⟂ₘ embeddedCircleMeasure μ :=
    circleCharacter_measurableEmbedding.mutuallySingular_map hμ.2.symm
  have hd := Besicovitch.ae_tendsto_rnDeriv (embeddedCircleMeasure circleMeasure) (embeddedCircleMeasure μ)
  have hz := Measure.rnDeriv_eq_zero_of_mutuallySingular hsing Measure.AbsolutelyContinuous.rfl
  have he : ∀ᵐ z ∂embeddedCircleMeasure μ, Tendsto (fun δ : ℝ =>
      embeddedCircleMeasure circleMeasure (closedBall z δ) / embeddedCircleMeasure μ (closedBall z δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [hd,hz] with z hd hz
    rwa [hz] at hd
  exact circleCharacter_measurableEmbedding.ae_map_iff.mp he

theorem circleCharacter_chord_eq (t ζ : Boundary) :
    ‖fourier (T := 1) 1 t-fourier (T := 1) 1 ζ‖ =
      ‖fourier (T := 1) 1 (t-ζ)-1‖ := by
  have he : fourier (T := 1) 1 (t-ζ)*fourier (T := 1) 1 ζ = fourier (T := 1) 1 t := by
    simp only [fourier_one,← Circle.coe_mul,← AddCircle.toCircle_add,sub_add_cancel]
  calc
    _ = ‖(fourier (T := 1) 1 (t-ζ)-1)*fourier (T := 1) 1 ζ‖ := by rw [sub_mul,he,one_mul]
    _ = _ := by rw [norm_mul,show ‖fourier (T := 1) 1 ζ‖ = 1 by simp,mul_one]

theorem norm_circleCharacter_coe_sub_one_le (x : ℝ) :
    ‖fourier (T := 1) 1 (x : Boundary)-1‖ ≤ 2*Real.pi*‖x‖ := by
  have he : fourier (T := 1) 1 (x : Boundary) = Complex.exp (Complex.I*((2*Real.pi*x : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he]
  apply Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)]

theorem singular_circleMeasure_eq_volume : circleMeasure = (volume : Measure Boundary) := by
  simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm

/-- The pushed normalized Haar measure has a uniform linear lower bound on chord balls. -/
theorem embeddedHaar_closedBall_lower (ζ : Boundary) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (δ/(2*Real.pi)) ≤
      embeddedCircleMeasure circleMeasure (closedBall (fourier (T := 1) 1 ζ) δ) := by
  change _ ≤ circleMeasure.map (fun t : Boundary => fourier (T := 1) 1 t)
    (closedBall (fourier (T := 1) 1 ζ) δ)
  rw [circleCharacter_measurableEmbedding.map_apply]
  have hr : 0 < δ/(4*Real.pi) := by positivity
  have hs : closedBall ζ (δ/(4*Real.pi)) ⊆
      (fun t : Boundary => fourier (T := 1) 1 t) ⁻¹' closedBall (fourier (T := 1) 1 ζ) δ := by
    intro t ht
    rw [Metric.mem_closedBall,dist_eq_norm] at ht
    obtain ⟨x,hx,hxn⟩ := QuotientAddGroup.exists_norm_mk_lt (t-ζ) hr
    have hxbound : ‖x‖ < δ/(2*Real.pi) := by
      calc
        ‖x‖ < ‖t-ζ‖+δ/(4*Real.pi) := hxn
        _ ≤ δ/(4*Real.pi)+δ/(4*Real.pi) := by linarith
        _ = _ := by field_simp; ring
    change dist (fourier (T := 1) 1 t) (fourier (T := 1) 1 ζ) ≤ δ
    rw [dist_eq_norm,circleCharacter_chord_eq,← hx]
    apply (norm_circleCharacter_coe_sub_one_le x).trans
    have h := mul_lt_mul_of_pos_left hxbound (by positivity : (0 : ℝ) < 2*Real.pi)
    have heq : (2*Real.pi)*(δ/(2*Real.pi)) = δ := by field_simp
    exact (h.trans_eq heq).le
  have hm : circleMeasure (closedBall ζ (δ/(4*Real.pi))) ≤
      circleMeasure ((fun t : Boundary => fourier (T := 1) 1 t) ⁻¹' closedBall (fourier (T := 1) 1 ζ) δ) :=
    measure_mono hs
  have hv : circleMeasure (closedBall ζ (δ/(4*Real.pi))) = ENNReal.ofReal (δ/(2*Real.pi)) := by
    rw [singular_circleMeasure_eq_volume,AddCircle.volume_closedBall]
    have heq : 2*(δ/(4*Real.pi)) = δ/(2*Real.pi) := by field_simp; ring
    have hle : 2*(δ/(4*Real.pi)) ≤ 1 := by
      rw [heq]
      apply (div_le_one (by positivity : (0 : ℝ) < 2*Real.pi)).mpr
      nlinarith [Real.two_le_pi]
    rw [min_eq_right hle,heq]
  rw [hv] at hm
  exact hm

/-- The literal preimage of a Euclidean chord ball on the circle. -/
def singularChordBall (ζ : Boundary) (δ : ℝ) : Set Boundary :=
  (fun t : Boundary => fourier (T := 1) 1 t) ⁻¹' closedBall (fourier (T := 1) 1 ζ) δ

theorem singularChordBall_measurable (ζ : Boundary) (δ : ℝ) : MeasurableSet (singularChordBall ζ δ) :=
  isClosed_closedBall.measurableSet.preimage (fourier (T := 1) 1).continuous.measurable

theorem embeddedCircleMeasure_chordBall (μ : Measure Boundary) (ζ : Boundary) (δ : ℝ) :
    embeddedCircleMeasure μ (closedBall (fourier (T := 1) 1 ζ) δ) = μ (singularChordBall ζ δ) :=
  circleCharacter_measurableEmbedding.map_apply μ _

/-- Actual radial point in the open disk. -/
def singularRadialPoint (ζ : Boundary) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) : Disk :=
  ⟨(r : ℂ)*fourier (T := 1) 1 ζ,by
    simpa only [disk,Set.mem_ofPred_eq,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_one,Circle.norm_coe,mul_one] using hr1⟩

@[simp] theorem norm_singularRadialPoint (ζ : Boundary) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖(singularRadialPoint ζ r hr hr1).val‖ = r := by
  simp only [singularRadialPoint,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
    fourier_one,Circle.norm_coe,mul_one]

theorem singular_poisson_integrable (μ : Measure Boundary) [IsFiniteMeasure μ] (w : Disk) :
    Integrable (atomicPoissonKernel w.val) μ := by
  change Integrable (fun t => (1-‖w.val‖^2)/‖fourier (T := 1) 1 t-w.val‖^2) μ
  simpa only [atomicPoissonKernel,singularInverseWeight,div_eq_mul_inv] using
    (singularInverseWeight_integrable μ w).const_mul (1-‖w.val‖^2)

theorem singular_poisson_nonneg (w : Disk) (t : Boundary) : 0 ≤ atomicPoissonKernel w.val t := by
  apply div_nonneg _ (sq_nonneg _)
  have hw : ‖w.val‖ < 1 := w.property
  nlinarith [norm_nonneg w.val]

/-- A chord-ball concentration gives an actual lower bound on the Poisson integral. -/
theorem singular_radial_poisson_lower (μ : Measure Boundary) [IsFiniteMeasure μ]
    (ζ : Boundary) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real (singularChordBall ζ δ)/(4*δ) ≤
      ∫ t,atomicPoissonKernel (((1-δ : ℝ) : ℂ)*fourier (T := 1) 1 ζ) t ∂μ := by
  let w := singularRadialPoint ζ (1-δ) (by linarith) (by linarith)
  have hnumer : δ ≤ 1-‖w.val‖^2 := by rw [norm_singularRadialPoint]; nlinarith
  have hball (t : Boundary) (ht : t ∈ singularChordBall ζ δ) :
      1/(4*δ) ≤ atomicPoissonKernel w.val t := by
    have ht' : ‖fourier (T := 1) 1 t-fourier (T := 1) 1 ζ‖ ≤ δ := by
      change dist (fourier (T := 1) 1 t) (fourier (T := 1) 1 ζ) ≤ δ at ht
      rwa [dist_eq_norm] at ht
    have hrad : ‖fourier (T := 1) 1 ζ-w.val‖ = δ := by
      change ‖fourier (T := 1) 1 ζ-(((1-δ : ℝ) : ℂ)*fourier (T := 1) 1 ζ)‖ = _
      rw [show fourier (T := 1) 1 ζ-(((1-δ : ℝ) : ℂ)*fourier (T := 1) 1 ζ) =
        (δ : ℂ)*fourier (T := 1) 1 ζ by push_cast; ring]
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hδ.le,show ‖fourier (T := 1) 1 ζ‖ = 1 by simp,mul_one]
    have hdist : ‖fourier (T := 1) 1 t-w.val‖ ≤ 2*δ := by
      have h := dist_triangle (fourier (T := 1) 1 t) (fourier (T := 1) 1 ζ) w.val
      simp only [dist_eq_norm] at h
      rw [hrad] at h
      linarith
    have hd : 0 < ‖fourier (T := 1) 1 t-w.val‖^2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (circlePoint_sub_disk_ne_zero t w))
    change 1/(4*δ) ≤ (1-‖w.val‖^2)/‖fourier (T := 1) 1 t-w.val‖^2
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4*δ) hd).mpr
    calc
      1*‖fourier (T := 1) 1 t-w.val‖^2 ≤ (2*δ)^2 := by
        simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg _) hdist 2
      _ = δ*(4*δ) := by ring
      _ ≤ (1-‖w.val‖^2)*(4*δ) := mul_le_mul_of_nonneg_right hnumer (by positivity)
  have hi := singular_poisson_integrable μ w
  calc
    μ.real (singularChordBall ζ δ)/(4*δ) = ∫ _ in singularChordBall ζ δ,1/(4*δ) ∂μ := by
      rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
      ring
    _ ≤ ∫ t in singularChordBall ζ δ,atomicPoissonKernel w.val t ∂μ :=
      setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn (singularChordBall_measurable ζ δ) hball
    _ ≤ ∫ t,atomicPoissonKernel w.val t ∂μ :=
      setIntegral_le_integral hi (Eventually.of_forall (singular_poisson_nonneg w))

/-- At a point with differentiated Haar/singular ratio zero, arbitrarily small chord balls
carry arbitrarily large mass relative to their radius. The finite/zero-denominator cases
are handled in the extended nonnegative reals before passing to real measures. -/
theorem singular_small_chord_mass (μ : Measure Boundary) (hμ : finiteSingular μ)
    (ζ : Boundary) (hζ : Tendsto (fun δ : ℝ =>
      embeddedCircleMeasure circleMeasure (closedBall (fourier (T := 1) 1 ζ) δ) /
        embeddedCircleMeasure μ (closedBall (fourier (T := 1) 1 ζ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (N ε : ℝ) (hN : 0 < N) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < ε ∧ N*δ < μ.real (singularChordBall ζ δ) := by
  let : IsFiniteMeasure μ := ⟨hμ.1⟩
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall := hζ.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal (c/N)))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < min ε 1 :=
    eventually_of_mem (Ioo_mem_nhdsGT (lt_min hε zero_lt_one)) fun _ h => h
  obtain ⟨δ,hRat,hδ,hδsmall⟩ := (hsmall.and hev).exists
  have hδ1 := (lt_min_iff.mp hδsmall).2
  have hδε := (lt_min_iff.mp hδsmall).1
  let R := embeddedCircleMeasure circleMeasure (closedBall (fourier (T := 1) 1 ζ) δ)
  let M := embeddedCircleMeasure μ (closedBall (fourier (T := 1) 1 ζ) δ)
  change R/M < ENNReal.ofReal (c/N) at hRat
  have hRtop : R ≠ ∞ := measure_ne_top _ _
  have hMtop : M ≠ ∞ := measure_ne_top _ _
  have hHaar : ENNReal.ofReal (δ/(2*Real.pi)) ≤ R := embeddedHaar_closedBall_lower ζ δ hδ hδ1
  have hRpos : 0 < R := (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hHaar
  have hMzero : M ≠ 0 := by
    intro hz
    rw [hz,ENNReal.div_zero hRpos.ne'] at hRat
    exact not_top_lt hRat
  have hMpos : 0 < M.toReal := ENNReal.toReal_pos hMzero hMtop
  have hRatTop : R/M ≠ ∞ := ne_top_of_lt hRat
  have hRatReal : R.toReal/M.toReal < c/N := by
    have h := (ENNReal.toReal_lt_toReal hRatTop ENNReal.ofReal_ne_top).mpr hRat
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofReal (by positivity : 0 ≤ c/N)] using h
  have hLower : c*δ ≤ R.toReal := by
    have h := ENNReal.toReal_mono hRtop hHaar
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ/(2*Real.pi))] at h
    convert h using 1
    dsimp [c]
    ring
  have hprod : R.toReal*N < c*M.toReal := (div_lt_div_iff₀ hMpos hN).mp hRatReal
  have hcomp : c*(N*δ) < c*M.toReal := by
    calc
      c*(N*δ) = (c*δ)*N := by ring
      _ ≤ R.toReal*N := mul_le_mul_of_nonneg_right hLower hN.le
      _ < c*M.toReal := hprod
  have hgrowth : N*δ < M.toReal := (mul_lt_mul_iff_right₀ hc).mp hcomp
  refine ⟨δ,hδ,hδ1,hδε,?_⟩
  simpa only [M,embeddedCircleMeasure_chordBall,measureReal_def] using hgrowth

/-- At almost every point of the literal singular measure there is a genuine radial disk
sequence approaching that circle point along which the actual inner analytic values tend to zero.
No atomicity, nonemptiness, or assumed boundary-value theorem is used. -/
theorem singular_radial_zero_sequence (u : BoundaryLInf) (μ : Measure Boundary)
    (hμ : HasSingularRepresentation u μ) :
    ∀ᵐ ζ ∂μ, ∃ r : ℕ → ℝ, (∀ n,0 ≤ r n ∧ r n < 1) ∧
      Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => innerValue u ((r n : ℂ)*fourier (T := 1) 1 ζ)) atTop (𝓝 0) := by
  let : IsFiniteMeasure μ := ⟨hμ.1.1⟩
  filter_upwards [singular_circle_ratio_zero μ hμ.1] with ζ hζ
  have hc (n : ℕ) := singular_small_chord_mass μ hμ.1 ζ hζ (4*((n : ℝ)+1))
    (1/((n : ℝ)+2)) (by positivity) (by positivity)
  choose δ hδ hδ1 hδsmall hmass using hc
  let r : ℕ → ℝ := fun n => 1-δ n
  have hr (n : ℕ) : 0 ≤ r n ∧ r n < 1 := by
    dsimp [r]
    constructor <;> linarith [hδ n,hδ1 n]
  have hnat2 : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hnat2
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    squeeze_zero (fun n => (hδ n).le) (fun n => (hδsmall n).le) hinv
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hδlim
  refine ⟨r,hr,hrlim,?_⟩
  have hpoisson (n : ℕ) : (n : ℝ)+1 ≤
      ∫ t,atomicPoissonKernel ((r n : ℂ)*fourier (T := 1) 1 ζ) t ∂μ := by
    have hN : (n : ℝ)+1 < μ.real (singularChordBall ζ (δ n))/(4*δ n) := by
      apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (hδ n))).mpr
      convert hmass n using 1; ring
    exact hN.le.trans (singular_radial_poisson_lower μ ζ (δ n) (hδ n) (hδ1 n))
  have hbound (n : ℕ) : ‖innerValue u ((r n : ℂ)*fourier (T := 1) 1 ζ)‖ ≤
      Real.exp (-((n : ℝ)+1)) := by
    let w := singularRadialPoint ζ (r n) (hr n).1 (hr n).2
    obtain ⟨α,hα,hval⟩ := hμ.2
    change ‖innerValue u w.val‖ ≤ _
    rw [hval _ w.property,norm_mul,hα,one_mul,norm_singularInnerValue_poisson μ w]
    exact Real.exp_le_exp.mpr (neg_le_neg (hpoisson n))
  have hnat1 : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ)+1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnat1)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hbound hexp)

end TTO.Paper.Proved
