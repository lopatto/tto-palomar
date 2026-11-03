/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CauchyDerivativeFoundations
public import TTO.PolynomialInnerOuterFoundations
public import TTO.HardyPolynomialApproximationFoundations
public import TTO.VMOACompactReductionFoundations

/-! Actual H¹ factorization and weighted Cauchy–Schwarz reduction.
The weighted embedding is an explicit intermediate estimate, supplied by PolarBoxEstimatesFoundations. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The complete weighted embedding needed for this fixed Hardy symbol. -/
def HardyWeightedEmbedding (g : Hardy) (A : ℝ) : Prop :=
  ∀ q : Hardy,
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖hardyWeightedPairingKernel g z‖^2*
      ‖analyticValue q.val z‖^2) ∂diskArea)≤ENNReal.ofReal (A^2*‖q‖^2)

def diskSqrtWeight (z : ℂ) : ℂ := (Real.sqrt (1-‖z‖^2) : ℂ)

theorem continuous_diskSqrtWeight : Continuous diskSqrtWeight := by
  unfold diskSqrtWeight
  fun_prop

theorem norm_diskSqrtWeight_sq_ae : (fun z => ‖diskSqrtWeight z‖^2)=ᵐ[diskArea]
    fun z => 1-‖z‖^2 := by
  filter_upwards [ae_mem_diskArea] with z hz
  have hPos : 0≤1-‖z‖^2 := by
    have hz1 : ‖z‖<1 := hz
    nlinarith [norm_nonneg z]
  simp only [diskSqrtWeight,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg (1-‖z‖^2)),Real.sq_sqrt hPos]

/-- An honest weighted extended-energy bound gives a native L² function and real bound. -/
theorem weighted_analytic_memLp_two (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (D : ℝ) (hEnergy : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) ∂diskArea)≤
      ENNReal.ofReal (D^2)) :
    MemLp (fun z => diskSqrtWeight z*F z) 2 diskArea ∧
      (∫ z,‖diskSqrtWeight z*F z‖^2 ∂diskArea)≤D^2 := by
  have hFM : AEStronglyMeasurable F diskArea := by
    rw [diskArea]
    exact (hF.continuousOn.aestronglyMeasurable
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul_measure _
  have hQM : AEStronglyMeasurable (fun z => diskSqrtWeight z*F z) diskArea :=
    continuous_diskSqrtWeight.aestronglyMeasurable.mul hFM
  have hEq : (fun z => ENNReal.ofReal (‖diskSqrtWeight z*F z‖^2))=ᵐ[diskArea]
      fun z => ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) := by
    filter_upwards [norm_diskSqrtWeight_sq_ae] with z hz
    rw [norm_mul,mul_pow,hz]
  have hI : Integrable (fun z => ‖diskSqrtWeight z*F z‖^2) diskArea := by
    refine ⟨hQM.norm.pow 2,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using
      (lintegral_congr_ae hEq).trans_le hEnergy |>.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hQM).mpr hI,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg D)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun z => sq_nonneg ‖diskSqrtWeight z*F z‖)]
  exact (lintegral_congr_ae hEq).trans_le hEnergy

/-- Weighted Cauchy–Schwarz with finite, explicit bounds and ordinary integrability. -/
theorem weighted_analytic_norm_product_bound (F G : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (hG : AnalyticOnNhd ℂ G disk)
    (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hFEnergy : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) ∂diskArea)≤
      ENNReal.ofReal (D^2))
    (hGEnergy : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖G z‖^2) ∂diskArea)≤
      ENNReal.ofReal (E^2)) :
    Integrable (fun z => (1-‖z‖^2)*‖F z‖*‖G z‖) diskArea ∧
      (∫ z,(1-‖z‖^2)*‖F z‖*‖G z‖ ∂diskArea)≤D*E := by
  have hU := weighted_analytic_memLp_two F hF D hFEnergy
  have hV := weighted_analytic_memLp_two G hG E hGEnergy
  have hInt := hU.1.norm.integrable_mul hV.1.norm
  have hEq : (fun z => ‖diskSqrtWeight z*F z‖*‖diskSqrtWeight z*G z‖)=ᵐ[diskArea]
      fun z => (1-‖z‖^2)*‖F z‖*‖G z‖ := by
    filter_upwards [norm_diskSqrtWeight_sq_ae] with z hz
    simp only [norm_mul]
    calc
      _ = ‖diskSqrtWeight z‖^2*‖F z‖*‖G z‖ := by ring
      _ = _ := by rw [hz]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=diskArea) Real.HolderConjugate.two_two
    (Eventually.of_forall fun z => norm_nonneg (diskSqrtWeight z*F z))
    (Eventually.of_forall fun z => norm_nonneg (diskSqrtWeight z*G z))
    (by simpa only [ENNReal.ofReal_ofNat] using hU.1.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hV.1.norm)
  simp only [Real.rpow_two] at hCS
  have hRoot {x R : ℝ} (hx : 0≤x) (hR : 0≤R) (h : x≤R^2) : x^(1/(2 : ℝ))≤R := by
    calc
      _ ≤ (R^2)^(1/(2 : ℝ)) := Real.rpow_le_rpow hx h (by positivity)
      _ = R := by rw [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_of_nonneg hR]
  refine ⟨hInt.congr hEq,?_⟩
  rw [← integral_congr_ae hEq]
  exact hCS.trans (mul_le_mul
    (hRoot (integral_nonneg fun z => sq_nonneg _) hD hU.2)
    (hRoot (integral_nonneg fun z => sq_nonneg _) hE hV.2)
    (Real.rpow_nonneg (integral_nonneg fun z => sq_nonneg _) _) hD)

/-- A single product-rule term, with actual integrability supplied by the embedding. -/
theorem hardy_weighted_factor_term_bound (g q r : Hardy) (A : ℝ) (hA : 0≤A)
    (hEmbedding : HardyWeightedEmbedding g A) :
    Integrable (fun z => (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      analyticValue q.val z*deriv (analyticValue r.val) z) diskArea ∧
    ‖∫ z,(conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      analyticValue q.val z*deriv (analyticValue r.val) z ∂diskArea‖≤A*‖q‖*‖r‖ := by
  let F : ℂ → ℂ := fun z => hardyWeightedPairingKernel g z*analyticValue q.val z
  let R : ℂ → ℂ := deriv (analyticValue r.val)
  have hF : AnalyticOnNhd ℂ F disk := fun z hz =>
    (analyticOnNhd_hardyWeightedPairingKernel g z hz).mul (analyticOnNhd_analyticValue q.val z hz)
  have hR : AnalyticOnNhd ℂ R disk := fun z hz =>
    (analyticOnNhd_analyticValue r.val z hz).deriv
  have hEnergy : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) ∂diskArea)≤
      ENNReal.ofReal ((A*‖q‖)^2) := by
    simpa only [F,norm_mul,mul_pow,mul_assoc] using hEmbedding q
  have hN := weighted_analytic_norm_product_bound F R hF hR (A*‖q‖) ‖r‖
    (mul_nonneg hA (norm_nonneg q)) (norm_nonneg r) hEnergy
    (analyticValue_deriv_weighted_energy_le r)
  let J : ℂ → ℂ := fun z =>
    (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      analyticValue q.val z*deriv (analyticValue r.val) z
  have hJM : AEStronglyMeasurable J diskArea := by
    rw [diskArea]
    have hCont : ContinuousOn J disk := by
      exact ((((Complex.continuous_conj.comp_continuousOn
        (analyticOnNhd_hardyWeightedPairingKernel g).continuousOn).mul
        (by fun_prop)).mul (analyticOnNhd_analyticValue q.val).continuousOn).mul hR.continuousOn)
    exact (hCont.aestronglyMeasurable
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul_measure _
  have hNorm : (fun z => ‖J z‖)=ᵐ[diskArea]
      fun z => (1-‖z‖^2)*‖F z‖*‖R z‖ := by
    filter_upwards [ae_mem_diskArea] with z hz
    have hPos : 0≤1-‖z‖^2 := by
      have hz1 : ‖z‖<1 := hz
      nlinarith [norm_nonneg z]
    change ‖(conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      analyticValue q.val z*deriv (analyticValue r.val) z‖=_
    simp only [F,R,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg hPos]
    ring
  have hJ : Integrable J diskArea := hN.1.mono' hJM (hNorm.mono fun z hz => hz.le)
  refine ⟨hJ,?_⟩
  exact (norm_integral_le_integral_norm _).trans
    ((integral_congr_ae hNorm).le.trans hN.2)

/-- Actual multiplication of the factor boundaries gives the polynomial on the disk. -/
theorem polynomial_disk_factorization (p : Polynomial ℂ) (q r : BoundaryLInf)
    (hq : toL2 q∈hardy) (hr : toL2 r∈hardy)
    (hp : multiplyInf q r=analyticPolynomialBoundary p) (z : ℂ) (hz : z∈disk) :
    p.eval z=analyticValue (toL2 q) z*analyticValue (toL2 r) z := by
  rw [← innerValue_analyticPolynomialBoundary p ⟨z,hz⟩,← hp,
    innerValue_multiplyInf q r hq hr ⟨z,hz⟩]
  rfl

/-- The product derivative is proved locally on the open disk, not inferred at the boundary. -/
theorem polynomial_disk_factor_derivative (p : Polynomial ℂ) (q r : BoundaryLInf)
    (hq : toL2 q∈hardy) (hr : toL2 r∈hardy)
    (hp : multiplyInf q r=analyticPolynomialBoundary p) (z : ℂ) (hz : z∈disk) :
    p.derivative.eval z=deriv (analyticValue (toL2 q)) z*analyticValue (toL2 r) z+
      analyticValue (toL2 q) z*deriv (analyticValue (toL2 r)) z := by
  have he : (fun w => p.eval w)=ᶠ[𝓝 z]
      fun w => analyticValue (toL2 q) w*analyticValue (toL2 r) w := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact polynomial_disk_factorization p q r hq hr hp w hw
  have hd := he.deriv_eq
  rw [Polynomial.deriv] at hd
  apply hd.trans
  simpa only [Pi.mul_apply] using! deriv_mul
    (analyticOnNhd_analyticValue (toL2 q) z hz).differentiableAt
    (analyticOnNhd_analyticValue (toL2 r) z hz).differentiableAt

/-- Actual polynomial H¹ factorization plus weighted Cauchy–Schwarz.
The zero mode is retained independently of the embedding constant. -/
theorem hardy_polynomial_l1_bound_of_weighted_embedding (g : Hardy) (A : ℝ) (hA : 0≤A)
    (hEmbedding : HardyWeightedEmbedding g A) (p : Polynomial ℂ) :
    ‖inner ℂ g.val (polynomialBoundary p).val‖≤
      (‖fourierCoeff g.val 0‖+2*A)*
        (∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure) := by
  obtain ⟨q,r,hq,hr,hp,hNorm⟩ := polynomialH1Factorization p
  let Q : Hardy := ⟨toL2 q,hq⟩
  let R : Hardy := ⟨toL2 r,hr⟩
  have hQR := hardy_weighted_factor_term_bound g Q R A hA hEmbedding
  have hRQ := hardy_weighted_factor_term_bound g R Q A hA hEmbedding
  let J : Hardy → Hardy → ℂ → ℂ := fun q r z =>
    (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      analyticValue q.val z*deriv (analyticValue r.val) z
  have hPair := (hardy_polynomial_weighted_pairing g p).2
  have hIntegral :
      (∫ z,(conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
        p.derivative.eval z ∂diskArea)=
        (∫ z,J Q R z ∂diskArea)+(∫ z,J R Q z ∂diskArea) := by
    rw [← integral_add hQR.1 hRQ.1]
    apply integral_congr_ae
    filter_upwards [ae_mem_diskArea] with z hz
    rw [polynomial_disk_factor_derivative p q r hq hr hp z hz]
    dsimp only [J,Q,R]
    ring
  have hZero : ‖p.coeff 0‖≤‖Q‖*‖R‖ := by
    have he := polynomial_disk_factorization p q r hq hr hp 0 (by norm_num [disk])
    rw [← Polynomial.coeff_zero_eq_eval_zero,analyticValue_at_zero,analyticValue_at_zero] at he
    rw [he,norm_mul]
    exact mul_le_mul (norm_fourierCoeff_le (toL2 q) 0)
      (norm_fourierCoeff_le (toL2 r) 0) (norm_nonneg _) (norm_nonneg _)
  have hConstant : ‖conj (fourierCoeff g.val 0)*p.coeff 0‖≤
      ‖fourierCoeff g.val 0‖*(‖Q‖*‖R‖) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left hZero (norm_nonneg _)
  rw [hPair,hIntegral,← hNorm]
  calc
    _ ≤ ‖conj (fourierCoeff g.val 0)*p.coeff 0‖+
        ‖(∫ z,J Q R z ∂diskArea)+(∫ z,J R Q z ∂diskArea)‖ := norm_add_le _ _
    _ ≤ ‖fourierCoeff g.val 0‖*(‖Q‖*‖R‖)+
        (A*‖Q‖*‖R‖+A*‖R‖*‖Q‖) :=
      add_le_add hConstant ((norm_add_le _ _).trans (add_le_add hQR.2 hRQ.2))
    _ = _ := by change _=(‖fourierCoeff g.val 0‖+2*A)*(‖Q‖*‖R‖); ring

/-- The same bound stated in the native L¹ norm used by the duality interface. -/
theorem finite_hardy_l1_bound_of_weighted_embedding (g : Hardy) (A : ℝ) (hA : 0≤A)
    (hEmbedding : HardyWeightedEmbedding g A) (N : ℕ) (c : ℕ → ℂ) :
    ‖inner ℂ g.val (∑ n∈range N,c n • hardyBasis n).val‖≤
      (‖fourierCoeff g.val 0‖+2*A)*
        ‖nativeL2toL1 (∑ n∈range N,c n • hardyBasis n).val‖ := by
  have h := hardy_polynomial_l1_bound_of_weighted_embedding g A hA hEmbedding
    (finiteHardyPolynomial N c)
  rw [← nativeL1_norm_polynomialBoundary,polynomialBoundary_finiteHardyPolynomial] at h
  exact h

/-- Universal weighted Hardy embedding controlled by arc mean oscillation.
Proved in PolarBoxEstimatesFoundations. -/
def HardyWeightedOscillationEmbedding : Prop :=
  ∃ C : ℝ,0<C ∧ ∀ g : Hardy,∀ B : ℝ,0≤B →
    (∀ a b : ℝ,a<b → b-a≤1 → meanOscillation g.val a b≤B) →
      HardyWeightedEmbedding g (C*B)

/-- The weighted analytic embedding implies the finite-Hardy L¹ pairing estimate. -/
theorem finiteHardyL1OscillationEstimate_of_weighted_embedding
    (hEmbedding : HardyWeightedOscillationEmbedding) : FiniteHardyL1OscillationEstimate := by
  obtain ⟨C,hC,hEmbedding⟩ := hEmbedding
  refine ⟨1+2*C,by positivity,?_⟩
  intro g B hB hMO N c
  have h := finite_hardy_l1_bound_of_weighted_embedding g (C*B)
    (mul_nonneg hC.le hB) (hEmbedding g B hB hMO) N c
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hn : 0≤‖fourierCoeff g.val 0‖ := norm_nonneg _
  nlinarith [mul_nonneg hC.le hn]

/-- Hartman criterion from the weighted oscillation embedding hypothesis. -/
theorem hartmanObligation_of_weighted_oscillation_embedding
    (hEmbedding : HardyWeightedOscillationEmbedding) : HartmanObligation :=
  hartmanObligation_of_finiteHardyL1OscillationEstimate
    (finiteHardyL1OscillationEstimate_of_weighted_embedding hEmbedding)

end TTO.Paper.Proved
