/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.DerivativeSzegoFrameFoundations
public import TTO.WeightedRadialRecoveryFoundations

/-! Actual weighted-area analytic pairings, without an unweighted L¹ derivative assumption. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The existing weighted moment proof needs only its exact weighted integrability. -/
theorem analytic_weighted_disk_moment_of_integrable (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (n : ℕ)
    (hI : Integrable (fun z => (conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z) diskArea) :
    (∫ z,(conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z ∂diskArea)=
      diskTaylorCoeff F n/(((n : ℂ)+1)*((n : ℂ)+2)) := by
  rw [integral_diskArea_polar _ hI]
  calc
    _ = ∫ r : ℝ,diskTaylorCoeff F n*(((1-r^2)*r^(2*n) : ℝ) : ℂ) ∂diskRadialMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_mem_diskRadialMeasure] with r hr
      have he (t : Boundary) :
          (conj ((r : ℂ)*fourier (T := 1) 1 t)^n*
            ((1-‖(r : ℂ)*fourier (T := 1) 1 t‖^2 : ℝ) : ℂ))*
              F ((r : ℂ)*fourier (T := 1) 1 t)=
          ((r : ℂ)^n*((1-r^2 : ℝ) : ℂ))*
            (conj (fourier (T := 1) 1 t)^n*F ((r : ℂ)*fourier (T := 1) 1 t)) := by
        simp only [map_mul,Complex.conj_ofReal,mul_pow,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg hr.1.le,fourier_one,Circle.norm_coe,mul_one]
        ring
      simp_rw [he]
      rw [integral_const_mul,analytic_radial_circle_coefficient F hF r hr.1.le hr.2 n]
      push_cast
      rw [pow_mul]
      ring
    _ = _ := by
      rw [integral_const_mul,integral_complex_ofReal,integral_weighted_radial_monomial]
      push_cast
      ring

theorem conjugate_analytic_weighted_disk_moment_of_integrable (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (n : ℕ)
    (hI : Integrable (fun z => (conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z) diskArea) :
    Integrable (fun z => (conj (F z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n) diskArea ∧
      (∫ z,(conj (F z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n ∂diskArea)=
        conj (diskTaylorCoeff F n)/(((n : ℂ)+1)*((n : ℂ)+2)) := by
  have he (z : ℂ) : conj ((conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z)=
      (conj (F z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n := by
    simp only [map_mul,map_pow,Complex.conj_conj,Complex.conj_ofReal]
    ring
  have hConj : Integrable (fun z => conj ((conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z)) diskArea :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hI
  refine ⟨hConj.congr (Eventually.of_forall he),?_⟩
  calc
    _ = ∫ z,conj ((conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z) ∂diskArea :=
      integral_congr_ae (Eventually.of_forall fun z => (he z).symm)
    _ = _ := by
      rw [integral_conj,analytic_weighted_disk_moment_of_integrable F hF n hI]
      simp [show (2 : ℂ)=1+1 by ring]

/-- The actual Hardy backward shift supplies the missing coefficient term. -/
def hardyWeightedPairingKernel (g : Hardy) (z : ℂ) : ℂ :=
  deriv (analyticValue g.val) z+analyticValue (hardyBackwardShift g.val) z

theorem analyticOnNhd_hardyWeightedPairingKernel (g : Hardy) :
    AnalyticOnNhd ℂ (hardyWeightedPairingKernel g) disk := by
  intro z hz
  exact ((analyticOnNhd_analyticValue g.val z hz).deriv).add
    (analyticOnNhd_analyticValue (hardyBackwardShift g.val) z hz)

theorem fourierCoeff_hardyBackwardShift_nonneg (g : Hardy) (n : ℕ) :
    fourierCoeff (hardyBackwardShift g.val) (n : ℤ)=fourierCoeff g.val ((n+1 : ℕ) : ℤ) := by
  rw [hardyBackwardShift,fourierCoeff_backwardShift,fourierCoeff_sub_L2,fourierCoeff_constL2,
    ite_eq_right (by omega : (n : ℤ)+1≠0),sub_zero]
  simp only [Nat.cast_add,Nat.cast_one]

theorem diskTaylorCoeff_hardyWeightedPairingKernel (g : Hardy) (n : ℕ) :
    diskTaylorCoeff (hardyWeightedPairingKernel g) n=
      ((n : ℂ)+2)*fourierCoeff g.val ((n+1 : ℕ) : ℤ) := by
  have hD : AnalyticAt ℂ (deriv (analyticValue g.val)) 0 :=
    (analyticOnNhd_analyticValue g.val 0 (by norm_num [disk])).deriv
  have hH : AnalyticAt ℂ (analyticValue (hardyBackwardShift g.val)) 0 :=
    analyticOnNhd_analyticValue (hardyBackwardShift g.val) 0 (by norm_num [disk])
  have hAdd : diskTaylorCoeff (hardyWeightedPairingKernel g) n=
      diskTaylorCoeff (deriv (analyticValue g.val)) n+
        diskTaylorCoeff (analyticValue (hardyBackwardShift g.val)) n := by
    unfold diskTaylorCoeff
    change iteratedDeriv n (deriv (analyticValue g.val)+analyticValue (hardyBackwardShift g.val)) 0/
      (n.factorial : ℂ)=_
    rw [iteratedDeriv_add hD.contDiffAt hH.contDiffAt,add_div]
  rw [hAdd,diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue,diskTaylorCoeff_analyticValue,
    fourierCoeff_hardyBackwardShift_nonneg]
  push_cast
  ring



theorem hardy_coefficient_energy_nat (g : Hardy) :
    (∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2))=
      ENNReal.ofReal (‖g‖^2) := by
  have hs := hasSum_basis_inner_norm_sq hardyBasis g
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg
    (fun n => sq_nonneg ‖inner ℂ (hardyBasis n) g‖) hs.summable]
  apply tsum_congr
  intro n
  rw [← hardyBasis_repr_eq_fourierCoeff,HilbertBasis.repr_apply_apply]

theorem hardyWeightedPairingKernel_weighted_energy_le (g : Hardy) :
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖hardyWeightedPairingKernel g z‖^2) ∂diskArea)≤
      ENNReal.ofReal (2*‖g‖^2) := by
  rw [analytic_weighted_disk_area_parseval _ (analyticOnNhd_hardyWeightedPairingKernel g)]
  have hTerm (n : ℕ) :
      ENNReal.ofReal (‖diskTaylorCoeff (hardyWeightedPairingKernel g) n‖^2/
        (((n : ℝ)+1)*((n : ℝ)+2)))≤
      2*ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) := by
    have hNorm : ‖(n : ℂ)+2‖=(n : ℝ)+2 := by
      simpa only [Nat.cast_add,Nat.cast_ofNat] using Complex.norm_natCast (n+2)
    rw [diskTaylorCoeff_hardyWeightedPairingKernel,norm_mul,mul_pow,hNorm]
    have hDen : 0<((n : ℝ)+1)*((n : ℝ)+2) := by positivity
    have hRatio : ((n : ℝ)+2)^2/(((n : ℝ)+1)*((n : ℝ)+2))≤2 := by
      apply (div_le_iff₀ hDen).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hh : ((n : ℝ)+2)^2*‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2/
        (((n : ℝ)+1)*((n : ℝ)+2))≤
        2*‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2 := by
      calc
        _ = (((n : ℝ)+2)^2/(((n : ℝ)+1)*((n : ℝ)+2)))*
            ‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hRatio (sq_nonneg _)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hh
  have hTail : (∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2))≤
      ∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2) := by
    calc
      _ ≤ ENNReal.ofReal (‖fourierCoeff g.val 0‖^2)+
          ∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) := le_add_self
      _ = _ := by
        simpa only [Nat.cast_zero] using! (tsum_eq_zero_add'
          (f := fun n : ℕ => ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2)) ENNReal.summable).symm
  calc
    _ ≤ ∑' n : ℕ,2*ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) :=
      ENNReal.tsum_le_tsum hTerm
    _ = 2*∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) :=
      ENNReal.tsum_mul_left
    _ ≤ 2*∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2) := by
      gcongr
    _ = _ := by
      rw [hardy_coefficient_energy_nat,ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),
        ENNReal.ofReal_ofNat]



/-- Weighted L² finiteness suffices for the actual weighted L¹ integrand.
No unweighted integrability of F is required or inferred. -/
theorem integrable_weighted_analytic_of_weighted_l2 (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk)
    (hFin : (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) ∂diskArea)<∞) :
    Integrable (fun z => ((1-‖z‖^2 : ℝ) : ℂ)*F z) diskArea := by
  have hFM : AEStronglyMeasurable F diskArea := by
    rw [diskArea]
    exact (hF.continuousOn.aestronglyMeasurable
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul_measure _
  let k : ℂ → ℂ := fun z => (Real.sqrt (1-‖z‖^2) : ℂ)
  have hK : Continuous k := by dsimp only [k]; fun_prop
  have hKN (z : ℂ) : ‖k z‖≤1 := by
    rw [show ‖k z‖=Real.sqrt (1-‖z‖^2) by
      simp only [k,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg (1-‖z‖^2))]]
    exact (Real.sqrt_le_sqrt (show 1-‖z‖^2≤1 by nlinarith [sq_nonneg ‖z‖])).trans_eq
      (by norm_num)
  have hQM : AEStronglyMeasurable (fun z => k z*F z) diskArea :=
    hK.aestronglyMeasurable.mul hFM
  have hEq : (fun z => ENNReal.ofReal (‖k z*F z‖^2))=ᵐ[diskArea]
      fun z => ENNReal.ofReal ((1-‖z‖^2)*‖F z‖^2) := by
    filter_upwards [ae_mem_diskArea] with z hz
    have hPos : 0≤1-‖z‖^2 := by
      have hh : ‖z‖<1 := hz
      nlinarith [norm_nonneg z]
    simp only [k,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg (1-‖z‖^2)),Real.sq_sqrt hPos]
  have hQI : Integrable (fun z => ‖k z*F z‖^2) diskArea := by
    refine ⟨hQM.norm.pow 2,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using
      (lintegral_congr_ae hEq).trans_lt hFin
  have hQ : MemLp (fun z => k z*F z) 2 diskArea :=
    (memLp_two_iff_integrable_sq_norm hQM).mpr hQI
  have hQL1 : Integrable (fun z => k z*F z) diskArea := hQ.integrable (by norm_num)
  have hTwice : Integrable (fun z => k z*(k z*F z)) diskArea := by
    apply hQL1.norm.mono' (hK.aestronglyMeasurable.mul hQM)
    exact Eventually.of_forall fun z => by
      change ‖k z*(k z*F z)‖≤‖k z*F z‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg (k z*F z)) (hKN z)
  apply hTwice.congr
  filter_upwards [ae_mem_diskArea] with z hz
  have hPos : 0≤1-‖z‖^2 := by
    have hh : ‖z‖<1 := hz
    nlinarith [norm_nonneg z]
  have hKK : k z*k z=((1-‖z‖^2 : ℝ) : ℂ) := by
    dsimp only [k]
    rw [← pow_two,← Complex.ofReal_pow,Real.sq_sqrt hPos]
  rw [← mul_assoc,hKK]

theorem integrable_weighted_analytic_monomial (F : ℂ → ℂ)
    (hI : Integrable (fun z => ((1-‖z‖^2 : ℝ) : ℂ)*F z) diskArea) (n : ℕ) :
    Integrable (fun z => (conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z) diskArea := by
  have hM : AEStronglyMeasurable
      (fun z => (conj z^n*((1-‖z‖^2 : ℝ) : ℂ))*F z) diskArea := by
    simpa only [mul_assoc] using!
      ((Complex.continuous_conj.pow n).aestronglyMeasurable.mul hI.aestronglyMeasurable)
  apply hI.norm.mono' hM
  filter_upwards [ae_mem_diskArea] with z hz
  rw [mul_assoc,norm_mul,norm_pow,Complex.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) (le_of_lt hz))

theorem hardyWeightedPairingKernel_weighted_integrable (g : Hardy) :
    Integrable (fun z => ((1-‖z‖^2 : ℝ) : ℂ)*hardyWeightedPairingKernel g z) diskArea :=
  integrable_weighted_analytic_of_weighted_l2 _ (analyticOnNhd_hardyWeightedPairingKernel g)
    ((hardyWeightedPairingKernel_weighted_energy_le g).trans_lt ENNReal.ofReal_lt_top)

theorem hardyWeightedPairingKernel_moment (g : Hardy) (n : ℕ) :
    Integrable (fun z => (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n) diskArea ∧
      (∫ z,(conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*z^n ∂diskArea)=
        conj (fourierCoeff g.val ((n+1 : ℕ) : ℤ))/((n : ℂ)+1) := by
  have h := conjugate_analytic_weighted_disk_moment_of_integrable _
    (analyticOnNhd_hardyWeightedPairingKernel g) n
    (integrable_weighted_analytic_monomial _ (hardyWeightedPairingKernel_weighted_integrable g) n)
  refine ⟨h.1,?_⟩
  rw [h.2,diskTaylorCoeff_hardyWeightedPairingKernel,map_mul,map_add,map_natCast,map_ofNat]
  have h1 : (n : ℂ)+1≠0 := by exact_mod_cast (show (n : ℝ)+1≠0 by positivity)
  have h2 : (n : ℂ)+2≠0 := by exact_mod_cast (show (n : ℝ)+2≠0 by positivity)
  field_simp



theorem polynomialBoundary_add_weightedPairing (p q : Polynomial ℂ) :
    polynomialBoundary (p+q)=polynomialBoundary p+polynomialBoundary q := by
  apply hardy_analyticValue_injective
  intro z hz
  rw [Submodule.coe_add,analyticValue_add _ _ hz,
    analyticValue_polynomialBoundary _ hz,analyticValue_polynomialBoundary _ hz,
    analyticValue_polynomialBoundary _ hz,Polynomial.eval_add]

theorem polynomialBoundary_monomial_weightedPairing (n : ℕ) (c : ℂ) :
    polynomialBoundary (Polynomial.monomial n c)=c • hardyBasis n := by
  apply hardy_analyticValue_injective
  intro z hz
  rw [Submodule.coe_smul,hardyBasis_apply]
  dsimp only [hardyMode]
  change analyticValue (polynomialBoundary (Polynomial.monomial n c)).val z=
    analyticValue (c • fourierBasis (T := 1) (n : ℤ)) z
  rw [analyticValue_smul _ _ hz,analyticValue_fourierBasis,
    analyticValue_polynomialBoundary _ hz,Polynomial.eval_monomial]

theorem inner_polynomialBoundary_monomial_weightedPairing (g : Hardy) (n : ℕ) (c : ℂ) :
    inner ℂ g.val (polynomialBoundary (Polynomial.monomial n c)).val=
      c*conj (fourierCoeff g.val (n : ℤ)) := by
  rw [polynomialBoundary_monomial_weightedPairing,Submodule.coe_smul,hardyBasis_apply]
  dsimp only [hardyMode]
  change inner ℂ g.val (c • fourierBasis (T := 1) (n : ℤ))=_
  rw [inner_smul_right]
  congr 1
  rw [← inner_conj_symm]
  congr 1
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

/-- Exact normalized weighted-area pairing for every actual Hardy vector and polynomial.
Both the constant mode and ordinary integrability are part of the conclusion. -/
theorem hardy_polynomial_weighted_pairing (g : Hardy) (p : Polynomial ℂ) :
    Integrable (fun z => (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
      p.derivative.eval z) diskArea ∧
      inner ℂ g.val (polynomialBoundary p).val=
        conj (fourierCoeff g.val 0)*p.coeff 0+
          ∫ z,(conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*
            p.derivative.eval z ∂diskArea := by
  classical
  let I : Polynomial ℂ → ℂ → ℂ := fun p z =>
    (conj (hardyWeightedPairingKernel g z)*((1-‖z‖^2 : ℝ) : ℂ))*p.derivative.eval z
  change Integrable (I p) diskArea ∧ inner ℂ g.val (polynomialBoundary p).val=
    conj (fourierCoeff g.val 0)*p.coeff 0+∫ z,I p z ∂diskArea
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hAdd (z : ℂ) : I (p+q) z=I p z+I q z := by
      dsimp only [I]
      rw [Polynomial.derivative_add,Polynomial.eval_add]
      ring
    have hInt : Integrable (I (p+q)) diskArea :=
      (hp.1.add hq.1).congr (Eventually.of_forall fun z => (hAdd z).symm)
    refine ⟨hInt,?_⟩
    rw [polynomialBoundary_add_weightedPairing,Submodule.coe_add,inner_add_right,
      Polynomial.coeff_add,integral_congr_ae (Eventually.of_forall hAdd),integral_add hp.1 hq.1,
      hp.2,hq.2]
    ring
  | monomial n c =>
    cases n with
    | zero =>
      have hI (z : ℂ) : I (Polynomial.monomial 0 c) z=0 := by simp [I]
      have hInt : Integrable (I (Polynomial.monomial 0 c)) diskArea := by
        apply (integrable_zero ℂ ℂ diskArea).congr
        exact Eventually.of_forall fun z => (hI z).symm
      refine ⟨hInt,?_⟩
      rw [inner_polynomialBoundary_monomial_weightedPairing]
      simp only [Nat.cast_zero,Polynomial.coeff_monomial,ite_true,hI,integral_zero,add_zero]
      ring
    | succ n =>
      have hM := hardyWeightedPairingKernel_moment g n
      have hI (z : ℂ) : I (Polynomial.monomial (n+1) c) z=
          (c*((n : ℂ)+1))*((conj (hardyWeightedPairingKernel g z)*
            ((1-‖z‖^2 : ℝ) : ℂ))*z^n) := by
        dsimp only [I]
        rw [Polynomial.derivative_monomial_succ,Polynomial.eval_monomial]
        ring
      have hInt : Integrable (I (Polynomial.monomial (n+1) c)) diskArea :=
        (hM.1.const_mul (c*((n : ℂ)+1))).congr (Eventually.of_forall fun z => (hI z).symm)
      refine ⟨hInt,?_⟩
      rw [inner_polynomialBoundary_monomial_weightedPairing,
        Polynomial.coeff_monomial,ite_eq_right (by omega : n+1≠0),mul_zero,zero_add,
        integral_congr_ae (Eventually.of_forall hI),integral_const_mul,hM.2]
      have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show (n : ℝ)+1≠0 by positivity)
      field_simp



theorem hardy_coefficient_energy_tail_le (g : Hardy) :
    (∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2))≤
      ENNReal.ofReal (‖g‖^2) := by
  calc
    _ ≤ ENNReal.ofReal (‖fourierCoeff g.val 0‖^2)+
        ∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) := le_add_self
    _ = ∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2) := by
      simpa only [Nat.cast_zero] using! (tsum_eq_zero_add'
        (f := fun n : ℕ => ENNReal.ofReal (‖fourierCoeff g.val (n : ℤ)‖^2)) ENNReal.summable).symm
    _ = _ := hardy_coefficient_energy_nat g

/-- The actual complex derivative has the standard normalized weighted-area bound. -/
theorem analyticValue_deriv_weighted_energy_le (g : Hardy) :
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖deriv (analyticValue g.val) z‖^2) ∂diskArea)≤
      ENNReal.ofReal (‖g‖^2) := by
  have hD : AnalyticOnNhd ℂ (deriv (analyticValue g.val)) disk :=
    fun z hz => (analyticOnNhd_analyticValue g.val z hz).deriv
  rw [analytic_weighted_disk_area_parseval _ hD]
  calc
    _ ≤ ∑' n : ℕ,ENNReal.ofReal (‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖^2) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue,norm_mul,mul_pow,
        Complex.norm_natCast,Nat.cast_add,Nat.cast_one]
      apply ENNReal.ofReal_le_ofReal
      have hDen : 0<((n : ℝ)+1)*((n : ℝ)+2) := by positivity
      apply (div_le_iff₀ hDen).mpr
      have hRatio : ((n : ℝ)+1)^2≤((n : ℝ)+1)*((n : ℝ)+2) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact (mul_le_mul_of_nonneg_right hRatio
        (sq_nonneg ‖fourierCoeff g.val ((n+1 : ℕ) : ℤ)‖)).trans_eq (mul_comm _ _)
    _ ≤ _ := hardy_coefficient_energy_tail_le g

end TTO.Paper.Proved
