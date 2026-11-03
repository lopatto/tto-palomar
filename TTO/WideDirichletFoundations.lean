/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.DirichletLocalizationFoundations

/-! A genuine signed finite-order low-pass kernel with a wide flat plateau.
The base Dirichlet width is (100m+2)N; the short smoothing factors retain BOTH signs. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The complete negative shift of the wide-base signed product. -/
def wideDirichletProductShift (m N : ℕ) : ℕ := (100*m+2)*N+m*N

/-- A finite-order flat low-pass mask; neither its negative nor its positive modes are discarded. -/
def wideDirichletProductPolynomial (m N : ℕ) : Polynomial ℂ :=
  ((((2*N+1 : ℕ) : ℂ)⁻¹)^m) •
    (centeredDirichletPolynomial ((100*m+2)*N)*(centeredDirichletPolynomial N)^m)

def wideDirichletProductKernel (m N : ℕ) (t : Boundary) : ℂ :=
  centeredDirichlet ((100*m+2)*N) t*
    (centeredDirichlet N t/((2*N+1 : ℕ) : ℂ))^m

/-- The actual polynomial degree is controlled by twice the literal negative shift. -/
theorem wideDirichletProductPolynomial_natDegree_le (m N : ℕ) :
    (wideDirichletProductPolynomial m N).natDegree≤2*wideDirichletProductShift m N := by
  refine (Polynomial.natDegree_smul_le _ _).trans (Polynomial.natDegree_mul_le.trans ?_)
  have hPow := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
    (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
  exact (Nat.add_le_add (centeredDirichletPolynomial_natDegree_le ((100*m+2)*N)) hPow).trans_eq (by
    dsimp only [wideDirichletProductShift]
    ring)

/-- Exact one plateau on all the Hankel frequencies up to (99m+2)N, with no asymptotic premise. -/
theorem wideDirichletProductPolynomial_coeff_plateau (m N k : ℕ) (hk : k≤(99*m+2)*N) :
    (wideDirichletProductPolynomial m N).coeff (wideDirichletProductShift m N+k)=1 := by
  have hDeg : ((centeredDirichletPolynomial N)^m).natDegree≤wideDirichletProductShift m N+k := by
    have h := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
      (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
    dsimp only [wideDirichletProductShift]
    nlinarith
  have hUpper : wideDirichletProductShift m N+k≤2*((100*m+2)*N) := by
    dsimp only [wideDirichletProductShift]
    nlinarith
  rw [wideDirichletProductPolynomial,Polynomial.coeff_smul,
    centeredDirichletPolynomial_mul_coeff_flat _ _ _ hDeg hUpper,
    Polynomial.eval_pow,centeredDirichletPolynomial_eval_one,smul_eq_mul,← mul_pow]
  have hDen : (((2*N+1 : ℕ) : ℂ))≠0 := by exact_mod_cast (by omega : 2*N+1≠0)
  rw [inv_mul_cancel₀ hDen,one_pow]

/-- Exact full symbol identity; the shift includes the negative modes of every factor. -/
theorem wideDirichletProductKernel_eq_shiftedSymbol (m N : ℕ) (t : Boundary) :
    wideDirichletProductKernel m N t=
      shiftedPolynomialSymbol (wideDirichletProductPolynomial m N) (wideDirichletProductShift m N) t := by
  rw [shiftedPolynomialSymbol,wideDirichletProductPolynomial,Polynomial.eval_smul,
    Polynomial.eval_mul,Polynomial.eval_pow,centeredDirichletPolynomial_eval,
    centeredDirichletPolynomial_eval,smul_eq_mul,wideDirichletProductShift,pow_add,pow_mul]
  dsimp only [wideDirichletProductKernel,centeredDirichlet]
  rw [div_pow,mul_pow]
  ring

theorem continuous_wideDirichletProductKernel (m N : ℕ) : Continuous (wideDirichletProductKernel m N) :=
  (continuous_centeredDirichlet ((100*m+2)*N)).mul
    (((continuous_centeredDirichlet N).div_const _).pow m)

/-- Peak height is proportional to N, with a constant depending only on the finite smoothing order. -/
theorem norm_wideDirichletProductKernel_le (m N : ℕ) (hN : 0<N) (t : Boundary) :
    ‖wideDirichletProductKernel m N t‖≤(200*(m : ℝ)+5)*(N : ℝ) := by
  rw [wideDirichletProductKernel,norm_mul,norm_pow]
  calc
    _ ≤ (2*(((100*m+2)*N : ℕ) : ℝ)+1)*1^m :=
      mul_le_mul (norm_centeredDirichlet_le _ t)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_centeredDirichlet_normalized_le_one N t) m)
        (pow_nonneg (norm_nonneg _) m) (by positivity)
    _ ≤ _ := by
      simp only [one_pow,mul_one,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have hNR : (1 : ℝ)≤(N : ℝ) := by exact_mod_cast hN
      nlinarith

/-- Arbitrary finite decay order, without differentiating a cutoff or dropping negative frequencies. -/
theorem norm_wideDirichletProductKernel_real_tail (m N : ℕ) (hN : 0<N) (x : ℝ)
    (hx : 0 < |x|) (hx1 : |x|≤1/2) :
    ‖wideDirichletProductKernel m N (x : Boundary)‖≤(N : ℝ)/((N : ℝ)*|x|)^(m+1) := by
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  rw [wideDirichletProductKernel,norm_mul,norm_pow]
  calc
    _ ≤ (1/(2*|x|))*(1/((N : ℝ)*|x|))^m :=
      mul_le_mul (norm_centeredDirichlet_real_le ((100*m+2)*N) x hx hx1)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_centeredDirichlet_normalized_real_le N hN x hx hx1) m)
        (pow_nonneg (norm_nonneg _) m) (by positivity)
    _ ≤ (1/|x|)*(1/((N : ℝ)*|x|))^m :=
      mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hx (by linarith)) (by positivity)
    _ = _ := by
      rw [one_div_pow,pow_succ]
      field_simp

/-- Everywhere on the real unit window, the actual kernel has a scale-invariant decaying profile. -/
theorem norm_wideDirichletProductKernel_real_decay (m N : ℕ) (hN : 0<N) (x : ℝ) (hx : |x|≤1/2) :
    ‖wideDirichletProductKernel m N (x : Boundary)‖≤
      (200*(m : ℝ)+5)*(N : ℝ)*2^(m+1)/(1+(N : ℝ)*|x|)^(m+1) := by
  exact two_scale_integer_decay_bound _ _ _ _ _ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    (Nat.cast_pos.mpr hN) (by positivity) (norm_wideDirichletProductKernel_le m N hN _)
    (fun hy => norm_wideDirichletProductKernel_real_tail m N hN x
      (by nlinarith [abs_nonneg x,Nat.cast_nonneg (α := ℝ) N]) hx)

theorem norm_wideDirichletProductKernel_rpow_real_decay (m N : ℕ) (hN : 0<N)
    (p : ℝ) (hp : 0<p) (x : ℝ) (hx : |x|≤1/2) :
    ‖wideDirichletProductKernel m N (x : Boundary)‖^p≤
      ((200*(m : ℝ)+5)*2^(m+1))^p*(N : ℝ)^p*
        (1+(N : ℝ)*|x|)^(-(((m+1 : ℕ) : ℝ)*p)) := by
  have hBase : 0≤1+(N : ℝ)*|x| := by positivity
  calc
    _ ≤ ((200*(m : ℝ)+5)*(N : ℝ)*2^(m+1)/(1+(N : ℝ)*|x|)^(m+1))^p :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_wideDirichletProductKernel_real_decay m N hN x hx) hp.le
    _ = _ := by
      rw [show (200*(m : ℝ)+5)*(N : ℝ)*2^(m+1)=((200*(m : ℝ)+5)*2^(m+1))*(N : ℝ) by ring,
        Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (Nat.cast_nonneg N),
        ← Real.rpow_natCast_mul hBase,Real.rpow_neg hBase,div_eq_mul_inv]

/-- Explicit finite-order Lp localization constant, independent of the positive scale N. -/
def wideDirichletProductLpConstant (m : ℕ) (p : ℝ) : ℝ :=
  2*((200*(m : ℝ)+5)*2^(m+1))^p/((((m+1 : ℕ) : ℝ)*p)-1)

theorem wideDirichletProductLpConstant_pos (m : ℕ) (p : ℝ)
    (hOrder : 1<((m+1 : ℕ) : ℝ)*p) : 0<wideDirichletProductLpConstant m p := by
  unfold wideDirichletProductLpConstant
  positivity

/-- The genuine signed product kernel satisfies the sharp scale N^(p−1).
Finite smoothing order can depend on p; no analytic projection or Jensen step is used. -/
theorem integral_wideDirichletProductKernel_rpow_le (m N : ℕ) (hN : 0<N)
    (p : ℝ) (hp : 0<p) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    Integrable (fun t => ‖wideDirichletProductKernel m N t‖^p) circleMeasure ∧
      (∫ t,‖wideDirichletProductKernel m N t‖^p ∂circleMeasure)≤
        wideDirichletProductLpConstant m p*(N : ℝ)^(p-1) := by
  have hNR : (0 : ℝ)<(N : ℝ) := Nat.cast_pos.mpr hN
  let q : ℝ := ((m+1 : ℕ) : ℝ)*p
  let D : ℝ := ((200*(m : ℝ)+5)*2^(m+1))^p*(N : ℝ)^p
  have hD : 0≤D := by dsimp only [D]; positivity
  have hCont : Continuous (fun t => ‖wideDirichletProductKernel m N t‖^p) :=
    (continuous_wideDirichletProductKernel m N).norm.rpow_const (fun _ => Or.inr hp.le)
  have hRealCont : Continuous (fun x : ℝ => ‖wideDirichletProductKernel m N (x : Boundary)‖^p) :=
    hCont.comp QuotientAddGroup.continuous_mk
  have hProfile := integral_one_add_mul_abs_rpow_neg_le (N : ℝ) q (1/2) hNR hOrder (by norm_num)
  have hHaar : (∫ t,‖wideDirichletProductKernel m N t‖^p ∂circleMeasure)=
      ∫ x in (-(1/2 : ℝ))..(1/2),‖wideDirichletProductKernel m N (x : Boundary)‖^p := by
    have hμ : circleMeasure=(volume : Measure Boundary) := by
      simpa only [ENNReal.ofReal_one,one_smul] using
        (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
    rw [hμ]
    symm
    convert AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1/2 : ℝ))
      (fun t => ‖wideDirichletProductKernel m N t‖^p) using 1; norm_num
  refine ⟨hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  calc
    _ = ∫ x in (-(1/2 : ℝ))..(1/2),‖wideDirichletProductKernel m N (x : Boundary)‖^p := hHaar
    _ ≤ ∫ x in (-(1/2 : ℝ))..(1/2),D*(1+(N : ℝ)*|x|)^(-q) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hRealCont.intervalIntegrable _ _) (hProfile.1.const_mul D)
      intro x hx
      exact norm_wideDirichletProductKernel_rpow_real_decay m N hN p hp x (abs_le.mpr hx)
    _ = D*(∫ x in (-(1/2 : ℝ))..(1/2),(1+(N : ℝ)*|x|)^(-q)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ D*(2/((N : ℝ)*(q-1))) := mul_le_mul_of_nonneg_left hProfile.2 hD
    _ = _ := by
      dsimp only [D,q,wideDirichletProductLpConstant]
      rw [Real.rpow_sub hNR,Real.rpow_one]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- Every positive p admits a concrete finite smoothing order and a uniform scale bound. -/
theorem exists_wideDirichletProduct_low_p_bound (p : ℝ) (hp : 0<p) :
    ∃ m : ℕ, ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N→
      (∫ t,‖wideDirichletProductKernel m N t‖^p ∂circleMeasure)≤C*(N : ℝ)^(p-1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/p)
  have hOrder : 1<((m+1 : ℕ) : ℝ)*p := by
    have h := (div_lt_iff₀ hp).mp hm
    push_cast
    nlinarith
  exact ⟨m,wideDirichletProductLpConstant m p,wideDirichletProductLpConstant_pos m p hOrder,
    fun N hN => (integral_wideDirichletProductKernel_rpow_le m N hN p hp hOrder).2⟩

/-- The flat plateau also includes the negative frequencies; this is not the analytic part of a kernel. -/
theorem wideDirichletProductPolynomial_coeff_negative_plateau (m N k : ℕ) (hk : k≤(99*m+2)*N) :
    (wideDirichletProductPolynomial m N).coeff (wideDirichletProductShift m N-k)=1 := by
  have hkS : k≤wideDirichletProductShift m N := by
    dsimp only [wideDirichletProductShift]
    nlinarith
  have hSub := Nat.sub_add_cancel hkS
  have hDeg : ((centeredDirichletPolynomial N)^m).natDegree≤wideDirichletProductShift m N-k := by
    have h := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
      (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
    dsimp only [wideDirichletProductShift] at hSub ⊢
    nlinarith
  have hUpper : wideDirichletProductShift m N-k≤2*((100*m+2)*N) := by
    dsimp only [wideDirichletProductShift] at hSub ⊢
    nlinarith
  rw [wideDirichletProductPolynomial,Polynomial.coeff_smul,
    centeredDirichletPolynomial_mul_coeff_flat _ _ _ hDeg hUpper,
    Polynomial.eval_pow,centeredDirichletPolynomial_eval_one,smul_eq_mul,← mul_pow]
  have hDen : (((2*N+1 : ℕ) : ℂ))≠0 := by exact_mod_cast (by omega : 2*N+1≠0)
  rw [inv_mul_cancel₀ hDen,one_pow]

/-- The actual centered mask vanishes beyond its finite localization window. -/
theorem wideDirichletProductPolynomial_coeff_zero (m N k : ℕ) (hk : wideDirichletProductShift m N<k) :
    (wideDirichletProductPolynomial m N).coeff (wideDirichletProductShift m N+k)=0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((wideDirichletProductPolynomial_natDegree_le m N).trans_lt (by omega))

/-- The negative shift is the outer support radius, exactly. -/
theorem wideDirichletProductShift_eq (m N : ℕ) :
    wideDirichletProductShift m N = (101*m+2)*N := by
  dsimp only [wideDirichletProductShift]
  ring

/-- Literal Laurent coefficients of the full signed polynomial modulation.
Negative polynomial indices are zero, rather than truncated to index zero. -/
def wideDirichletSignedWeight (m N : ℕ) (k : ℤ) : ℂ :=
  if 0 ≤ (wideDirichletProductShift m N : ℤ)+k then
    (wideDirichletProductPolynomial m N).coeff ((wideDirichletProductShift m N : ℤ)+k).toNat
  else 0

/-- The flat polynomial range before shifting is exact. -/
theorem wideDirichletProductPolynomial_coeff_flat (m N n : ℕ)
    (hlo : 2*m*N ≤ n) (hhi : n ≤ 2*((100*m+2)*N)) :
    (wideDirichletProductPolynomial m N).coeff n = 1 := by
  have hDeg : ((centeredDirichletPolynomial N)^m).natDegree ≤ n := by
    have h := (Polynomial.natDegree_pow_le (p := centeredDirichletPolynomial N) (n := m)).trans
      (Nat.mul_le_mul_left m (centeredDirichletPolynomial_natDegree_le N))
    nlinarith
  rw [wideDirichletProductPolynomial,Polynomial.coeff_smul,
    centeredDirichletPolynomial_mul_coeff_flat _ _ _ hDeg hhi,
    Polynomial.eval_pow,centeredDirichletPolynomial_eval_one,smul_eq_mul,← mul_pow]
  have hDen : (((2*N+1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (by omega : 2*N+1 ≠ 0)
  rw [inv_mul_cancel₀ hDen,one_pow]

/-- Both signs of the plateau, expressed as actual Laurent coefficients. -/
theorem wideDirichletSignedWeight_plateau (m N : ℕ) (k : ℤ)
    (hk : |k| ≤ (((99*m+2)*N : ℕ) : ℤ)) : wideDirichletSignedWeight m N k = 1 := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hk
  have hShift : ((99*m+2)*N : ℕ) ≤ wideDirichletProductShift m N := by
    rw [wideDirichletProductShift_eq]
    nlinarith
  have hn : 0 ≤ (wideDirichletProductShift m N : ℤ)+k := by omega
  rw [wideDirichletSignedWeight,ite_eq_left hn]
  have he := Int.natCast_toNat_eq_self.mpr hn
  apply wideDirichletProductPolynomial_coeff_flat
  · have hEq : (wideDirichletProductShift m N : ℤ)-(((99*m+2)*N : ℕ) : ℤ) =
        ((2*m*N : ℕ) : ℤ) := by rw [wideDirichletProductShift_eq]; push_cast; ring
    exact_mod_cast (show ((2*m*N : ℕ) : ℤ) ≤
      (((wideDirichletProductShift m N : ℤ)+k).toNat : ℤ) by omega)
  · have hEq : (wideDirichletProductShift m N : ℤ)+(((99*m+2)*N : ℕ) : ℤ) =
        ((2*((100*m+2)*N) : ℕ) : ℤ) := by rw [wideDirichletProductShift_eq]; push_cast; ring
    exact_mod_cast (show (((wideDirichletProductShift m N : ℤ)+k).toNat : ℤ) ≤
      ((2*((100*m+2)*N) : ℕ) : ℤ) by omega)

/-- The full signed mask vanishes past the exact outer support radius. -/
theorem wideDirichletSignedWeight_zero (m N : ℕ) (k : ℤ)
    (hk : (((101*m+2)*N : ℕ) : ℤ) < |k|) : wideDirichletSignedWeight m N k = 0 := by
  rw [← wideDirichletProductShift_eq] at hk
  unfold wideDirichletSignedWeight
  split_ifs with hn
  · have he := Int.natCast_toNat_eq_self.mpr hn
    have hpos : 0 ≤ k := by
      by_contra hneg
      rw [abs_of_nonpos (by omega : k ≤ 0)] at hk
      omega
    rw [abs_of_nonneg hpos] at hk
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    apply (wideDirichletProductPolynomial_natDegree_le m N).trans_lt
    exact_mod_cast (show ((2*wideDirichletProductShift m N : ℕ) : ℤ) <
      (((wideDirichletProductShift m N : ℤ)+k).toNat : ℤ) by push_cast; omega)
  · rfl

end TTO.Paper.Proved
