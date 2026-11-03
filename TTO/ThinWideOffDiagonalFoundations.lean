/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ThinWideBandFoundations
public import TTO.PolynomialSchurFoundations
public import TTO.CappedSchattenFoundations

/-! Actual distant ordered corners and literal nearby-band localization. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

def scheduledWideSize (m n : ℕ) : ℕ :=
  3*thinWideBandHalfwidth m (thinWideScale n) (thinWideScale (n+1))

def scheduledWideRow (m n : ℕ) : ℕ :=
  thinWideBandRowStart m (thinWideScale n) (thinWideScale (n+1))

def scheduledWideColumn (m n : ℕ) : ℕ :=
  thinWideBandColumnStart m (thinWideScale n) (thinWideScale (n+1))

/-- An actual ordered corner of the original polynomial Hankel matrix. -/
def scheduledWideCorner (m n k : ℕ) (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (scheduledWideSize m k)) →L[ℂ]
      EuclideanSpace ℂ (Fin (scheduledWideSize m n)) :=
  polynomialHankelRectangleOffset (scheduledWideSize m n) (scheduledWideSize m k)
    (scheduledWideRow m n+scheduledWideColumn m k) P

theorem scheduledWideCorner_single_apply (m n k : ℕ) (P : Polynomial ℂ)
    (i : Fin (scheduledWideSize m n)) (j : Fin (scheduledWideSize m k)) :
    scheduledWideCorner m n k P (EuclideanSpace.single j (1 : ℂ)) i =
      P.coeff ((scheduledWideRow m n+i.val)+(scheduledWideColumn m k+j.val)) := by
  rw [scheduledWideCorner,polynomialHankelRectangleOffset_single_apply]
  congr 1
  omega

theorem scheduledWide_coordinate_windows (m n : ℕ) (hm : 1 ≤ m) :
    (∀ i : Fin (scheduledWideSize m n),20*m*thinWideScale n ≤ scheduledWideRow m n+i.val ∧
      scheduledWideRow m n+i.val < 150*m*thinWideScale n) ∧
    (∀ i : Fin (scheduledWideSize m n),20*m*thinWideScale n ≤ scheduledWideColumn m n+i.val ∧
      scheduledWideColumn m n+i.val < 150*m*thinWideScale n) :=
  thinWideBand_coordinate_windows m _ _ hm (thinWideScale_ten_le n)
    (thinWideScale_monotone (Nat.le_succ n)) (thinWideScale_ratio n)

theorem scheduledWide_size_le (m n : ℕ) (hm : 1 ≤ m) :
    scheduledWideSize m n ≤ 60*m*thinWideScale n := by
  have h := (thinWideBand_placement_bounds m _ _ hm (thinWideScale_ten_le n)
    (thinWideScale_monotone (Nat.le_succ n)) (thinWideScale_ratio n)).1
  dsimp only [scheduledWideSize]
  nlinarith

theorem scheduledWide_starts_le (m n : ℕ) (hm : 1 ≤ m) :
    scheduledWideRow m n ≤ 102*m*thinWideScale n ∧
    scheduledWideColumn m n ≤ 102*m*thinWideScale n := by
  have h := (thinWideBand_placement_bounds m _ _ hm (thinWideScale_ten_le n)
    (thinWideScale_monotone (Nat.le_succ n)) (thinWideScale_ratio n)).2.2
  dsimp only [scheduledWideRow,scheduledWideColumn,thinWideBandRowStart,thinWideBandColumnStart]
  constructor <;> omega

/-- The genuine polynomial localized by a fixed two-hundred-band neighborhood. -/
def wideNeighborPolynomial (m n : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  wideLowpassPolynomial m (thinWideScale (n+100)) P-
    wideLowpassPolynomial m (thinWideScale (n-100)) P

/-- The neighbor polynomial is exactly the finite sum of the original thin bands. -/
theorem wideNeighborPolynomial_eq_sum (m n : ℕ) (P : Polynomial ℂ) :
    wideNeighborPolynomial m n P =
      ∑ j ∈ Finset.Ico (n-100) (n+100),
        thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P := by
  rw [Finset.sum_Ico_eq_sub _ (by omega : n-100 ≤ n+100)]
  have hLo := wideLowpassPolynomial_telescope m thinWideScale P (n-100)
  have hHi := wideLowpassPolynomial_telescope m thinWideScale P (n+100)
  dsimp only [wideNeighborPolynomial]
  linear_combination hLo-hHi

/-- The actual neighbor polynomial has the literal finite outer frequency support. -/
theorem wideNeighborPolynomial_coeff_high (m n : ℕ) (P : Polynomial ℂ) (j : ℕ)
    (hj : (101*m+2)*thinWideScale (n+100) < j) :
    (wideNeighborPolynomial m n P).coeff j = 0 := by
  exact thinWideBandPolynomial_coeff_high m _ _ (thinWideScale_monotone (by omega)) P j hj

theorem wideNeighborPolynomial_natDegree_le (m n : ℕ) (P : Polynomial ℂ) :
    (wideNeighborPolynomial m n P).natDegree ≤ (101*m+2)*thinWideScale (n+100) :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => wideNeighborPolynomial_coeff_high m n P j hj)

/-- Localization is exactly one on every frequency used by a distant corner. -/
theorem wideNeighborPolynomial_coeff_eq (m n : ℕ) (hm : 1 ≤ m) (hn : 100 ≤ n)
    (P : Polynomial ℂ) (j : ℕ)
    (hlo : 20*m*thinWideScale n ≤ j) (hhi : j < 170*m*thinWideScale n) :
    (wideNeighborPolynomial m n P).coeff j = P.coeff j := by
  have hBig := thinWideScale_sparse_gap n 100 le_rfl
  have hSmall := thinWideScale_sparse_gap (n-100) 100 le_rfl
  rw [Nat.sub_add_cancel hn] at hSmall
  have hBigM := Nat.mul_le_mul_left m hBig
  have hSmallM := Nat.mul_le_mul_left m hSmall
  have hSmallPos := thinWideScale_ten_le (n-100)
  have hLargePos := thinWideScale_ten_le n
  have hPlateau : j ≤ (99*m+2)*thinWideScale (n+100) := by nlinarith
  have hOutside : wideDirichletProductShift m (thinWideScale (n-100)) < j := by
    rw [wideDirichletProductShift_eq]
    nlinarith
  change (thinWideBandPolynomial m (thinWideScale (n-100)) (thinWideScale (n+100)) P).coeff j = _
  rw [thinWideBandPolynomial_coeff]
  simp only [wideDirichletPositiveWeight,
    wideDirichletProductPolynomial_coeff_plateau m _ j hPlateau,
    wideDirichletProductPolynomial_coeff_zero m _ j hOutside,sub_zero,one_mul]

/-- The genuine coefficient interval of EITHER ordered distant corner. -/
theorem scheduledWide_far_indices (m n k : ℕ) (hm : 1 ≤ m) (hnk : k+100 ≤ n) :
    (∀ i : Fin (scheduledWideSize m n),∀ j : Fin (scheduledWideSize m k),
      20*m*thinWideScale n ≤ (scheduledWideRow m n+i.val)+(scheduledWideColumn m k+j.val) ∧
      (scheduledWideRow m n+i.val)+(scheduledWideColumn m k+j.val) < 170*m*thinWideScale n) ∧
    (∀ i : Fin (scheduledWideSize m k),∀ j : Fin (scheduledWideSize m n),
      20*m*thinWideScale n ≤ (scheduledWideRow m k+i.val)+(scheduledWideColumn m n+j.val) ∧
      (scheduledWideRow m k+i.val)+(scheduledWideColumn m n+j.val) < 170*m*thinWideScale n) := by
  have hGap := thinWideScale_sparse_gap k (n-k) (by omega)
  rw [Nat.add_sub_of_le (by omega : k ≤ n)] at hGap
  have hGapM := Nat.mul_le_mul_left m hGap
  obtain ⟨hRn,hCn⟩ := scheduledWide_coordinate_windows m n hm
  obtain ⟨hRk,hCk⟩ := scheduledWide_coordinate_windows m k hm
  constructor
  · intro i j
    have hi := hRn i
    have hj := hCk j
    constructor <;> nlinarith
  · intro i j
    have hi := hRk i
    have hj := hCn j
    constructor <;> nlinarith

/-- Actual equality of both ordered distant corners, prior to any norm estimate. -/
theorem scheduledWide_far_corner_neighbor (m n k : ℕ) (hm : 1 ≤ m) (hnk : k+100 ≤ n)
    (P : Polynomial ℂ) :
    scheduledWideCorner m n k P = scheduledWideCorner m n k (wideNeighborPolynomial m n P) ∧
    scheduledWideCorner m k n P = scheduledWideCorner m k n (wideNeighborPolynomial m n P) := by
  obtain ⟨hForward,hReverse⟩ := scheduledWide_far_indices m n k hm hnk
  constructor
  · apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (scheduledWideSize m k)) ℂ).toBasis.ext
    intro j
    rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    ext i
    change scheduledWideCorner m n k P (EuclideanSpace.single j (1 : ℂ)) i =
      scheduledWideCorner m n k (wideNeighborPolynomial m n P) (EuclideanSpace.single j (1 : ℂ)) i
    rw [scheduledWideCorner_single_apply,scheduledWideCorner_single_apply,
      wideNeighborPolynomial_coeff_eq m n hm (by omega) P _ (hForward i j).1 (hForward i j).2]
  · apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (scheduledWideSize m n)) ℂ).toBasis.ext
    intro j
    rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    ext i
    change scheduledWideCorner m k n P (EuclideanSpace.single j (1 : ℂ)) i =
      scheduledWideCorner m k n (wideNeighborPolynomial m n P) (EuclideanSpace.single j (1 : ℂ)) i
    rw [scheduledWideCorner_single_apply,scheduledWideCorner_single_apply,
      wideNeighborPolynomial_coeff_eq m n hm (by omega) P _ (hReverse i j).1 (hReverse i j).2]

/-- A literal cyclic sample length strictly beyond the neighbor polynomial degree. -/
def wideNeighborSample (m n : ℕ) : ℕ := 2*(101*m+2)*thinWideScale (n+100)

theorem wideNeighborSample_pos (m n : ℕ) : 0 < wideNeighborSample m n := by
  have h := thinWideScale_ten_le (n+100)
  dsimp only [wideNeighborSample]
  positivity

theorem wideNeighborPolynomial_natDegree_lt_sample (m n : ℕ) (P : Polynomial ℂ) :
    (wideNeighborPolynomial m n P).natDegree < wideNeighborSample m n := by
  apply (wideNeighborPolynomial_natDegree_le m n P).trans_lt
  have h := thinWideScale_ten_le (n+100)
  dsimp only [wideNeighborSample]
  nlinarith

/-- Both distant ordered shapes fit the SAME literal neighbor sample length. -/
theorem scheduledWide_far_sample_shape (m n k : ℕ) (hm : 1 ≤ m) (hnk : k+100 ≤ n) :
    scheduledWideRow m n+scheduledWideColumn m k+scheduledWideSize m n+scheduledWideSize m k ≤
      wideNeighborSample m n ∧
    scheduledWideRow m k+scheduledWideColumn m n+scheduledWideSize m k+scheduledWideSize m n ≤
      wideNeighborSample m n := by
  obtain ⟨hRn,hCn⟩ := scheduledWide_starts_le m n hm
  obtain ⟨hRk,hCk⟩ := scheduledWide_starts_le m k hm
  have hSn := scheduledWide_size_le m n hm
  have hSk := scheduledWide_size_le m k hm
  have hMono := thinWideScale_monotone (by omega : k ≤ n)
  have hBig := thinWideScale_sparse_gap n 100 le_rfl
  have hMonoM := Nat.mul_le_mul_left m hMono
  have hBigM := Nat.mul_le_mul_left m hBig
  dsimp only [wideNeighborSample]
  constructor <;> nlinarith

/-- Actual rectangular estimate for BOTH ordered distant corners, retaining the honest neighbor Lp mass. -/
theorem scheduledWide_far_rectangular_upper (m n k : ℕ) (hm : 1 ≤ m) (hnk : k+100 ≤ n)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    schattenNorm p (scheduledWideCorner m n k P)^p ≤
      (wideNeighborSample m n : ℝ)^(1-p)*
        (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure)*
        (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p ∧
    schattenNorm p (scheduledWideCorner m k n P)^p ≤
      (wideNeighborSample m n : ℝ)^(1-p)*
        (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure)*
        (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p := by
  let : NeZero (wideNeighborSample m n) := ⟨Nat.ne_of_gt (wideNeighborSample_pos m n)⟩
  obtain ⟨hForward,hReverse⟩ := scheduledWide_far_corner_neighbor m n k hm hnk P
  obtain ⟨hSize,hSize'⟩ := scheduledWide_far_sample_shape m n k hm hnk
  constructor
  · rw [hForward]
    exact polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral _ _ _ _ hSize
      (wideNeighborPolynomial m n P) (wideNeighborPolynomial_natDegree_lt_sample m n P) p hp hp1
  · rw [hReverse]
    simpa only [scheduledWideCorner,mul_comm (Real.sqrt (scheduledWideSize m k : ℝ))] using!
      polynomialHankelRectangleOffset_schattenNorm_rpow_le_integral _ _ _ _ hSize'
        (wideNeighborPolynomial m n P) (wideNeighborPolynomial_natDegree_lt_sample m n P) p hp hp1

/-- Actual finite scalar power subadditivity, with no concavity assumption used beyond its valid range. -/
theorem complex_norm_finset_sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : ‖∑ i ∈ s,f i‖^p ≤ ∑ i ∈ s,‖f i‖^p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,norm_zero,Real.zero_rpow hp.ne',le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    calc
      _ ≤ (‖f i‖+‖∑ j ∈ s,f j‖)^p := Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le
      _ ≤ ‖f i‖^p+‖∑ j ∈ s,f j‖^p := Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hp.le hp1
      _ ≤ _ := add_le_add_right ih _

/-- The actual neighbor Lp mass is bounded by the finite sum of actual nearby band masses. -/
theorem wideNeighborPolynomial_lp_le_sum (m n : ℕ) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
      ∑ j ∈ Finset.Ico (n-100) (n+100),
        ∫ τ : Boundary,‖(thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
          (fourier (T := 1) 1 τ)‖^p ∂circleMeasure := by
  have hCont (Q : Polynomial ℂ) : Continuous (fun τ : Boundary => ‖Q.eval (fourier (T := 1) 1 τ)‖^p) := by
    apply (Real.continuous_rpow_const hp.le).comp
    fun_prop
  have hInt (Q : Polynomial ℂ) : Integrable (fun τ : Boundary => ‖Q.eval (fourier (T := 1) 1 τ)‖^p) circleMeasure :=
    (hCont Q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum _ (fun j _hj => hInt (thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P))]
  apply integral_mono (hInt _) (integrable_finsetSum _ (fun j _hj => hInt (thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P)))
  intro τ
  dsimp only
  rw [wideNeighborPolynomial_eq_sum,Polynomial.eval_finsetSum]
  exact complex_norm_finset_sum_rpow_le _ _ p hp hp1

/-- The uniform scale loss of the fixed one-hundred-step neighborhood. -/
def wideNeighborScaleConstant : ℝ := (11/10 : ℝ)*(11/10 : ℝ)^100

def wideNeighborSampleConstant (m : ℕ) : ℝ := 2*(101*(m : ℝ)+2)*wideNeighborScaleConstant

def wideOffDiagonalFactorConstant (m : ℕ) (p : ℝ) : ℝ :=
  (wideNeighborSampleConstant m)^(1-p)*(60*(m : ℝ))^p*(11/10 : ℝ)^(p/2)

theorem wideNeighborScaleConstant_pos : 0 < wideNeighborScaleConstant := by
  dsimp only [wideNeighborScaleConstant]
  positivity

theorem wideNeighborSampleConstant_pos (m : ℕ) : 0 < wideNeighborSampleConstant m := by
  dsimp only [wideNeighborSampleConstant]
  exact mul_pos (by positivity) wideNeighborScaleConstant_pos

/-- Exact geometric control of the literal sample length, with no scale-dependent constant. -/
theorem wideNeighborSample_real_le (m n : ℕ) :
    (wideNeighborSample m n : ℝ) ≤ wideNeighborSampleConstant m*(thinWideScale n : ℝ) := by
  have h := (thinWideScale_geometric_comparison n 100).2
  have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2*(101*(m : ℝ)+2))
  dsimp only [wideNeighborSample,wideNeighborSampleConstant,wideNeighborScaleConstant]
  push_cast
  nlinarith

/-- The complete rectangular factor has the genuine geometric off-diagonal decay. -/
theorem scheduledWide_rectangular_factor_decay (m n k : ℕ) (hm : 1 ≤ m) (hkn : k ≤ n)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (wideNeighborSample m n : ℝ)^(1-p)*
      (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p ≤
    wideOffDiagonalFactorConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*(thinWideScale n : ℝ) := by
  have ha : (0 : ℝ) < (thinWideScale n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<10) (thinWideScale_ten_le n))
  have hb : (0 : ℝ) < (thinWideScale k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<10) (thinWideScale_ten_le k))
  have hE : (0 : ℝ) < 60*(m : ℝ) := by exact_mod_cast (by nlinarith : 0<60*m)
  have hNr : (scheduledWideSize m n : ℝ) ≤ 60*(m : ℝ)*(thinWideScale n : ℝ) := by exact_mod_cast scheduledWide_size_le m n hm
  have hKr : (scheduledWideSize m k : ℝ) ≤ 60*(m : ℝ)*(thinWideScale k : ℝ) := by exact_mod_cast scheduledWide_size_le m k hm
  have hNpow := Real.rpow_le_rpow (Nat.cast_nonneg (scheduledWideSize m n)) hNr (by linarith : 0 ≤ p/2)
  have hKpow := Real.rpow_le_rpow (Nat.cast_nonneg (scheduledWideSize m k)) hKr (by linarith : 0 ≤ p/2)
  rw [Real.mul_rpow hE.le ha.le] at hNpow
  rw [Real.mul_rpow hE.le hb.le] at hKpow
  have hRoot : (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p =
      (scheduledWideSize m n : ℝ)^(p/2)*(scheduledWideSize m k : ℝ)^(p/2) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
      ← Real.rpow_mul (Nat.cast_nonneg _),← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [show (1/2 : ℝ)*p = p/2 by ring]
  have hRootLe : (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p ≤
      (60*(m : ℝ))^p*(thinWideScale n : ℝ)^(p/2)*(thinWideScale k : ℝ)^(p/2) := by
    rw [hRoot]
    apply (mul_le_mul hNpow hKpow (Real.rpow_nonneg (by positivity) _) (by positivity)).trans_eq
    have hEpow : (60*(m : ℝ))^(p/2)*(60*(m : ℝ))^(p/2) = (60*(m : ℝ))^p := by
      rw [← Real.rpow_add hE]
      congr 1
      ring
    calc
      _ = ((60*(m : ℝ))^(p/2)*(60*(m : ℝ))^(p/2))*
          (thinWideScale n : ℝ)^(p/2)*(thinWideScale k : ℝ)^(p/2) := by ring
      _ = _ := by rw [hEpow]
  have hComp := (thinWideScale_geometric_comparison k (n-k)).1
  rw [Nat.add_sub_of_le hkn] at hComp
  have hd : (0 : ℝ) < (11/10 : ℝ)^(n-k) := by positivity
  have hKratio : (thinWideScale k : ℝ) ≤ ((11/10 : ℝ)*(thinWideScale n : ℝ))/(11/10 : ℝ)^(n-k) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hKratioPow := Real.rpow_le_rpow hb.le hKratio (by linarith : 0 ≤ p/2)
  have hDecay : (((11/10 : ℝ)^(n-k))^(p/2))⁻¹ = (11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2) := by
    rw [← Real.rpow_neg hd.le,← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 11/10)]
    congr 1
    ring
  rw [Real.div_rpow (by positivity) hd.le,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 11/10) ha.le] at hKratioPow
  change (thinWideScale k : ℝ)^(p/2) ≤
    ((11/10 : ℝ)^(p/2)*(thinWideScale n : ℝ)^(p/2))*(((11/10 : ℝ)^(n-k))^(p/2))⁻¹ at hKratioPow
  rw [hDecay] at hKratioPow
  have hSamplePos := wideNeighborSampleConstant_pos m
  have hQpow := Real.rpow_le_rpow (Nat.cast_nonneg (wideNeighborSample m n))
    (wideNeighborSample_real_le m n) (by linarith : 0 ≤ 1-p)
  rw [Real.mul_rpow (wideNeighborSampleConstant_pos m).le ha.le] at hQpow
  have hA : (thinWideScale n : ℝ)^(1-p)*(thinWideScale n : ℝ)^(p/2)*
      (thinWideScale n : ℝ)^(p/2) = (thinWideScale n : ℝ) := by
    rw [← Real.rpow_add ha,← Real.rpow_add ha,show 1-p+p/2+p/2=1 by ring,Real.rpow_one]
  calc
    _ ≤ ((wideNeighborSampleConstant m)^(1-p)*(thinWideScale n : ℝ)^(1-p))*
        ((60*(m : ℝ))^p*(thinWideScale n : ℝ)^(p/2)*(thinWideScale k : ℝ)^(p/2)) :=
      mul_le_mul hQpow hRootLe (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ ≤ ((wideNeighborSampleConstant m)^(1-p)*(thinWideScale n : ℝ)^(1-p))*
        ((60*(m : ℝ))^p*(thinWideScale n : ℝ)^(p/2)*
          ((11/10 : ℝ)^(p/2)*(thinWideScale n : ℝ)^(p/2)*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKratioPow (by positivity)) (by positivity)
    _ = _ := by
      dsimp only [wideOffDiagonalFactorConstant]
      calc
        _ = ((wideNeighborSampleConstant m)^(1-p)*(60*(m : ℝ))^p*(11/10 : ℝ)^(p/2))*
            (11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
            ((thinWideScale n : ℝ)^(1-p)*(thinWideScale n : ℝ)^(p/2)*(thinWideScale n : ℝ)^(p/2)) := by ring
        _ = _ := by rw [hA]

theorem wideOffDiagonalFactorConstant_pos (m : ℕ) (hm : 1 ≤ m) (p : ℝ) :
    0 < wideOffDiagonalFactorConstant m p := by
  have hSample := wideNeighborSampleConstant_pos m
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0<m)
  dsimp only [wideOffDiagonalFactorConstant]
  positivity

/-- Literal scale-weighted circle mass of one actual thin band. -/
def scheduledWideBandMass (m j : ℕ) (P : Polynomial ℂ) (p : ℝ) : ℝ :=
  (thinWideScale j : ℝ)*(∫ τ : Boundary,
    ‖(thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
      (fourier (T := 1) 1 τ)‖^p ∂circleMeasure)

/-- Every nearby scale is comparable to the large corner scale, uniformly. -/
theorem wideNeighbor_scale_comparison (n j : ℕ) (hn : 100 ≤ n)
    (hj : j ∈ Finset.Ico (n-100) (n+100)) :
    (thinWideScale n : ℝ) ≤ wideNeighborScaleConstant*(thinWideScale j : ℝ) := by
  have h := (thinWideScale_geometric_comparison (n-100) 100).2
  rw [Nat.sub_add_cancel hn] at h
  have hMono : (thinWideScale (n-100) : ℝ) ≤ (thinWideScale j : ℝ) := by
    exact_mod_cast thinWideScale_monotone (Finset.mem_Ico.mp hj).1
  change (thinWideScale n : ℝ) ≤ wideNeighborScaleConstant*(thinWideScale (n-100) : ℝ) at h
  exact h.trans (mul_le_mul_of_nonneg_left hMono wideNeighborScaleConstant_pos.le)

/-- The honest neighbor mass is paid by a fixed finite window of actual scale-weighted band masses. -/
theorem wideNeighborPolynomial_weighted_mass_le (m n : ℕ) (hn : 100 ≤ n) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (thinWideScale n : ℝ)*
      (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
    wideNeighborScaleConstant*(∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) := by
  have hLp := wideNeighborPolynomial_lp_le_sum m n P p hp hp1
  calc
    _ ≤ (thinWideScale n : ℝ)*(∑ j ∈ Finset.Ico (n-100) (n+100),
        ∫ τ : Boundary,‖(thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
          (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) :=
      mul_le_mul_of_nonneg_left hLp (Nat.cast_nonneg _)
    _ = ∑ j ∈ Finset.Ico (n-100) (n+100),(thinWideScale n : ℝ)*
        (∫ τ : Boundary,‖(thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
          (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Ico (n-100) (n+100),wideNeighborScaleConstant*scheduledWideBandMass m j P p := by
      apply Finset.sum_le_sum
      intro j hj
      have h := mul_le_mul_of_nonneg_right (wideNeighbor_scale_comparison n j hn hj)
        (integral_nonneg (μ := circleMeasure) fun τ => Real.rpow_nonneg (norm_nonneg
          ((thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
            (fourier (T := 1) 1 τ))) p)
      simpa only [scheduledWideBandMass,mul_assoc] using h
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The full off-diagonal corner constant is chosen only from m and p. -/
def wideOffDiagonalConstant (m : ℕ) (p : ℝ) : ℝ :=
  wideOffDiagonalFactorConstant m p*wideNeighborScaleConstant

theorem wideOffDiagonalConstant_pos (m : ℕ) (hm : 1 ≤ m) (p : ℝ) :
    0 < wideOffDiagonalConstant m p :=
  mul_pos (wideOffDiagonalFactorConstant_pos m hm p) wideNeighborScaleConstant_pos

/-- Actual exponentially decaying error estimate for BOTH ordered off-diagonal corners.
No assumption on the polynomial, global Hankel operator, or band budget is made. -/
theorem scheduledWide_far_schattenNorm_budget (m n k : ℕ) (hm : 1 ≤ m) (hnk : k+100 ≤ n)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    schattenNorm p (scheduledWideCorner m n k P)^p ≤
      wideOffDiagonalConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
        (∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) ∧
    schattenNorm p (scheduledWideCorner m k n P)^p ≤
      wideOffDiagonalConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
        (∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) := by
  have hRect := scheduledWide_far_rectangular_upper m n k hm hnk P p hp hp1
  have hFactor := scheduledWide_rectangular_factor_decay m n k hm (by omega) p hp hp1
  have hMass := wideNeighborPolynomial_weighted_mass_le m n (by omega) P p hp hp1
  have hFactorPos := wideOffDiagonalFactorConstant_pos m hm p
  have hCommon : (wideNeighborSample m n : ℝ)^(1-p)*
      (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure)*
      (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p ≤
      wideOffDiagonalConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
        (∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) := by
    calc
      _ = ((wideNeighborSample m n : ℝ)^(1-p)*
          (Real.sqrt (scheduledWideSize m n : ℝ)*Real.sqrt (scheduledWideSize m k : ℝ))^p)*
          (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) := by ring
      _ ≤ (wideOffDiagonalFactorConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*(thinWideScale n : ℝ))*
          (∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) :=
        mul_le_mul_of_nonneg_right hFactor (integral_nonneg fun τ => Real.rpow_nonneg (norm_nonneg _) p)
      _ = (wideOffDiagonalFactorConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2))*
          ((thinWideScale n : ℝ)*(∫ τ : Boundary,‖(wideNeighborPolynomial m n P).eval
            (fourier (T := 1) 1 τ)‖^p ∂circleMeasure)) := by ring
      _ ≤ (wideOffDiagonalFactorConstant m p*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2))*
          (wideNeighborScaleConstant*(∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p)) :=
        mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = _ := by dsimp only [wideOffDiagonalConstant]; ring
  exact ⟨hRect.1.trans hCommon,hRect.2.trans hCommon⟩

/-- The off-diagonal constant precedes EVERY scale pair, polynomial, and orientation. -/
theorem exists_scheduledWide_far_schattenNorm_budget (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ n k : ℕ,k+100 ≤ n → ∀ P : Polynomial ℂ,
      schattenNorm p (scheduledWideCorner m n k P)^p ≤ C*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
        (∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) ∧
      schattenNorm p (scheduledWideCorner m k n P)^p ≤ C*(11/10 : ℝ)^(-((n-k : ℕ) : ℝ)*p/2)*
        (∑ j ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m j P p) :=
  ⟨wideOffDiagonalConstant m p,wideOffDiagonalConstant_pos m hm p,
    fun n k hnk P => scheduledWide_far_schattenNorm_budget m n k hm hnk P p hp hp1⟩

end TTO.Paper.Proved
