/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WideDirichletFoundations
public import TTO.OffsetShortBandHankelLowerFoundations

/-! Actual thin wide-plateau polynomial bands and a concrete geometric scale schedule.
The short-band lower bound uses only the proved two-compression reconstruction. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Nonnegative Laurent coefficients of the full signed wide low-pass kernel. -/
def wideDirichletPositiveWeight (m N k : ℕ) : ℂ :=
  (wideDirichletProductPolynomial m N).coeff (wideDirichletProductShift m N+k)

/-- The actual finite coefficientwise polynomial multiplier. -/
def wideLowpassPolynomial (m N : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ P.support, Polynomial.monomial k (wideDirichletPositiveWeight m N k*P.coeff k)

theorem wideLowpassPolynomial_coeff (m N : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    (wideLowpassPolynomial m N P).coeff k = wideDirichletPositiveWeight m N k*P.coeff k := by
  classical
  simp only [wideLowpassPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  by_cases hk : P.coeff k = 0
  · simp [Polynomial.mem_support_iff,hk]
  · simp [Polynomial.mem_support_iff,hk]

/-- A genuine difference of two finite low-pass multipliers. -/
def thinWideBandPolynomial (m N N' : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  wideLowpassPolynomial m N' P-wideLowpassPolynomial m N P

theorem thinWideBandPolynomial_coeff (m N N' : ℕ) (P : Polynomial ℂ) (k : ℕ) :
    (thinWideBandPolynomial m N N' P).coeff k =
      (wideDirichletPositiveWeight m N' k-wideDirichletPositiveWeight m N k)*P.coeff k := by
  rw [thinWideBandPolynomial,Polynomial.coeff_sub,wideLowpassPolynomial_coeff,wideLowpassPolynomial_coeff]
  ring

def thinWideBandStart (m N : ℕ) : ℕ := (99*m+2)*N+1

def thinWideBandEnd (m N' : ℕ) : ℕ := (101*m+2)*N'

def thinWideBandHalfwidth (m N N' : ℕ) : ℕ :=
  (thinWideBandEnd m N'-thinWideBandStart m N+2)/2

/-- Exact cancellation of BOTH plateaux at every frequency below the positive band. -/
theorem thinWideBandPolynomial_coeff_low (m N N' : ℕ) (hNN' : N ≤ N') (P : Polynomial ℂ)
    (k : ℕ) (hk : k < thinWideBandStart m N) :
    (thinWideBandPolynomial m N N' P).coeff k = 0 := by
  have hkN : k ≤ (99*m+2)*N := by dsimp only [thinWideBandStart] at hk; omega
  have hkN' : k ≤ (99*m+2)*N' := hkN.trans (Nat.mul_le_mul_left _ hNN')
  rw [thinWideBandPolynomial_coeff]
  simp only [wideDirichletPositiveWeight,wideDirichletProductPolynomial_coeff_plateau m N k hkN,
    wideDirichletProductPolynomial_coeff_plateau m N' k hkN',sub_self,zero_mul]

/-- The exact outer polynomial support is retained, with its endpoint included. -/
theorem thinWideBandPolynomial_coeff_high (m N N' : ℕ) (hNN' : N ≤ N') (P : Polynomial ℂ)
    (k : ℕ) (hk : thinWideBandEnd m N' < k) :
    (thinWideBandPolynomial m N N' P).coeff k = 0 := by
  have hkN' : wideDirichletProductShift m N' < k := by
    rw [wideDirichletProductShift_eq]
    exact hk
  have hkN : wideDirichletProductShift m N < k := by
    rw [wideDirichletProductShift_eq]
    exact (Nat.mul_le_mul_left (101*m+2) hNN').trans_lt hk
  rw [thinWideBandPolynomial_coeff]
  simp only [wideDirichletPositiveWeight,wideDirichletProductPolynomial_coeff_zero m N k hkN,
    wideDirichletProductPolynomial_coeff_zero m N' k hkN',sub_self,zero_mul]

/-- The chosen integer halfwidth covers the whole actual band, fits above zero,
and is comparable below to mN. All endpoint rounding is explicit. -/
theorem thinWideBand_geometry (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) :
    2*thinWideBandHalfwidth m N N' ≤ thinWideBandStart m N ∧
    thinWideBandEnd m N' < thinWideBandStart m N+2*thinWideBandHalfwidth m N N' ∧
    m*N ≤ thinWideBandHalfwidth m N N' := by
  let b := thinWideBandStart m N
  let B := thinWideBandEnd m N'
  have hMono : (101*m+2)*N ≤ B := Nat.mul_le_mul_left _ hNN'
  have hbB : b ≤ B := by
    dsimp only [b,B,thinWideBandStart,thinWideBandEnd] at *
    nlinarith
  have hSub : B-b+b = B := Nat.sub_add_cancel hbB
  have hWidth : B+2 ≤ 2*b := by
    have h := Nat.mul_le_mul_left (101*m+2) hRatio
    dsimp only [b,B,thinWideBandStart,thinWideBandEnd] at *
    nlinarith
  have hLower : 2*(m*N) ≤ B-b+1 := by
    dsimp only [b,B,thinWideBandStart,thinWideBandEnd] at *
    nlinarith
  change 2*((B-b+2)/2) ≤ b ∧ B < b+2*((B-b+2)/2) ∧ m*N ≤ (B-b+2)/2
  omega

/-- Every actual thin band is covered by the proved arbitrary-offset cyclic lower bound. -/
theorem thinWideBand_polynomial_integral_lower (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (2*(thinWideBandHalfwidth m N N' : ℝ))*
      (∫ τ : Boundary, ‖(thinWideBandPolynomial m N N' P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
      2*schattenNorm p (polynomialHankelRectangleOffset
        (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
        (thinWideBandStart m N-2*thinWideBandHalfwidth m N N')
        (thinWideBandPolynomial m N N' P))^p := by
  obtain ⟨hFit,hCover,_hLower⟩ := thinWideBand_geometry m N N' hm hN hNN' hRatio
  apply offsetShortBand_polynomial_integral_lower _ _ hFit _ _ _ p hp hp1
  · exact thinWideBandPolynomial_coeff_low m N N' hNN' P
  · intro k hk
    apply thinWideBandPolynomial_coeff_high m N N' hNN' P k
    omega

/-- The concrete geometric schedule, with its actual ceiling rather than an implicit choice. -/
def thinWideScale (n : ℕ) : ℕ := ⌈(10 : ℝ)*(11/10 : ℝ)^n⌉₊

theorem thinWideScale_zero : thinWideScale 0 = 10 := by
  norm_num [thinWideScale]

/-- Bernoulli's inequality also gives an explicit elementary divergence bound. -/
theorem thinWideScale_lower (n : ℕ) : n+10 ≤ thinWideScale n := by
  have hBern := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1/10) n
  norm_num only [show (1 : ℝ)+1/10 = 11/10 by norm_num] at hBern
  have hCeil := Nat.le_ceil ((10 : ℝ)*(11/10 : ℝ)^n)
  change 10*(11/10 : ℝ)^n ≤ (thinWideScale n : ℝ) at hCeil
  have h : (n : ℝ)+10 ≤ (thinWideScale n : ℝ) := by nlinarith
  exact_mod_cast h

theorem thinWideScale_ten_le (n : ℕ) : 10 ≤ thinWideScale n :=
  (by omega : 10 ≤ n+10).trans (thinWideScale_lower n)

theorem thinWideScale_monotone : Monotone thinWideScale := by
  apply monotone_nat_of_le_succ
  intro n
  apply Nat.ceil_mono
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 11/10) n]

/-- Ceiling errors are absorbed by the initial scale ten, giving the exact requested ratio. -/
theorem thinWideScale_ratio (n : ℕ) : 5*thinWideScale (n+1) ≤ 6*thinWideScale n := by
  have hOne : (1 : ℝ) ≤ (11/10 : ℝ)^n := one_le_pow₀ (by norm_num)
  have hCeil := Nat.le_ceil ((10 : ℝ)*(11/10 : ℝ)^n)
  have hCeil' := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 10*(11/10 : ℝ)^(n+1))
  change 10*(11/10 : ℝ)^n ≤ (thinWideScale n : ℝ) at hCeil
  change (thinWideScale (n+1) : ℝ) < 10*(11/10 : ℝ)^(n+1)+1 at hCeil'
  rw [pow_succ] at hCeil'
  have h : 5*(thinWideScale (n+1) : ℝ) ≤ 6*(thinWideScale n : ℝ) := by nlinarith
  exact_mod_cast h

theorem tendsto_thinWideScale : Tendsto thinWideScale atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans ((by omega : n ≤ n+10).trans (thinWideScale_lower n))

/-- The concrete scale schedule supplies EVERY premise of the actual thin-band geometry. -/
theorem thinWideScale_band_geometry (m n : ℕ) (hm : 1 ≤ m) :
    2*thinWideBandHalfwidth m (thinWideScale n) (thinWideScale (n+1)) ≤
      thinWideBandStart m (thinWideScale n) ∧
    thinWideBandEnd m (thinWideScale (n+1)) < thinWideBandStart m (thinWideScale n)+
      2*thinWideBandHalfwidth m (thinWideScale n) (thinWideScale (n+1)) ∧
    m*thinWideScale n ≤ thinWideBandHalfwidth m (thinWideScale n) (thinWideScale (n+1)) :=
  thinWideBand_geometry m _ _ hm (thinWideScale_ten_le n)
    (thinWideScale_monotone (Nat.le_succ n)) (thinWideScale_ratio n)

/-- Exact telescoping, including the base low-pass block and hence the constant mode. -/
theorem wideLowpassPolynomial_telescope (m : ℕ) (s : ℕ → ℕ) (P : Polynomial ℂ) (J : ℕ) :
    wideLowpassPolynomial m (s 0) P+
      (∑ j ∈ Finset.range J, thinWideBandPolynomial m (s j) (s (j+1)) P) =
      wideLowpassPolynomial m (s J) P := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih,thinWideBandPolynomial]
    abel

/-- Once the polynomial degree lies in the plateau, the actual multiplier is the identity. -/
theorem wideLowpassPolynomial_eq_self (m N : ℕ) (P : Polynomial ℂ)
    (hP : P.natDegree ≤ (99*m+2)*N) : wideLowpassPolynomial m N P = P := by
  ext k
  rw [wideLowpassPolynomial_coeff]
  by_cases hk : k ≤ P.natDegree
  · rw [wideDirichletPositiveWeight,
      wideDirichletProductPolynomial_coeff_plateau m N k (hk.trans hP),one_mul]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k),mul_zero]

/-- A concrete finite exact resolution of every polynomial; no infinite sum is presumed. -/
theorem thinWideScale_polynomial_resolution (m : ℕ) (P : Polynomial ℂ) (J : ℕ)
    (hJ : P.natDegree ≤ J) :
    wideLowpassPolynomial m (thinWideScale 0) P+
      (∑ j ∈ Finset.range J,
        thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P) = P := by
  rw [wideLowpassPolynomial_telescope]
  apply wideLowpassPolynomial_eq_self
  have hScale : J ≤ thinWideScale J := (by omega : J ≤ J+10).trans (thinWideScale_lower J)
  have hMul : thinWideScale J ≤ (99*m+2)*thinWideScale J := by nlinarith
  exact hJ.trans (hScale.trans hMul)

theorem thinWideScale_polynomial_band_eventually_zero (m : ℕ) (P : Polynomial ℂ) (j : ℕ)
    (hj : P.natDegree ≤ j) :
    thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P = 0 := by
  have hEq (n : ℕ) (hn : P.natDegree ≤ n) : wideLowpassPolynomial m (thinWideScale n) P = P := by
    apply wideLowpassPolynomial_eq_self
    have hScale : n ≤ thinWideScale n := (by omega : n ≤ n+10).trans (thinWideScale_lower n)
    have hMul : thinWideScale n ≤ (99*m+2)*thinWideScale n := by nlinarith
    exact hn.trans (hScale.trans hMul)
  rw [thinWideBandPolynomial,hEq (j+1) (by omega),hEq j hj,sub_self]

/-- Uniform concrete bounds for the actual band halfwidth and Hankel offset. -/
theorem thinWideBand_placement_bounds (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) :
    thinWideBandHalfwidth m N N' ≤ 20*m*N ∧
    50*m*N ≤ thinWideBandStart m N-2*thinWideBandHalfwidth m N N' ∧
    thinWideBandStart m N ≤ 102*m*N := by
  let b := thinWideBandStart m N
  let B := thinWideBandEnd m N'
  have hMono : (101*m+2)*N ≤ B := Nat.mul_le_mul_left _ hNN'
  have hbB : b ≤ B := by
    dsimp only [b,B,thinWideBandStart,thinWideBandEnd] at *
    nlinarith
  have hSub : B-b+b = B := Nat.sub_add_cancel hbB
  have hRatio' := Nat.mul_le_mul_left (101*m+2) hRatio
  have hWidth : B-b+2 ≤ 40*m*N := by
    dsimp only [b,B,thinWideBandStart,thinWideBandEnd] at *
    nlinarith
  have hL : thinWideBandHalfwidth m N N' ≤ 20*m*N := by
    change (B-b+2)/2 ≤ 20*m*N
    have hWidth2 : B-b+2 ≤ 2*(20*m*N) := by nlinarith
    omega
  have hFit := (thinWideBand_geometry m N N' hm hN hNN' hRatio).1
  have hSubL := Nat.sub_add_cancel hFit
  refine ⟨hL,?_,?_⟩
  · dsimp only [thinWideBandStart] at *
    nlinarith
  · dsimp only [thinWideBandStart]
    nlinarith

def thinWideBandRowStart (m N N' : ℕ) : ℕ :=
  (thinWideBandStart m N-2*thinWideBandHalfwidth m N N')/2

def thinWideBandColumnStart (m N N' : ℕ) : ℕ :=
  thinWideBandStart m N-2*thinWideBandHalfwidth m N N'-thinWideBandRowStart m N N'

theorem thinWideBand_starts_add (m N N' : ℕ) :
    thinWideBandRowStart m N N'+thinWideBandColumnStart m N N' =
      thinWideBandStart m N-2*thinWideBandHalfwidth m N N' := by
  dsimp only [thinWideBandRowStart,thinWideBandColumnStart]
  omega

/-- The balanced row and column windows both live in one fixed multiplicative annulus. -/
theorem thinWideBand_coordinate_windows (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) :
    (∀ i : Fin (3*thinWideBandHalfwidth m N N'),
      20*m*N ≤ thinWideBandRowStart m N N'+i.val ∧
      thinWideBandRowStart m N N'+i.val < 150*m*N) ∧
    (∀ i : Fin (3*thinWideBandHalfwidth m N N'),
      20*m*N ≤ thinWideBandColumnStart m N N'+i.val ∧
      thinWideBandColumnStart m N N'+i.val < 150*m*N) := by
  obtain ⟨hL,hS,hB⟩ := thinWideBand_placement_bounds m N N' hm hN hNN' hRatio
  let d := m*N
  let s := thinWideBandStart m N-2*thinWideBandHalfwidth m N N'
  have hd : 10 ≤ d := by dsimp only [d]; nlinarith
  have hLd : thinWideBandHalfwidth m N N' ≤ 20*d := by simpa only [d,mul_assoc] using hL
  have hSd : 50*d ≤ s := by simpa only [s,d,mul_assoc] using hS
  have hBd : s ≤ 102*d := by
    apply (Nat.sub_le _ _).trans
    simpa only [d,mul_assoc] using hB
  have hRow : 20*d ≤ s/2 ∧ s/2+3*thinWideBandHalfwidth m N N' ≤ 150*d := by omega
  have hCol : 20*d ≤ s-s/2 ∧ s-s/2+3*thinWideBandHalfwidth m N N' ≤ 150*d := by omega
  constructor
  · intro i
    change 20*m*N ≤ s/2+i.val ∧ s/2+i.val < 150*m*N
    have hi := i.isLt
    simp only [mul_assoc]
    change 20*d ≤ s/2+i.val ∧ s/2+i.val < 150*d
    omega
  · intro i
    change 20*m*N ≤ s-s/2+i.val ∧ s-s/2+i.val < 150*m*N
    have hi := i.isLt
    simp only [mul_assoc]
    change 20*d ≤ s-s/2+i.val ∧ s-s/2+i.val < 150*d
    omega

/-- Two-sided geometric comparison keeps the actual ceiling errors explicit. -/
theorem thinWideScale_geometric_comparison (n k : ℕ) :
    (10/11 : ℝ)*(11/10 : ℝ)^k*(thinWideScale n : ℝ) ≤ (thinWideScale (n+k) : ℝ) ∧
    (thinWideScale (n+k) : ℝ) ≤ (11/10 : ℝ)*(11/10 : ℝ)^k*(thinWideScale n : ℝ) := by
  have hOne : (1 : ℝ) ≤ (11/10 : ℝ)^n := one_le_pow₀ (by norm_num)
  have hOne' : (1 : ℝ) ≤ (11/10 : ℝ)^(n+k) := one_le_pow₀ (by norm_num)
  have hnLo := Nat.le_ceil ((10 : ℝ)*(11/10 : ℝ)^n)
  have hnHi := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 10*(11/10 : ℝ)^n)
  have hnkLo := Nat.le_ceil ((10 : ℝ)*(11/10 : ℝ)^(n+k))
  have hnkHi := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 10*(11/10 : ℝ)^(n+k))
  change 10*(11/10 : ℝ)^n ≤ (thinWideScale n : ℝ) at hnLo
  change (thinWideScale n : ℝ) < 10*(11/10 : ℝ)^n+1 at hnHi
  change 10*(11/10 : ℝ)^(n+k) ≤ (thinWideScale (n+k) : ℝ) at hnkLo
  change (thinWideScale (n+k) : ℝ) < 10*(11/10 : ℝ)^(n+k)+1 at hnkHi
  have hnAdj : (10/11 : ℝ)*(thinWideScale n : ℝ) ≤ 10*(11/10 : ℝ)^n := by nlinarith
  have hnkAdj : (thinWideScale (n+k) : ℝ) ≤ (11/10 : ℝ)*(10*(11/10 : ℝ)^(n+k)) := by nlinarith
  constructor
  · have h := mul_le_mul_of_nonneg_right hnAdj (by positivity : (0 : ℝ) ≤ (11/10 : ℝ)^k)
    rw [pow_add] at hnkLo
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hnLo (by positivity : (0 : ℝ) ≤ (11/10 : ℝ)*(11/10 : ℝ)^k)
    rw [pow_add] at hnkAdj
    nlinarith

/-- A fixed sparse gap already separates every ten-fold dilation of these scales. -/
theorem thinWideScale_sparse_gap (n k : ℕ) (hk : 100 ≤ k) :
    10*thinWideScale n ≤ thinWideScale (n+k) := by
  have hBern := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1/10) k
  norm_num only [show (1 : ℝ)+1/10 = 11/10 by norm_num] at hBern
  have hkR : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hPow : (11 : ℝ) ≤ (11/10 : ℝ)^k := by nlinarith
  have hComp := (thinWideScale_geometric_comparison n k).1
  have hN : (0 : ℝ) ≤ (thinWideScale n : ℝ) := Nat.cast_nonneg _
  have h : 10*(thinWideScale n : ℝ) ≤ (thinWideScale (n+k) : ℝ) := by nlinarith
  exact_mod_cast h

/-- The actual common coordinate annuli are disjoint at every gap of at least one hundred. -/
theorem thinWideScale_annuli_disjoint (m n k : ℕ) (hk : 100 ≤ k) :
    Disjoint (Set.Ico (20*m*thinWideScale n) (150*m*thinWideScale n))
      (Set.Ico (20*m*thinWideScale (n+k)) (150*m*thinWideScale (n+k))) := by
  have hGap := thinWideScale_sparse_gap n k hk
  have hMul := Nat.mul_le_mul_left m hGap
  have hSep : 150*m*thinWideScale n ≤ 20*m*thinWideScale (n+k) := by nlinarith
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge (hSep.trans hy.1)) hx.2

end TTO.Paper.Proved
