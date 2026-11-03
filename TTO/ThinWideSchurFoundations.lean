/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ThinWideBandFoundations
public import TTO.WideDirichletFoundations
public import TTO.PolynomialSchurFoundations
public import TTO.CappedSchattenFoundations

/-! Uniform actual local Schur localization for the thin wide-plateau bands.
The sampling identity uses the full signed kernel, including negative modulation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- A uniform local Schur constant, independent of scale, dimensions, offset, and operator. -/
def wideLocalSchurConstant (m : ℕ) (p : ℝ) : ℝ :=
  wideDirichletProductLpConstant m p*(1000*(m : ℝ)+1000)^(1-p)

theorem wideLocalSchurConstant_pos (m : ℕ) (p : ℝ)
    (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) : 0 < wideLocalSchurConstant m p := by
  exact mul_pos (wideDirichletProductLpConstant_pos m p hOrder)
    (Real.rpow_pos_of_pos (by positivity) _)

/-- Actual full-signed-kernel Schur bound on every bounded local rectangle.
The reference scale N is separate from the smoothing scale T, with N≤T≤2N. -/
theorem wide_local_schur_schattenNorm_rpow_le (m N T r c s : ℕ) (hN : 0 < N)
    (hNT : N ≤ T) (hTN : T ≤ 2*N) (hShape : s+r+c ≤ 250*m*N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelSchurOffset r c (wideDirichletProductShift m T+s)
      (wideDirichletProductPolynomial m T) A)^p ≤ wideLocalSchurConstant m p*schattenNorm p A^p := by
  let Q : ℕ := (1000*m+1000)*N
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hT : 0 < T := hN.trans_le hNT
  have hSize : wideDirichletProductShift m T+s+r+c ≤ Q := by
    rw [wideDirichletProductShift_eq]
    dsimp only [Q]
    nlinarith
  have hDegree : (wideDirichletProductPolynomial m T).natDegree < Q := by
    apply (wideDirichletProductPolynomial_natDegree_le m T).trans_lt
    rw [wideDirichletProductShift_eq]
    dsimp only [Q]
    nlinarith
  have hSchur := polynomialHankelSchurOffset_schattenNorm_rpow_le_symbol_integral
    Q r c (wideDirichletProductShift m T+s) hSize (wideDirichletProductPolynomial m T) hDegree A p hp hp1
  have hKernel : (∫ τ : Boundary,‖shiftedPolynomialSymbol (wideDirichletProductPolynomial m T)
      (wideDirichletProductShift m T+s) τ‖^p ∂circleMeasure) =
      ∫ τ : Boundary,‖wideDirichletProductKernel m T τ‖^p ∂circleMeasure := by
    apply integral_congr_ae
    exact Eventually.of_forall fun τ => by
      dsimp only
      rw [wideDirichletProductKernel_eq_shiftedSymbol,shiftedPolynomialSymbol_norm,shiftedPolynomialSymbol_norm]
  rw [hKernel] at hSchur
  have hLp := (integral_wideDirichletProductKernel_rpow_le m T hT p hp hOrder).2
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hPower : (T : ℝ)^(p-1) ≤ (N : ℝ)^(p-1) :=
    Real.rpow_le_rpow_of_nonpos hNR (by exact_mod_cast hNT) (by linarith)
  have hLpN : (∫ τ : Boundary,‖wideDirichletProductKernel m T τ‖^p ∂circleMeasure) ≤
      wideDirichletProductLpConstant m p*(N : ℝ)^(p-1) :=
    hLp.trans (mul_le_mul_of_nonneg_left hPower (wideDirichletProductLpConstant_pos m p hOrder).le)
  apply hSchur.trans
  calc
    _ ≤ (Q : ℝ)^(1-p)*(wideDirichletProductLpConstant m p*(N : ℝ)^(p-1))*schattenNorm p A^p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLpN (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (schattenNorm_nonneg p A) _)
    _ = _ := by
      have hQR : (Q : ℝ) = (1000*(m : ℝ)+1000)*(N : ℝ) := by dsimp only [Q]; push_cast; ring
      rw [hQR,Real.mul_rpow (by positivity) hNR.le]
      have hCancel : (N : ℝ)^(1-p)*(N : ℝ)^(p-1)=1 := by
        rw [← Real.rpow_add hNR,show 1-p+(p-1)=0 by ring,Real.rpow_zero]
      dsimp only [wideLocalSchurConstant]
      calc
        _ = wideDirichletProductLpConstant m p*(1000*(m : ℝ)+1000)^(1-p)*
            ((N : ℝ)^(1-p)*(N : ℝ)^(p-1))*schattenNorm p A^p := by ring
        _ = _ := by rw [hCancel,mul_one]

/-- The polynomial low-pass acts on the actual corner by precisely this shifted Schur mask. -/
theorem wideLowpassPolynomial_rectangle_eq_schur (m T r c s : ℕ) (P : Polynomial ℂ) :
    polynomialHankelRectangleOffset r c s (wideLowpassPolynomial m T P) =
      polynomialHankelSchurOffset r c (wideDirichletProductShift m T+s)
        (wideDirichletProductPolynomial m T) (polynomialHankelRectangleOffset r c s P) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  ext i
  change polynomialHankelRectangleOffset r c s (wideLowpassPolynomial m T P)
      (EuclideanSpace.single j (1 : ℂ)) i =
    polynomialHankelSchurOffset r c (wideDirichletProductShift m T+s)
      (wideDirichletProductPolynomial m T) (polynomialHankelRectangleOffset r c s P)
      (EuclideanSpace.single j (1 : ℂ)) i
  rw [polynomialHankelRectangleOffset_single_apply,polynomialHankelSchurOffset_single_apply,
    polynomialHankelRectangleOffset_single_apply,wideLowpassPolynomial_coeff]
  simp only [wideDirichletPositiveWeight,Nat.add_assoc]

/-- Literal Schur difference identity for a thin band on the SAME actual corner. -/
theorem thinWideBandPolynomial_rectangle_eq_schur_sub (m N N' r c s : ℕ) (P : Polynomial ℂ) :
    polynomialHankelRectangleOffset r c s (thinWideBandPolynomial m N N' P) =
      polynomialHankelSchurOffset r c (wideDirichletProductShift m N'+s)
        (wideDirichletProductPolynomial m N') (polynomialHankelRectangleOffset r c s P)-
      polynomialHankelSchurOffset r c (wideDirichletProductShift m N+s)
        (wideDirichletProductPolynomial m N) (polynomialHankelRectangleOffset r c s P) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  ext i
  change polynomialHankelRectangleOffset r c s (thinWideBandPolynomial m N N' P)
      (EuclideanSpace.single j (1 : ℂ)) i =
    polynomialHankelSchurOffset r c (wideDirichletProductShift m N'+s)
      (wideDirichletProductPolynomial m N') (polynomialHankelRectangleOffset r c s P)
      (EuclideanSpace.single j (1 : ℂ)) i-
    polynomialHankelSchurOffset r c (wideDirichletProductShift m N+s)
      (wideDirichletProductPolynomial m N) (polynomialHankelRectangleOffset r c s P)
      (EuclideanSpace.single j (1 : ℂ)) i
  rw [polynomialHankelRectangleOffset_single_apply,thinWideBandPolynomial_coeff,
    polynomialHankelSchurOffset_single_apply,polynomialHankelSchurOffset_single_apply,
    polynomialHankelRectangleOffset_single_apply]
  simp only [wideDirichletPositiveWeight,Nat.add_assoc]
  ring

/-- Uniform thin-band Schur control on every bounded local corner. -/
theorem thinWideBand_rectangle_schattenNorm_rpow_le (m N N' r c s : ℕ) (hN : 0 < N)
    (hNN' : N ≤ N') (hN'N : N' ≤ 2*N) (hShape : s+r+c ≤ 250*m*N)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelRectangleOffset r c s (thinWideBandPolynomial m N N' P))^p ≤
      (2*wideLocalSchurConstant m p)*schattenNorm p (polynomialHankelRectangleOffset r c s P)^p := by
  let A := polynomialHankelRectangleOffset r c s P
  let B := polynomialHankelSchurOffset r c (wideDirichletProductShift m N+s) (wideDirichletProductPolynomial m N) A
  let B' := polynomialHankelSchurOffset r c (wideDirichletProductShift m N'+s) (wideDirichletProductPolynomial m N') A
  have hB : schattenNorm p B^p ≤ wideLocalSchurConstant m p*schattenNorm p A^p :=
    wide_local_schur_schattenNorm_rpow_le m N N r c s hN le_rfl (by omega) hShape A p hp hp1 hOrder
  have hB' : schattenNorm p B'^p ≤ wideLocalSchurConstant m p*schattenNorm p A^p :=
    wide_local_schur_schattenNorm_rpow_le m N N' r c s hN hNN' hN'N hShape A p hp hp1 hOrder
  rw [thinWideBandPolynomial_rectangle_eq_schur_sub]
  change schattenNorm p (B'-B)^p ≤ _
  have hTri : schattenNorm p (B'-B)^p ≤ schattenNorm p B'^p+schattenNorm p B^p := by
    simpa only [sub_eq_add_neg,schattenNorm,approximationNumber_neg] using
      finite_schattenNorm_add_rpow_le B' (-B) p hp hp1
  exact hTri.trans ((add_le_add hB' hB).trans_eq (by dsimp only [A]; ring))

/-- The uniform local estimate on the actual halfwidth/offset supplied by the band geometry. -/
theorem thinWideBand_local_corner_bound (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelRectangleOffset
      (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
      (thinWideBandStart m N-2*thinWideBandHalfwidth m N N') (thinWideBandPolynomial m N N' P))^p ≤
    (2*wideLocalSchurConstant m p)*schattenNorm p (polynomialHankelRectangleOffset
      (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
      (thinWideBandStart m N-2*thinWideBandHalfwidth m N N') P)^p := by
  obtain ⟨hL,_hS,hB⟩ := thinWideBand_placement_bounds m N N' hm hN hNN' hRatio
  have hShape : thinWideBandStart m N-2*thinWideBandHalfwidth m N N'+
      3*thinWideBandHalfwidth m N N'+3*thinWideBandHalfwidth m N N' ≤ 250*m*N := by
    have hSub := Nat.sub_le (thinWideBandStart m N) (2*thinWideBandHalfwidth m N N')
    nlinarith
  exact thinWideBand_rectangle_schattenNorm_rpow_le m N N' _ _ _ (by omega) hNN' (by omega)
    hShape P p hp hp1 hOrder

/-- The localization constant is chosen BEFORE every scale and polynomial. -/
theorem exists_thinWideBand_local_corner_bound (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    ∃ C : ℝ,0 < C ∧ ∀ N N' : ℕ,10 ≤ N → N ≤ N' → 5*N' ≤ 6*N → ∀ P : Polynomial ℂ,
      schattenNorm p (polynomialHankelRectangleOffset
        (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
        (thinWideBandStart m N-2*thinWideBandHalfwidth m N N') (thinWideBandPolynomial m N N' P))^p ≤
      C*schattenNorm p (polynomialHankelRectangleOffset
        (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
        (thinWideBandStart m N-2*thinWideBandHalfwidth m N N') P)^p :=
  ⟨2*wideLocalSchurConstant m p,mul_pos (by norm_num) (wideLocalSchurConstant_pos m p hOrder),
    fun N N' hN hNN' hRatio P => thinWideBand_local_corner_bound m N N' hm hN hNN' hRatio P p hp hp1 hOrder⟩

/-- The actual thin-band Lp mass is paid for by the SAME original polynomial corner.
This is a single-band estimate; collective sparse off-diagonal control remains separate. -/
theorem thinWideBand_lp_controlled_by_corner (m N N' : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    (N : ℝ)*(∫ τ : Boundary,‖(thinWideBandPolynomial m N N' P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) ≤
      (2*wideLocalSchurConstant m p)*schattenNorm p (polynomialHankelRectangleOffset
        (3*thinWideBandHalfwidth m N N') (3*thinWideBandHalfwidth m N N')
        (thinWideBandStart m N-2*thinWideBandHalfwidth m N N') P)^p := by
  have hLower := thinWideBand_polynomial_integral_lower m N N' hm hN hNN' hRatio P p hp hp1
  have hSchur := thinWideBand_local_corner_bound m N N' hm hN hNN' hRatio P p hp hp1 hOrder
  have hMass := hLower.trans (mul_le_mul_of_nonneg_left hSchur (by norm_num : (0 : ℝ) ≤ 2))
  have hL := (thinWideBand_geometry m N N' hm hN hNN' hRatio).2.2
  have hNL : N ≤ thinWideBandHalfwidth m N N' := (by nlinarith : N ≤ m*N).trans hL
  have hNLR : (N : ℝ) ≤ (thinWideBandHalfwidth m N N' : ℝ) := by exact_mod_cast hNL
  calc
    _ ≤ (thinWideBandHalfwidth m N N' : ℝ)*
        (∫ τ : Boundary,‖(thinWideBandPolynomial m N N' P).eval (fourier (T := 1) 1 τ)‖^p ∂circleMeasure) :=
      mul_le_mul_of_nonneg_right hNLR (integral_nonneg fun τ => Real.rpow_nonneg (norm_nonneg _) p)
    _ ≤ _ := by nlinarith

end TTO.Paper.Proved
