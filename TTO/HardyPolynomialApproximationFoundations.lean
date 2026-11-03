/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialH1FactorizationFoundations
public import TTO.L1FunctionalSymbolFoundations

/-! Exact finite Hardy sums as analytic polynomials and their native L¹ norm. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal ComplexConjugate InnerProductSpace Topology Polynomial
namespace TTO.Paper.Proved

def finiteHardyPolynomial (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (c n)

theorem eval_finiteHardyPolynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (finiteHardyPolynomial N c).eval z=∑ n ∈ Finset.range N,c n*z^n := by
  simp only [finiteHardyPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem polynomialBoundary_finiteHardyPolynomial (N : ℕ) (c : ℕ → ℂ) :
    polynomialBoundary (finiteHardyPolynomial N c)=∑ n ∈ Finset.range N,c n • hardyBasis n := by
  apply hardy_analyticValue_injective
  intro z hz
  rw [analyticValue_polynomialBoundary _ hz]
  have hsum : (∑ n ∈ Finset.range N,c n • hardyBasis n : Hardy).val =
      ∑ n ∈ Finset.range N,c n • fourierBasis (T:=1) (n : ℤ) := by
    simp only [Submodule.coe_sum,Submodule.coe_smul,hardyBasis_apply]
    rfl
  rw [hsum,analyticValue_finset_sum _ _ hz,eval_finiteHardyPolynomial]
  apply Finset.sum_congr rfl
  intro n _
  rw [analyticValue_smul _ _ hz,analyticValue_fourierBasis]

theorem exists_polynomialBoundary_finite_hardy_sum (N : ℕ) (c : ℕ → ℂ) :
    ∃ p : Polynomial ℂ,polynomialBoundary p=∑ n ∈ Finset.range N,c n • hardyBasis n :=
  ⟨finiteHardyPolynomial N c,polynomialBoundary_finiteHardyPolynomial N c⟩

theorem nativeL1_norm_polynomialBoundary (p : Polynomial ℂ) :
    ‖nativeL2toL1 (polynomialBoundary p).val‖ =
      ∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure := by
  rw [L1.norm_eq_integral_norm]
  change (∫ t,‖(polynomialBoundary p).val t‖ ∂circleMeasure)=_
  apply integral_congr_ae
  have h2 := toL2_analyticPolynomialBoundary p
  filter_upwards [toL2_ae (analyticPolynomialBoundary p),analyticPolynomialBoundary_ae p] with t ht hp
  have he := congrArg (fun f : BoundaryL2 => f t) h2
  exact congrArg norm (he.symm.trans (ht.trans hp))

end TTO.Paper.Proved
