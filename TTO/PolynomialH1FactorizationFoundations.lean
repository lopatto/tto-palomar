/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HardySquareRootFoundations
public import TTO.FiniteBlaschkeFoundations

/-! Native bounded Hardy factors of polynomial boundary functions from explicit inner/outer data. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology Polynomial
namespace TTO.Paper.Proved
open Reduction

def analyticPolynomialCircle (p : Polynomial ℂ) : C(Boundary,ℂ) :=
  ⟨fun t => p.eval (fourier (T:=1) 1 t), p.continuous.comp (fourier (T:=1) 1).continuous⟩

def analyticPolynomialBoundary (p : Polynomial ℂ) : BoundaryLInf :=
  ContinuousMap.toLp ∞ circleMeasure ℂ (analyticPolynomialCircle p)

theorem analyticPolynomialBoundary_ae (p : Polynomial ℂ) :
    analyticPolynomialBoundary p =ᵐ[circleMeasure] fun t => p.eval (fourier (T:=1) 1 t) :=
  ContinuousMap.coeFn_toLp (p:=∞) (𝕜:=ℂ) circleMeasure (analyticPolynomialCircle p)

theorem toL2_analyticPolynomialBoundary (p : Polynomial ℂ) :
    toL2 (analyticPolynomialBoundary p)=(polynomialBoundary p).val := by
  classical
  apply Lp.ext
  filter_upwards [toL2_ae (analyticPolynomialBoundary p), analyticPolynomialBoundary_ae p,
    Lp.coeFn_finsetSum (Finset.range (p.natDegree+1))
      (fun i => p.coeff i • fourierBasis (T:=1) (i : ℤ)),
    ae_all_iff.2 (fun i : ℕ => Lp.coeFn_smul (p.coeff i) (fourierBasis (T:=1) (i : ℤ))),
    ae_all_iff.2 (fun i : ℕ => fourierBasis_ae (i : ℤ))] with t ht hp hs hsm hmode
  rw [ht,hp]
  change p.eval (fourier (T:=1) 1 t)=
    (∑ i ∈ Finset.range (p.natDegree+1), p.coeff i • fourierBasis (T:=1) (i : ℤ)) t
  rw [hs,Finset.sum_apply,Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsm i]
  change p.coeff i*(fourier (T:=1) 1 t)^i=p.coeff i*((fourierBasis (T:=1) (i : ℤ)) t)
  rw [hmode i]
  congr 1
  simp [fourier_apply,AddCircle.toCircle_nsmul]

theorem analyticPolynomialBoundary_hardy (p : Polynomial ℂ) :
    toL2 (analyticPolynomialBoundary p)∈hardy := by
  rw [toL2_analyticPolynomialBoundary]
  exact (polynomialBoundary p).property

theorem innerValue_analyticPolynomialBoundary (p : Polynomial ℂ) (z : Disk) :
    innerValue (analyticPolynomialBoundary p) z.val=p.eval z.val := by
  change analyticValue (toL2 (analyticPolynomialBoundary p)) z.val=_
  rw [toL2_analyticPolynomialBoundary]
  exact analyticValue_polynomialBoundary p z.property

theorem norm_toL2_sq_integral (q : BoundaryLInf) :
    ‖toL2 q‖^2=∫ t, ‖q t‖^2 ∂circleMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (toL2 q) (toL2 q)
  calc
    ‖toL2 q‖^2 = RCLike.re (inner ℂ (toL2 q) (toL2 q)) := norm_sq_eq_re_inner (𝕜:=ℂ) _
    _ = ∫ t, RCLike.re (inner ℂ (toL2 q t) (toL2 q t)) ∂circleMeasure := by
      rw [L2.inner_def,← integral_re hi]
    _ = ∫ t, ‖q t‖^2 ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [toL2_ae q] with t ht
      rw [← norm_sq_eq_re_inner (𝕜:=ℂ),ht]

theorem norm_inner_square_factorization (u q : BoundaryLInf) (hu : IsInner u) :
    ‖toL2 q‖*‖toL2 (multiplyInf u q)‖ =
      ∫ t, ‖multiplyInf u (multiplyInf q q) t‖ ∂circleMeasure := by
  have hr : ‖toL2 (multiplyInf u q)‖=‖toL2 q‖ := by
    rw [toL2_multiplyInf]
    exact (innerMultiplyIsometry u hu).norm_map (toL2 q)
  rw [hr,← pow_two,norm_toL2_sq_integral]
  apply integral_congr_ae
  filter_upwards [multiplyInf_ae u (multiplyInf q q),multiplyInf_ae q q,hu.2] with t h1 h2 ht
  rw [h1,h2,norm_mul,norm_mul,ht,one_mul,pow_two]

theorem hardy_listProduct (l : List BoundaryLInf) (hl : ∀ a∈l,toL2 a∈hardy) :
    toL2 (l.foldr multiplyInf (constLInf 1))∈hardy := by
  induction l with
  | nil => rw [List.foldr_nil,toL2_constLInf]; exact constantCoreLaws.hardy 1
  | cons a l ih =>
    rw [List.foldr_cons,toL2_multiplyInf]
    exact multiply_mem_hardy a (hl a (by simp)) _ (ih (fun b hb => hl b (by simp [hb])))

theorem innerValue_listProduct_hardy (l : List BoundaryLInf) (hl : ∀ a∈l,toL2 a∈hardy) (z : Disk) :
    innerValue (l.foldr multiplyInf (constLInf 1)) z.val=(l.map (fun a => innerValue a z.val)).prod := by
  induction l with
  | nil =>
    change analyticValue (toL2 (constLInf 1)) z.val=1
    rw [toL2_constLInf,constL2_fourier,one_smul]
    simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z.val
  | cons a l ih =>
    rw [List.foldr_cons,innerValue_multiplyInf _ _ (hl a (by simp))
      (hardy_listProduct l (fun b hb => hl b (by simp [hb]))) z,
      List.map_cons,List.prod_cons,ih (fun b hb => hl b (by simp [hb]))]


theorem toL2_smul_boundary (c : ℂ) (a : BoundaryLInf) :
    toL2 (c • a)=c • toL2 a := by
  rw [← boundaryInclusion_apply,map_smul,boundaryInclusion_apply]

theorem innerValue_smul_boundary (c : ℂ) (a : BoundaryLInf) (z : Disk) :
    innerValue (c • a) z.val=c*innerValue a z.val := by
  change analyticValue (toL2 (c • a)) z.val=_
  rw [toL2_smul_boundary,analyticValue_smul c _ z.property]
  rfl

theorem eq_of_hardy_innerValue_eq (a b : BoundaryLInf) (ha : toL2 a∈hardy) (hb : toL2 b∈hardy)
    (he : ∀ z : Disk,innerValue a z.val=innerValue b z.val) : a=b := by
  have hL2 : toL2 a=toL2 b := by
    have h : (⟨toL2 a,ha⟩ : Hardy)=⟨toL2 b,hb⟩ := by
      apply hardy_analyticValue_injective
      intro z hz
      exact he ⟨z,hz⟩
    exact congrArg Subtype.val h
  apply Lp.ext
  filter_upwards [toL2_ae a,toL2_ae b] with t ha hb
  exact ha.symm.trans ((congrArg (fun f : BoundaryL2 => f t) hL2).trans hb)

def finiteOuterSquareRoot {m : ℕ} (c : ℂ) (β : Fin m → ℂ) (hβ : ∀ i,‖β i‖≤1) : BoundaryLInf :=
  Complex.sqrt c • finiteProduct (fun i => hardyLinearSquareRoot (β i) (hβ i))

theorem finiteOuterSquareRoot_hardy {m : ℕ} (c : ℂ) (β : Fin m → ℂ) (hβ : ∀ i,‖β i‖≤1) :
    toL2 (finiteOuterSquareRoot c β hβ)∈hardy := by
  rw [finiteOuterSquareRoot,toL2_smul_boundary]
  apply hardy.smul_mem
  apply hardy_listProduct
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact (hardyLinearSquareRoot_spec (β i) (hβ i)).1

theorem innerValue_finiteOuterSquareRoot_sq {m : ℕ} (c : ℂ) (β : Fin m → ℂ)
    (hβ : ∀ i,‖β i‖≤1) (z : Disk) :
    (innerValue (finiteOuterSquareRoot c β hβ) z.val)^2=c*∏ i,(1-β i*z.val) := by
  rw [finiteOuterSquareRoot,innerValue_smul_boundary]
  have hprod : innerValue (finiteProduct (fun i => hardyLinearSquareRoot (β i) (hβ i))) z.val =
      ∏ i,Complex.sqrt (1-β i*z.val) := by
    have h := innerValue_listProduct_hardy
      (List.ofFn (fun i => hardyLinearSquareRoot (β i) (hβ i)))
      (fun a ha => by
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
        exact (hardyLinearSquareRoot_spec (β i) (hβ i)).1) z
    simpa only [finiteProduct,List.map_ofFn,List.prod_ofFn,Function.comp_apply,
      (fun i => (hardyLinearSquareRoot_spec (β i) (hβ i)).2.1 z.val z.property)] using h
  rw [hprod,mul_pow,complex_sqrt_sq,← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact complex_sqrt_sq _

/-- Explicit inner/outer polynomial data gives actual bounded Hardy factors with the sharp H¹ norm identity. -/
theorem polynomialH1Factorization_of_finite_data (p : Polynomial ℂ) (u : BoundaryLInf) (hu : IsInner u)
    {m : ℕ} (c : ℂ) (β : Fin m → ℂ) (hβ : ∀ i,‖β i‖≤1)
    (hp : ∀ z : Disk,p.eval z.val=innerValue u z.val*c*∏ i,(1-β i*z.val)) :
    ∃ q r : BoundaryLInf,toL2 q∈hardy ∧ toL2 r∈hardy ∧
      multiplyInf q r=analyticPolynomialBoundary p ∧
      ‖toL2 q‖*‖toL2 r‖=∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure := by
  let q := finiteOuterSquareRoot c β hβ
  have hq : toL2 q∈hardy := finiteOuterSquareRoot_hardy c β hβ
  let r := multiplyInf u q
  have hr : toL2 r∈hardy := by
    rw [toL2_multiplyInf]
    exact multiply_mem_hardy u hu.1 (toL2 q) hq
  have hqq : toL2 (multiplyInf q q)∈hardy := by
    rw [toL2_multiplyInf]
    exact multiply_mem_hardy q hq (toL2 q) hq
  have hqqU : toL2 (multiplyInf u (multiplyInf q q))∈hardy := by
    rw [toL2_multiplyInf]
    exact multiply_mem_hardy u hu.1 _ hqq
  have hP : analyticPolynomialBoundary p=multiplyInf u (multiplyInf q q) := by
    apply eq_of_hardy_innerValue_eq _ _ (analyticPolynomialBoundary_hardy p) hqqU
    intro z
    rw [innerValue_analyticPolynomialBoundary,innerValue_multiplyInf _ _ hu.1 hqq,
      innerValue_multiplyInf _ _ hq hq]
    rw [← pow_two,innerValue_finiteOuterSquareRoot_sq c β hβ z,hp z]
    ring
  refine ⟨q,r,hq,hr,?_,?_⟩
  · rw [hP]
    apply Lp.ext
    filter_upwards [multiplyInf_ae q r,multiplyInf_ae u q,
      multiplyInf_ae u (multiplyInf q q),multiplyInf_ae q q] with t h1 h2 h3 h4
    change r t=u t*q t at h2
    rw [h1,h2,h3,h4]
    ring
  · change ‖toL2 q‖*‖toL2 (multiplyInf u q)‖=_
    rw [norm_inner_square_factorization u q hu,← hP]
    apply integral_congr_ae
    filter_upwards [analyticPolynomialBoundary_ae p] with t ht
    exact congrArg norm ht

theorem polynomialH1Factorization_of_list_data (p : Polynomial ℂ) (u : BoundaryLInf) (hu : IsInner u)
    (c : ℂ) (β : List ℂ) (hβ : ∀ b∈β,‖b‖≤1)
    (hp : ∀ z : Disk,p.eval z.val=innerValue u z.val*c*(β.map (fun b => 1-b*z.val)).prod) :
    ∃ q r : BoundaryLInf,toL2 q∈hardy ∧ toL2 r∈hardy ∧
      multiplyInf q r=analyticPolynomialBoundary p ∧
      ‖toL2 q‖*‖toL2 r‖=∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure := by
  apply polynomialH1Factorization_of_finite_data p u hu c (fun i : Fin β.length => β.get i)
    (fun i => hβ _ (List.get_mem _ _))
  intro z
  rw [hp z]
  congr 1
  rw [← List.prod_ofFn]
  congr 1
  symm
  change List.ofFn ((fun b : ℂ => 1-b*z.val) ∘ β.get)=(β.map (fun b => 1-b*z.val))
  rw [← List.map_ofFn,List.ofFn_get]

end TTO.Paper.Proved
