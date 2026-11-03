/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.QuotientFoundations
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Finite Blaschke model spaces through literal polynomial annihilators. -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology Polynomial

namespace TTO.Paper.Proved
open Reduction

/-- The ordinary analytic polynomial as a native Hardy boundary class. -/
def polynomialBoundary (P : Polynomial ℂ) : Hardy :=
  ⟨∑ i ∈ Finset.range (P.natDegree+1), P.coeff i • fourierBasis (T := 1) (i : ℤ),
    hardy.sum_mem (fun i _ => hardy.smul_mem _ (fourierBasis_mem_hardy i))⟩

theorem analyticValue_finset_sum {I : Type*} (s : Finset I) (f : I → BoundaryL2)
    {z : ℂ} (hz : ‖z‖ < 1) : analyticValue (∑ i ∈ s, f i) z = ∑ i ∈ s, analyticValue (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty,Finset.sum_empty,analyticValue_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,analyticValue_add _ _ hz,ih]

theorem analyticValue_polynomialBoundary (P : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (polynomialBoundary P).val z = P.eval z := by
  change analyticValue (∑ i ∈ Finset.range (P.natDegree+1), P.coeff i • fourierBasis (T := 1) (i : ℤ)) z = _
  rw [analyticValue_finset_sum _ _ hz,Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [analyticValue_smul _ _ hz,analyticValue_fourierBasis]

def blaschkeNumerator {n : ℕ} (a : Fin n → Disk) : Polynomial ℂ :=
  ∏ i, (Polynomial.X-Polynomial.C (a i).val)

def blaschkeDenominator {n : ℕ} (a : Fin n → Disk) : Polynomial ℂ :=
  ∏ i, (1-Polynomial.C (conj (a i).val)*Polynomial.X)

theorem blaschkeNumerator_monic {n : ℕ} (a : Fin n → Disk) : (blaschkeNumerator a).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact Polynomial.monic_X_sub_C _

def blaschkePhase (a : Disk) : ℂ := if a.val = 0 then 1 else -((‖a.val‖ : ℂ)/a.val)

theorem blaschkePhase_ne_zero (a : Disk) : blaschkePhase a ≠ 0 := by
  unfold blaschkePhase
  split_ifs with h
  · exact one_ne_zero
  · exact neg_ne_zero.mpr (div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)) h)

theorem blaschkeFactor_clear (a : Disk) {z : ℂ} (hz : ‖z‖ < 1) :
    blaschkeFactor a z*(1-conj a.val*z) = blaschkePhase a*(z-a.val) := by
  have hd : 1-conj a.val*z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    rw [norm_one,norm_mul,Complex.norm_conj] at hn
    have hpr := mul_le_mul_of_nonneg_left hz.le (norm_nonneg a.val)
    have hlt : ‖a.val‖*‖z‖ < 1 := by
      have ha : ‖a.val‖ < 1 := a.property
      linarith
    linarith
  unfold blaschkeFactor blaschkePhase
  split_ifs with ha
  · simp only [ha,map_zero,zero_mul,sub_zero,mul_one,one_mul]
  · rw [div_mul_cancel₀ _ hd]
    ring

/-- Clear the finite Blaschke denominators inside the existing Hardy model. -/
theorem finiteBlaschke_annihilator (u : BoundaryLInf) (hu : IsInner u) {n : ℕ}
    (a : Fin n → Disk) (hb : HasBlaschkeZeros u a) :
    ∃ q : Hardy, (polynomialBoundary (blaschkeNumerator a)).val = multiply u q.val := by
  classical
  obtain ⟨α,hα,hval⟩ := hb.2
  have hα0 : α ≠ 0 := by intro h; rw [h,norm_zero] at hα; norm_num at hα
  let c : ℂ := α*∏ i, blaschkePhase (a i)
  have hc : c ≠ 0 := mul_ne_zero hα0 (Finset.prod_ne_zero_iff.mpr (fun i _ => blaschkePhase_ne_zero (a i)))
  let q : Hardy := c⁻¹ • polynomialBoundary (blaschkeDenominator a)
  refine ⟨q,?_⟩
  change (polynomialBoundary (blaschkeNumerator a)).val =
    (⟨multiply u q.val,multiply_mem_hardy u hu.1 q.val q.property⟩ : Hardy).val
  apply congrArg (fun f : Hardy => f.val)
  apply hardy_analyticValue_injective (polynomialBoundary (blaschkeNumerator a))
    ⟨multiply u q.val,multiply_mem_hardy u hu.1 q.val q.property⟩
  intro z hz
  rw [analyticValue_polynomialBoundary _ hz,analyticValue_multiply u hu.1 q ⟨z,hz⟩]
  change (blaschkeNumerator a).eval z = innerValue u z*analyticValue
    (c⁻¹ • (polynomialBoundary (blaschkeDenominator a)).val) z
  rw [analyticValue_smul _ _ hz,analyticValue_polynomialBoundary _ hz]
  have he : innerValue u z*(blaschkeDenominator a).eval z = c*(blaschkeNumerator a).eval z := by
    rw [hval z hz]
    simp only [blaschkeDenominator,blaschkeNumerator,Polynomial.eval_prod,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,tprod_fintype]
    change (α*∏ i, blaschkeFactor (a i) z)*(∏ i, (1-conj (a i).val*z)) =
      (α*∏ i, blaschkePhase (a i))*(∏ i, (z-(a i).val))
    rw [mul_assoc,← Finset.prod_mul_distrib]
    have hfprod : (∏ i : Fin n, blaschkeFactor (a i) z*(1-conj (a i).val*z)) =
        ∏ i : Fin n, blaschkePhase (a i)*(z-(a i).val) :=
      Finset.prod_congr rfl (fun i _ => blaschkeFactor_clear (a i) hz)
    rw [hfprod]
    rw [Finset.prod_mul_distrib,mul_assoc]
  field_simp
  linear_combination he.symm


/-- Literal positive Fourier multiplication, including the constant mode. -/
theorem mode_multiply_fourierBasis (k i : ℕ) :
    multiply (mode (k : ℤ)) (fourierBasis (T := 1) (i : ℤ)) = fourierBasis (T := 1) ((k+i : ℕ) : ℤ) := by
  apply Lp.ext
  filter_upwards [multiply_ae (mode (k : ℤ)) (fourierBasis (T := 1) (i : ℤ)),mode_ae (k : ℤ),
    fourierBasis_ae (i : ℤ),fourierBasis_ae ((k+i : ℕ) : ℤ)] with t hm hk hi hki
  rw [hm,hk,hi,hki,Nat.cast_add,fourier_add]

theorem mode_multiply_polynomialBoundary (P : Polynomial ℂ) (k : ℕ) :
    multiply (mode (k : ℤ)) (polynomialBoundary P).val =
      ∑ i ∈ Finset.range (P.natDegree+1), P.coeff i • fourierBasis (T := 1) ((k+i : ℕ) : ℤ) := by
  change multiply (mode (k : ℤ)) (∑ i ∈ Finset.range (P.natDegree+1),
    P.coeff i • fourierBasis (T := 1) (i : ℤ)) = _
  simp only [map_sum,map_smul,mode_multiply_fourierBasis]

/-- A monic polynomial in uH² forces the actual model space to be finite dimensional. -/
theorem finiteDimensional_model_of_annihilator (u : BoundaryLInf) (hu : IsInner u)
    (P : Polynomial ℂ) (hP : P.Monic) (q : Hardy)
    (hq : (polynomialBoundary P).val = multiply u q.val) : FiniteDimensional ℂ (Model u) := by
  classical
  let d := P.natDegree
  let V : Submodule ℂ (Model u) := Submodule.span ℂ (Set.range (fun j : Fin d => projectedMode u hu j.val))
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hclosed : IsClosed (V : Set (Model u)) := V.closed_of_finiteDimensional
  have hproj (m : ℕ) : (model u).orthogonalProjectionOnto (fourierBasis (T := 1) (m : ℤ)) = projectedMode u hu m :=
    Subtype.ext (modelProjection_fourierBasis u hu m)
  have he (k : ℕ) : ∑ i ∈ Finset.range (d+1), P.coeff i • projectedMode u hu (k+i) = 0 := by
    have hz : (model u).orthogonalProjectionOnto (multiply (mode (k : ℤ)) (polynomialBoundary P).val) = 0 := by
      rw [hq,multiply_comm]
      exact modelProjection_multiply_hardy_zero u ⟨_,mode_multiply_hardy q k⟩
    rw [mode_multiply_polynomialBoundary] at hz
    simpa only [map_sum,map_smul,hproj] using hz
  have hrec (k : ℕ) : projectedMode u hu (k+d) =
      -(∑ i ∈ Finset.range d, P.coeff i • projectedMode u hu (k+i)) := by
    have hz := he k
    rw [Finset.sum_range_succ,hP.coeff_natDegree,one_smul] at hz
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)
  have hm (m : ℕ) : projectedMode u hu m ∈ V := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hmd : m < d
      · exact Submodule.subset_span ⟨⟨m,hmd⟩,rfl⟩
      · have hdm : d ≤ m := by omega
        have heq : m-d+d = m := Nat.sub_add_cancel hdm
        rw [← heq,hrec]
        apply V.neg_mem
        apply V.sum_mem
        intro i hi
        apply V.smul_mem
        apply ih
        have hid : i < d := Finset.mem_range.mp hi
        omega
  have hspan : Submodule.span ℂ (Set.range (projectedMode u hu)) ≤ V := by
    apply Submodule.span_le.mpr
    rintro y ⟨m,rfl⟩
    exact hm m
  have htop : (⊤ : Submodule ℂ (Model u)) ≤ V := by
    have hc := (Submodule.span ℂ (Set.range (projectedMode u hu))).topologicalClosure_minimal hspan hclosed
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (projectedModes_dense u hu)] at hc
    exact hc
  exact FiniteDimensional.of_surjective (K := ℂ) (V := ↥V) (V₂ := Model u) V.subtype
    (fun x => ⟨⟨x,htop trivial⟩,rfl⟩)


theorem finiteBlaschke_model_finiteDimensional (u : BoundaryLInf) (hu : IsInner u)
    {n : ℕ} (a : Fin n → Disk) (hb : HasBlaschkeZeros u a) : FiniteDimensional ℂ (Model u) := by
  obtain ⟨q,hq⟩ := finiteBlaschke_annihilator u hu a hb
  exact finiteDimensional_model_of_annihilator u hu _ (blaschkeNumerator_monic a) q hq

/-- In a finite-dimensional model, the actual dense bounded core is the whole space. -/
theorem bounded_of_finiteDimensional_model (u : BoundaryLInf) (hu : IsInner u)
    [FiniteDimensional ℂ (Model u)] (f : Model u) : IsBounded f.val := by
  let B : Submodule ℂ (Model u) := boundedL2.comap (model u).subtype
  have hc : IsClosed (B : Set (Model u)) := B.closed_of_finiteDimensional
  have hd : Dense (B : Set (Model u)) := bounded_modelCore_dense u hu
  have hf : f ∈ closure (B : Set (Model u)) := hd f
  rw [hc.closure_eq] at hf
  exact hf

/-- Every L² symbol gives an actual bounded TTO on a finite-dimensional model space. -/
theorem finiteDimensional_model_tto (u : BoundaryLInf) (hu : IsInner u)
    [FiniteDimensional ℂ (Model u)] (σ : BoundaryL2) :
    ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u σ A := by
  let J : Model u →ₗ[ℂ] boundedL2 := {
    toFun := fun f => ⟨f.val,bounded_of_finiteDimensional_model u hu f⟩
    map_add' := fun f g => Subtype.ext rfl
    map_smul' := fun c f => Subtype.ext rfl }
  let L := (model u).orthogonalProjectionOnto.toLinearMap.comp ((coreMultiply σ).comp J)
  let A := L.toContinuousLinearMap
  refine ⟨A,fun f g _hf _hg => ?_⟩
  change inner ℂ g ((model u).orthogonalProjectionOnto
    (coreMultiply σ ⟨f.val,bounded_of_finiteDimensional_model u hu f⟩)) = coreForm σ f.val g.val
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact (coreForm_eq_inner_left σ f.val g.val (bounded_of_finiteDimensional_model u hu f)).symm

/-- The full finite Blaschke conclusion, for arbitrary L² symbols and every positive p. -/
theorem finiteBlaschkeTheorem : FiniteBlaschkeConclusion := by
  intro u hu _ n a hb
  let : FiniteDimensional ℂ (Model u) := finiteBlaschke_model_finiteDimensional u hu a hb
  refine ⟨inferInstance,fun σ => ?_⟩
  obtain ⟨A,hA⟩ := finiteDimensional_model_tto u hu σ
  refine ⟨⟨A,hA⟩,⟨A,hA,(finiteDim_schatten A 2 (by norm_num)).2.1⟩,fun p hp => ?_⟩
  exact ⟨A,hA,finiteDim_schatten A p hp⟩

end TTO.Paper.Proved
