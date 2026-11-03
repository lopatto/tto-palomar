/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IndexedDiagonalFoundations
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-! Actual normalized cyclic Fourier vectors for finite polynomial Hankel factorizations.
The characters use the native ZMod-to-circle map without importing arithmetic Gauss sums. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The j-th actual character of the finite cyclic group. -/
def finiteCyclicCharacter (N : ℕ) [NeZero N] (j : ZMod N) : AddChar (ZMod N) ℂ where
  toFun k := fourier (T:=1) 1 (ZMod.toAddCircle (j*k))
  map_zero_eq_one' := by simp
  map_add_eq_mul' k l := by
    simp only [mul_add,map_add,fourier_one,AddCircle.toCircle_add,Circle.coe_mul]

@[simp] theorem finiteCyclicCharacter_apply (N : ℕ) [NeZero N] (j k : ZMod N) :
    finiteCyclicCharacter N j k=fourier (T:=1) 1 (ZMod.toAddCircle (j*k)) := rfl

theorem finiteCyclicCharacter_injective (N : ℕ) [NeZero N] :
    Function.Injective (finiteCyclicCharacter N) := by
  intro j k hjk
  have he := congrArg (fun χ : AddChar (ZMod N) ℂ => χ 1) hjk
  simp only [finiteCyclicCharacter_apply,mul_one,fourier_one] at he
  apply ZMod.toAddCircle_injective N
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ)≠0)
  exact Subtype.ext he

/-- Normalized actual Fourier characters in native finite Euclidean space. -/
def finiteFourierVector (N : ℕ) [NeZero N] (j : ZMod N) :
    EuclideanSpace ℂ (ZMod N) :=
  ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • WithLp.toLp 2 (fun k => finiteCyclicCharacter N j k)

theorem inner_finiteFourierVector (N : ℕ) [NeZero N] (j k : ZMod N) :
    inner ℂ (finiteFourierVector N j) (finiteFourierVector N k)=
      RCLike.wInner (𝕜:=ℂ) RCLike.cWeight
        (fun x => finiteCyclicCharacter N j x) (fun x => finiteCyclicCharacter N k x) := by
  have hSq : ((Real.sqrt (N : ℝ))⁻¹)^2=(N : ℝ)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [RCLike.wInner_cWeight_eq_expect,Fintype.expect_eq_sum_div_card]
  simp only [finiteFourierVector,inner_smul_left,inner_smul_right,PiLp.inner_apply,
    ZMod.card]
  have hs : (starRingEnd ℂ) ((Real.sqrt (N : ℝ) : ℂ)⁻¹)=
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by simp
  rw [hs]
  have he := congrArg (fun t : ℝ => (t : ℂ)) hSq
  push_cast at he
  rw [← mul_assoc,← pow_two,he]
  ring

theorem orthonormal_finiteFourierVector (N : ℕ) [NeZero N] :
    Orthonormal ℂ (finiteFourierVector N) := by
  classical
  rw [orthonormal_iff_ite]
  intro j k
  rw [inner_finiteFourierVector]
  have he := AddChar.wInner_cWeight_eq_boole (finiteCyclicCharacter N j) (finiteCyclicCharacter N k)
  simpa only [(finiteCyclicCharacter_injective N).eq_iff] using he

/-- The actual cyclic Fourier orthonormal basis has exactly the expected finite dimension. -/
def finiteFourierBasis (N : ℕ) [NeZero N] :
    OrthonormalBasis (ZMod N) ℂ (EuclideanSpace ℂ (ZMod N)) :=
  OrthonormalBasis.mk (orthonormal_finiteFourierVector N)
    ((orthonormal_finiteFourierVector N).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [finrank_euclideanSpace])).ge


@[simp] theorem finiteFourierBasis_apply (N : ℕ) [NeZero N] (j : ZMod N) :
    finiteFourierBasis N j=finiteFourierVector N j := by
  simp only [finiteFourierBasis,OrthonormalBasis.coe_mk]

theorem finiteCyclicCharacter_neg_index (N : ℕ) [NeZero N] (j i : ZMod N) :
    finiteCyclicCharacter N (-j) i=conj (finiteCyclicCharacter N j i) := by
  rw [← AddChar.map_neg_eq_conj]
  simp only [finiteCyclicCharacter_apply,neg_mul,mul_neg]

/-- The literal unnormalized cyclic Hankel matrix, as a native finite Hilbert operator. -/
def cyclicHankelOperator (N : ℕ) [NeZero N] (a : ZMod N → ℂ) :
    EuclideanSpace ℂ (ZMod N) →L[ℂ] EuclideanSpace ℂ (ZMod N) :=
  (Matrix.toEuclideanLin (fun i k : ZMod N => a (i+k))).toContinuousLinearMap

@[simp] theorem cyclicHankelOperator_apply (N : ℕ) [NeZero N] (a : ZMod N → ℂ)
    (x : EuclideanSpace ℂ (ZMod N)) (i : ZMod N) :
    cyclicHankelOperator N a x i=∑ k : ZMod N,a (i+k)*x k := rfl

/-- The Fourier eigenweights use the plus sign, matching polynomial evaluation at the nodes. -/
def cyclicFourierWeight (N : ℕ) [NeZero N] (a : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  ∑ t : ZMod N,a t*finiteCyclicCharacter N j t

theorem cyclicHankelOperator_fourierBasis (N : ℕ) [NeZero N] (a : ZMod N → ℂ)
    (j : ZMod N) :
    cyclicHankelOperator N a (finiteFourierBasis N j)=
      cyclicFourierWeight N a j • finiteFourierBasis N (-j) := by
  ext i
  simp only [cyclicHankelOperator_apply,finiteFourierBasis_apply,finiteFourierVector,
    PiLp.smul_apply,smul_eq_mul,finiteCyclicCharacter_neg_index]
  have he : (∑ k : ZMod N,a (i+k)*
      ((Real.sqrt (N : ℝ) : ℂ)⁻¹*finiteCyclicCharacter N j k))=
      ∑ t : ZMod N,a t*
        ((Real.sqrt (N : ℝ) : ℂ)⁻¹*finiteCyclicCharacter N j (t-i)) := by
    apply Fintype.sum_equiv (Equiv.addLeft i)
    intro k
    simp only [Equiv.coe_addLeft,add_sub_cancel_left]
  rw [he]
  simp_rw [AddChar.map_sub_eq_div,div_eq_mul_inv,AddChar.inv_apply_eq_conj]
  dsimp only [cyclicFourierWeight]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  ring


/-- Actual cyclic Hankel coordinates between the Fourier basis and its reversed basis. -/
def cyclicFourierDiagonal (N : ℕ) [NeZero N] (a : ZMod N → ℂ) :
    IndexedOperator (ZMod N) :=
  (((finiteFourierBasis N).reindex (Equiv.neg (ZMod N))).toHilbertBasis).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    cyclicHankelOperator N a ∘L
      ((finiteFourierBasis N).toHilbertBasis).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem cyclicFourierDiagonal_diagonal (N : ℕ) [NeZero N] (a : ZMod N → ℂ) :
    IndexedDiagonal (cyclicFourierWeight N a) (cyclicFourierDiagonal N a) := by
  let b := finiteFourierBasis N
  let c := b.reindex (Equiv.neg (ZMod N))
  intro j
  let : DecidableEq (ZMod N) := Classical.decEq _
  simp only [cyclicFourierDiagonal,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [HilbertBasis.repr_symm_single]
  rw [show (finiteFourierBasis N).toHilbertBasis j=finiteFourierBasis N j from
    congrFun (finiteFourierBasis N).coe_toHilbertBasis j]
  rw [cyclicHankelOperator_fourierBasis]
  have hc : finiteFourierBasis N (-j)=c.toHilbertBasis j := by
    rw [congrFun c.coe_toHilbertBasis j]
    simp only [c,b,OrthonormalBasis.reindex_apply,Equiv.neg_symm,Equiv.neg_apply]
  change c.toHilbertBasis.repr (cyclicFourierWeight N a j • finiteFourierBasis N (-j))=_
  rw [hc,map_smul,HilbertBasis.repr_self]

theorem approximationNumber_cyclicFourierDiagonal (N : ℕ) [NeZero N]
    (a : ZMod N → ℂ) (n : ℕ) :
    approximationNumber (cyclicFourierDiagonal N a) n=
      approximationNumber (cyclicHankelOperator N a) n := by
  let e := ((finiteFourierBasis N).toHilbertBasis).repr
  let f := (((finiteFourierBasis N).reindex (Equiv.neg (ZMod N))).toHilbertBasis).repr
  apply le_antisymm
  · exact approximationNumber_comp_contractions _ _ _
      (norm_isometry_clm_le_one f.toLinearIsometry)
      (norm_isometry_clm_le_one e.symm.toLinearIsometry) n
  · have h := approximationNumber_comp_contractions
      f.symm.toContinuousLinearEquiv.toContinuousLinearMap (cyclicFourierDiagonal N a)
      e.toContinuousLinearEquiv.toContinuousLinearMap
      (norm_isometry_clm_le_one f.symm.toLinearIsometry)
      (norm_isometry_clm_le_one e.toLinearIsometry) n
    have he : f.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        cyclicFourierDiagonal N a ∘L e.toContinuousLinearEquiv.toContinuousLinearMap=
          cyclicHankelOperator N a := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [cyclicFourierDiagonal,ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      change f.symm (f (cyclicHankelOperator N a (e.symm (e x))))=_
      rw [e.symm_apply_apply,f.symm_apply_apply]
    rw [he] at h
    exact h

/-- Exact finite cyclic Hankel singular-value power sum for EVERY positive real p. -/
theorem cyclicHankelOperator_power_sum (N : ℕ) [NeZero N] (a : ZMod N → ℂ)
    (p : ℝ) (hp : 0<p) :
    (∑' n : ℕ,(approximationNumber (cyclicHankelOperator N a) n : ℝ)^p)=
      ∑ j : ZMod N,‖cyclicFourierWeight N a j‖^p := by
  have hw : summableValues p (cyclicFourierWeight N a) := by
    unfold summableValues
    exact (hasSum_fintype (fun j : ZMod N => ‖cyclicFourierWeight N a j‖^p)).summable
  have he := indexedDiagonal_power_sum_eq (cyclicFourierWeight N a)
    (cyclicFourierDiagonal N a) (cyclicFourierDiagonal_diagonal N a) p hp hw
  simpa only [approximationNumber_cyclicFourierDiagonal,tsum_fintype] using he

theorem cyclicHankelOperator_schattenNorm_rpow (N : ℕ) [NeZero N] (a : ZMod N → ℂ)
    (p : ℝ) (hp : 0<p) :
    schattenNorm p (cyclicHankelOperator N a)^p=
      ∑ j : ZMod N,‖cyclicFourierWeight N a j‖^p := by
  rw [schattenNorm_rpow hp]
  exact cyclicHankelOperator_power_sum N a p hp

end TTO.Paper.Proved
