/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.FiniteSchattenInterpolationFoundations
public import TTO.TriangularFoundations
public import TTO.SchattenAveragingFoundations

/-! Explicit finite block multipliers and the Cotlar route to uniform triangular bounds. -/

@[expose] public section
noncomputable section
open Filter Finset Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

section BlockAlgebra
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : ℕ}

/-- An actual finite orthogonal block decomposition; zero blocks and N=0 are retained. -/
structure TriangularBlocks (Q : Fin N → H →L[ℂ] H) : Prop where
  sum_eq : (∑ i, Q i)=ContinuousLinearMap.id ℂ H
  adjoint_eq : ∀ i, (Q i).adjoint=Q i
  idempotent : ∀ i, Q i ∘L Q i=Q i
  orthogonal : ∀ i j, i≠j → Q i ∘L Q j=0

def operatorBlock (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) (i j : Fin N) :
    H →L[ℂ] H := Q i ∘L A ∘L Q j

theorem block_projection_apply (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (i j : Fin N) (x : H) :
    Q i (Q j x)=if i=j then Q i x else 0 := by
  by_cases hij : i=j
  · subst j
    simpa only [ite_true,ContinuousLinearMap.comp_apply] using
      congrArg (fun T : H →L[ℂ] H => T x) (hQ.idempotent i)
  · simpa only [hij,ite_false,ContinuousLinearMap.comp_apply,_root_.zero_apply] using
      congrArg (fun T : H →L[ℂ] H => T x) (hQ.orthogonal i j hij)

theorem sum_blocks_apply (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q) (x : H) :
    (∑ i, Q i x)=x := by
  simpa only [_root_.sum_apply,ContinuousLinearMap.id_apply] using
    congrArg (fun T : H →L[ℂ] H => T x) hQ.sum_eq

def blockMultiplier (Q : Fin N → H →L[ℂ] H) (m : Fin N → Fin N → ℂ)
    (A : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, ∑ j, m i j • operatorBlock Q A i j

def blockMultiplierLinear (Q : Fin N → H →L[ℂ] H) (m : Fin N → Fin N → ℂ) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := blockMultiplier Q m
  map_add' A B := by
    simp only [blockMultiplier,operatorBlock,ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp,smul_add,sum_add_distrib]
  map_smul' c A := by
    simp only [blockMultiplier,operatorBlock,ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.smul_comp,smul_smul,Finset.smul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [mul_comm]
    rfl

theorem operatorBlock_multiplier (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (m : Fin N → Fin N → ℂ) (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (blockMultiplier Q m A) i j=m i j • operatorBlock Q A i j := by
  ext x
  simp only [operatorBlock,blockMultiplier,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  simp_rw [block_projection_apply Q hQ]
  simp only [apply_ite,map_zero,smul_zero]
  simp

theorem operatorBlock_ext (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A B : H →L[ℂ] H) (h : ∀ i j, operatorBlock Q A i j=operatorBlock Q B i j) :
    A=B := by
  ext x
  calc
    A x = ∑ i, ∑ j, Q i (A (Q j x)) := by
      simp_rw [← map_sum,sum_blocks_apply Q hQ]
    _ = ∑ i, ∑ j, Q i (B (Q j x)) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      exact congrArg (fun T : H →L[ℂ] H => T x) (h i j)
    _ = B x := by
      simp_rw [← map_sum, sum_blocks_apply Q hQ]

def triangularSign (i j : Fin N) : ℂ := if j < i then 1 else if i < j then -1 else 0

def triangularHilbert (Q : Fin N → H →L[ℂ] H) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  blockMultiplierLinear Q triangularSign

def blockPinching (Q : Fin N → H →L[ℂ] H) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  blockMultiplierLinear Q (fun i j => if i=j then 1 else 0)

theorem triangularSign_cotlar (i j k : Fin N) :
    triangularSign i k*triangularSign k j =
      triangularSign i j*(triangularSign i k+triangularSign k j)-1+
        (if i=k ∧ k=j then 1 else 0) := by
  unfold triangularSign
  split_ifs <;> norm_num <;> omega

omit [CompleteSpace H] in
theorem operatorBlock_add (Q : Fin N → H →L[ℂ] H) (A B : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (A+B) i j=operatorBlock Q A i j+operatorBlock Q B i j := by
  ext x
  simp only [operatorBlock,ContinuousLinearMap.comp_apply,add_apply,map_add]

omit [CompleteSpace H] in
theorem operatorBlock_sub (Q : Fin N → H →L[ℂ] H) (A B : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (A-B) i j=operatorBlock Q A i j-operatorBlock Q B i j := by
  ext x
  simp only [operatorBlock,ContinuousLinearMap.comp_apply,sub_apply,map_sub]

theorem operatorBlock_product (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A B : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (A ∘L B) i j=
      ∑ k, operatorBlock Q A i k ∘L operatorBlock Q B k j := by
  ext x
  simp only [operatorBlock,ContinuousLinearMap.comp_apply,_root_.sum_apply]
  simp_rw [block_projection_apply Q hQ]
  simp only [ite_true]
  simp_rw [← map_sum,sum_blocks_apply Q hQ]

def diagonalSign (i j : Fin N) : ℂ := if i=j then 1 else 0

theorem triangularSign_cotlar_diagonal (i j k : Fin N) :
    triangularSign i k*triangularSign k j =
      triangularSign i j*(triangularSign i k+triangularSign k j)-1+
        diagonalSign i k*diagonalSign k j := by
  rw [triangularSign_cotlar]
  congr 1
  unfold diagonalSign
  split_ifs <;> simp_all

theorem operatorBlock_hilbert (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (triangularHilbert Q A) i j=triangularSign i j • operatorBlock Q A i j :=
  operatorBlock_multiplier Q hQ triangularSign A i j

theorem operatorBlock_pinching (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (blockPinching Q A) i j=diagonalSign i j • operatorBlock Q A i j :=
  operatorBlock_multiplier Q hQ (fun i j => if i=j then 1 else 0) A i j

/-- The actual finite-block Cotlar identity, valid also for noncommuting block entries. -/
theorem triangularHilbert_cotlar (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A B : H →L[ℂ] H) :
    triangularHilbert Q A ∘L triangularHilbert Q B =
      triangularHilbert Q (triangularHilbert Q A ∘L B+A ∘L triangularHilbert Q B) -
        A ∘L B + blockPinching Q A ∘L blockPinching Q B := by
  apply operatorBlock_ext Q hQ
  intro i j
  simp only [operatorBlock_add,operatorBlock_sub,operatorBlock_hilbert Q hQ,
    operatorBlock_product Q hQ,operatorBlock_pinching Q hQ]
  simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
  rw [← sum_add_distrib,Finset.smul_sum,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [mul_comm (triangularSign k j) (triangularSign i k),
    triangularSign_cotlar_diagonal i j k,
    mul_comm (diagonalSign i k) (diagonalSign k j)]
  simp only [add_smul,sub_smul,mul_smul,one_smul,smul_add]

def blockSign (ε : Fin N → Bool) (i : Fin N) : ℂ := if ε i then 1 else -1

@[simp] theorem norm_blockSign (ε : Fin N → Bool) (i : Fin N) : ‖blockSign ε i‖=1 := by
  unfold blockSign
  cases ε i <;> norm_num

@[simp] theorem blockSign_mul_self (ε : Fin N → Bool) (i : Fin N) :
    blockSign ε i*blockSign ε i=1 := by
  unfold blockSign
  cases ε i <;> norm_num

def flipBlockSign (i : Fin N) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun ε := Function.update ε i (!(ε i))
  invFun ε := Function.update ε i (!(ε i))
  left_inv ε := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update,hj]
  right_inv ε := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Function.update,hj]

theorem blockSign_flip_self (ε : Fin N → Bool) (i : Fin N) :
    blockSign (flipBlockSign i ε) i = -blockSign ε i := by
  simp only [blockSign,flipBlockSign,Equiv.coe_fn_mk]
  simp only [Function.update_self]
  cases ε i <;> norm_num

theorem blockSign_flip_other (ε : Fin N → Bool) (i j : Fin N) (hji : j≠i) :
    blockSign (flipBlockSign i ε) j=blockSign ε j := by
  simp [blockSign,flipBlockSign,Function.update,hji]

/-- Exact finite sign cancellation; no probability or independence theorem is assumed. -/
theorem sum_blockSign_product (i j : Fin N) :
    (∑ ε : Fin N → Bool, blockSign ε i*blockSign ε j) =
      if i=j then (Fintype.card (Fin N → Bool) : ℂ) else 0 := by
  by_cases hij : i=j
  · subst j
    simp only [blockSign_mul_self,ite_true,sum_const,nsmul_eq_mul,mul_one]
    simp
  · rw [ite_eq_right hij]
    let S : ℂ := ∑ ε : Fin N → Bool, blockSign ε i*blockSign ε j
    have hs : S = -S := by
      calc
        S = ∑ ε : Fin N → Bool, blockSign (flipBlockSign i ε) i *
            blockSign (flipBlockSign i ε) j :=
          (Equiv.sum_comp (flipBlockSign i) (fun ε => blockSign ε i*blockSign ε j)).symm
        _ = ∑ ε : Fin N → Bool, -(blockSign ε i*blockSign ε j) := by
          apply sum_congr rfl
          intro ε hε
          rw [blockSign_flip_self,blockSign_flip_other ε i j (Ne.symm hij),neg_mul]
        _ = -S := sum_neg_distrib _
    have htwo : (2 : ℂ)*S=0 := by linear_combination hs
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

def signBlockOperator (Q : Fin N → H →L[ℂ] H) (ε : Fin N → Bool) : H →L[ℂ] H :=
  ∑ i, blockSign ε i • Q i

theorem projection_signBlock_apply (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (ε : Fin N → Bool) (i : Fin N) (x : H) :
    Q i (signBlockOperator Q ε x)=blockSign ε i • Q i x := by
  simp only [signBlockOperator,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  simp_rw [block_projection_apply Q hQ]
  simp only [smul_ite,smul_zero]
  simp

theorem signBlock_projection_apply (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (ε : Fin N → Bool) (i : Fin N) (x : H) :
    signBlockOperator Q ε (Q i x)=blockSign ε i • Q i x := by
  simp only [signBlockOperator,_root_.sum_apply,_root_.smul_apply]
  simp_rw [block_projection_apply Q hQ]
  simp only [smul_ite,smul_zero]
  simp

theorem operatorBlock_signConjugate (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (ε : Fin N → Bool) (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (signBlockOperator Q ε ∘L A ∘L signBlockOperator Q ε) i j =
      (blockSign ε i*blockSign ε j) • operatorBlock Q A i j := by
  ext x
  simp only [operatorBlock,ContinuousLinearMap.comp_apply,projection_signBlock_apply Q hQ,
    signBlock_projection_apply Q hQ,map_smul,_root_.smul_apply,smul_smul]
  rw [mul_comm]

theorem norm_signBlockOperator_le (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (ε : Fin N → Bool) : ‖signBlockOperator Q ε‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have ho := orthogonal_block_ranges Q hQ.adjoint_eq hQ.orthogonal
  have hsign : ‖signBlockOperator Q ε x‖^2 = ∑ i, ‖Q i x‖^2 := by
    rw [signBlockOperator,_root_.sum_apply]
    have h := norm_sum_sq_of_orthogonal univ (fun i => blockSign ε i • Q i x)
      (fun i hi j hj hij => by
        rw [inner_smul_left,inner_smul_right,ho i j hij x x,mul_zero,mul_zero])
    simpa only [_root_.smul_apply,norm_smul,norm_blockSign,one_mul] using h
  have hplain : ‖x‖^2=∑ i, ‖Q i x‖^2 := by
    simpa only [sum_blocks_apply Q hQ] using
      norm_sum_sq_of_orthogonal univ (fun i => Q i x) (fun i hi j hj hij => ho i j hij x x)
  rw [one_mul]
  exact le_of_sq_le_sq (hsign.trans hplain.symm).le (norm_nonneg x)

omit [CompleteSpace H] in
theorem operatorBlock_sum {ι : Type*} (s : Finset ι) (Q : Fin N → H →L[ℂ] H)
    (A : ι → H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (∑ a ∈ s, A a) i j=∑ a ∈ s, operatorBlock Q (A a) i j := by
  ext x
  simp only [operatorBlock,_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]

omit [CompleteSpace H] in
theorem operatorBlock_smul (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) (c : ℂ) (i j : Fin N) :
    operatorBlock Q (c • A) i j=c • operatorBlock Q A i j := by
  ext x
  simp only [operatorBlock,_root_.smul_apply,ContinuousLinearMap.comp_apply,map_smul]

/-- Literal diagonal pinching is the finite average of the explicit sign conjugations. -/
theorem blockPinching_sign_average (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) :
    blockPinching Q A =
      ∑ ε : Fin N → Bool, (Fintype.card (Fin N → Bool) : ℂ)⁻¹ •
        (signBlockOperator Q ε ∘L A ∘L signBlockOperator Q ε) := by
  apply operatorBlock_ext Q hQ
  intro i j
  rw [operatorBlock_pinching Q hQ,operatorBlock_sum]
  simp only [operatorBlock_smul,operatorBlock_signConjugate Q hQ,smul_smul]
  rw [← sum_smul,← mul_sum,sum_blockSign_product]
  have hn : (Fintype.card (Fin N → Bool) : ℂ)≠0 := by exact_mod_cast
    (Fintype.card_ne_zero (α := Fin N → Bool))
  by_cases hij : i=j
  · simp only [diagonalSign,hij,ite_true,inv_mul_cancel₀ hn,one_smul]
  · simp only [diagonalSign,hij,ite_false,mul_zero,zero_smul]

/-- Diagonal block pinching contracts every actual Schatten norm with p≥1.
The proof uses the explicit finite sign average and the proved ordinary convex ball. -/
theorem schatten_blockPinching (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (p : ℝ) (hp : 1 ≤ p) (A : H →L[ℂ] H) (hA : Schatten p A) :
    Schatten p (blockPinching Q A) ∧ schattenNorm p (blockPinching Q A) ≤ schattenNorm p A := by
  let K : ℕ := Fintype.card (Fin N → Bool)
  have hK : (K : ℝ)≠0 := by exact_mod_cast (Fintype.card_ne_zero (α := Fin N → Bool))
  have hw0 (ε : Fin N → Bool) (hε : ε ∈ Finset.univ) : 0 ≤ (K : ℝ)⁻¹ := by positivity
  have hw : (∑ _ : Fin N → Bool, (K : ℝ)⁻¹)=1 := by
    simp only [sum_const,card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hK
  have hz (ε : Fin N → Bool) (hε : ε ∈ Finset.univ) :
      signBlockOperator Q ε ∘L A ∘L signBlockOperator Q ε ∈
        schattenClosedBall (H := H) p (schattenNorm p A) := by
    have hU := norm_signBlockOperator_le Q hQ ε
    refine ⟨schatten_comp hA _ _,?_⟩
    have h := schattenNorm_le_of_approx_le hA 1 zero_le_one (fun n => by
      simpa only [one_mul] using NNReal.coe_le_coe.mpr
        (approximationNumber_comp_contractions _ A _ hU hU n))
    simpa only [one_mul] using h
  have hmem := (convex_schattenClosedBall (H := H) p hp (schattenNorm p A)).sum_mem hw0 hw hz
  have he : blockPinching Q A =
      ∑ ε : Fin N → Bool, (K : ℝ)⁻¹ •
        (signBlockOperator Q ε ∘L A ∘L signBlockOperator Q ε) := by
    rw [blockPinching_sign_average Q hQ A]
    apply sum_congr rfl
    intro ε hε
    have hc : (K : ℂ)⁻¹=(((K : ℝ)⁻¹ : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_inv (K : ℝ)).symm
    rw [show (Fintype.card (Fin N → Bool) : ℂ)⁻¹=(K : ℂ)⁻¹ from rfl,hc]
    exact algebraMap_smul ℂ ((K : ℝ)⁻¹) _
  rw [← he] at hmem
  exact hmem

theorem operatorBlock_adjoint (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q A.adjoint i j=(operatorBlock Q A j i).adjoint := by
  simp only [operatorBlock,ContinuousLinearMap.adjoint_comp,hQ.adjoint_eq,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace H] in
theorem operatorBlock_neg (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (-A) i j = -operatorBlock Q A i j := by
  ext x
  simp only [operatorBlock,ContinuousLinearMap.comp_apply,_root_.neg_apply,map_neg]

theorem triangularHilbert_adjoint (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) :
    triangularHilbert Q A.adjoint = -(triangularHilbert Q A).adjoint := by
  apply operatorBlock_ext Q hQ
  intro i j
  simp only [operatorBlock_hilbert Q hQ,operatorBlock_neg,operatorBlock_adjoint Q hQ]
  unfold triangularSign
  split_ifs <;> simp_all
  omega

theorem blockPinching_adjoint (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) :
    blockPinching Q A.adjoint = (blockPinching Q A).adjoint := by
  apply operatorBlock_ext Q hQ
  intro i j
  simp only [operatorBlock_pinching Q hQ,operatorBlock_adjoint Q hQ]
  unfold diagonalSign
  split_ifs <;> simp_all

omit [CompleteSpace H] in
theorem triangularCut_eq_multiplier (Q : Fin N → H →L[ℂ] H) (A : H →L[ℂ] H) :
    triangularCut Q A=blockMultiplier Q (fun i j => if j < i then 1 else 0) A := by
  simp only [triangularCut,blockMultiplier,operatorBlock]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem operatorBlock_cut (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (i j : Fin N) :
    operatorBlock Q (triangularCut Q A) i j=
      (if j < i then 1 else 0 : ℂ) • operatorBlock Q A i j := by
  rw [triangularCut_eq_multiplier]
  exact operatorBlock_multiplier Q hQ _ A i j

/-- The signed transform is exactly strict lower minus strict upper, with literal frozen cuts. -/
theorem triangularHilbert_eq_cut_sub_adjoint
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q) (A : H →L[ℂ] H) :
    triangularHilbert Q A=triangularCut Q A-(triangularCut Q A.adjoint).adjoint := by
  apply operatorBlock_ext Q hQ
  intro i j
  simp only [operatorBlock_hilbert Q hQ,operatorBlock_sub,operatorBlock_adjoint Q hQ,
    operatorBlock_cut Q hQ]
  unfold triangularSign
  split_ifs <;> simp_all
  omega

theorem schattenNorm_adjoint_eq (A : H →L[ℂ] H) (p : ℝ) :
    schattenNorm p A.adjoint=schattenNorm p A := by
  simp only [schattenNorm,approximationNumber_adjoint]

/-- The existing exact p=2 triangular contraction gives a dimension-free signed base bound. -/
theorem schatten_triangularHilbert_two
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (hA : Schatten 2 A) :
    Schatten 2 (triangularHilbert Q A) ∧
      schattenNorm 2 (triangularHilbert Q A) ≤ 2*schattenNorm 2 A := by
  have hcut := triangularConstant_two H N Q hQ.sum_eq
    (fun i => ⟨hQ.adjoint_eq i,hQ.idempotent i⟩) hQ.orthogonal A hA
  have hAdj : Schatten 2 A.adjoint := (schatten_adjoint_iff A 2).mpr hA
  have hupper := triangularConstant_two H N Q hQ.sum_eq
    (fun i => ⟨hQ.adjoint_eq i,hQ.idempotent i⟩) hQ.orthogonal A.adjoint hAdj
  have hu : Schatten 2 (triangularCut Q A.adjoint).adjoint :=
    (schatten_adjoint_iff _ 2).mpr hupper.1
  rw [triangularHilbert_eq_cut_sub_adjoint Q hQ A]
  refine ⟨by simpa only [sub_eq_add_neg] using schatten_add hcut.1 (schatten_neg hu),?_⟩
  have ht := schattenNorm_add_le_sharp 2 (by norm_num) (triangularCut Q A)
    (-(triangularCut Q A.adjoint).adjoint) hcut.1 (schatten_neg hu)
  have hn : schattenNorm 2 (-(triangularCut Q A.adjoint).adjoint)=
      schattenNorm 2 (triangularCut Q A.adjoint) := by
    simp only [schattenNorm,approximationNumber_neg,approximationNumber_adjoint]
  rw [hn] at ht
  have hupper' : schattenNorm 2 (triangularCut Q A.adjoint) ≤ schattenNorm 2 A := by
    simpa only [one_mul,schattenNorm_adjoint_eq] using hupper.2
  have hcut' : schattenNorm 2 (triangularCut Q A) ≤ schattenNorm 2 A := by
    simpa only [one_mul] using hcut.2
  rw [sub_eq_add_neg]
  linarith

/-- Positive-square form of the exact Cotlar identity. -/
theorem triangularHilbert_square (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) :
    triangularHilbert Q A ∘L (triangularHilbert Q A).adjoint =
      A ∘L A.adjoint-blockPinching Q A ∘L (blockPinching Q A).adjoint -
        triangularHilbert Q (triangularHilbert Q A ∘L A.adjoint -
          A ∘L (triangularHilbert Q A).adjoint) := by
  have h := triangularHilbert_cotlar Q hQ A A.adjoint
  rw [triangularHilbert_adjoint Q hQ,blockPinching_adjoint Q hQ,
    ContinuousLinearMap.comp_neg,ContinuousLinearMap.comp_neg,← sub_eq_add_neg] at h
  have hh := congrArg (fun T : H →L[ℂ] H => -T) h
  convert hh using 1 <;> abel

end BlockAlgebra
section FiniteProductBounds
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem approximationNumber_zero_of_finrank_le (A : H →L[ℂ] H) (n : ℕ)
    (hn : Module.finrank ℂ H ≤ n) : approximationNumber A n=0 := by
  apply approximationNumber_eq_zero_of_rank_le A n
  have hr : A.rank ≤ (Module.finrank ℂ H : Cardinal) :=
    (LinearMap.rank_le_domain _).trans_eq (Module.finrank_eq_rank ℂ H).symm
  exact hr.trans (by exact_mod_cast hn)

omit [CompleteSpace H] in
theorem finite_schatten_power_sum (A : H →L[ℂ] H) (p : ℝ) (hp : 0 < p)
    (M : ℕ) (hM : Module.finrank ℂ H ≤ M) :
    (∑' n, (approximationNumber A n : ℝ)^p)=
      ∑ n ∈ range M, (approximationNumber A n : ℝ)^p := by
  apply tsum_eq_sum
  intro n hn
  rw [approximationNumber_zero_of_finrank_le A n (by
    have hMn : M ≤ n := by simpa only [Finset.mem_range,not_lt] using hn
    omega)]
  simp only [NNReal.coe_zero,Real.zero_rpow hp.ne']

theorem finite_sum_even_odd (f : ℕ → ℝ) (d : ℕ) :
    (∑ n ∈ range (2*d), f n)=
      (∑ n ∈ range d, f (2*n))+(∑ n ∈ range d, f (2*n+1)) := by
  induction d with
  | zero => simp only [mul_zero,range_zero,sum_empty,add_zero]
  | succ d ih =>
    rw [show 2*(d+1)=(2*d+1)+1 by omega, sum_range_succ,sum_range_succ,ih,
      sum_range_succ,sum_range_succ]
    ring

omit [CompleteSpace H] in
/-- A dimension-free coarse product Holder bound, sufficient for the Cotlar recurrence.
It is derived from actual approximation-number products and scalar Cauchy–Schwarz. -/
theorem finite_schatten_product_bound (p : ℝ) (hp : 1 ≤ p) (A B : H →L[ℂ] H) :
    schattenNorm p (A ∘L B) ≤ 2*schattenNorm (2*p) A*schattenNorm (2*p) B := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let d := Module.finrank ℂ H
  have heven (n : ℕ) :
      (approximationNumber (A ∘L B) (2*n) : ℝ) ≤
        (approximationNumber A n : ℝ)*(approximationNumber B n : ℝ) := by
    exact_mod_cast (show approximationNumber (A ∘L B) (2*n) ≤
      approximationNumber A n*approximationNumber B n by
        simpa only [two_mul] using approximationNumber_comp_add A B n n)
  have hodd (n : ℕ) :
      (approximationNumber (A ∘L B) (2*n+1) : ℝ) ≤
        (approximationNumber A n : ℝ)*(approximationNumber B n : ℝ) :=
    (NNReal.coe_le_coe.mpr (approximationNumber_antitone (A ∘L B) (Nat.le_succ (2*n)))).trans (heven n)
  have hs : schattenNorm p (A ∘L B)^p ≤ 2*
      ∑ n ∈ range d, ((approximationNumber A n : ℝ)*(approximationNumber B n : ℝ))^p := by
    rw [schattenNorm_rpow hp0,finite_schatten_power_sum _ p hp0 (2*d) (by dsimp [d]; omega),
      finite_sum_even_odd]
    rw [two_mul]
    exact add_le_add
      (sum_le_sum (fun n hn => Real.rpow_le_rpow (NNReal.coe_nonneg _) (heven n) hp0.le))
      (sum_le_sum (fun n hn => Real.rpow_le_rpow (NNReal.coe_nonneg _) (hodd n) hp0.le))
  have hpowA : (∑ n ∈ range d, ((approximationNumber A n : ℝ)^p)^2)=
      schattenNorm (2*p) A^(2*p) := by
    rw [schattenNorm_rpow (by positivity : 0 < 2*p),finite_schatten_power_sum A (2*p)
      (by positivity) d le_rfl]
    apply sum_congr rfl
    intro n hn
    rw [← Real.rpow_mul_natCast (NNReal.coe_nonneg _) p 2]
    congr 1
    ring
  have hpowB : (∑ n ∈ range d, ((approximationNumber B n : ℝ)^p)^2)=
      schattenNorm (2*p) B^(2*p) := by
    rw [schattenNorm_rpow (by positivity : 0 < 2*p),finite_schatten_power_sum B (2*p)
      (by positivity) d le_rfl]
    apply sum_congr rfl
    intro n hn
    rw [← Real.rpow_mul_natCast (NNReal.coe_nonneg _) p 2]
    congr 1
    ring
  have hc := Real.inner_le_Lp_mul_Lq_of_nonneg (s := range d)
    (f := fun n => (approximationNumber A n : ℝ)^p)
    (g := fun n => (approximationNumber B n : ℝ)^p) Real.HolderConjugate.two_two
    (fun n hn => Real.rpow_nonneg (NNReal.coe_nonneg _) p)
    (fun n hn => Real.rpow_nonneg (NNReal.coe_nonneg _) p)
  simp only [Real.rpow_two] at hc
  rw [hpowA,hpowB] at hc
  have hAA : (schattenNorm (2*p) A^(2*p))^(1/(2 : ℝ))=schattenNorm (2*p) A^p := by
    rw [← Real.rpow_mul (Reduction.schattenNorm_nonneg (2*p) A)]
    congr 1
    ring
  have hBB : (schattenNorm (2*p) B^(2*p))^(1/(2 : ℝ))=schattenNorm (2*p) B^p := by
    rw [← Real.rpow_mul (Reduction.schattenNorm_nonneg (2*p) B)]
    congr 1
    ring
  rw [hAA,hBB] at hc
  have hmul : (∑ n ∈ range d,
      ((approximationNumber A n : ℝ)*(approximationNumber B n : ℝ))^p) =
      ∑ n ∈ range d, (approximationNumber A n : ℝ)^p*(approximationNumber B n : ℝ)^p := by
    apply sum_congr rfl
    intro n hn
    exact Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  rw [hmul] at hs
  have hmain := hs.trans (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
  have htwo : (2 : ℝ) ≤ 2^p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hAn := Reduction.schattenNorm_nonneg (2*p) A
  have hBn := Reduction.schattenNorm_nonneg (2*p) B
  have h2A : 0 ≤ 2*schattenNorm (2*p) A := mul_nonneg (by norm_num) hAn
  apply (Real.rpow_le_rpow_iff (Reduction.schattenNorm_nonneg p _)
    (mul_nonneg h2A hBn) hp0).mp
  rw [Real.mul_rpow h2A (Reduction.schattenNorm_nonneg (2*p) B),
    Real.mul_rpow (by norm_num) (Reduction.schattenNorm_nonneg (2*p) A)]
  apply hmain.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hAn p)) (Real.rpow_nonneg hBn p)

theorem finiteSequenceDiagonal_single_outside {M : ℕ} (c : Fin M → ℂ) (n : ℕ) (hn : M ≤ n) :
    finiteSequenceDiagonal c (lp.single 2 n (1 : ℂ))=0 := by
  have h := diagonalTruncation_isDiagonal (finiteSequenceWeights c) (range M) n
  simpa [finiteSequenceDiagonal,finiteSequenceWeights,not_lt.mpr hn] using h

omit [FiniteDimensional ℂ H] in
/-- An actual finite orthonormal eigenbasis identifies all approximation infima with the
native zero-extended sequence diagonal; zero eigenvalues are retained. -/
theorem approximationNumber_of_basis_diagonal
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
    (A : H →L[ℂ] H) (c : Fin (Module.finrank ℂ H) → ℂ)
    (ha : ∀ i, A (b i)=c i • b i) (n : ℕ) :
    approximationNumber A n=approximationNumber (finiteSequenceDiagonal c) n := by
  let R := finiteAnalysis (fun i => b i)
  have hR : ‖R‖ ≤ 1 := norm_finiteAnalysis_le_one (fun i => b i)
    (fun x => (b.sum_sq_norm_inner_right x).le)
  have hR' : ‖R.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map R).trans_le hR
  have hAf : A=R.adjoint ∘L finiteSequenceDiagonal c ∘L R := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    change A (b i)=R.adjoint (finiteSequenceDiagonal c (R (b i)))
    rw [show R (b i)=lp.single 2 i.val (1 : ℂ) from finiteAnalysis_orthonormal_column _ b.orthonormal i,
      finiteSequenceDiagonal_single,map_smul,finiteAnalysis_adjoint_single]
    exact ha i
  have hDf : finiteSequenceDiagonal c=R ∘L A ∘L R.adjoint := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞)≠⊤)
    intro k
    apply ContinuousLinearMap.ext_ring
    by_cases hk : k<Module.finrank ℂ H
    · let i : Fin (Module.finrank ℂ H) := ⟨k,hk⟩
      change finiteSequenceDiagonal c (lp.single 2 i.val (1 : ℂ))=
        R (A (R.adjoint (lp.single 2 i.val (1 : ℂ))))
      rw [finiteSequenceDiagonal_single,finiteAnalysis_adjoint_single,ha,map_smul,
        finiteAnalysis_orthonormal_column _ b.orthonormal]
    · change finiteSequenceDiagonal c (lp.single 2 k (1 : ℂ))=
        R (A (R.adjoint (lp.single 2 k (1 : ℂ))))
      rw [finiteSequenceDiagonal_single_outside c k (not_lt.mp hk),
        finiteAnalysis_adjoint_single_outside _ k (not_lt.mp hk),map_zero,map_zero]
  apply le_antisymm
  · calc
      _ = approximationNumber (R.adjoint ∘L finiteSequenceDiagonal c ∘L R) n :=
        congrArg (fun T => approximationNumber T n) hAf
      _ ≤ _ := approximationNumber_comp_contractions R.adjoint _ R hR' hR n
  · calc
      _ = approximationNumber (R ∘L A ∘L R.adjoint) n :=
        congrArg (fun T => approximationNumber T n) hDf
      _ ≤ _ := approximationNumber_comp_contractions R A R.adjoint hR hR' n

omit [FiniteDimensional ℂ H] in
theorem schattenNorm_of_basis_diagonal
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
    (A : H →L[ℂ] H) (c : Fin (Module.finrank ℂ H) → ℂ)
    (ha : ∀ i, A (b i)=c i • b i) (p : ℝ) (hp : 0 < p) :
    schattenNorm p A=FiniteThorin.vectorNorm p c := by
  simpa only [schattenNorm,approximationNumber_of_basis_diagonal b A c ha] using
    schattenNorm_finiteSequenceDiagonal c p hp

/-- The literal positive square has the expected exact Schatten gauge. -/
theorem finite_schatten_adjoint_square (A : H →L[ℂ] H) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (A.adjoint ∘L A)=schattenNorm (2*p) A^2 := by
  let b := gramBasis A
  let c : Fin (Module.finrank ℂ H) → ℂ := fun i => ((‖A (b i)‖^2 : ℝ) : ℂ)
  have ha (i) : (A.adjoint ∘L A) (b i)=c i • b i := by
    have h := (gramSymmetric A).apply_eigenvectorBasis rfl i
    change (A.adjoint ∘L A) (b i)=
      ((gramSymmetric A).eigenvalues rfl i : ℂ) • b i at h
    rw [← gramBasis_norm_sq A i] at h
    exact h
  rw [schattenNorm_of_basis_diagonal b _ c ha p hp]
  unfold FiniteThorin.vectorNorm schattenNorm
  rw [finiteGram_power_sum A (2*p) (by positivity)]
  have hsum : (∑ i, ‖c i‖^p)=∑ i, ‖A (gramBasis A i)‖^(2*p) := by
    apply sum_congr rfl
    intro i hi
    simp only [c,b,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg ‖A (gramBasis A i)‖)]
    rw [← Real.rpow_natCast_mul (norm_nonneg (A (gramBasis A i))) 2 p]
    norm_num
  rw [hsum,← Real.rpow_mul_natCast
    (sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (A (gramBasis A i))) (2*p)))
      (1/(2*p)) 2]
  congr 1
  field_simp
  ring

theorem finite_schatten_square_adjoint (A : H →L[ℂ] H) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (A ∘L A.adjoint)=schattenNorm (2*p) A^2 := by
  simpa only [ContinuousLinearMap.adjoint_adjoint,schattenNorm,approximationNumber_adjoint]
    using finite_schatten_adjoint_square A.adjoint p hp

theorem finite_schatten_sub_bound (p : ℝ) (hp : 1 ≤ p) (A B : H →L[ℂ] H) :
    schattenNorm p (A-B) ≤ schattenNorm p A+schattenNorm p B := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  simpa only [sub_eq_add_neg,schattenNorm,approximationNumber_neg] using
    schattenNorm_add_le_sharp p hp A (-B) (finiteDim_schatten A p hp0)
      (schatten_neg (finiteDim_schatten B p hp0))

/-- Cotlar doubles a dimension-free signed-transform norm bound with an explicit finite constant. -/
theorem finite_triangularHilbert_doubling {N : ℕ}
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (p C : ℝ) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hBound : ∀ A : H →L[ℂ] H,
      schattenNorm p (triangularHilbert Q A) ≤ C*schattenNorm p A)
    (A : H →L[ℂ] H) :
    schattenNorm (2*p) (triangularHilbert Q A) ≤
      (4*C+2)*schattenNorm (2*p) A := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let X := triangularHilbert Q A
  let D := blockPinching Q A
  let x := schattenNorm (2*p) X
  let a := schattenNorm (2*p) A
  have hx : 0 ≤ x := Reduction.schattenNorm_nonneg _ _
  have ha : 0 ≤ a := Reduction.schattenNorm_nonneg _ _
  have hD : schattenNorm (2*p) D ≤ a :=
    (schatten_blockPinching Q hQ (2*p) (by linarith) A
      (finiteDim_schatten A (2*p) (by positivity))).2
  have hdiff : schattenNorm p (X ∘L A.adjoint-A ∘L X.adjoint) ≤ 4*x*a := by
    calc
      _ ≤ schattenNorm p (X ∘L A.adjoint)+schattenNorm p (A ∘L X.adjoint) :=
        finite_schatten_sub_bound p hp _ _
      _ ≤ 2*schattenNorm (2*p) X*schattenNorm (2*p) A.adjoint+
          2*schattenNorm (2*p) A*schattenNorm (2*p) X.adjoint :=
        add_le_add (finite_schatten_product_bound p hp X A.adjoint)
          (finite_schatten_product_bound p hp A X.adjoint)
      _ = 4*x*a := by
        rw [schattenNorm_adjoint_eq,schattenNorm_adjoint_eq]
        dsimp only [x,a]
        ring
  have hsq : x^2 ≤ a^2+schattenNorm (2*p) D^2+
      C*schattenNorm p (X ∘L A.adjoint-A ∘L X.adjoint) := by
    calc
      x^2 = schattenNorm p (X ∘L X.adjoint) :=
        (finite_schatten_square_adjoint X p hp0).symm
      _ = schattenNorm p (A ∘L A.adjoint-D ∘L D.adjoint-
          triangularHilbert Q (X ∘L A.adjoint-A ∘L X.adjoint)) := by
        rw [show X ∘L X.adjoint=A ∘L A.adjoint-D ∘L D.adjoint-
          triangularHilbert Q (X ∘L A.adjoint-A ∘L X.adjoint) from
            triangularHilbert_square Q hQ A]
      _ ≤ schattenNorm p (A ∘L A.adjoint-D ∘L D.adjoint)+
          schattenNorm p (triangularHilbert Q (X ∘L A.adjoint-A ∘L X.adjoint)) :=
        finite_schatten_sub_bound p hp _ _
      _ ≤ schattenNorm p (A ∘L A.adjoint)+schattenNorm p (D ∘L D.adjoint)+
          C*schattenNorm p (X ∘L A.adjoint-A ∘L X.adjoint) :=
        add_le_add (finite_schatten_sub_bound p hp _ _) (hBound _)
      _ = _ := by
        rw [finite_schatten_square_adjoint A p hp0,finite_schatten_square_adjoint D p hp0]
  have hDsq : schattenNorm (2*p) D^2 ≤ a^2 := by
    exact (sq_le_sq₀ (Reduction.schattenNorm_nonneg _ _) ha).mpr hD
  have hCdiff := mul_le_mul_of_nonneg_left hdiff hC
  have hquad : x^2 ≤ 2*a^2+4*C*x*a := by nlinarith [hsq,hDsq,hCdiff]
  change x ≤ (4*C+2)*a
  by_contra hbad
  have hgt : (4*C+2)*a < x := lt_of_not_ge hbad
  have hxpos : 0 < x := (mul_nonneg (by linarith : 0 ≤ 4*C+2) ha).trans_lt hgt
  have hprod : 0 < (x-(4*C+2)*a)*(x+2*a) :=
    mul_pos (sub_pos.mpr hgt) (by linarith)
  have hCaa : 0 ≤ C*a^2 := mul_nonneg hC (sq_nonneg a)
  nlinarith [hquad,hprod,hCaa]

def triangularDyadicConstant : ℕ → ℝ
  | 0 => 2
  | n+1 => 4*triangularDyadicConstant n+2

theorem triangularDyadicConstant_pos (n : ℕ) : 0 < triangularDyadicConstant n := by
  induction n with
  | zero => norm_num [triangularDyadicConstant]
  | succ n ih => dsimp only [triangularDyadicConstant]; linarith

theorem finite_triangularHilbert_dyadic {N : ℕ}
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q) (n : ℕ) (A : H →L[ℂ] H) :
    schattenNorm ((2 : ℝ)^(n+1)) (triangularHilbert Q A) ≤
      triangularDyadicConstant n*schattenNorm ((2 : ℝ)^(n+1)) A := by
  induction n generalizing A with
  | zero =>
    simpa only [zero_add,pow_one,triangularDyadicConstant] using
      (schatten_triangularHilbert_two Q hQ A (finiteDim_schatten A 2 (by norm_num))).2
  | succ n ih =>
    have he : (2 : ℝ)^(n+1+1)=2*((2 : ℝ)^(n+1)) := by rw [pow_succ]; ring
    rw [show n+1+1=n+1+1 from rfl,he]
    exact finite_triangularHilbert_doubling Q hQ ((2 : ℝ)^(n+1))
      (triangularDyadicConstant n) (one_le_pow₀ (by norm_num)) (triangularDyadicConstant_pos n).le ih A

end FiniteProductBounds
theorem geometricMean_le_max (a b θ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : θ ∈ Icc (0 : ℝ) 1) : a^(1-θ)*b^θ ≤ max a b := by
  have hm : 0 ≤ max a b := ha.trans (le_max_left _ _)
  calc
    _ ≤ (max a b)^(1-θ)*(max a b)^θ :=
      mul_le_mul (Real.rpow_le_rpow ha (le_max_left _ _) (by linarith [hθ.2]))
        (Real.rpow_le_rpow hb (le_max_right _ _) hθ.1)
        (Real.rpow_nonneg hb _) (Real.rpow_nonneg hm _)
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hm (by linarith [hθ.2]) hθ.1,
        sub_add_cancel,Real.rpow_one]

theorem natCast_add_two_le_dyadic (n : ℕ) : (n : ℝ)+2 ≤ (2 : ℝ)^(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Every p≥2 admits a finite signed-transform constant independent of dimension and block count. -/
theorem exists_finite_triangularHilbert_bound_ge_two (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [FiniteDimensional ℂ H] [CompleteSpace H], ∀ N : ℕ, ∀ Q : Fin N → H →L[ℂ] H,
        TriangularBlocks Q → ∀ A : H →L[ℂ] H,
          schattenNorm p (triangularHilbert Q A) ≤ C*schattenNorm p A := by
  by_cases hp2 : p=2
  · subst p
    refine ⟨2,by norm_num,?_⟩
    intro H _ _ _ _ N Q hQ A
    exact (schatten_triangularHilbert_two Q hQ A (finiteDim_schatten A 2 (by norm_num))).2
  have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
  have hp0 : 0 < p := by linarith
  obtain ⟨n,hn⟩ := exists_nat_gt p
  let r : ℝ := (2 : ℝ)^(n+1)
  have hrp : p<r := hn.trans_le (le_trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2)
    (natCast_add_two_le_dyadic n))
  have hr2 : 2 < r := hpgt.trans hrp
  have hr0 : 0 < r := by linarith
  let θ : ℝ := r*(p-2)/(p*(r-2))
  have hden : 0 < p*(r-2) := mul_pos hp0 (by linarith)
  have hθ : θ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (mul_pos hr0 (by linarith)) hden,?_⟩
    exact (div_lt_iff₀ hden).mpr (by nlinarith [hrp])
  have hmean : p*((1-θ)*(1/(2 : ℝ))+θ*(1/r))=1 := by
    dsimp only [θ]
    field_simp [hp0.ne',hr0.ne',(sub_pos.mpr hr2).ne']
    ring
  refine ⟨max 2 (triangularDyadicConstant n),(by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) (le_max_left _ _)),?_⟩
  intro H _ _ _ _ N Q hQ A
  have hbase (B : H →L[ℂ] H) :
      schattenNorm 2 (triangularHilbert Q B) ≤ 2*schattenNorm 2 B :=
    (schatten_triangularHilbert_two Q hQ B (finiteDim_schatten B 2 (by norm_num))).2
  have hd (B : H →L[ℂ] H) :
      schattenNorm r (triangularHilbert Q B) ≤ triangularDyadicConstant n*schattenNorm r B :=
    finite_triangularHilbert_dyadic Q hQ n B
  have hh := finiteSchatten_interpolation (triangularHilbert Q) 2 r p θ 2 (triangularDyadicConstant n)
    (by norm_num) (by linarith) (by linarith) hθ hmean (by norm_num)
    (triangularDyadicConstant_pos n).le hbase hd A
  exact hh.trans (mul_le_mul_of_nonneg_right
    (geometricMean_le_max 2 (triangularDyadicConstant n) θ (by norm_num)
      (triangularDyadicConstant_pos n).le ⟨hθ.1.le,hθ.2.le⟩)
      (Reduction.schattenNorm_nonneg p A))

section FiniteHilbertSchmidtPairing
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "dH" => Module.finrank ℂ H

def finiteBasisTrace (b : OrthonormalBasis (Fin dH) ℂ H) (T : H →L[ℂ] H) : ℂ :=
  ∑ i, inner ℂ (b i) (T (b i))

def finiteHSPair (b : OrthonormalBasis (Fin dH) ℂ H) (B A : H →L[ℂ] H) : ℂ :=
  ∑ i, inner ℂ (B (b i)) (A (b i))

omit [CompleteSpace H] in
theorem basis_linear_expansion (b : OrthonormalBasis (Fin dH) ℂ H)
    (T : H →L[ℂ] H) (x : H) :
    T x=∑ i, inner ℂ (b i) x • T (b i) := by
  calc
    T x=T (∑ i, inner ℂ (b i) x • b i) := congrArg T (b.sum_repr' x).symm
    _ = _ := by rw [map_sum]; simp only [map_smul]

omit [CompleteSpace H] in
theorem finiteBasisTrace_independent (b c : OrthonormalBasis (Fin dH) ℂ H)
    (T : H →L[ℂ] H) : finiteBasisTrace b T=finiteBasisTrace c T := by
  have he (i : Fin dH) : inner ℂ (b i) (T (b i))=
      ∑ j, inner ℂ (c j) (b i)*inner ℂ (b i) (T (c j)) := by
    rw [basis_linear_expansion c T (b i),inner_sum]
    apply sum_congr rfl
    intro j hj
    rw [inner_smul_right]
  unfold finiteBasisTrace
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  exact b.sum_inner_mul_inner (c j) (T (c j))

omit [CompleteSpace H] in
theorem finiteBasisTrace_comp_comm (b : OrthonormalBasis (Fin dH) ℂ H)
    (T R : H →L[ℂ] H) :
    finiteBasisTrace b (T ∘L R)=finiteBasisTrace b (R ∘L T) := by
  have he (L K : H →L[ℂ] H) (i : Fin dH) :
      inner ℂ (b i) ((L ∘L K) (b i))=
        ∑ j, inner ℂ (b j) (K (b i))*inner ℂ (b i) (L (b j)) := by
    change inner ℂ (b i) (L (K (b i)))=_
    rw [basis_linear_expansion b L (K (b i)),inner_sum]
    apply sum_congr rfl
    intro j hj
    rw [inner_smul_right]
  unfold finiteBasisTrace
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

theorem finiteHSPair_eq_trace (b : OrthonormalBasis (Fin dH) ℂ H) (B A : H →L[ℂ] H) :
    finiteHSPair b B A=finiteBasisTrace b (B.adjoint ∘L A) := by
  simp only [finiteHSPair,finiteBasisTrace,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem finiteHSPair_independent (b c : OrthonormalBasis (Fin dH) ℂ H) (B A : H →L[ℂ] H) :
    finiteHSPair b B A=finiteHSPair c B A := by
  rw [finiteHSPair_eq_trace,finiteHSPair_eq_trace]
  exact finiteBasisTrace_independent b c _

theorem finiteHSPair_comp_left (b : OrthonormalBasis (Fin dH) ℂ H) (B L A : H →L[ℂ] H) :
    finiteHSPair b B (L ∘L A)=finiteHSPair b (L.adjoint ∘L B) A := by
  simp only [finiteHSPair,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

theorem finiteHSPair_comp_right (b : OrthonormalBasis (Fin dH) ℂ H) (B A R : H →L[ℂ] H) :
    finiteHSPair b B (A ∘L R)=finiteHSPair b (B ∘L R.adjoint) A := by
  rw [finiteHSPair_eq_trace,finiteHSPair_eq_trace,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  simpa only [ContinuousLinearMap.comp_assoc] using finiteBasisTrace_comp_comm b (B.adjoint ∘L A) R

omit [CompleteSpace H] in
theorem finiteHSPair_sum_right {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis (Fin dH) ℂ H) (B : H →L[ℂ] H) (A : ι → H →L[ℂ] H) :
    finiteHSPair b B (∑ i ∈ s, A i)=∑ i ∈ s, finiteHSPair b B (A i) := by
  simp only [finiteHSPair,_root_.sum_apply,inner_sum]
  exact sum_comm

omit [CompleteSpace H] in
theorem finiteHSPair_sum_left {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis (Fin dH) ℂ H) (B : ι → H →L[ℂ] H) (A : H →L[ℂ] H) :
    finiteHSPair b (∑ i ∈ s, B i) A=∑ i ∈ s, finiteHSPair b (B i) A := by
  simp only [finiteHSPair,_root_.sum_apply,sum_inner]
  exact sum_comm

omit [CompleteSpace H] in
theorem finiteHSPair_smul_right (b : OrthonormalBasis (Fin dH) ℂ H)
    (B A : H →L[ℂ] H) (c : ℂ) : finiteHSPair b B (c • A)=c*finiteHSPair b B A := by
  simp only [finiteHSPair,_root_.smul_apply,inner_smul_right,mul_sum]

omit [CompleteSpace H] in
theorem finiteHSPair_smul_left (b : OrthonormalBasis (Fin dH) ℂ H)
    (B A : H →L[ℂ] H) (c : ℂ) : finiteHSPair b (c • B) A=conj c*finiteHSPair b B A := by
  simp only [finiteHSPair,_root_.smul_apply,inner_smul_left,mul_sum]

theorem finiteHSPair_block {N : ℕ} (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (b : OrthonormalBasis (Fin dH) ℂ H) (B A : H →L[ℂ] H) (i j : Fin N) :
    finiteHSPair b B (operatorBlock Q A i j)=finiteHSPair b (operatorBlock Q B i j) A := by
  unfold operatorBlock
  rw [finiteHSPair_comp_left,finiteHSPair_comp_right,hQ.adjoint_eq,hQ.adjoint_eq,
    ContinuousLinearMap.comp_assoc]

theorem conj_triangularSign {N : ℕ} (i j : Fin N) : conj (triangularSign i j)=triangularSign i j := by
  unfold triangularSign
  split_ifs <;> simp

/-- The signed transform is HS-selfadjoint, despite reversing sign under the operator adjoint. -/
theorem finiteHSPair_triangularHilbert {N : ℕ} (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (b : OrthonormalBasis (Fin dH) ℂ H) (B A : H →L[ℂ] H) :
    finiteHSPair b B (triangularHilbert Q A)=finiteHSPair b (triangularHilbert Q B) A := by
  change finiteHSPair b B (blockMultiplier Q triangularSign A)=
    finiteHSPair b (blockMultiplier Q triangularSign B) A
  simp only [blockMultiplier,finiteHSPair_sum_right,finiteHSPair_sum_left,
    finiteHSPair_smul_right,finiteHSPair_smul_left,finiteHSPair_block Q hQ,conj_triangularSign]

variable [FiniteDimensional ℂ H]

/-- Actual finite HS Hölder, obtained from the proved Bessel-coordinate inequality. -/
theorem finiteHSPair_holder (b : OrthonormalBasis (Fin dH) ℂ H)
    (p q : ℝ) (hpq : p.HolderConjugate q) (B A : H →L[ℂ] H) :
    ‖finiteHSPair b B A‖ ≤ schattenNorm q B*schattenNorm p A := by
  let u : Fin dH → H := fun i => NormedSpace.normalize (B (gramBasis B i))
  let v : Fin dH → H := fun i => gramBasis B i
  have huB (x : H) : ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2 :=
    normalizedFamily_bessel _ (gramBasis_images_orthogonal B) x
  have hvB (x : H) : ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2 :=
    ((gramBasis B).sum_sq_norm_inner_right x).le
  have huN (i) : ‖u i‖ ≤ 1 := by
    dsimp only [u]
    by_cases hi : B (gramBasis B i)=0
    · simp [hi,NormedSpace.normalize]
    · rw [NormedSpace.norm_normalize hi]
  have hvN (i) : ‖v i‖ ≤ 1 := (gramBasis B).norm_eq_one i |>.le
  have he : finiteHSPair b B A =
      ∑ i, (‖B (gramBasis B i)‖ : ℂ)*inner ℂ (u i) (A (v i)) := by
    rw [finiteHSPair_independent b (gramBasis B)]
    unfold finiteHSPair
    apply sum_congr rfl
    intro i hi
    conv_lhs =>
      rw [← complex_norm_smul_normalize (B (gramBasis B i)),inner_smul_left,Complex.conj_ofReal]
  have hn : FiniteThorin.vectorNorm q (fun i : Fin dH => (‖B (gramBasis B i)‖ : ℂ))=
      schattenNorm q B := by
    unfold FiniteThorin.vectorNorm schattenNorm
    rw [finiteGram_power_sum B q hpq.symm.pos]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [Complex.norm_real,norm_norm]
  rw [he]
  have h := finite_besselPair_complex_holder A u v huB hvB huN hvN p q hpq
    (fun i => (‖B (gramBasis B i)‖ : ℂ))
  simpa only [hn] using h

def besselCoefficientOperator {N : ℕ} (u v : Fin N → H) (c : Fin N → ℂ) : H →L[ℂ] H :=
  (finiteAnalysis u).adjoint ∘L finiteSequenceDiagonal c ∘L finiteAnalysis v

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
theorem finiteAnalysis_apply_smul {N : ℕ} (v : Fin N → H) (x : H) :
    finiteAnalysis v x=∑ i, inner ℂ (v i) x • (lp.single 2 i.val (1 : ℂ) : SequenceL2) := by
  rw [finiteAnalysis_apply]
  apply sum_congr rfl
  intro i hi
  rw [← lp.single_smul]
  simp only [smul_eq_mul,mul_one]

omit [FiniteDimensional ℂ H] in
theorem besselCoefficientOperator_apply {N : ℕ} (u v : Fin N → H) (c : Fin N → ℂ) (x : H) :
    besselCoefficientOperator u v c x=∑ i, (c i*inner ℂ (v i) x) • u i := by
  simp only [besselCoefficientOperator,ContinuousLinearMap.comp_apply]
  rw [finiteAnalysis_apply_smul]
  simp only [map_sum,map_smul,finiteSequenceDiagonal_single,finiteAnalysis_adjoint_single,smul_smul]
  apply sum_congr rfl
  intro i hi
  rw [mul_comm]

omit [FiniteDimensional ℂ H] in
theorem schattenNorm_besselCoefficient_le {N : ℕ} (u v : Fin N → H) (c : Fin N → ℂ)
    (huB : ∀ x : H, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2)
    (hvB : ∀ x : H, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2)
    (p : ℝ) (hp : 0 < p) :
    schattenNorm p (besselCoefficientOperator u v c) ≤ FiniteThorin.vectorNorm p c := by
  have hD := finiteSequenceDiagonal_schatten c p hp
  have hU := norm_finiteAnalysis_le_one u huB
  have hV := norm_finiteAnalysis_le_one v hvB
  have hU' : ‖(finiteAnalysis u).adjoint‖ ≤ 1 :=
    (ContinuousLinearMap.adjoint.norm_map _).trans_le hU
  have hn : ‖(finiteAnalysis u).adjoint‖*‖finiteAnalysis v‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hU' hV (norm_nonneg _) zero_le_one
  calc
    _ ≤ _ := schattenNorm_comp_le hD _ _
    _ ≤ 1*schattenNorm p (finiteSequenceDiagonal c) :=
      mul_le_mul_of_nonneg_right hn (Reduction.schattenNorm_nonneg p _)
    _ = _ := by rw [one_mul,schattenNorm_finiteSequenceDiagonal c p hp]

omit [FiniteDimensional ℂ H] in
theorem finiteHSPair_besselCoefficient {N : ℕ} (b : OrthonormalBasis (Fin dH) ℂ H)
    (u v : Fin N → H) (c : Fin N → ℂ) (A : H →L[ℂ] H) :
    finiteHSPair b (besselCoefficientOperator u v c) A=
      ∑ i, conj (c i)*inner ℂ (u i) (A (v i)) := by
  unfold finiteHSPair
  simp_rw [besselCoefficientOperator_apply,sum_inner,inner_smul_left,map_mul,inner_conj_symm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  calc
    _ = conj (c i)*(∑ j, inner ℂ (b j) (v i)*inner ℂ (u i) (A (b j))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      congr 1
      have h := congrArg (fun x : H => inner ℂ (u i) x) (basis_linear_expansion b A (v i))
      simpa only [inner_sum,inner_smul_right] using h.symm

/-- A genuine HS-selfadjoint map transfers a conjugate-exponent Schatten bound.
Both finite duality inequalities are proved from actual coefficient operators. -/
theorem finite_schatten_dual_bound (b : OrthonormalBasis (Fin dH) ℂ H)
    (T : (H →L[ℂ] H) → H →L[ℂ] H) (p q C : ℝ)
    (hpq : p.HolderConjugate q) (hC : 0 ≤ C)
    (hSelf : ∀ B A, finiteHSPair b B (T A)=finiteHSPair b (T B) A)
    (hBound : ∀ B : H →L[ℂ] H, schattenNorm q (T B) ≤ C*schattenNorm q B)
    (A : H →L[ℂ] H) : schattenNorm p (T A) ≤ C*schattenNorm p A := by
  apply schattenNorm_le_of_besselPair_bounds (T A) p q (C*schattenNorm p A) hpq
    (mul_nonneg hC (Reduction.schattenNorm_nonneg p A))
  intro N u v huB hvB huN hvN c
  let B := besselCoefficientOperator u v (fun i => conj (c i))
  have he : finiteHSPair b B (T A)=∑ i, c i*inner ℂ (u i) (T A (v i)) := by
    simpa only [B,Complex.conj_conj] using
      finiteHSPair_besselCoefficient b u v (fun i => conj (c i)) (T A)
  have hn : schattenNorm q B ≤ FiniteThorin.vectorNorm q c := by
    simpa only [B,FiniteThorin.vectorNorm,Complex.norm_conj] using
      schattenNorm_besselCoefficient_le u v (fun i => conj (c i)) huB hvB q hpq.symm.pos
  rw [← he,hSelf]
  calc
    _ ≤ schattenNorm q (T B)*schattenNorm p A := finiteHSPair_holder b p q hpq (T B) A
    _ ≤ C*schattenNorm q B*schattenNorm p A :=
      mul_le_mul_of_nonneg_right (hBound B) (Reduction.schattenNorm_nonneg p A)
    _ ≤ C*FiniteThorin.vectorNorm q c*schattenNorm p A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC)
        (Reduction.schattenNorm_nonneg p A)
    _ = _ := by ring

end FiniteHilbertSchmidtPairing
/-- Uniform finite signed-transform bounds for the entire range 1<p<∞.
Conjugate-exponent transport uses the proved finite HS coordinate duality. -/
theorem exists_finite_triangularHilbert_bound (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [FiniteDimensional ℂ H] [CompleteSpace H], ∀ N : ℕ, ∀ Q : Fin N → H →L[ℂ] H,
        TriangularBlocks Q → ∀ A : H →L[ℂ] H,
          schattenNorm p (triangularHilbert Q A) ≤ C*schattenNorm p A := by
  by_cases hp2 : 2 ≤ p
  · exact exists_finite_triangularHilbert_bound_ge_two p hp2
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq2 : 2 ≤ q := by
    by_contra hq
    have hplt : p<2 := lt_of_not_ge hp2
    have hqlt : q<2 := lt_of_not_ge hq
    have hpi := one_div_lt_one_div_of_lt hpq.pos hplt
    have hqi := one_div_le_one_div_of_le hpq.symm.pos hqlt.le
    simp only [one_div] at hpi hqi
    linarith [hpq.inv_add_inv_eq_one]
  obtain ⟨C,hC,hBound⟩ := exists_finite_triangularHilbert_bound_ge_two q hq2
  refine ⟨C,hC,?_⟩
  intro H _ _ _ _ N Q hQ A
  let b := gramBasis (ContinuousLinearMap.id ℂ H)
  exact finite_schatten_dual_bound b (triangularHilbert Q) p q C hpq hC.le
    (fun B D => finiteHSPair_triangularHilbert Q hQ b B D)
    (hBound H N Q hQ) A

section StrictCutConversion
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : ℕ}

/-- Recover the literal frozen strictly lower cut from the identity, pinching and signed transform. -/
theorem triangularCut_eq_half (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) :
    triangularCut Q A=(1/2 : ℂ) • (A-blockPinching Q A+triangularHilbert Q A) := by
  apply operatorBlock_ext Q hQ
  intro i j
  simp only [operatorBlock_cut Q hQ,operatorBlock_smul,operatorBlock_add,operatorBlock_sub,
    operatorBlock_hilbert Q hQ,operatorBlock_pinching Q hQ]
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [triangularSign,diagonalSign,hij,not_lt_of_ge hij.le,ne_of_lt hij]
  · subst j
    simp [triangularSign,diagonalSign]
  · simp only [triangularSign,diagonalSign,ite_eq_left hji,
      ite_eq_right (not_lt_of_ge hji.le),ite_eq_right (Ne.symm (ne_of_lt hji)),
      one_smul,zero_smul,sub_zero]
    rw [← two_smul ℂ (operatorBlock Q A i j),smul_smul]
    norm_num

variable [FiniteDimensional ℂ H]

theorem finite_triangularCut_bound (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (p C : ℝ) (hp : 1 < p) (hH : ∀ A : H →L[ℂ] H,
      schattenNorm p (triangularHilbert Q A) ≤ C*schattenNorm p A) (A : H →L[ℂ] H) :
    schattenNorm p (triangularCut Q A) ≤ (C+2)*schattenNorm p A := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hP := (schatten_blockPinching Q hQ p hp.le A (finiteDim_schatten A p hp0)).2
  have hsum : schattenNorm p (A-blockPinching Q A+triangularHilbert Q A) ≤
      (C+2)*schattenNorm p A := by
    calc
      _ ≤ schattenNorm p (A-blockPinching Q A)+schattenNorm p (triangularHilbert Q A) :=
        schattenNorm_add_le_sharp p hp.le _ _ (finiteDim_schatten _ p hp0) (finiteDim_schatten _ p hp0)
      _ ≤ schattenNorm p A+schattenNorm p (blockPinching Q A)+C*schattenNorm p A :=
        add_le_add (finite_schatten_sub_bound p hp.le _ _) (hH A)
      _ ≤ schattenNorm p A+schattenNorm p A+C*schattenNorm p A :=
        by linarith [hP]
      _ = _ := by ring
  have hhalf : ‖(1/2 : ℂ)‖=(1/2 : ℝ) := by norm_num
  rw [triangularCut_eq_half Q hQ A]
  calc
    _ ≤ ‖(1/2 : ℂ)‖*schattenNorm p (A-blockPinching Q A+triangularHilbert Q A) :=
      schattenNorm_smul_le (finiteDim_schatten _ p hp0) _
    _ ≤ schattenNorm p (A-blockPinching Q A+triangularHilbert Q A) := by
      have hn := Reduction.schattenNorm_nonneg p (A-blockPinching Q A+triangularHilbert Q A)
      rw [hhalf]
      linarith
    _ ≤ _ := hsum

end StrictCutConversion

/-- Uniform finite-dimensional strict triangular bounds for all p>1, with literal cuts. -/
theorem exists_finite_triangularCut_bound (p : ℝ) (hp : 1 < p) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [FiniteDimensional ℂ H] [CompleteSpace H], ∀ N : ℕ, ∀ Q : Fin N → H →L[ℂ] H,
        TriangularBlocks Q → ∀ A : H →L[ℂ] H,
          schattenNorm p (triangularCut Q A) ≤ τ*schattenNorm p A := by
  obtain ⟨C,hC,h⟩ := exists_finite_triangularHilbert_bound p hp
  refine ⟨C+2,by linarith,?_⟩
  intro H _ _ _ _ N Q hQ A
  exact finite_triangularCut_bound Q hQ p C hp (h H N Q hQ) A


section InvariantFiniteCorners
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : ℕ}

/-- The finite block-invariant hull of a source subspace. -/
def blockInvariantHull (Q : Fin N → H →L[ℂ] H) (M₀ : Submodule ℂ H) : Submodule ℂ H :=
  ⨆ i, M₀.map (Q i).toLinearMap

instance blockInvariantHull_finiteDimensional (Q : Fin N → H →L[ℂ] H)
    (M₀ : Submodule ℂ H) [FiniteDimensional ℂ M₀] :
    FiniteDimensional ℂ (blockInvariantHull Q M₀) := by
  unfold blockInvariantHull
  infer_instance

theorem le_blockInvariantHull (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (M₀ : Submodule ℂ H) : M₀ ≤ blockInvariantHull Q M₀ := by
  intro x hx
  rw [← sum_blocks_apply Q hQ x]
  apply Submodule.sum_mem
  intro i hi
  exact (le_iSup (fun j => M₀.map (Q j).toLinearMap) i) ⟨x,hx,rfl⟩

theorem blocks_preserve_hull (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (M₀ : Submodule ℂ H) (i : Fin N) (x : H) (hx : x ∈ blockInvariantHull Q M₀) :
    Q i x ∈ blockInvariantHull Q M₀ := by
  change x ∈ ⨆ j, M₀.map (Q j).toLinearMap at hx
  refine Submodule.iSup_induction (fun j => M₀.map (Q j).toLinearMap)
    (motive := fun y => Q i y ∈ blockInvariantHull Q M₀) hx ?_ ?_ ?_
  · intro j y hy
    obtain ⟨z,hz,rfl⟩ := hy
    change Q i (Q j z) ∈ blockInvariantHull Q M₀
    rw [block_projection_apply Q hQ i j z]
    split_ifs with hij
    · subst j
      exact (le_iSup (fun j => M₀.map (Q j).toLinearMap) i) ⟨z,hz,rfl⟩
    · exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Literal block compressions to an invariant closed subspace. -/
def compressedBlocks (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (i : Fin N) : M →L[ℂ] M :=
  M.orthogonalProjectionOnto ∘L Q i ∘L M.subtypeL

omit [CompleteSpace H] in
theorem compressedBlocks_coe (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (hInv : ∀ i x, x ∈ M → Q i x ∈ M)
    (i : Fin N) (x : M) : (compressedBlocks M Q i x : H)=Q i x := by
  change (M.orthogonalProjectionOnto (Q i x) : H)=Q i x
  exact congrArg Subtype.val
    (M.orthogonalProjectionOnto_mem_subspace_eq_self ⟨Q i x,hInv i x x.property⟩)

omit [CompleteSpace H] in
theorem compressedBlocks_intertwine (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (hInv : ∀ i x, x ∈ M → Q i x ∈ M) (i : Fin N) :
    Q i ∘L M.subtypeL=M.subtypeL ∘L compressedBlocks M Q i := by
  ext x
  exact (compressedBlocks_coe M Q hInv i x).symm

theorem compressedBlocks_properties (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (hInv : ∀ i x, x ∈ M → Q i x ∈ M) : TriangularBlocks (compressedBlocks M Q) := by
  have hpoint := compressedBlocks_coe M Q hInv
  refine ⟨?_,?_,?_,?_⟩
  · ext x
    simp only [_root_.sum_apply,ContinuousLinearMap.id_apply,Submodule.coe_sum,hpoint]
    exact sum_blocks_apply Q hQ x
  · intro i
    unfold compressedBlocks
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
      Submodule.adjoint_subtypeL,Submodule.adjoint_orthogonalProjectionOnto,hQ.adjoint_eq]
    rfl
  · intro i
    ext x
    simp only [ContinuousLinearMap.comp_apply,hpoint]
    exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (hQ.idempotent i)
  · intro i j hij
    ext x
    simp only [ContinuousLinearMap.comp_apply,hpoint,_root_.zero_apply,Submodule.coe_zero]
    exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (hQ.orthogonal i j hij)

theorem compressedBlocks_projection_intertwine (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (hInv : ∀ i x, x ∈ M → Q i x ∈ M) (i : Fin N) :
    M.orthogonalProjectionOnto ∘L Q i =
      compressedBlocks M Q i ∘L M.orthogonalProjectionOnto := by
  have h := congrArg ContinuousLinearMap.adjoint (compressedBlocks_intertwine M Q hInv i)
  have hc := (compressedBlocks_properties M Q hQ hInv).adjoint_eq i
  simpa only [ContinuousLinearMap.adjoint_comp,Submodule.adjoint_subtypeL,hQ.adjoint_eq,hc] using h

theorem triangularCut_compressed (M : Submodule ℂ H) [CompleteSpace M]
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (hInv : ∀ i x, x ∈ M → Q i x ∈ M) (A : M →L[ℂ] M) :
    triangularCut Q (M.subtypeL ∘L A ∘L M.orthogonalProjectionOnto) =
      M.subtypeL ∘L triangularCut (compressedBlocks M Q) A ∘L M.orthogonalProjectionOnto := by
  ext x
  simp only [triangularCut,_root_.sum_apply,ContinuousLinearMap.comp_apply]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hij
  · simp only [ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply]
    rw [← compressedBlocks_coe M Q hInv i]
    congr 1
    rw [← ContinuousLinearMap.comp_apply M.orthogonalProjectionOnto (Q j),
      compressedBlocks_projection_intertwine M Q hQ hInv j]
    rfl
  · simp only [_root_.zero_apply,map_zero]

theorem norm_sub_double_projection_le (M : Submodule ℂ H) [CompleteSpace M]
    (A R : H →L[ℂ] H) (hRange : ∀ x, R x ∈ M) (hAdj : ∀ x, R.adjoint x ∈ M)
    (δ : ℝ) (hError : ‖A-R‖ ≤ δ) :
    ‖A-M.starProjection ∘L A ∘L M.starProjection‖ ≤ 4*δ := by
  have hRright : R ∘L M.starProjection=R :=
    comp_starProjection_eq_of_adjoint_range M R hAdj
  have hRleft : M.starProjection ∘L R=R := by
    ext x
    change (M.orthogonalProjectionOnto (R x) : H)=R x
    exact congrArg Subtype.val (M.orthogonalProjectionOnto_mem_subspace_eq_self ⟨R x,hRange x⟩)
  have hRight := norm_sub_comp_starProjection_le M A R hRright δ hError
  have hLeft : ‖A-M.starProjection ∘L A‖ ≤ 2*δ := by
    have he : A-M.starProjection ∘L A=(A-R)-M.starProjection ∘L (A-R) := by
      rw [ContinuousLinearMap.comp_sub,hRleft]
      abel
    have hc : ‖M.starProjection ∘L (A-R)‖ ≤ ‖A-R‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right M.starProjection_norm_le (norm_nonneg (A-R)))
    rw [he]
    have ht := norm_sub_le (A-R) (M.starProjection ∘L (A-R))
    linarith
  have he : A-M.starProjection ∘L A ∘L M.starProjection =
      (A-A ∘L M.starProjection)+(A-M.starProjection ∘L A) ∘L M.starProjection := by
    rw [ContinuousLinearMap.sub_comp]
    abel
  have hc : ‖(A-M.starProjection ∘L A) ∘L M.starProjection‖ ≤ ‖A-M.starProjection ∘L A‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left M.starProjection_norm_le (norm_nonneg (A-M.starProjection ∘L A)))
  rw [he]
  have ht := norm_add_le (A-A ∘L M.starProjection) ((A-M.starProjection ∘L A) ∘L M.starProjection)
  linarith

/-- The literal cut depends continuously on the ordinary operator norm. -/
theorem continuous_triangularCut (Q : Fin N → H →L[ℂ] H) :
    Continuous (fun A : H →L[ℂ] H => triangularCut Q A) := by
  unfold triangularCut
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  split_ifs <;> fun_prop

/-- Contractive finite invariant corners pass the uniform finite-space estimate to every Hilbert space.
The approximating finite-rank operators are used only to choose the corners. -/
theorem schatten_triangularCut_of_finite (p τ : ℝ) (hp : 0 < p) (hτ : 0 ≤ τ)
    (hFinite : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
      [FiniteDimensional ℂ F] [CompleteSpace F], ∀ n : ℕ, ∀ Q' : Fin n → F →L[ℂ] F,
      TriangularBlocks Q' → ∀ T : F →L[ℂ] F,
        schattenNorm p (triangularCut Q' T) ≤ τ*schattenNorm p T)
    (Q : Fin N → H →L[ℂ] H) (hQ : TriangularBlocks Q)
    (A : H →L[ℂ] H) (hA : Schatten p A) :
    Schatten p (triangularCut Q A) ∧ schattenNorm p (triangularCut Q A) ≤ τ*schattenNorm p A := by
  let S : Set (H →L[ℂ] H) :=
    (fun T => triangularCut Q T) ⁻¹' schattenClosedBall p (τ*schattenNorm p A)
  have hS : IsClosed S :=
    (isClosed_schattenClosedBall p hp (τ*schattenNorm p A)).preimage (continuous_triangularCut Q)
  apply hS.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨R,⟨r,hr⟩,hAR⟩ := compact_finiteRank_approx A hA.2.1 (ε/8) (by positivity)
  have hr' := rank_adjoint_le_of_rank_le R hr
  let : FiniteDimensional ℂ R.range := Module.rank_lt_aleph0_iff.mp
    (hr.trans_lt (Cardinal.natCast_lt_aleph0 (n := r)))
  let : FiniteDimensional ℂ R.adjoint.range := Module.rank_lt_aleph0_iff.mp
    (hr'.trans_lt (Cardinal.natCast_lt_aleph0 (n := r)))
  let M₀ : Submodule ℂ H := R.range ⊔ R.adjoint.range
  let M : Submodule ℂ H := blockInvariantHull Q M₀
  let : FiniteDimensional ℂ M₀ := inferInstance
  let : FiniteDimensional ℂ M := inferInstance
  let : CompleteSpace M := FiniteDimensional.complete ℂ M
  have hInv : ∀ i x, x ∈ M → Q i x ∈ M := blocks_preserve_hull Q hQ M₀
  have hM₀ : M₀ ≤ M := le_blockInvariantHull Q hQ M₀
  have hRange : ∀ x, R x ∈ M := fun x =>
    hM₀ ((show R.range ≤ M₀ from le_sup_left) ⟨x,rfl⟩)
  have hAdj : ∀ x, R.adjoint x ∈ M := fun x =>
    hM₀ ((show R.adjoint.range ≤ M₀ from le_sup_right) ⟨x,rfl⟩)
  let J := M.subtypeL
  let P := M.orthogonalProjectionOnto
  have hJ : ‖J‖ ≤ 1 := norm_isometry_clm_le_one M.subtypeₗᵢ
  have hP : ‖P‖ ≤ 1 := M.orthogonalProjectionOnto_norm_le
  have hPJ : ‖P‖*‖J‖ ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul hP hJ (norm_nonneg J) zero_le_one
      _ = 1 := one_mul 1
  have hJP : ‖J‖*‖P‖ ≤ 1 := by simpa only [mul_comm] using hPJ
  let C : M →L[ℂ] M := P ∘L A ∘L J
  have hCnorm : schattenNorm p C ≤ schattenNorm p A := by
    calc
      _ ≤ (‖P‖*‖J‖)*schattenNorm p A := schattenNorm_comp_le hA P J
      _ ≤ 1*schattenNorm p A := mul_le_mul_of_nonneg_right hPJ (Reduction.schattenNorm_nonneg p A)
      _ = _ := one_mul _
  let Q' := compressedBlocks M Q
  have hQ' : TriangularBlocks Q' := compressedBlocks_properties M Q hQ hInv
  have hCut : Schatten p (triangularCut Q' C) := finiteDim_schatten _ p hp
  let Z : H →L[ℂ] H := J ∘L C ∘L P
  have hZ : Z=M.starProjection ∘L A ∘L M.starProjection := by
    ext x
    rfl
  have hCZ : triangularCut Q Z=J ∘L triangularCut Q' C ∘L P :=
    triangularCut_compressed M Q hQ hInv C
  refine ⟨Z,?_,?_⟩
  · change Schatten p (triangularCut Q Z) ∧ schattenNorm p (triangularCut Q Z) ≤ _
    rw [hCZ]
    refine ⟨schatten_comp hCut J P,?_⟩
    calc
      _ ≤ (‖J‖*‖P‖)*schattenNorm p (triangularCut Q' C) := schattenNorm_comp_le hCut J P
      _ ≤ schattenNorm p (triangularCut Q' C) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hJP (Reduction.schattenNorm_nonneg p (triangularCut Q' C))
      _ ≤ τ*schattenNorm p C := hFinite M N Q' hQ' C
      _ ≤ τ*schattenNorm p A := mul_le_mul_of_nonneg_left hCnorm hτ
  · rw [dist_eq_norm,hZ]
    have he := norm_sub_double_projection_le M A R hRange hAdj (ε/8) hAR
    linarith

end InvariantFiniteCorners

/-- Uniform strict triangular truncation on every complete complex Hilbert space, for all p>1.
All finite dimensions, block counts and ambient Hilbert spaces share the same constant. -/
theorem triangularBound : TriangularBoundObligation := by
  intro p hp
  obtain ⟨τ,hτ,hFinite⟩ := exists_finite_triangularCut_bound p hp
  refine ⟨τ,hτ,?_⟩
  intro H _ _ _ N Q hSum hProj hOrth A hA
  have hQ : TriangularBlocks Q :=
    ⟨hSum,fun i => (hProj i).1,fun i => (hProj i).2,hOrth⟩
  exact schatten_triangularCut_of_finite p τ (zero_lt_one.trans hp) hτ.le
    hFinite Q hQ A hA

end TTO.Paper.Proved
