/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelLpBoundsFoundations
public import TTO.HankelShiftFoundations
public import TTO.WeakOperatorFoundations

/-! Actual all-p Schatten reconstruction from uniformly bounded finite Hankel corners. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Native finite coordinate analysis is the literal initial-coordinate inclusion in l2. -/
def finiteSequenceInclusion (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] SequenceL2 :=
  finiteAnalysis (EuclideanSpace.basisFun (Fin N) ℂ)

theorem finiteSequenceInclusion_at (N : ℕ) (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    finiteSequenceInclusion N x i.val=x i := by
  simp only [finiteSequenceInclusion,finiteAnalysis_at,EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left,map_one,one_mul]

theorem finiteSequenceInclusion_adjoint_single (N : ℕ) (i : Fin N) :
    (finiteSequenceInclusion N).adjoint (lp.single 2 i.val (1 : ℂ))=
      EuclideanSpace.single i (1 : ℂ) := by
  simpa only [finiteSequenceInclusion,EuclideanSpace.basisFun_apply] using
    finiteAnalysis_adjoint_single (EuclideanSpace.basisFun (Fin N) ℂ) i

theorem norm_finiteSequenceInclusion_le_one (N : ℕ) : ‖finiteSequenceInclusion N‖≤1 := by
  apply norm_finiteAnalysis_le_one
  intro x
  exact ((EuclideanSpace.basisFun (Fin N) ℂ).sum_sq_norm_inner_right x).le

def finiteHankelSequenceCorner (N : ℕ) (a : ℕ → ℂ) : SequenceOperator :=
  finiteSequenceInclusion N ∘L finiteHankelCoefficientMatrix N a ∘L
    (finiteSequenceInclusion N).adjoint

theorem finiteHankelSequenceCorner_entry (N : ℕ) (a : ℕ → ℂ) (i j : Fin N) :
    finiteHankelSequenceCorner N a (lp.single 2 j.val (1 : ℂ)) i.val=a (i.val+j.val) := by
  simp only [finiteHankelSequenceCorner,ContinuousLinearMap.comp_apply,
    finiteSequenceInclusion_adjoint_single,finiteSequenceInclusion_at,
    finiteHankelCoefficientMatrix_entry]

theorem finiteHankelSequenceCorner_schatten (N : ℕ) (a : ℕ → ℂ) (p : ℝ) (hp : 0<p) :
    Schatten p (finiteHankelSequenceCorner N a) ∧
      schattenNorm p (finiteHankelSequenceCorner N a)≤
        schattenNorm p (finiteHankelCoefficientMatrix N a) :=
  schatten_contracting_composition (finiteDim_schatten _ p hp) _ _
    (norm_finiteSequenceInclusion_le_one N)
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le (norm_finiteSequenceInclusion_le_one N))

/-- Genuine compact Schatten operator existence, not an assumed completion of a quasi-normed space. -/
theorem exists_schatten_sequenceHankel_of_finite_bound (a : ℕ → ℂ) (p C : ℝ) (hp : 0<p)
    (hBound : ∀ N : ℕ,schattenNorm p (finiteHankelCoefficientMatrix N a)≤C) :
    ∃ Z : SequenceOperator,Schatten p Z ∧ schattenNorm p Z≤C ∧
      ∀ i j : ℕ,Z (lp.single 2 j (1 : ℂ)) i=a (i+j) := by
  let T := fun N : ℕ => finiteHankelSequenceCorner N a
  have hT (N : ℕ) : Schatten p (T N) ∧ schattenNorm p (T N)≤C :=
    ⟨(finiteHankelSequenceCorner_schatten N a p hp).1,
      (finiteHankelSequenceCorner_schatten N a p hp).2.trans (hBound N)⟩
  obtain ⟨k,hk,Z,hZ,hZN,hLim⟩ := schatten_ball_subsequence p hp C T hT
  refine ⟨Z,hZ,hZN,?_⟩
  intro i j
  have hL : Tendsto (fun n => T (k n) (lp.single 2 j (1 : ℂ)) i) atTop
      (𝓝 (Z (lp.single 2 j (1 : ℂ)) i)) := by
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using
      hLim (lp.single 2 j (1 : ℂ)) (lp.single 2 i (1 : ℂ))
  have he : (fun n => T (k n) (lp.single 2 j (1 : ℂ)) i) =ᶠ[atTop]
      (fun _ : ℕ => a (i+j)) := by
    filter_upwards [hk.tendsto_atTop.eventually (eventually_gt_atTop (max i j))] with n hn
    exact finiteHankelSequenceCorner_entry (k n) a
      ⟨i,lt_of_le_of_lt (le_max_left i j) hn⟩
      ⟨j,lt_of_le_of_lt (le_max_right i j) hn⟩
  exact tendsto_nhds_unique hL (tendsto_const_nhds.congr' he.symm)

theorem sequenceAdjoint_single_entry (A : SequenceOperator) (i j : ℕ) :
    A.adjoint (lp.single 2 j (1 : ℂ)) i=conj (A (lp.single 2 i (1 : ℂ)) j) := by
  simpa only [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,map_one,
    mul_one,one_mul] using
    ContinuousLinearMap.adjoint_inner_right A (lp.single 2 i (1 : ℂ)) (lp.single 2 j (1 : ℂ))

/-- Actual classical Hankel synthesis from its positive coefficient matrices.
The adjoint supplies exactly the conjugations required by the represented L2 symbol. -/
theorem exists_schattenHankel_of_coefficient_corners (g : BoundaryL2) (p C : ℝ) (hp : 0<p)
    (hBound : ∀ N : ℕ,schattenNorm p (finiteHankelCoefficientMatrix N
      (fun n => fourierCoeff g (n : ℤ)))≤C) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤C := by
  obtain ⟨Z,hZ,hZN,hEntry⟩ := exists_schatten_sequenceHankel_of_finite_bound
    (fun n => fourierCoeff g (n : ℤ)) p C hp hBound
  have hAdj : Schatten p Z.adjoint := (schatten_adjoint_iff Z p).mpr hZ
  obtain ⟨hHS,hHN⟩ := schatten_hankelFromSequence Z.adjoint hAdj
  refine ⟨hankelFromSequence Z.adjoint,?_,hHS,?_⟩
  · apply representsHankel_fromSequence_coefficients
    intro i j
    rw [sequenceAdjoint_single_entry,hEntry,Nat.add_comm]
  · exact hHN.trans ((schattenNorm_adjoint_eq Z p).trans_le hZN)


/-- Actual infinite Schatten Hankel matrix from analytic weighted energy, with the same uniform bound. -/
theorem exists_schatten_sequenceHankel_of_analytic_energy
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (p q : ℝ)
    (hpq : p.HolderConjugate q)
    (hE : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞) :
    ∃ Z : SequenceOperator,Schatten p Z ∧
      schattenNorm p Z≤pellerStrongConstant q^(1/q)*
        lpNorm (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure ∧
      ∀ i j : ℕ,Z (lp.single 2 j (1 : ℂ)) i=
        diskTaylorCoeff G (i+j)/(((i+j : ℕ) : ℂ)+1) :=
  exists_schatten_sequenceHankel_of_finite_bound _ p _ hpq.pos
    (fun N => schattenNorm_finiteHankelCoefficientMatrix_le N G hG p q hpq hE)


/-- The positive Hankel coefficients are the actual moments of the shifted analytic derivative. -/
theorem diskTaylorCoeff_coordinate_deriv_div (g : BoundaryL2) (n : ℕ) :
    diskTaylorCoeff (deriv (analyticValue (multiply coordinate g))) n/((n : ℂ)+1)=
      fourierCoeff g (n : ℤ) := by
  rw [diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue,fourierCoeff_coordinate_product]
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show (n : ℝ)+1≠0 by positivity)
  field_simp

/-- Genuine represented Schatten Hankel existence from the source's shifted derivative,
with no assumption of an already bounded Hankel operator. -/
theorem exists_schattenHankel_of_coordinate_derivative_energy
    (g : BoundaryL2) (p q : ℝ) (hpq : p.HolderConjugate q)
    (hE : (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue (multiply coordinate g)) z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞) :
    ∃ H : HankelOperator,RepresentsHankel (star (multiply coordinate g)) H ∧
      Schatten p H ∧ schattenNorm p H≤pellerStrongConstant q^(1/q)*
        lpNorm (pellerLift (deriv (analyticValue (multiply coordinate g))))
          (ENNReal.ofReal p) pellerPolarMeasure := by
  let G := deriv (analyticValue (multiply coordinate g))
  have hG : AnalyticOnNhd ℂ G disk :=
    fun z hz => (analyticOnNhd_analyticValue (multiply coordinate g) z hz).deriv
  have hCoeff : (fun n => diskTaylorCoeff G n/((n : ℂ)+1))=
      (fun n : ℕ => fourierCoeff g (n : ℤ)) :=
    funext (diskTaylorCoeff_coordinate_deriv_div g)
  apply exists_schattenHankel_of_coefficient_corners g p _ hpq.pos
  intro N
  have h := schattenNorm_finiteHankelCoefficientMatrix_le N G hG p q hpq hE
  rw [hCoeff] at h
  exact h

end TTO.Paper.Proved
