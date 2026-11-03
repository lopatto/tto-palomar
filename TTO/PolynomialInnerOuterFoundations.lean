/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations
public import TTO.PolynomialH1FactorizationFoundations
public import TTO.AngularFoundations
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Finite root reflection into an actual inner boundary factor and affine disk factors.
No Hardy factorization or Nehari theorem is assumed. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Roots inside the disk are reflected; all other roots are inverted. -/
def reflectedRootBeta (a : ℂ) : ℂ := if ‖a‖<1 then conj a else a⁻¹

def reflectedRootInner (a : ℂ) : BoundaryLInf :=
  if h : ‖a‖<1 then blaschkeBoundary ⟨a,h⟩ else constLInf 1

def reflectedRootScale (a : ℂ) : ℂ :=
  if h : ‖a‖<1 then (blaschkePhase ⟨a,h⟩)⁻¹ else -a

theorem norm_reflectedRootBeta_le_one (a : ℂ) : ‖reflectedRootBeta a‖≤1 := by
  unfold reflectedRootBeta
  split_ifs with ha
  · simpa only [Complex.norm_conj] using ha.le
  · have h1 : 1≤‖a‖ := le_of_not_gt ha
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one h1)).mpr h1

theorem reflectedRootInner_isInner (a : ℂ) : IsInner (reflectedRootInner a) := by
  unfold reflectedRootInner
  split_ifs
  · exact blaschkeBoundary_isInner _
  · exact isInner_constLInf_one

theorem reflectedRootScale_ne_zero (a : ℂ) : reflectedRootScale a≠0 := by
  unfold reflectedRootScale
  split_ifs with ha
  · exact inv_ne_zero (blaschkePhase_ne_zero _)
  · apply neg_ne_zero.mpr
    intro hz
    rw [hz,norm_zero] at ha
    norm_num at ha

theorem innerValue_const_one_disk (z : Disk) : innerValue (constLInf 1) z.val=1 := by
  change analyticValue (toL2 (constLInf 1)) z.val=1
  rw [toL2_constLInf,constL2_fourier,one_smul]
  simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z.val

/-- Literal reflected linear factor, including a=0 and every boundary root. -/
theorem reflectedRoot_factor (a : ℂ) (z : Disk) :
    z.val-a=innerValue (reflectedRootInner a) z.val*reflectedRootScale a*
      (1-reflectedRootBeta a*z.val) := by
  by_cases ha : ‖a‖<1
  · simp only [reflectedRootInner,reflectedRootScale,reflectedRootBeta,dite_eq_left ha,ite_eq_left ha]
    rw [innerValue_blaschkeBoundary]
    have hb := blaschkeFactor_clear (⟨a,ha⟩ : Disk) z.property
    have hp := blaschkePhase_ne_zero (⟨a,ha⟩ : Disk)
    calc
      _ = (blaschkePhase ⟨a,ha⟩)⁻¹*(blaschkePhase ⟨a,ha⟩*(z.val-a)) := by
        rw [← mul_assoc,inv_mul_cancel₀ hp,one_mul]
      _ = (blaschkePhase ⟨a,ha⟩)⁻¹*(blaschkeFactor ⟨a,ha⟩ z.val*(1-conj a*z.val)) := by rw [hb]
      _ = _ := by ring
  · simp only [reflectedRootInner,reflectedRootScale,reflectedRootBeta,dite_eq_right ha,ite_eq_right ha,
      innerValue_const_one_disk,one_mul]
    have hne : a≠0 := by
      intro hz
      rw [hz,norm_zero] at ha
      norm_num at ha
    field_simp
    ring

/-- The actual finite inner factor retains all repeated roots. -/
def reflectedRootsInner (r : List ℂ) : BoundaryLInf :=
  (r.map reflectedRootInner).foldr multiplyInf (constLInf 1)

theorem reflectedRootsInner_isInner (r : List ℂ) : IsInner (reflectedRootsInner r) := by
  apply isInner_listProduct
  intro u hu
  obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hu
  exact reflectedRootInner_isInner a

theorem innerValue_reflectedRootsInner (r : List ℂ) (z : Disk) :
    innerValue (reflectedRootsInner r) z.val =
      (r.map (fun a => innerValue (reflectedRootInner a) z.val)).prod := by
  have h := innerValue_listProduct (r.map reflectedRootInner) (by
    intro u hu
    obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hu
    exact reflectedRootInner_isInner a) z
  simpa only [reflectedRootsInner,List.map_map,Function.comp_def] using h

theorem reflectedRoots_factor (r : List ℂ) (z : Disk) :
    (r.map (fun a => z.val-a)).prod = innerValue (reflectedRootsInner r) z.val*
      (r.map reflectedRootScale).prod*(r.map (fun a => 1-reflectedRootBeta a*z.val)).prod := by
  rw [innerValue_reflectedRootsInner]
  induction r with
  | nil => simp
  | cons a r ih =>
    simp only [List.map_cons,List.prod_cons] at ih ⊢
    rw [reflectedRoot_factor a z,ih]
    ring

/-- Every complex polynomial has a literal finite inner/affine-disk factorization.
Zero and constant polynomials and roots on the unit circle are included. -/
theorem polynomial_inner_outer_data (p : Polynomial ℂ) :
    ∃ u : BoundaryLInf,IsInner u ∧ ∃ c : ℂ,∃ β : List ℂ,
      (∀ b∈β,‖b‖≤1) ∧ ∀ z : Disk,
        p.eval z.val=innerValue u z.val*c*(β.map (fun b => 1-b*z.val)).prod := by
  let r := p.roots.toList
  refine ⟨reflectedRootsInner r,reflectedRootsInner_isInner r,
    p.leadingCoeff*(r.map reflectedRootScale).prod,r.map reflectedRootBeta,?_,?_⟩
  · intro b hb
    obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hb
    exact norm_reflectedRootBeta_le_one a
  · intro z
    have he : p.eval z.val=p.leadingCoeff*(r.map (fun a => z.val-a)).prod := by
      have h := (IsAlgClosed.splits p).eval_eq_prod_roots z.val
      rw [← Multiset.coe_toList p.roots,Multiset.map_coe,Multiset.prod_coe] at h
      exact h
    simp only [List.map_map,Function.comp_def]
    rw [he,reflectedRoots_factor r z]
    ring

/-- Actual H¹ factorization of every analytic polynomial, with no external proof input. -/
theorem polynomialH1Factorization (p : Polynomial ℂ) :
    ∃ q r : BoundaryLInf,toL2 q∈hardy ∧ toL2 r∈hardy ∧
      multiplyInf q r=analyticPolynomialBoundary p ∧
      ‖toL2 q‖*‖toL2 r‖=∫ t,‖p.eval (fourier (T:=1) 1 t)‖ ∂circleMeasure := by
  obtain ⟨u,hu,c,β,hβ,hp⟩ := polynomial_inner_outer_data p
  exact polynomialH1Factorization_of_list_data p u hu c β hβ hp

end TTO.Paper.Proved
