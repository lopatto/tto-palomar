/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HardyL1SymbolFoundations
public import TTO.ContinuousHankelFoundations

/-! Actual bounded Hankel symbols from an explicit Hardy L¹ functional bound.
The bound remains an intermediate premise; no Nehari theorem is asserted here. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem hankelColumn_fourierCoeff (σ : BoundaryL2) (i j : ℕ) :
    inner ℂ (negativeBasis i) (hankelColumn σ j) =
      fourierCoeff σ (-(i : ℤ)-1-(j : ℤ)) := by
  rw [hankelColumn_inner,coreForm_eq_inner_left σ _ _ (bounded_hardyBasis j)]
  simp only [hardyBasis_apply,negativeBasis_apply]
  change inner ℂ (fourierBasis (T := 1) (-(i : ℤ)-1))
    (coreMultiply σ ⟨fourierBasis (T := 1) (j : ℤ),bounded_fourierBasis (j : ℤ)⟩)=_
  rw [coreMultiply_fourierBasis,← HilbertBasis.repr_apply_apply,fourierBasis_repr,
    fourierCoeff_mode_multiply]

theorem hardy_pairing_symbol_negative_coefficient (g : BoundaryL2) (b : BoundaryLInf)
    (hb : ∀ f : Hardy, inner ℂ g f.val = ∫ t, f.val t*b t ∂circleMeasure) (n : ℕ) :
    fourierCoeff (toL2 b) (-(n : ℤ)) = conj (fourierCoeff g (n : ℤ)) := by
  calc
    _ = ∫ t, (hardyBasis n).val t*b t ∂circleMeasure := by
      change (∫ t : Boundary, fourier (T := 1) (-(-(n : ℤ))) t*(toL2 b) t ∂circleMeasure)=_
      rw [neg_neg]
      apply integral_congr_ae
      filter_upwards [toL2_ae b,fourierBasis_ae (n : ℤ)] with t ht hn
      rw [ht,hardyBasis_apply]
      change fourier (T := 1) (n : ℤ) t*b t=(fourierBasis (T := 1) (n : ℤ)) t*b t
      rw [hn]
    _ = inner ℂ g (hardyBasis n).val := (hb (hardyBasis n)).symm
    _ = _ := by
      rw [← inner_conj_symm,hardyBasis_apply]
      change conj (inner ℂ (fourierBasis (T := 1) (n : ℤ)) g)=_
      rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

/-- The shift is multiplication by the actual conjugate circle coordinate. -/
def shiftedHardyPairingSymbol (b : BoundaryLInf) : BoundaryLInf :=
  multiplyInf (star coordinate) b

theorem norm_shiftedHardyPairingSymbol_le (b : BoundaryLInf) :
    ‖shiftedHardyPairingSymbol b‖ ≤ ‖b‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [multiplyInf_ae (star coordinate) b,Lp.coeFn_star coordinate,coordinate_ae] with t hm hs hz
  change ‖(multiplyInf (star coordinate) b) t‖ ≤ ‖b t‖
  rw [hm]
  rw [norm_mul,hs]
  change ‖conj (coordinate t)‖*‖b t‖ ≤ ‖b t‖
  rw [Complex.norm_conj,hz,fourier_one,Circle.norm_coe,one_mul]

theorem shiftedHardyPairingSymbol_sameHankel (g : BoundaryL2) (b : BoundaryLInf)
    (hb : ∀ f : Hardy, inner ℂ g f.val = ∫ t, f.val t*b t ∂circleMeasure) :
    SameHankel (star (multiply coordinate g)) (toL2 (shiftedHardyPairingSymbol b)) := by
  let a := shiftedHardyPairingSymbol b
  let H := boundedHankelOperator a
  have hArep : RepresentsHankel (toL2 a) H := boundedHankelOperator_represents a
  have hCoef (i j : ℕ) : inner ℂ (negativeBasis i) (hankelColumn (toL2 a) j) =
      conj (fourierCoeff g ((i+j : ℕ) : ℤ)) := by
    rw [hankelColumn_fourierCoeff]
    change fourierCoeff (toL2 (multiplyInf (star coordinate) b)) (-(i : ℤ)-1-(j : ℤ))=_
    rw [toL2_multiplyInf,fourierCoeff_backwardShift]
    have he : -(i : ℤ)-1-(j : ℤ)+1 = -((i+j : ℕ) : ℤ) := by push_cast; ring
    rw [he,hardy_pairing_symbol_negative_coefficient g b hb]
  have hOrig : RepresentsHankel (star (multiply coordinate g)) H := by
    apply representsHankel_of_columns
    intro j
    rw [representsHankel_columns (toL2 a) H hArep]
    apply negativeBasis.repr.injective
    apply lp.ext
    funext i
    rw [negativeBasis.repr_apply_apply,negativeBasis.repr_apply_apply,hCoef,
      hankelColumn_coefficient]
  intro f v hf hv
  exact (hOrig f v hf hv).symm.trans (hArep f v hf hv)

/-- Bounded symbols follow from the explicit Hardy bound, with the constant preserved. -/
theorem exists_sameHankel_bounded_symbol_of_hardy_l1_bound
    (g : BoundaryL2) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f : Hardy, ‖inner ℂ g f.val‖ ≤ C*‖nativeL2toL1 f.val‖) :
    ∃ a : BoundaryLInf, ‖a‖ ≤ C ∧
      SameHankel (star (multiply coordinate g)) (toL2 a) := by
  obtain ⟨b,hbN,hb⟩ := exists_bounded_symbol_of_hardy_l1_bound g C hC hBound
  exact ⟨shiftedHardyPairingSymbol b,(norm_shiftedHardyPairingSymbol_le b).trans hbN,
    shiftedHardyPairingSymbol_sameHankel g b hb⟩

theorem exists_sameHankel_bounded_symbol_of_finite_hardy_l1_bound
    (g : BoundaryL2) (C : ℝ) (hC : 0 ≤ C)
    (hFinite : ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g (∑ n ∈ range N, c n • hardyBasis n).val‖ ≤
        C*‖nativeL2toL1 (∑ n ∈ range N, c n • hardyBasis n).val‖) :
    ∃ a : BoundaryLInf, ‖a‖ ≤ C ∧
      SameHankel (star (multiply coordinate g)) (toL2 a) :=
  exists_sameHankel_bounded_symbol_of_hardy_l1_bound g C hC
    (hardy_l1_bound_of_finite_basis g C hFinite)

end TTO.Paper.Proved
