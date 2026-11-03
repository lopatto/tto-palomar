/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.L1FunctionalSymbolFoundations
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Symbol representation from an explicit L¹ bound on actual Hardy vectors.
The norm bound is an intermediate mathematical premise, not a Nehari conclusion. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem nativeL2toL1_injective : Function.Injective nativeL2toL1 := by
  intro f g hfg
  have he := congrArg Subtype.val hfg
  change f.val=g.val at he
  exact Subtype.ext he

/-- The image is taken in the actual native L¹ space. -/
def hardyL1Map : Hardy →ₗ[ℂ] BoundaryL1 :=
  nativeL2toL1.toLinearMap.comp hardy.subtype

theorem hardyL1Map_injective : Function.Injective hardyL1Map := by
  intro f g hfg
  apply Subtype.ext
  exact nativeL2toL1_injective hfg

def hardyL1Equiv : Hardy ≃ₗ[ℂ] hardyL1Map.range :=
  LinearEquiv.ofInjective hardyL1Map hardyL1Map_injective

theorem hardyL1Equiv_coe (f : Hardy) :
    (hardyL1Equiv f).val = nativeL2toL1 f.val := rfl

theorem hardyL1Equiv_symm_coe (x : hardyL1Map.range) :
    nativeL2toL1 (hardyL1Equiv.symm x).val=x.val := by
  rw [← hardyL1Equiv_coe,hardyL1Equiv.apply_symm_apply]

/-- A complex Hardy functional bounded in the native L¹ norm has an actual L∞
symbol with the same bound. Its premise is retained explicitly. -/
theorem exists_bounded_symbol_of_hardy_l1_bound (g : BoundaryL2) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f : Hardy, ‖inner ℂ g f.val‖ ≤ C*‖nativeL2toL1 f.val‖) :
    ∃ σ : BoundaryLInf, ‖σ‖ ≤ C ∧ ∀ f : Hardy,
      inner ℂ g f.val = ∫ t, f.val t*σ t ∂circleMeasure := by
  let l : hardyL1Map.range →ₗ[ℂ] ℂ :=
    (innerSL ℂ g).toLinearMap.comp (hardy.subtype.comp hardyL1Equiv.symm.toLinearMap)
  have hlBound (x : hardyL1Map.range) : ‖l x‖ ≤ C*‖x‖ := by
    have hb := hBound (hardyL1Equiv.symm x)
    rw [hardyL1Equiv_symm_coe] at hb
    exact hb
  let ell : hardyL1Map.range →L[ℂ] ℂ := l.mkContinuous C hlBound
  have hEll : ‖ell‖ ≤ C := ContinuousLinearMap.opNorm_le_bound _ hC hlBound
  obtain ⟨L,hL,hNorm⟩ := exists_extension_norm_eq hardyL1Map.range ell
  obtain ⟨σ,hσNorm,hσ⟩ := exists_bounded_symbol_of_l1_functional L
  refine ⟨σ,hσNorm.trans (hNorm.trans_le hEll),?_⟩
  intro f
  have hLf := hL (hardyL1Equiv f)
  rw [hardyL1Equiv_coe] at hLf
  have he : ell (hardyL1Equiv f)=inner ℂ g f.val := by
    change inner ℂ g (hardyL1Equiv.symm (hardyL1Equiv f)).val=_
    rw [hardyL1Equiv.symm_apply_apply]
  rw [he] at hLf
  exact hLf.symm.trans (hσ f.val)

/-- Finite basis tests suffice for the explicit Hardy L¹ bound. -/
theorem hardy_l1_bound_of_finite_basis (g : BoundaryL2) (C : ℝ)
    (hFinite : ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g (∑ n ∈ range N, c n • hardyBasis n).val‖ ≤
        C*‖nativeL2toL1 (∑ n ∈ range N, c n • hardyBasis n).val‖) :
    ∀ f : Hardy, ‖inner ℂ g f.val‖ ≤ C*‖nativeL2toL1 f.val‖ := by
  intro f
  have hClosed : IsClosed {x : Hardy |
      ‖inner ℂ g x.val‖ ≤ C*‖nativeL2toL1 x.val‖} :=
    isClosed_le ((continuous_const.inner continuous_subtype_val).norm)
      (continuous_const.mul ((nativeL2toL1.continuous.comp continuous_subtype_val).norm))
  have hs := (hardyBasis.hasSum_repr f).tendsto_sum_nat
  exact hClosed.mem_of_tendsto hs
    (Eventually.of_forall fun N => hFinite N (hardyBasis.repr f))

theorem exists_bounded_symbol_of_finite_hardy_l1_bound (g : BoundaryL2) (C : ℝ) (hC : 0 ≤ C)
    (hFinite : ∀ (N : ℕ) (c : ℕ → ℂ),
      ‖inner ℂ g (∑ n ∈ range N, c n • hardyBasis n).val‖ ≤
        C*‖nativeL2toL1 (∑ n ∈ range N, c n • hardyBasis n).val‖) :
    ∃ σ : BoundaryLInf, ‖σ‖ ≤ C ∧ ∀ f : Hardy,
      inner ℂ g f.val = ∫ t, f.val t*σ t ∂circleMeasure :=
  exists_bounded_symbol_of_hardy_l1_bound g C hC (hardy_l1_bound_of_finite_basis g C hFinite)

end TTO.Paper.Proved
