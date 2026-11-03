/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AnalyticBoundaryFoundations
public import Mathlib.Analysis.Complex.SqrtDeriv

/-! Actual bounded Hardy square roots of affine disk factors, including boundary zeros. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z := by
  change (z^(2⁻¹ : ℂ))^2=z
  exact Complex.cpow_ofNat_inv_pow z 2

theorem norm_complex_sqrt_sq (z : ℂ) : ‖Complex.sqrt z‖^2=‖z‖ := by
  simpa only [norm_pow] using congrArg norm (complex_sqrt_sq z)

def linearSquareRoot (β z : ℂ) : ℂ := Complex.sqrt (1-β*z)

theorem linearFactor_slitPlane (β : ℂ) (hβ : ‖β‖≤1) (z : Disk) : 1-β*z.val∈Complex.slitPlane := by
  have hm : ‖β*z.val‖<1 := by
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right hβ (norm_nonneg z.val)).trans_eq (one_mul _)).trans_lt z.property
  have hr : (β*z.val).re<1 := (Complex.re_le_norm _).trans_lt hm
  change 0<(1-β*z.val).re ∨ (1-β*z.val).im≠0
  left
  rw [Complex.sub_re,Complex.one_re]
  linarith

theorem analyticOnNhd_linearSquareRoot (β : ℂ) (hβ : ‖β‖≤1) :
    AnalyticOnNhd ℂ (linearSquareRoot β) disk := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_norm continuous_const)
  intro z hz
  have hBase : DifferentiableAt ℂ (fun w : ℂ => 1-β*w) z := by fun_prop
  exact ((Complex.differentiableAt_sqrt (linearFactor_slitPlane β hβ ⟨z,hz⟩)).comp z hBase).differentiableWithinAt

theorem norm_linearSquareRoot_le_two (β : ℂ) (hβ : ‖β‖≤1) (z : Disk) :
    ‖linearSquareRoot β z.val‖≤2 := by
  have hm : ‖β*z.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hβ z.property.le (norm_nonneg z.val) zero_le_one).trans_eq (one_mul 1)
  have hn : ‖1-β*z.val‖≤2 := by
    have h := norm_sub_le (1 : ℂ) (β*z.val)
    rw [norm_one] at h
    linarith
  have hs := norm_complex_sqrt_sq (1-β*z.val)
  change ‖Complex.sqrt (1-β*z.val)‖≤2
  nlinarith [norm_nonneg (Complex.sqrt (1-β*z.val))]

def hardyLinearSquareRoot (β : ℂ) (hβ : ‖β‖≤1) : BoundaryLInf :=
  Classical.choose (exists_boundedAnalyticBoundary (linearSquareRoot β)
    (analyticOnNhd_linearSquareRoot β hβ) 2
    (fun z hz => norm_linearSquareRoot_le_two β hβ ⟨z,hz⟩))

theorem hardyLinearSquareRoot_spec (β : ℂ) (hβ : ‖β‖≤1) :
    toL2 (hardyLinearSquareRoot β hβ)∈hardy ∧
      (∀ z∈disk,innerValue (hardyLinearSquareRoot β hβ) z=Complex.sqrt (1-β*z)) ∧
      (∀ᵐ t ∂circleMeasure,‖hardyLinearSquareRoot β hβ t‖≤2) ∧ ‖hardyLinearSquareRoot β hβ‖≤2 :=
  Classical.choose_spec (exists_boundedAnalyticBoundary (linearSquareRoot β)
    (analyticOnNhd_linearSquareRoot β hβ) 2
    (fun z hz => norm_linearSquareRoot_le_two β hβ ⟨z,hz⟩))

def affineDiskBoundary (β : ℂ) : BoundaryLInf := constLInf 1-β • coordinate

theorem affineDiskBoundary_toL2 (β : ℂ) :
    toL2 (affineDiskBoundary β)=constL2 1-β • toL2 coordinate := by
  rw [←boundaryInclusion_apply]
  change boundaryInclusion (constLInf 1-β • coordinate)=_
  rw [map_sub,map_smul,boundaryInclusion_apply,boundaryInclusion_apply,toL2_constLInf]

theorem affineDiskBoundary_hardy (β : ℂ) : toL2 (affineDiskBoundary β)∈hardy := by
  rw [affineDiskBoundary_toL2]
  apply hardy.sub_mem (constantCoreLaws.hardy 1)
  apply hardy.smul_mem β
  change toL2 (mode 1)∈hardy
  rw [toL2_mode]
  exact fourierBasis_mem_hardy 1

theorem innerValue_affineDiskBoundary (β : ℂ) (z : Disk) :
    innerValue (affineDiskBoundary β) z.val=1-β*z.val := by
  change analyticValue (toL2 (affineDiskBoundary β)) z.val=_
  rw [affineDiskBoundary_toL2]
  change analyticValue (constL2 1-β • toL2 (mode 1)) z.val=_
  rw [toL2_mode,constL2_fourier,one_smul,analyticValue_sub _ _ z.property,
    analyticValue_smul β _ z.property]
  have h0 : analyticValue (fourierBasis (T:=1) 0) z.val=1 := by
    simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z.val
  have h1 : analyticValue (fourierBasis (T:=1) 1) z.val=z.val := by
    simpa only [Nat.cast_one,pow_one] using analyticValue_fourierBasis 1 z.val
  rw [h0,h1]

/-- The square is an equality of the actual native L∞ boundary classes. -/
theorem hardyLinearSquareRoot_square (β : ℂ) (hβ : ‖β‖≤1) :
    multiplyInf (hardyLinearSquareRoot β hβ) (hardyLinearSquareRoot β hβ)=constLInf 1-β • coordinate := by
  let q := hardyLinearSquareRoot β hβ
  have hq : toL2 q∈hardy := (hardyLinearSquareRoot_spec β hβ).1
  have hLeft : toL2 (multiplyInf q q)∈hardy := by
    rw [toL2_multiplyInf]
    exact multiply_mem_hardy q hq (toL2 q) hq
  have hL2 : toL2 (multiplyInf q q)=toL2 (affineDiskBoundary β) := by
    have he : (⟨toL2 (multiplyInf q q),hLeft⟩ : Hardy)=
        ⟨toL2 (affineDiskBoundary β),affineDiskBoundary_hardy β⟩ := by
      apply hardy_analyticValue_injective
      intro z hz
      change innerValue (multiplyInf q q) z=innerValue (affineDiskBoundary β) z
      rw [innerValue_multiplyInf q q hq hq ⟨z,hz⟩,innerValue_affineDiskBoundary β ⟨z,hz⟩,
        (hardyLinearSquareRoot_spec β hβ).2.1 z hz]
      change Complex.sqrt (1-β*z)*Complex.sqrt (1-β*z)=1-β*z
      simpa only [pow_two] using complex_sqrt_sq (1-β*z)
    exact congrArg Subtype.val he
  apply Lp.ext
  filter_upwards [toL2_ae (multiplyInf q q),toL2_ae (affineDiskBoundary β)] with t hl hr
  exact hl.symm.trans ((congrArg (fun f : BoundaryL2 => f t) hL2).trans hr)

end TTO.Paper.Proved
