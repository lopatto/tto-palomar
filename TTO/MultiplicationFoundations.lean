/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations

/-! Two literal measure-theoretic fields of the polynomial multiplication package.
This does not establish its compactness or Schatten classification fields. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- An actual represented fiber multiplier with zero base symbol is the zero operator. -/
theorem fiberMultiplier_zero (μ : Measure Boundary) (f : Boundary → ℂ)
    (M : Lp ℂ 2 (fiberMeasure μ) →L[ℂ] Lp ℂ 2 (fiberMeasure μ))
    (hM : RepresentsMultiplier (fiberMeasure μ) (fun t => f t.1) M)
    (hf : ∀ᵐ t ∂μ, f t = 0) : M = 0 := by
  have hz : ∀ᵐ t ∂fiberMeasure μ, f t.1 = 0 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := volume.restrict (Set.Ioo (0 : ℝ) 1))).ae hf
  apply ContinuousLinearMap.ext
  intro a
  change M a = (0 : Lp ℂ 2 (fiberMeasure μ))
  apply Lp.ext
  filter_upwards [hM a,hz,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := fiberMeasure μ)] with t hm ht h0
  calc
    (M a) t = f t.1*a t := hm
    _ = 0 := by rw [ht,zero_mul]
    _ = (0 : Lp ℂ 2 (fiberMeasure μ)) t := h0.symm

/-- For a measure carried by a countable set, a.e. equality is exactly equality at its atoms. -/
theorem atomicMeasure_ae_zero_iff (μ : Measure Boundary) (hμ : AtomicMeasure μ)
    (f : Boundary → ℂ) :
    (∀ᵐ t ∂μ, f t = 0) ↔ ∀ t, 0 < μ {t} → f t = 0 := by
  constructor
  · intro hf t ht
    by_contra hne
    have hz : μ {t} = 0 := measure_mono_null (by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hne) (ae_iff.mp hf)
    exact ht.ne' hz
  · intro hf
    obtain ⟨s,hs,hsm⟩ := hμ
    have hbad : μ (s ∩ {t | f t ≠ 0}) = 0 :=
      (measure_null_iff_singleton (hs.mono inter_subset_left)).mpr (by
        intro t ht
        by_contra hn
        exact ht.2 (hf t (pos_iff_ne_zero.mpr hn)))
    have hsae : ∀ᵐ t ∂μ, t ∈ s := by
      exact ae_iff.mpr hsm
    have hba : ∀ᵐ t ∂μ, t ∉ s ∩ {t | f t ≠ 0} :=
      measure_eq_zero_iff_ae_notMem.mp hbad
    filter_upwards [hsae,hba] with t ht hn
    by_contra hf0
    exact hn ⟨ht,hf0⟩

section GeneralMultipliers
variable {X : Type} [MeasurableSpace X] (μ : Measure X)

/-- An actual represented multiplication operator with an a.e. zero symbol is zero. -/
theorem representedMultiplier_zero_of_ae (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hM : RepresentsMultiplier μ f M)
    (hf : ∀ᵐ x ∂μ, f x = 0) : M = 0 := by
  apply ContinuousLinearMap.ext
  intro a
  change M a = (0 : Lp ℂ 2 μ)
  apply Lp.ext
  filter_upwards [hM a,hf,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hm hx h0
  calc
    (M a) x = f x*a x := hm
    _ = 0 := by rw [hx,zero_mul]
    _ = (0 : Lp ℂ 2 μ) x := h0.symm

variable [IsFiniteMeasure μ]

/-- Testing the actual constant-one vector reads the multiplier symbol a.e.; no symbol
measurability assumption is needed. -/
theorem representedMultiplier_one_ae (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hM : RepresentsMultiplier μ f M) :
    (M ((memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ)))) =ᵐ[μ] f := by
  filter_upwards [hM ((memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ))),
    (memLp_const (1 : ℂ) : MemLp (fun _ : X => (1 : ℂ)) 2 μ).coeFn_toLp] with x hm h1
  simpa only [h1,mul_one] using hm

/-- On a finite measure space the symbol of an actual bounded represented multiplier is in L². -/
theorem representedMultiplier_memLp (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hM : RepresentsMultiplier μ f M) : MemLp f 2 μ :=
  (Lp.memLp (M ((memLp_const (1 : ℂ)).toLp (fun _ : X => (1 : ℂ))))).ae_eq
    (representedMultiplier_one_ae μ f M hM)

/-- On a finite measure space zero represented multiplication is equivalent to its literal
symbol being zero a.e. -/
theorem representedMultiplier_zero_iff (f : X → ℂ)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hM : RepresentsMultiplier μ f M) :
    M = 0 ↔ ∀ᵐ x ∂μ, f x = 0 := by
  constructor
  · intro hz
    have he := representedMultiplier_one_ae μ f M hM
    rw [hz,_root_.zero_apply] at he
    exact he.symm.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ))
  · exact representedMultiplier_zero_of_ae μ f M hM

end GeneralMultipliers
end TTO.Paper.Proved
