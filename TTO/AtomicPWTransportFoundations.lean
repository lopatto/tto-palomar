/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.L2TranslationFoundations

/-! Actual unitary transports for arbitrary single-atom location and unimodular phase.
All point values, native model spaces and compact-test forms retain their original meanings. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Rotation of the actual native open-disk subtype. -/
def phaseRotateDisk (c : ℂ) (hc : ‖c‖ = 1) (z : Disk) : Disk :=
  ⟨c * z.val, by change ‖c * z.val‖ < 1; rw [norm_mul,hc,one_mul]; exact z.property⟩

theorem phaseRotateDisk_surjective (c : ℂ) (hc : ‖c‖ = 1) :
    Function.Surjective (phaseRotateDisk c hc) := by
  intro z
  have hconj : ‖conj c‖ = 1 := by simpa only [Complex.norm_conj] using hc
  refine ⟨phaseRotateDisk (conj c) hconj z,?_⟩
  apply Subtype.ext
  change c * (conj c * z.val) = z.val
  rw [← mul_assoc,Complex.mul_conj',hc,Complex.ofReal_one,one_pow,one_mul]

theorem phaseRotation_kernel_factor (c : ℂ) (hc : ‖c‖ = 1) (z w : ℂ) :
    conj (c * z) * (c * w) = conj z * w := by
  have hp : conj c * c = 1 := by simp only [Complex.conj_mul',hc,one_pow,Complex.ofReal_one]
  rw [map_mul]
  calc
    _ = (conj c * c) * (conj z * w) := by ring
    _ = _ := by rw [hp,one_mul]

theorem hardyKernels_dense :
    Dense (Submodule.span ℂ (Set.range szegoKernel) : Set Hardy) := by
  apply hardyCayleyKernels_dense.mono
  apply Submodule.span_mono
  rintro _ ⟨w,rfl⟩
  exact ⟨upperCayleyDisk w.val w.property,rfl⟩

theorem exists_hardyPhaseRotation (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ R : Hardy ≃ₗᵢ[ℂ] Hardy, ∀ z : Disk, R (szegoKernel z) = szegoKernel (phaseRotateDisk c hc z) := by
  have hGram (z w : Disk) :
      inner ℂ (szegoKernel z) (szegoKernel w) =
        inner ℂ (szegoKernel (phaseRotateDisk c hc z)) (szegoKernel (phaseRotateDisk c hc w)) := by
    rw [inner_szegoKernel,inner_szegoKernel,analyticValue_szegoKernel _ z.property,
      analyticValue_szegoKernel _ (phaseRotateDisk c hc z).property]
    change (1 - conj w.val * z.val)⁻¹ = (1 - conj (c * w.val) * (c * z.val))⁻¹
    rw [phaseRotation_kernel_factor c hc]
  have hrange : Set.range (fun z : Disk => szegoKernel (phaseRotateDisk c hc z)) =
      Set.range szegoKernel := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      exact ⟨phaseRotateDisk c hc z,rfl⟩
    · rintro _ ⟨z,rfl⟩
      obtain ⟨w,rfl⟩ := phaseRotateDisk_surjective c hc z
      exact ⟨w,rfl⟩
  have hd : Dense (Submodule.span ℂ (Set.range
      (fun z : Disk => szegoKernel (phaseRotateDisk c hc z))) : Set Hardy) := by
    rw [hrange]
    exact hardyKernels_dense
  exact exists_unitary_of_equal_gram_dense szegoKernel
    (fun z : Disk => szegoKernel (phaseRotateDisk c hc z)) hGram hardyKernels_dense hd

/-- This is a constructed native Hardy unitary, not an assumed boundary pullback. -/
def hardyPhaseRotation (c : ℂ) (hc : ‖c‖ = 1) : Hardy ≃ₗᵢ[ℂ] Hardy :=
  Classical.choose (exists_hardyPhaseRotation c hc)

theorem hardyPhaseRotation_kernel (c : ℂ) (hc : ‖c‖ = 1) (z : Disk) :
    hardyPhaseRotation c hc (szegoKernel z) = szegoKernel (phaseRotateDisk c hc z) :=
  Classical.choose_spec (exists_hardyPhaseRotation c hc) z

theorem hardyPhaseRotation_eval (c : ℂ) (hc : ‖c‖ = 1) (f : Hardy) (z : Disk) :
    analyticValue (hardyPhaseRotation c hc f).val (phaseRotateDisk c hc z).val =
      analyticValue f.val z.val := by
  calc
    _ = inner ℂ (szegoKernel (phaseRotateDisk c hc z)) (hardyPhaseRotation c hc f) :=
      (inner_szegoKernel _ _).symm
    _ = inner ℂ (hardyPhaseRotation c hc (szegoKernel z)) (hardyPhaseRotation c hc f) := by
      rw [hardyPhaseRotation_kernel]
    _ = _ := (hardyPhaseRotation c hc).inner_map_map _ _
    _ = _ := inner_szegoKernel z f

theorem hardyPhaseRotation_symm_eval (c : ℂ) (hc : ‖c‖ = 1) (f : Hardy) (z : Disk) :
    analyticValue ((hardyPhaseRotation c hc).symm f).val z.val =
      analyticValue f.val (phaseRotateDisk c hc z).val := by
  have he := hardyPhaseRotation_eval c hc ((hardyPhaseRotation c hc).symm f) z
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he.symm

/-- Rotation preserves actual native essential boundedness of a Hardy vector. -/
theorem hardyPhaseRotation_bounded (c : ℂ) (hc : ‖c‖ = 1) (f : Hardy)
    (hf : IsBounded f.val) : IsBounded (hardyPhaseRotation c hc f).val := by
  let b : BoundaryLInf := hf.toLp f.val
  have he : toL2 b = f.val := Lp.ext ((toL2_ae b).trans hf.coeFn_toLp)
  have hb : toL2 b ∈ hardy := he.symm ▸ f.property
  apply bounded_hardy_of_analyticValue_bound (hardyPhaseRotation c hc f) ‖b‖
  intro z hz
  obtain ⟨w,hw⟩ := phaseRotateDisk_surjective c hc ⟨z,hz⟩
  have hw' : (phaseRotateDisk c hc w).val = z := congrArg Subtype.val hw
  rw [← hw',hardyPhaseRotation_eval]
  have hn := norm_innerValue_le b hb w
  change ‖analyticValue (toL2 b) w.val‖ ≤ ‖b‖ at hn
  rwa [he] at hn

/-- Phase and disk rotations cancel in the genuine model-kernel Gram matrices. -/
theorem exists_modelPhaseRotation (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val) :
    ∃ R : Model u₀ ≃ₗᵢ[ℂ] Model u, ∀ z : Disk,
      R (modelReproducingKernel u₀ hu₀ z) = modelReproducingKernel u hu (phaseRotateDisk c hc z) := by
  have hGram (z w : Disk) :
      inner ℂ (modelReproducingKernel u₀ hu₀ z) (modelReproducingKernel u₀ hu₀ w) =
        inner ℂ (modelReproducingKernel u hu (phaseRotateDisk c hc z))
          (modelReproducingKernel u hu (phaseRotateDisk c hc w)) := by
    rw [inner_modelReproducingKernel,inner_modelReproducingKernel,
      analyticValue_modelReproducingKernel _ _ _ z.property,
      analyticValue_modelReproducingKernel _ _ _ (phaseRotateDisk c hc z).property]
    unfold kernelValue
    rw [hval w,hval z]
    change (1 - conj (innerValue u₀ w.val) * innerValue u₀ z.val) / (1 - conj w.val * z.val) =
      (1 - conj (α * innerValue u₀ w.val) * (α * innerValue u₀ z.val)) /
        (1 - conj (c * w.val) * (c * z.val))
    rw [phaseRotation_kernel_factor α hα,phaseRotation_kernel_factor c hc]
  have hrange : Set.range (fun z : Disk => modelReproducingKernel u hu (phaseRotateDisk c hc z)) =
      Set.range (modelReproducingKernel u hu) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      exact ⟨phaseRotateDisk c hc z,rfl⟩
    · rintro _ ⟨z,rfl⟩
      obtain ⟨w,rfl⟩ := phaseRotateDisk_surjective c hc z
      exact ⟨w,rfl⟩
  have hd : Dense (Submodule.span ℂ (Set.range
      (fun z : Disk => modelReproducingKernel u hu (phaseRotateDisk c hc z))) : Set (Model u)) := by
    rw [hrange]
    exact modelReproducingKernels_dense u hu
  exact exists_unitary_of_equal_gram_dense (modelReproducingKernel u₀ hu₀)
    (fun z : Disk => modelReproducingKernel u hu (phaseRotateDisk c hc z))
    hGram (modelReproducingKernels_dense u₀ hu₀) hd

def modelPhaseRotation (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val) :
    Model u₀ ≃ₗᵢ[ℂ] Model u :=
  Classical.choose (exists_modelPhaseRotation u₀ u hu₀ hu c α hc hα hval)

theorem modelPhaseRotation_kernel (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val)
    (z : Disk) :
    modelPhaseRotation u₀ u hu₀ hu c α hc hα hval (modelReproducingKernel u₀ hu₀ z) =
      modelReproducingKernel u hu (phaseRotateDisk c hc z) :=
  Classical.choose_spec (exists_modelPhaseRotation u₀ u hu₀ hu c α hc hα hval) z

theorem modelPhaseRotation_eval (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val)
    (f : Model u₀) (z : Disk) :
    analyticValue (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val
        (phaseRotateDisk c hc z).val = analyticValue f.val z.val := by
  let R := modelPhaseRotation u₀ u hu₀ hu c α hc hα hval
  calc
    _ = inner ℂ (modelReproducingKernel u hu (phaseRotateDisk c hc z)) (R f) :=
      (inner_modelReproducingKernel _ _ _ _).symm
    _ = inner ℂ (R (modelReproducingKernel u₀ hu₀ z)) (R f) := by
      rw [show R (modelReproducingKernel u₀ hu₀ z) =
        modelReproducingKernel u hu (phaseRotateDisk c hc z) from
        modelPhaseRotation_kernel u₀ u hu₀ hu c α hc hα hval z]
    _ = _ := R.inner_map_map _ _
    _ = _ := inner_modelReproducingKernel u₀ hu₀ z f

/-- The genuine model unitary agrees with the genuine Hardy unitary on native embeddings. -/
theorem modelPhaseRotation_hardy (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val)
    (f : Model u₀) :
    (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val =
      (hardyPhaseRotation c hc ⟨f.val,f.property.1⟩).val := by
  have he :
      (⟨(modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val,
        (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).property.1⟩ : Hardy) =
      hardyPhaseRotation c hc ⟨f.val,f.property.1⟩ := by
    apply hardy_analyticValue_injective
    intro z hz
    obtain ⟨w,hw⟩ := phaseRotateDisk_surjective c hc ⟨z,hz⟩
    have hw' : (phaseRotateDisk c hc w).val = z := congrArg Subtype.val hw
    change analyticValue (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val z =
      analyticValue (hardyPhaseRotation c hc ⟨f.val,f.property.1⟩).val z
    rw [← hw',modelPhaseRotation_eval,hardyPhaseRotation_eval]
  exact congrArg Subtype.val he

/-- Rotation intertwines the actual bounded-input Hardy core multiplication.
The analytic symbol itself remains arbitrary H². -/
theorem coreMultiply_hardyPhaseRotation (c : ℂ) (hc : ‖c‖ = 1) (φ f : Hardy)
    (hf : IsBounded f.val) :
    coreMultiply φ.val
        ⟨(hardyPhaseRotation c hc f).val,hardyPhaseRotation_bounded c hc f hf⟩ =
      (hardyPhaseRotation c hc
        ⟨coreMultiply ((hardyPhaseRotation c hc).symm φ).val ⟨f.val,hf⟩,
          coreMultiply_mem_hardy ((hardyPhaseRotation c hc).symm φ) f hf⟩).val := by
  let R := hardyPhaseRotation c hc
  have hb : IsBounded (R f).val := hardyPhaseRotation_bounded c hc f hf
  let P : Hardy := ⟨coreMultiply (R.symm φ).val ⟨f.val,hf⟩,coreMultiply_mem_hardy (R.symm φ) f hf⟩
  have hp : coreMultiply φ.val ⟨(R f).val,hb⟩ ∈ hardy := coreMultiply_mem_hardy φ (R f) hb
  have he : (⟨coreMultiply φ.val ⟨(R f).val,hb⟩,hp⟩ : Hardy) = R P := by
    apply hardy_analyticValue_injective
    intro z hz
    obtain ⟨w,hw⟩ := phaseRotateDisk_surjective c hc ⟨z,hz⟩
    have hw' : (phaseRotateDisk c hc w).val = z := congrArg Subtype.val hw
    change analyticValue (coreMultiply φ.val ⟨(R f).val,hb⟩) z = analyticValue (R P).val z
    rw [← hw']
    calc
      _ = analyticValue φ.val (phaseRotateDisk c hc w).val *
          analyticValue (R f).val (phaseRotateDisk c hc w).val :=
        analyticValue_coreMultiply φ (R f) hb (phaseRotateDisk c hc w).property
      _ = analyticValue φ.val (phaseRotateDisk c hc w).val * analyticValue f.val w.val := by
        rw [hardyPhaseRotation_eval]
      _ = analyticValue (R.symm φ).val w.val * analyticValue f.val w.val := by
        rw [hardyPhaseRotation_symm_eval]
      _ = analyticValue P.val w.val :=
        (analyticValue_coreMultiply (R.symm φ) f hf w.property).symm
      _ = analyticValue (R P).val (phaseRotateDisk c hc w).val :=
        (hardyPhaseRotation_eval c hc P w).symm
  exact congrArg Subtype.val he

/-- The original core form is invariant under the constructed Hardy rotation. -/
theorem coreForm_hardyPhaseRotation (c : ℂ) (hc : ‖c‖ = 1) (φ f g : Hardy)
    (hf : IsBounded f.val) :
    coreForm φ.val (hardyPhaseRotation c hc f).val (hardyPhaseRotation c hc g).val =
      coreForm ((hardyPhaseRotation c hc).symm φ).val f.val g.val := by
  rw [coreForm_eq_inner_left _ _ _ (hardyPhaseRotation_bounded c hc f hf),
    coreForm_eq_inner_left _ _ _ hf]
  change inner ℂ (hardyPhaseRotation c hc g).val
    (coreMultiply φ.val
      ⟨(hardyPhaseRotation c hc f).val,hardyPhaseRotation_bounded c hc f hf⟩) =
    inner ℂ g.val (coreMultiply ((hardyPhaseRotation c hc).symm φ).val ⟨f.val,hf⟩)
  rw [coreMultiply_hardyPhaseRotation c hc φ f hf]
  change inner ℂ (hardyPhaseRotation c hc g)
    (hardyPhaseRotation c hc
      ⟨coreMultiply ((hardyPhaseRotation c hc).symm φ).val ⟨f.val,hf⟩,
        coreMultiply_mem_hardy ((hardyPhaseRotation c hc).symm φ) f hf⟩) =
    inner ℂ g
      (⟨coreMultiply ((hardyPhaseRotation c hc).symm φ).val ⟨f.val,hf⟩,
        coreMultiply_mem_hardy ((hardyPhaseRotation c hc).symm φ) f hf⟩ : Hardy)
  exact (hardyPhaseRotation c hc).inner_map_map _ _

theorem modelPhaseRotation_bounded (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val)
    (f : Model u₀) (hf : IsBounded f.val) :
    IsBounded (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val := by
  rw [modelPhaseRotation_hardy]
  exact hardyPhaseRotation_bounded c hc ⟨f.val,f.property.1⟩ hf

theorem coreForm_modelPhaseRotation (u₀ u : BoundaryLInf) (hu₀ : IsInner u₀) (hu : IsInner u)
    (c α : ℂ) (hc : ‖c‖ = 1) (hα : ‖α‖ = 1)
    (hval : ∀ z : Disk, innerValue u (phaseRotateDisk c hc z).val = α * innerValue u₀ z.val)
    (φ : Hardy) (f g : Model u₀) (hf : IsBounded f.val) :
    coreForm φ.val (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval f).val
        (modelPhaseRotation u₀ u hu₀ hu c α hc hα hval g).val =
      coreForm ((hardyPhaseRotation c hc).symm φ).val f.val g.val := by
  rw [modelPhaseRotation_hardy,modelPhaseRotation_hardy]
  exact coreForm_hardyPhaseRotation c hc φ ⟨f.val,f.property.1⟩ ⟨g.val,g.property.1⟩ hf

/-- The atom's actual unimodular circle coordinate. -/
def atomPhase (ζ : Boundary) : ℂ := fourier (T := 1) 1 ζ

theorem norm_atomPhase (ζ : Boundary) : ‖atomPhase ζ‖ = 1 := by
  simp only [atomPhase,fourier_apply,Circle.norm_coe]

/-- The full source SingleAtom hypothesis gives exactly the rotated normalized phase relation. -/
theorem singleAtom_phase_relation (u : BoundaryLInf) (ζ : Boundary) (hζ : SingleAtom u ζ) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ α : ℂ, ‖α‖ = 1 ∧
      ∀ z : Disk, innerValue u (phaseRotateDisk (atomPhase ζ) (norm_atomPhase ζ) z).val =
        α * innerValue (normalizedAtomBoundary ℓ) z.val := by
  obtain ⟨ℓ,hℓ,α,hα,hval⟩ := hζ
  refine ⟨ℓ,hℓ,α,hα,?_⟩
  intro z
  rw [hval _ (phaseRotateDisk (atomPhase ζ) (norm_atomPhase ζ) z).property,
    normalizedAtomBoundary_value ℓ hℓ z.property]
  let c := atomPhase ζ
  have hc : c ≠ 0 := by
    intro he
    have hn := norm_atomPhase ζ
    change ‖c‖ = 1 at hn
    simp only [he,norm_zero,zero_ne_one] at hn
  have hquot : (c + c * z.val) / (c - c * z.val) = (1 + z.val) / (1 - z.val) := by
    calc
      _ = (c * (1 + z.val)) / (c * (1 - z.val)) := by congr 1 <;> ring
      _ = _ := mul_div_mul_left _ _ hc
  change α * Complex.exp (-(ℓ : ℂ) * (c + c * z.val) / (c - c * z.val)) =
    α * Complex.exp (-(ℓ : ℂ) * (1 + z.val) / (1 - z.val))
  congr 1
  congr 1
  calc
    _ = -(ℓ : ℂ) * ((c + c * z.val) / (c - c * z.val)) := by ring
    _ = -(ℓ : ℂ) * ((1 + z.val) / (1 - z.val)) := by rw [hquot]
    _ = _ := by ring

/-- Every source single-atom inner function has actual rotated finite-interval and full-Hardy PW maps,
a dense bounded literal smooth core, and the proved causal correlation formula. -/
theorem exists_singleAtomPWTransport (u : BoundaryLInf) (hu : IsInner u)
    (ζ : Boundary) (hζ : SingleAtom u ζ) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u,
      ∃ H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy,
        (∀ (f : IntervalL2 ℓ) (w : ℂ), 0 < w.im →
          analyticValue (U f).val (atomPhase ζ * ((w - Complex.I) / (w + Complex.I))) /
              ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) =
            (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
              ∫ t in Ioo (0 : ℝ) ℓ, Complex.exp ((t : ℂ) * w * Complex.I) * f t) ∧
        (∀ (g : HalfLineL2) (w : ℂ), 0 < w.im →
          analyticValue (H g).val (atomPhase ζ * ((w - Complex.I) / (w + Complex.I))) /
              ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) =
            (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
              ∫ t in Ioi (0 : ℝ), Complex.exp ((t : ℂ) * w * Complex.I) * g t) ∧
        Dense (pwSmoothModelCore U : Set (Model u)) ∧
        (∀ f ∈ pwSmoothModelCore U, IsBounded f.val) ∧
        ∀ (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
          (hb : IntervalSmoothCompact ℓ b),
          coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
            (Complex.I / (Real.sqrt 2 : ℂ)) *
              ∫ t in Ioi (0 : ℝ), (H.symm φ) t *
                (-deriv (pwCorrelation a b) t + pwCorrelation a b t) := by
  obtain ⟨ℓ,hℓ,α,hα,hval⟩ := singleAtom_phase_relation u ζ hζ
  let u₀ := normalizedAtomBoundary ℓ
  have hu₀ : IsInner u₀ := (normalizedAtomBoundary_inner_value ℓ hℓ).1
  let c := atomPhase ζ
  have hc : ‖c‖ = 1 := norm_atomPhase ζ
  let Ru := modelPhaseRotation u₀ u hu₀ hu c α hc hα hval
  let Rh := hardyPhaseRotation c hc
  obtain ⟨U₀,hU₀⟩ := exists_normalizedPaleyWienerUnitary ℓ hℓ
  let U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u := U₀.trans Ru
  let H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy := halfLinePWEquiv.trans Rh
  refine ⟨ℓ,hℓ,U,H,?_,?_,?_,?_,?_⟩
  · intro f w hw
    change analyticValue (Ru (U₀ f)).val (c * upperCayley w) /
      ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) = _
    have hp : analyticValue (Ru (U₀ f)).val (c * upperCayley w) =
        analyticValue (U₀ f).val (upperCayley w) :=
      modelPhaseRotation_eval u₀ u hu₀ hu c α hc hα hval (U₀ f) (upperCayleyDisk w hw)
    rw [hp]
    exact hU₀ f w hw
  · intro g w hw
    change analyticValue (Rh (halfLinePWEquiv g)).val (c * upperCayley w) /
      ((Real.sqrt Real.pi : ℂ) * (w + Complex.I)) = _
    have hp : analyticValue (Rh (halfLinePWEquiv g)).val (c * upperCayley w) =
        analyticValue (halfLinePWEquiv g).val (upperCayley w) :=
      hardyPhaseRotation_eval c hc (halfLinePWEquiv g) (upperCayleyDisk w hw)
    rw [hp]
    exact halfLinePWEquiv_formula g w hw
  · exact pwSmoothModelCore_dense ℓ hℓ u U
  · intro f hf
    obtain ⟨a,ha,rfl⟩ := (mem_pwSmoothModelCore_iff ℓ u U f).mp hf
    change IsBounded (Ru (U₀ (smoothIntervalL2 ℓ a ha))).val
    exact modelPhaseRotation_bounded u₀ u hu₀ hu c α hc hα hval _
      (bounded_paleyWiener_smoothCompact ℓ hℓ u₀ U₀ hU₀ a ha)
  · intro φ a b ha hb
    change coreForm φ.val (Ru (U₀ (smoothIntervalL2 ℓ a ha))).val
      (Ru (U₀ (smoothIntervalL2 ℓ b hb))).val = _
    rw [coreForm_modelPhaseRotation u₀ u hu₀ hu c α hc hα hval φ _ _
      (bounded_paleyWiener_smoothCompact ℓ hℓ u₀ U₀ hU₀ a ha)]
    rw [coreForm_pwTests_correlation ℓ hℓ u₀ U₀ hU₀ (Rh.symm φ) a b ha hb]
    have hg : halfLinePWEquiv.symm (Rh.symm φ) = H.symm φ := rfl
    rw [hg]

end TTO.Paper.Proved
