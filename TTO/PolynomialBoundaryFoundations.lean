/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations
public import TTO.AngularFoundations

/-! Direct polynomial compactness tests at boundary zero sequences of an inner function. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Before normalization, the coordinate residual of the literal model kernel is uniformly
bounded by its bounded numerator. The Szegő denominator cancels in the boundary norm. -/
theorem modelKernel_coordinate_residual_norm_le (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    ‖multiply coordinate (modelReproducingKernel u hu w).val -
      w.val • (modelReproducingKernel u hu w).val‖ ≤ 1 + ‖innerValue u w.val‖ := by
  have hb : 0 ≤ 1 + ‖innerValue u w.val‖ := by positivity
  have hbound : ∀ᵐ t ∂circleMeasure,
      ‖(multiply coordinate (modelReproducingKernel u hu w).val -
        w.val • (modelReproducingKernel u hu w).val) t‖ ≤ 1 + ‖innerValue u w.val‖ := by
    filter_upwards [multiply_ae coordinate (modelReproducingKernel u hu w).val,
      Lp.coeFn_sub (multiply coordinate (modelReproducingKernel u hu w).val)
        (w.val • (modelReproducingKernel u hu w).val),
      Lp.coeFn_smul w.val (modelReproducingKernel u hu w).val,
      coordinate_ae, modelReproducingKernel_ae u hu w, hu.2]
      with t hm hs hsm he hk hut
    rw [hs]
    change ‖multiply coordinate (modelReproducingKernel u hu w).val t -
      (w.val • (modelReproducingKernel u hu w).val) t‖ ≤ _
    rw [hm, hsm]
    change ‖coordinate t * (modelReproducingKernel u hu w).val t -
      w.val * (modelReproducingKernel u hu w).val t‖ ≤ _
    rw [he, ← sub_mul, hk]
    unfold kernelBoundary
    rw [norm_mul, norm_div, norm_kernelDenominator]
    have hne : ‖fourier (T := 1) 1 t - w.val‖ ≠ 0 := by
      rw [← norm_kernelDenominator]
      exact norm_ne_zero_iff.mpr (kernelDenominator_ne_zero w t)
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖conj (innerValue u w.val) * u t‖ := norm_sub_le _ _
      _ = _ := by rw [norm_one, norm_mul, Complex.norm_conj, hut, mul_one]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hb hbound

/-- The normalized coordinate residual is bounded by an inverse kernel norm, which tends
zero at every boundary approach where the inner function tends to zero. -/
theorem normalizedModelKernel_coordinate_residual_norm_le (u : BoundaryLInf)
    (hu : IsInner u) (w : Disk) :
    ‖multiply coordinate (NormedSpace.normalize (modelReproducingKernel u hu w)).val -
      w.val • (NormedSpace.normalize (modelReproducingKernel u hu w)).val‖ ≤
      ‖modelReproducingKernel u hu w‖⁻¹ * (1 + ‖innerValue u w.val‖) := by
  have he : NormedSpace.normalize (modelReproducingKernel u hu w) =
      ((‖modelReproducingKernel u hu w‖⁻¹ : ℝ) : ℂ) • modelReproducingKernel u hu w := by
    rw [NormedSpace.normalize]
    exact (Complex.coe_smul ..).symm
  rw [he, Submodule.coe_smul, map_smul, smul_comm w.val,
    ← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (modelKernel_coordinate_residual_norm_le u hu w)
    (inv_nonneg.mpr (norm_nonneg _))

/-- At any boundary approach where u tends to zero, the inverse model-kernel norm tends zero. -/
theorem modelKernel_inverse_norm_tendsto {I : Type*} (L : Filter I) (u : BoundaryLInf)
    (hu : IsInner u) (w : I → Disk) (ζ : Boundary)
    (hw : Tendsto (fun i => (w i).val) L (𝓝 (fourier (T := 1) 1 ζ)))
    (hzero : Tendsto (fun i => innerValue u (w i).val) L (𝓝 0)) :
    Tendsto (fun i => ‖modelReproducingKernel u hu (w i)‖⁻¹) L (𝓝 0) := by
  have hnorm : Tendsto (fun i => ‖(w i).val‖) L (𝓝 1) := by
    simpa only [fourier_apply, Circle.norm_coe] using hw.norm
  have hnum : Tendsto (fun i => 1 - ‖(w i).val‖ ^ 2) L (𝓝 0) := by
    simpa only [one_pow, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hnorm.pow 2)
  have hden : Tendsto (fun i => 1 - ‖innerValue u (w i).val‖ ^ 2) L (𝓝 1) := by
    simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
      tendsto_const_nhds.sub (hzero.norm.pow 2)
  have ht := (hnum.div hden one_ne_zero).sqrt
  simp only [zero_div, Real.sqrt_zero] at ht
  convert ht using 1
  funext i
  exact inverse_modelKernel_norm u hu (w i)

/-- The actual normalized model kernels are weakly null along every boundary approach on
which u tends to zero. There is no nontangential or separability premise. -/
theorem normalizedModelKernel_weak_tendsto {I : Type*} (L : Filter I) (u : BoundaryLInf)
    (hu : IsInner u) (hn : Nonconstant u) (w : I → Disk) (ζ : Boundary)
    (hw : Tendsto (fun i => (w i).val) L (𝓝 (fourier (T := 1) 1 ζ)))
    (hzero : Tendsto (fun i => innerValue u (w i).val) L (𝓝 0)) :
    ∀ v : Model u, Tendsto (fun i => inner ℂ v
      (NormedSpace.normalize (modelReproducingKernel u hu (w i)))) L (𝓝 0) := by
  apply tendsto_inner_of_dense_tests L _
    (fun i => (norm_normalize_modelReproducingKernel u hu hn (w i)).le)
    (modelReproducingKernel u hu) (modelReproducingKernels_dense u hu)
  intro a
  have hk : Tendsto (fun i => kernelValue u a.val (w i).val) L
      (𝓝 (1 / (1 - conj a.val * fourier (T := 1) 1 ζ))) := by
    unfold kernelValue
    have h := ((tendsto_const_nhds (x := (1 : ℂ))).sub
      (hzero.const_mul (conj (innerValue u a.val)))).div
      ((tendsto_const_nhds (x := (1 : ℂ))).sub (hw.const_mul (conj a.val)))
      (kernelDenominator_ne_zero a ζ)
    simp only [mul_zero, sub_zero] at h
    convert h using 1
  have hi := modelKernel_inverse_norm_tendsto L u hu w ζ hw hzero
  have hc := (Complex.continuous_ofReal.tendsto 0).comp hi
  have ht := hc.mul hk.star
  simp only [Complex.ofReal_zero, zero_mul] at ht
  apply ht.congr'
  exact Eventually.of_forall fun i => by
    have he := unitModelKernelAt_pair u hu a (w i)
    rw [unitModelKernelAt, dite_eq_left (w i).property, ← inverse_modelKernel_norm] at he
    exact he.symm

/-- A compact polynomial TTO must vanish at every boundary point reached along disk nodes
where its inner function tends zero. This is a direct test with the actual normalized kernels. -/
theorem compactPolynomial_boundary_value_zero {I : Type*} (L : Filter I) [NeBot L]
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (q : BiPolynomial)
    (hA : HasCompactTTO u (polynomialSymbol q)) (w : I → Disk) (ζ : Boundary)
    (hw : Tendsto (fun i => (w i).val) L (𝓝 (fourier (T := 1) 1 ζ)))
    (hzero : Tendsto (fun i => innerValue u (w i).val) L (𝓝 0)) :
    polynomialValue q (fourier (T := 1) 1 ζ) = 0 := by
  let A := boundedSymbolOperator u (biPolynomialBoundary q)
  let f (i : I) := NormedSpace.normalize (modelReproducingKernel u hu (w i))
  have hnorm (i : I) : ‖f i‖ = 1 := norm_normalize_modelReproducingKernel u hu hn (w i)
  obtain ⟨B, hB, hcB⟩ := hA
  have hBA : B = A := coreLaws.unique u hu hn _ B A hB
    (boundedSymbolOperator_represents u (biPolynomialBoundary q))
  have hcA : IsCompactOperator A := hBA ▸ hcB
  have hweak := normalizedModelKernel_weak_tendsto L u hu hn w ζ hw hzero
  have hcompact := compact_tendsto_zero_of_inner L f (fun i => (hnorm i).le) hweak A hcA
  have hinv := modelKernel_inverse_norm_tendsto L u hu w ζ hw hzero
  have hbound : Tendsto (fun i => biPolynomialLipschitzBound q *
      (‖modelReproducingKernel u hu (w i)‖⁻¹ * (1 + ‖innerValue u (w i).val‖))) L (𝓝 0) := by
    have ht := (hinv.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hzero.norm)).const_mul (biPolynomialLipschitzBound q)
    simp only [norm_zero, add_zero, zero_mul, mul_zero] at ht
    convert ht using 1
  have hineq (i : I) : ‖polynomialValue q (w i).val‖ ≤ ‖A (f i)‖ +
      biPolynomialLipschitzBound q *
        (‖modelReproducingKernel u hu (w i)‖⁻¹ * (1 + ‖innerValue u (w i).val‖)) := by
    have hres := (polynomial_column_norm_le u q (w i) (f i)).trans
      (mul_le_mul_of_nonneg_left (normalizedModelKernel_coordinate_residual_norm_le u hu (w i))
        (biPolynomialLipschitzBound_nonneg q))
    calc
      _ = ‖polynomialValue q (w i).val • f i‖ := by rw [norm_smul, hnorm, mul_one]
      _ = ‖A (f i) - (A (f i) - polynomialValue q (w i).val • f i)‖ := by congr 1; abel
      _ ≤ ‖A (f i)‖ + ‖A (f i) - polynomialValue q (w i).val • f i‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (le_refl ‖A (f i)‖) hres
  have hsum : Tendsto (fun i => ‖A (f i)‖ + biPolynomialLipschitzBound q *
      (‖modelReproducingKernel u hu (w i)‖⁻¹ * (1 + ‖innerValue u (w i).val‖))) L (𝓝 0) := by
    have ht := hcompact.norm.add hbound
    simp only [norm_zero, zero_add] at ht
    convert ht using 1
  have hqzero : Tendsto (fun i => ‖polynomialValue q (w i).val‖) L (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hineq hsum
  have hcont : Continuous (polynomialValue q) := by
    unfold polynomialValue Finsupp.sum
    fun_prop
  have hvalue := ((hcont.tendsto _).comp hw).norm
  have hz := tendsto_nhds_unique hqzero hvalue
  exact norm_eq_zero.mp hz.symm

end TTO.Paper.Proved
