/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HankelVarianceFoundations
public import TTO.BlaschkeFoundations

/-! Actual Hankel shift and centered energy bounds toward literal arc BMO. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The native Hardy multiplier by the actual first circle character. -/
def hardyCoordinateShift : Hardy →L[ℂ] Hardy := hardyMultiply coordinate coordinate_isInner.1

theorem hardyCoordinateShift_norm (f : Hardy) : ‖hardyCoordinateShift f‖=‖f‖ := by
  exact (innerMultiplyIsometry coordinate coordinate_isInner).norm_map f.val

theorem norm_hardyCoordinateShift_le_one : ‖hardyCoordinateShift‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [hardyCoordinateShift_norm,one_mul]


theorem coreForm_canonical_coordinate (g f v : BoundaryL2) :
    coreForm (star (multiply coordinate g)) (multiply coordinate f) v=coreForm (star g) f v := by
  unfold coreForm
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (multiply coordinate g),multiply_ae coordinate g,
    multiply_ae coordinate f,Lp.coeFn_star g,coordinate_unimodular]
    with t hs hzg hzf hgs hz
  change (star (multiply coordinate g)) t=star (multiply coordinate g t) at hs
  change (star g) t=star (g t) at hgs
  have hunit : conj (coordinate t)*coordinate t=1 := by
    rw [Complex.conj_mul',hz]
    norm_num
  rw [hs,hzg,hzf,hgs]
  simp only [Complex.star_def,map_mul]
  calc
    _ = (conj (coordinate t)*coordinate t)*(conj (g t)*f t*conj (v t)) := by ring
    _ = _ := by rw [hunit,one_mul]

def hankelCoordinateUnshift (H : HankelOperator) : HankelOperator := H ∘L hardyCoordinateShift

theorem norm_hankelCoordinateUnshift_le (H : HankelOperator) : ‖hankelCoordinateUnshift H‖≤‖H‖ := by
  calc
    _ ≤ ‖H‖*‖hardyCoordinateShift‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H‖*1 := mul_le_mul_of_nonneg_left norm_hardyCoordinateShift_le_one (norm_nonneg H)
    _ = _ := mul_one _

theorem hankelCoordinateUnshift_represents (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    RepresentsHankel (star g) (hankelCoordinateUnshift H) := by
  intro f v hf hv
  exact (hH (hardyCoordinateShift f) v (bounded_multiply coordinate f.val hf) hv).trans
    (coreForm_canonical_coordinate g f.val v.val)


theorem representedHankel_szego_value (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (w : Disk) :
    H (szegoKernel w)=hardy.orthogonal.orthogonalProjectionOnto (multiply (szegoInf w) σ) := by
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [hH (szegoKernel w) (negativeBasis i) (bounded_szegoKernel w) (bounded_negativeBasis i),
    coreForm_eq_inner_left σ (szegoKernel w).val (negativeBasis i).val (bounded_szegoKernel w)]
  rfl


theorem hankel_centered_poisson_energy (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (w : Disk) :
    Integrable (fun t => ‖g.val t-analyticValue g.val w.val‖^2*atomicPoissonKernel w.val t) circleMeasure ∧
      (∫ t,‖g.val t-analyticValue g.val w.val‖^2*atomicPoissonKernel w.val t ∂circleMeasure)≤‖H‖^2 := by
  let K := hankelCoordinateUnshift H
  have hK : RepresentsHankel (star g.val) K := hankelCoordinateUnshift_represents g.val H hH
  have hV := representedHankel_szego_value (star g.val) K hK w
  have hE := negativeProjection_szego_centered_energy g w
  rw [← hV] at hE
  have hδ : 0<1-‖w.val‖^2 := by have hw : ‖w.val‖<1 := w.property; nlinarith [norm_nonneg w.val]
  have hAE : (fun t => ‖g.val t-analyticValue g.val w.val‖^2*atomicPoissonKernel w.val t)=ᵐ[circleMeasure]
      (fun t => (1-‖w.val‖^2)*(‖g.val t-analyticValue g.val w.val‖^2*‖(szegoKernel w).val t‖^2)) := by
    filter_upwards [szegoKernel_ae w] with t hk
    simp only [atomicPoissonKernel,hk,norm_inv,norm_kernelDenominator,inv_pow,div_eq_mul_inv]
    ring
  have hKN : ‖K (szegoKernel w)‖≤‖H‖*‖szegoKernel w‖ :=
    (K.le_opNorm _).trans (mul_le_mul_of_nonneg_right (norm_hankelCoordinateUnshift_le H) (norm_nonneg _))
  have hSquare : ‖K (szegoKernel w)‖^2≤‖H‖^2*‖szegoKernel w‖^2 := by
    nlinarith only [mul_le_mul hKN hKN (norm_nonneg (K (szegoKernel w)))
      (mul_nonneg (norm_nonneg H) (norm_nonneg (szegoKernel w)))]
  refine ⟨(hE.1.const_mul (1-‖w.val‖^2)).congr hAE.symm,?_⟩
  calc
    _ = (1-‖w.val‖^2)*(∫ t,‖g.val t-analyticValue g.val w.val‖^2*‖(szegoKernel w).val t‖^2 ∂circleMeasure) := by
      rw [integral_congr_ae hAE,integral_const_mul]
    _ = (1-‖w.val‖^2)*‖K (szegoKernel w)‖^2 := by rw [← hE.2]; rfl
    _ ≤ (1-‖w.val‖^2)*(‖H‖^2*‖szegoKernel w‖^2) := mul_le_mul_of_nonneg_left hSquare hδ.le
    _ = ‖H‖^2*((1-‖w.val‖^2)*(1-‖w.val‖^2)⁻¹) := by rw [norm_szegoKernel_sq]; ring
    _ = _ := by rw [mul_inv_cancel₀ hδ.ne',mul_one]

end TTO.Paper.Proved
