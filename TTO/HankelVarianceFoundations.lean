/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicFoundations

/-! Native Szegő projection identities toward the Hankel/mean-oscillation bridge. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction


theorem szego_conjugate_pairing (g : BoundaryL2) (w : Disk) (n : ℕ) :
    inner ℂ (hardyBasis n).val (multiply (szegoInf w) (star g))=
      conj (inner ℂ (szegoKernel w).val (multiply (mode (n : ℤ)) g)) := by
  rw [hardyBasis_apply]
  have hRight := coreForm_eq_inner_right g (fourierBasis (T:=1) (n : ℤ))
    (szegoKernel w).val (bounded_szegoKernel w)
  have hLeft : coreForm g (fourierBasis (T:=1) (n : ℤ)) (szegoKernel w).val=
      inner ℂ (szegoKernel w).val (multiply (mode (n : ℤ)) g) := by
    rw [coreForm_eq_inner_left _ _ _ (bounded_fourierBasis (n : ℤ))]
    change inner ℂ (szegoKernel w).val
      (coreMultiply g ⟨fourierBasis (T:=1) (n : ℤ),bounded_fourierBasis (n : ℤ)⟩)=_
    rw [coreMultiply_fourierBasis]
  calc
    _ = conj (inner ℂ (multiply (szegoInf w) (star g)) (fourierBasis (T:=1) (n : ℤ))) :=
      (inner_conj_symm _ _).symm
    _ = conj (coreForm g (fourierBasis (T:=1) (n : ℤ)) (szegoKernel w).val) :=
      congrArg conj hRight.symm
    _ = _ := congrArg conj hLeft


theorem hardyProjection_szego_conjugate (g : Hardy) (w : Disk) :
    hardy.orthogonalProjectionOnto (multiply (szegoInf w) (star g.val))=
      conj (analyticValue g.val w.val) • szegoKernel w := by
  apply hardyBasis.repr.injective
  apply lp.ext
  funext n
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,szego_conjugate_pairing]
  rw [inner_smul_right (𝕜:=ℂ) (hardyBasis n) (szegoKernel w)]
  have hMode : toL2 (mode (n : ℤ))∈hardy := by
    rw [toL2_mode]
    exact fourierBasis_mem_hardy n
  have hMul := mode_multiply_hardy g n
  have hn : inner ℂ (hardyBasis n) (szegoKernel w)=conj w.val^n := by
    rw [← inner_conj_symm (𝕜:=ℂ) (hardyBasis n) (szegoKernel w),inner_szegoKernel,hardyBasis_apply]
    change conj (analyticValue (fourierBasis (T:=1) (n : ℤ)) w.val)=_
    rw [analyticValue_fourierBasis,map_pow]
  change conj (inner ℂ (szegoKernel w) (⟨multiply (mode (n : ℤ)) g.val,hMul⟩ : Hardy))=_
  rw [inner_szegoKernel,analyticValue_multiply _ hMode g w,hn]
  unfold innerValue
  rw [toL2_mode,analyticValue_fourierBasis]
  simp only [map_mul,map_pow]
  ring


theorem szegoInf_multiply_const (w : Disk) (c : ℂ) :
    multiply (szegoInf w) (constL2 c)=c • (szegoKernel w).val := by
  apply Lp.ext
  have hc : constL2 c=ᵐ[circleMeasure] (fun _ => c) := (memLp_const c).coeFn_toLp
  filter_upwards [multiply_ae (szegoInf w) (constL2 c),hc,
    Lp.coeFn_smul c (szegoKernel w).val,(bounded_szegoKernel w).coeFn_toLp]
    with t hm hct hs hk
  change (szegoInf w) t=(szegoKernel w).val t at hk
  rw [hm,hct,hs]
  change (szegoInf w) t*c=c*(szegoKernel w).val t
  rw [hk,mul_comm]


theorem negativeProjection_szego_conjugate_centered (g : Hardy) (w : Disk) :
    (hardy.orthogonal.orthogonalProjectionOnto (multiply (szegoInf w) (star g.val))).val=
      multiply (szegoInf w) (star (g.val-constL2 (analyticValue g.val w.val))) := by
  rw [Submodule.orthogonalProjectionOnto_orthogonal]
  change multiply (szegoInf w) (star g.val)-
    (hardy.orthogonalProjectionOnto (multiply (szegoInf w) (star g.val))).val=_
  rw [hardyProjection_szego_conjugate]
  rw [boundary_star_sub,map_sub,boundary_star_constL2,szegoInf_multiply_const]
  rfl


theorem negativeProjection_szego_centered_energy (g : Hardy) (w : Disk) :
    Integrable (fun t => ‖g.val t-analyticValue g.val w.val‖^2*‖(szegoKernel w).val t‖^2) circleMeasure ∧
    ‖(hardy.orthogonal.orthogonalProjectionOnto (multiply (szegoInf w) (star g.val))).val‖^2=
      ∫ t,‖g.val t-analyticValue g.val w.val‖^2*‖(szegoKernel w).val t‖^2 ∂circleMeasure := by
  let F := multiply (szegoInf w) (star (g.val-constL2 (analyticValue g.val w.val)))
  have hc : constL2 (analyticValue g.val w.val)=ᵐ[circleMeasure]
      (fun _ => analyticValue g.val w.val) := (memLp_const _).coeFn_toLp
  have hAE : (fun t => ‖F t‖^2)=ᵐ[circleMeasure]
      (fun t => ‖g.val t-analyticValue g.val w.val‖^2*‖(szegoKernel w).val t‖^2) := by
    filter_upwards [multiply_ae (szegoInf w) (star (g.val-constL2 (analyticValue g.val w.val))),
      Lp.coeFn_star (g.val-constL2 (analyticValue g.val w.val)),
      Lp.coeFn_sub g.val (constL2 (analyticValue g.val w.val)),hc,
      (bounded_szegoKernel w).coeFn_toLp] with t hm hs hSub hct hk
    change (star (g.val-constL2 (analyticValue g.val w.val))) t=
      star ((g.val-constL2 (analyticValue g.val w.val)) t) at hs
    change (g.val-constL2 (analyticValue g.val w.val)) t=
      g.val t-(constL2 (analyticValue g.val w.val)) t at hSub
    change (szegoInf w) t=(szegoKernel w).val t at hk
    change ‖multiply (szegoInf w) (star (g.val-constL2 (analyticValue g.val w.val))) t‖^2=_
    rw [hm,hs,hSub,hct,hk,norm_mul,norm_star,mul_pow,mul_comm]
  have hInt : Integrable (fun t => ‖F t‖^2) circleMeasure :=
    (Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have hNorm : ‖F‖^2=∫ t,‖F t‖^2 ∂circleMeasure := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def F F)
    rw [← integral_re] at h
    · simpa only [← norm_sq_eq_re_inner] using h
    · exact L2.integrable_inner F F
  refine ⟨hInt.congr hAE,?_⟩
  rw [negativeProjection_szego_conjugate_centered]
  exact hNorm.trans (integral_congr_ae hAE)

end TTO.Paper.Proved
