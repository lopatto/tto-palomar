/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedHardyPairingFoundations

/-! Actual Cauchy derivative kernels for arbitrary native Haar L² boundary data. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem fourierCoeff_hardyProjection_nonneg (f : BoundaryL2) (n : ℕ) :
    fourierCoeff (hardy.orthogonalProjectionOnto f).val (n : ℤ)=fourierCoeff f (n : ℤ) := by
  rw [← hardyBasis_repr_eq_fourierCoeff,HilbertBasis.repr_apply_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,hardyBasis_apply]
  dsimp only [hardyMode]
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

theorem analyticValue_hardyProjection (f : BoundaryL2) (z : ℂ) :
    analyticValue (hardy.orthogonalProjectionOnto f).val z=analyticValue f z := by
  unfold analyticValue
  congr 1
  funext n
  rw [fourierCoeff_hardyProjection_nonneg]

theorem derivativeSzegoValue_hardyProjection (f : BoundaryL2) (z : ℂ) :
    derivativeSzegoValue (hardy.orthogonalProjectionOnto f).val z=derivativeSzegoValue f z := by
  unfold derivativeSzegoValue
  congr 1
  funext n
  rw [fourierCoeff_hardyProjection_nonneg]

theorem inner_derivativeSzegoKernel_boundaryL2 (w : Disk) (f : BoundaryL2) :
    inner ℂ (derivativeSzegoKernel w).val f=derivativeSzegoValue f w.val := by
  have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (derivativeSzegoKernel w) f
  rw [inner_derivativeSzegoKernel,derivativeSzegoValue_hardyProjection] at h
  exact h.symm

theorem hasSum_complex_succ_geometric {x : ℂ} (hx : ‖x‖<1) :
    HasSum (fun n : ℕ => ((n : ℂ)+1)*x^n) ((1-x)^2)⁻¹ := by
  have h0 := hasSum_geometric_of_norm_lt_one hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have hn : (1 : ℂ)-x≠0 := by
    intro h
    have he : x=1 := (sub_eq_zero.mp h).symm
    simp only [he,norm_one,lt_self_iff_false] at hx
  convert h1.add h0 using 1
  · funext n
    ring
  · field_simp
    ring

/-- The native derivative Szegő vector has its literal bounded rational representative. -/
theorem derivativeSzegoKernel_ae (w : Disk) :
    (derivativeSzegoKernel w).val =ᵐ[circleMeasure]
      fun t => ((1-conj w.val*fourier (T := 1) 1 t)^2)⁻¹ := by
  let G : ℕ → C(Boundary,ℂ) := fun n => derivativeSzegoCoeff w n • fourier (T := 1) (n : ℤ)
  have hG : Summable G := by
    refine Summable.of_norm_bounded (summable_norm_derivativeSzegoCoeff w) fun n => ?_
    rw [norm_smul,fourier_norm,mul_one]
  have hClass : (derivativeSzegoKernel w).val=ContinuousMap.toLp 2 circleMeasure ℂ (∑' n,G n) := by
    rw [derivativeSzegoKernel,← hardy.subtypeL_apply,
      ContinuousLinearMap.map_tsum _ (summable_derivativeSzegoKernel w),
      ContinuousLinearMap.map_tsum _ hG]
    congr 1
    funext n
    simp [G,coe_fourierBasis,hardyMode]
  rw [hClass]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure (∑' n,G n)] with t ht
  rw [ht]
  refine (ContinuousMap.tsum_apply hG t).symm.trans ?_
  have hProd : ‖conj w.val*fourier (T := 1) 1 t‖<1 := by
    simpa only [disk,Set.mem_ofPred_eq,norm_mul,Complex.norm_conj,fourier_one,Circle.norm_coe,mul_one] using w.property
  rw [← (hasSum_complex_succ_geometric hProd).tsum_eq]
  congr 1
  funext n
  simp only [G,derivativeSzegoCoeff,ContinuousMap.smul_apply,smul_eq_mul,fourier_apply,
    natCast_zsmul,AddCircle.toCircle_nsmul,Circle.coe_pow,one_zsmul,mul_pow]
  ring

theorem derivativeSzegoKernel_eq_square (w : Disk) :
    (derivativeSzegoKernel w).val=multiply (szegoInf w) (szegoKernel w).val := by
  apply Lp.ext
  filter_upwards [derivativeSzegoKernel_ae w,multiply_ae (szegoInf w) (szegoKernel w).val,
    (bounded_szegoKernel w).coeFn_toLp,szegoKernel_ae w] with t hd hm hb hk
  change (szegoInf w) t=(szegoKernel w).val t at hb
  rw [hd,hm,hb,hk,← inv_pow,pow_two]

theorem bounded_derivativeSzegoKernel (w : Disk) : IsBounded (derivativeSzegoKernel w).val := by
  rw [derivativeSzegoKernel_eq_square]
  exact bounded_multiply (szegoInf w) _ (bounded_szegoKernel w)

/-- The genuine derivative of the analytic extension, with no Hardy premise on f. -/
theorem derivativeSzegoValue_backwardShift (f : BoundaryL2) (w : Disk) :
    derivativeSzegoValue (multiply (star coordinate) f) w.val=deriv (analyticValue f) w.val := by
  have hD : AnalyticOnNhd ℂ (deriv (analyticValue f)) disk :=
    fun z hz => (analyticOnNhd_analyticValue f z hz).deriv
  rw [← (hasSum_diskTaylorCoeff _ hD w.property).tsum_eq]
  unfold derivativeSzegoValue
  congr 1
  funext n
  rw [diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue,fourierCoeff_backwardShift]
  simp only [Nat.cast_add,Nat.cast_one]

theorem analyticValue_deriv_eq_derivativeSzegoPair (f : BoundaryL2) (w : Disk) :
    deriv (analyticValue f) w.val=
      inner ℂ (derivativeSzegoKernel w).val (multiply (star coordinate) f) := by
  rw [inner_derivativeSzegoKernel_boundaryL2,derivativeSzegoValue_backwardShift]

theorem cauchy_derivative_integral_conj (f : BoundaryL2) (w : Disk) :
    Integrable (fun t => f t*conj (fourier (T := 1) 1 t)/
      (1-w.val*conj (fourier (T := 1) 1 t))^2) circleMeasure ∧
      deriv (analyticValue f) w.val=∫ t,f t*conj (fourier (T := 1) 1 t)/
        (1-w.val*conj (fourier (T := 1) 1 t))^2 ∂circleMeasure := by
  have hAE : (fun t => inner ℂ ((derivativeSzegoKernel w).val t)
      ((multiply (star coordinate) f) t))=ᵐ[circleMeasure]
      fun t => f t*conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))^2 := by
    filter_upwards [derivativeSzegoKernel_ae w,multiply_ae (star coordinate) f,
      Lp.coeFn_star coordinate,coordinate_ae] with t hd hm hs hc
    change (star coordinate) t=conj (coordinate t) at hs
    rw [RCLike.inner_apply,hd,hm,hs,hc]
    simp only [map_inv₀,map_pow,map_sub,map_one,map_mul,Complex.conj_conj,div_eq_mul_inv]
    ring
  refine ⟨(L2.integrable_inner _ _).congr hAE,?_⟩
  rw [analyticValue_deriv_eq_derivativeSzegoPair,L2.inner_def]
  exact integral_congr_ae hAE



theorem unitCircle_cauchy_derivative_kernel (e z : ℂ) (he : ‖e‖=1) :
    conj e/(1-z*conj e)^2=e/(e-z)^2 := by
  have hUnit : conj e*e=1 := by simp only [Complex.conj_mul',he,one_pow,Complex.ofReal_one]
  have hInv : (conj e)⁻¹=e := inv_eq_of_mul_eq_one_right hUnit
  have hFactor : 1-z*conj e=(e-z)*conj e := by
    calc
      _ = e*conj e-z*conj e := by rw [mul_comm e (conj e),hUnit]
      _ = _ := by ring
  have hCancel : conj e*e^2=e := by
    calc
      _ = (conj e*e)*e := by ring
      _ = _ := by rw [hUnit,one_mul]
  rw [hFactor,mul_pow,div_eq_mul_inv,mul_inv_rev,← inv_pow,hInv,div_eq_mul_inv]
  calc
    _ = (conj e*e^2)*((e-z)^2)⁻¹ := by ring
    _ = _ := by rw [hCancel]

/-- Literal Cauchy derivative formula and integrability for every native boundary L² class. -/
theorem cauchy_derivative_integral (f : BoundaryL2) (w : Disk) :
    Integrable (fun t => f t*fourier (T := 1) 1 t/
      (fourier (T := 1) 1 t-w.val)^2) circleMeasure ∧
      deriv (analyticValue f) w.val=∫ t,f t*fourier (T := 1) 1 t/
        (fourier (T := 1) 1 t-w.val)^2 ∂circleMeasure := by
  have h := cauchy_derivative_integral_conj f w
  have he (t : Boundary) : f t*conj (fourier (T := 1) 1 t)/
      (1-w.val*conj (fourier (T := 1) 1 t))^2=
      f t*fourier (T := 1) 1 t/(fourier (T := 1) 1 t-w.val)^2 := by
    calc
      _ = f t*(conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))^2) := by ring
      _ = f t*(fourier (T := 1) 1 t/(fourier (T := 1) 1 t-w.val)^2) := by
        rw [unitCircle_cauchy_derivative_kernel _ _ (by simp)]
      _ = _ := by ring
  exact ⟨h.1.congr (Eventually.of_forall he),h.2.trans (integral_congr_ae (Eventually.of_forall he))⟩

theorem inner_szegoKernel_boundaryL2 (w : Disk) (f : BoundaryL2) :
    inner ℂ (szegoKernel w).val f=analyticValue f w.val := by
  have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (szegoKernel w) f
  rw [inner_szegoKernel,analyticValue_hardyProjection] at h
  exact h.symm

theorem analyticValue_backwardShift_integral (f : BoundaryL2) (w : Disk) :
    Integrable (fun t => f t*conj (fourier (T := 1) 1 t)/
      (1-w.val*conj (fourier (T := 1) 1 t))) circleMeasure ∧
      analyticValue (multiply (star coordinate) f) w.val=∫ t,f t*conj (fourier (T := 1) 1 t)/
        (1-w.val*conj (fourier (T := 1) 1 t)) ∂circleMeasure := by
  have hAE : (fun t => inner ℂ ((szegoKernel w).val t)
      ((multiply (star coordinate) f) t))=ᵐ[circleMeasure]
      fun t => f t*conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t)) := by
    filter_upwards [szegoKernel_ae w,multiply_ae (star coordinate) f,
      Lp.coeFn_star coordinate,coordinate_ae] with t hk hm hs hc
    change (star coordinate) t=conj (coordinate t) at hs
    rw [RCLike.inner_apply,hk,hm,hs,hc]
    simp only [map_inv₀,map_sub,map_one,map_mul,Complex.conj_conj,div_eq_mul_inv]
    ring
  refine ⟨(L2.integrable_inner _ _).congr hAE,?_⟩
  rw [← inner_szegoKernel_boundaryL2 w (multiply (star coordinate) f),L2.inner_def]
  exact integral_congr_ae hAE

theorem fourierCoeff_hardyBackwardShift_boundaryL2 (f : BoundaryL2) (n : ℕ) :
    fourierCoeff (hardyBackwardShift f) (n : ℤ)=fourierCoeff f ((n+1 : ℕ) : ℤ) := by
  rw [hardyBackwardShift,fourierCoeff_backwardShift,fourierCoeff_sub_L2,fourierCoeff_constL2,
    ite_eq_right (by omega : (n : ℤ)+1≠0),sub_zero]
  simp only [Nat.cast_add,Nat.cast_one]

theorem analyticValue_hardyBackwardShift_eq_raw (f : BoundaryL2) (z : ℂ) :
    analyticValue (hardyBackwardShift f) z=analyticValue (multiply (star coordinate) f) z := by
  unfold analyticValue
  congr 1
  funext n
  rw [fourierCoeff_hardyBackwardShift_boundaryL2,fourierCoeff_backwardShift]
  simp only [Nat.cast_add,Nat.cast_one]

/-- The same actual weighted kernel is defined for all boundary L² data. -/
def cauchyWeightedHardyKernel (f : BoundaryL2) (z : ℂ) : ℂ :=
  deriv (analyticValue f) z+analyticValue (hardyBackwardShift f) z

theorem cauchyWeightedHardyKernel_eq_projection (f : BoundaryL2) (z : ℂ) :
    cauchyWeightedHardyKernel f z=hardyWeightedPairingKernel (hardy.orthogonalProjectionOnto f) z := by
  have hVal : analyticValue (hardy.orthogonalProjectionOnto f).val=analyticValue f :=
    funext (analyticValue_hardyProjection f)
  have hBack : analyticValue (hardyBackwardShift (hardy.orthogonalProjectionOnto f).val) z=
      analyticValue (hardyBackwardShift f) z := by
    unfold analyticValue
    congr 1
    funext n
    rw [fourierCoeff_hardyBackwardShift_boundaryL2,fourierCoeff_hardyBackwardShift_boundaryL2,
      fourierCoeff_hardyProjection_nonneg]
  unfold cauchyWeightedHardyKernel hardyWeightedPairingKernel
  rw [hVal,hBack]

theorem cauchyWeightedHardyKernel_weighted_energy_le (f : BoundaryL2) :
    (∫⁻ z,ENNReal.ofReal ((1-‖z‖^2)*‖cauchyWeightedHardyKernel f z‖^2) ∂diskArea)≤
      ENNReal.ofReal (2*‖f‖^2) := by
  simp_rw [cauchyWeightedHardyKernel_eq_projection]
  have h := hardyWeightedPairingKernel_weighted_energy_le (hardy.orthogonalProjectionOnto f)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hn := hardy.norm_orthogonalProjectionOnto_apply_le f
  nlinarith [norm_nonneg (hardy.orthogonalProjectionOnto f),norm_nonneg f]



/-- Literal circle kernel of the weighted Hardy pairing transform. -/
def cauchyWeightedBoundaryKernel (w : Disk) (t : Boundary) : ℂ :=
  conj (fourier (T := 1) 1 t)*(2-w.val*conj (fourier (T := 1) 1 t))/
    (1-w.val*conj (fourier (T := 1) 1 t))^2

theorem norm_cauchy_denominator (w : Disk) (t : Boundary) :
    ‖1-w.val*conj (fourier (T := 1) 1 t)‖=‖fourier (T := 1) 1 t-w.val‖ := by
  have hUnit : conj (fourier (T := 1) 1 t)*fourier (T := 1) 1 t=1 := by
    simp only [Complex.conj_mul',fourier_one,Circle.norm_coe,one_pow,Complex.ofReal_one]
  have hFactor : (1-w.val*conj (fourier (T := 1) 1 t))*fourier (T := 1) 1 t=
      fourier (T := 1) 1 t-w.val := by
    rw [sub_mul,one_mul,mul_assoc,hUnit,mul_one]
  calc
    _ = ‖(1-w.val*conj (fourier (T := 1) 1 t))*fourier (T := 1) 1 t‖ := by
      rw [norm_mul,show ‖fourier (T := 1) 1 t‖=1 by simp,mul_one]
    _ = _ := by rw [hFactor]

theorem cauchy_denominator_ne_zero (w : Disk) (t : Boundary) :
    1-w.val*conj (fourier (T := 1) 1 t)≠0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_cauchy_denominator]
  apply norm_ne_zero_iff.mpr
  intro he
  have hEq : fourier (T := 1) 1 t=w.val := sub_eq_zero.mp he
  have hw : ‖w.val‖<1 := w.property
  rw [← hEq,show ‖fourier (T := 1) 1 t‖=1 by simp] at hw
  exact (lt_irrefl (1 : ℝ)) hw

theorem cauchyWeightedBoundaryKernel_eq_split (w : Disk) (t : Boundary) :
    cauchyWeightedBoundaryKernel w t=
      conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))^2+
        conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t)) := by
  unfold cauchyWeightedBoundaryKernel
  have hn := cauchy_denominator_ne_zero w t
  field_simp
  ring

theorem norm_cauchyWeightedBoundaryKernel_le (w : Disk) (t : Boundary) :
    ‖cauchyWeightedBoundaryKernel w t‖≤3/‖fourier (T := 1) 1 t-w.val‖^2 := by
  have hNum : ‖conj (fourier (T := 1) 1 t)*(2-w.val*conj (fourier (T := 1) 1 t))‖≤3 := by
    rw [norm_mul,Complex.norm_conj,show ‖fourier (T := 1) 1 t‖=1 by simp,one_mul]
    calc
      _ ≤ ‖(2 : ℂ)‖+‖w.val*conj (fourier (T := 1) 1 t)‖ := norm_sub_le _ _
      _ ≤ 3 := by
        rw [norm_mul,Complex.norm_conj,show ‖fourier (T := 1) 1 t‖=1 by simp,mul_one]
        have hw : ‖w.val‖<1 := w.property
        norm_num
        linarith
  rw [cauchyWeightedBoundaryKernel,norm_div,norm_pow,norm_cauchy_denominator]
  exact div_le_div_of_nonneg_right hNum (sq_nonneg _)

/-- Every arbitrary native L² datum has this ordinary integrable weighted Cauchy kernel. -/
theorem cauchyWeightedHardyKernel_integral (f : BoundaryL2) (w : Disk) :
    Integrable (fun t => f t*cauchyWeightedBoundaryKernel w t) circleMeasure ∧
      cauchyWeightedHardyKernel f w.val=∫ t,f t*cauchyWeightedBoundaryKernel w t ∂circleMeasure := by
  have hD := cauchy_derivative_integral_conj f w
  have hB := analyticValue_backwardShift_integral f w
  have hAE : ((fun t => f t*conj (fourier (T := 1) 1 t)/
      (1-w.val*conj (fourier (T := 1) 1 t))^2)+
      (fun t => f t*conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))))=ᵐ[circleMeasure]
      fun t => f t*cauchyWeightedBoundaryKernel w t := by
    refine Eventually.of_forall fun t => ?_
    change f t*conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))^2+
      f t*conj (fourier (T := 1) 1 t)/(1-w.val*conj (fourier (T := 1) 1 t))=
        f t*cauchyWeightedBoundaryKernel w t
    rw [cauchyWeightedBoundaryKernel_eq_split]
    ring
  refine ⟨(hD.1.add hB.1).congr hAE,?_⟩
  unfold cauchyWeightedHardyKernel
  rw [analyticValue_hardyBackwardShift_eq_raw,hD.2,hB.2,← integral_add hD.1 hB.1]
  exact integral_congr_ae hAE

theorem cauchyWeightedHardyKernel_constL2 (c : ℂ) (w : Disk) :
    cauchyWeightedHardyKernel (constL2 c) w.val=0 := by
  rw [cauchyWeightedHardyKernel_eq_projection]
  let G := hardy.orthogonalProjectionOnto (constL2 c)
  have hCoef (n : ℕ) : diskTaylorCoeff (hardyWeightedPairingKernel G) n=0 := by
    rw [diskTaylorCoeff_hardyWeightedPairingKernel]
    change ((n : ℂ)+2)*fourierCoeff (hardy.orthogonalProjectionOnto (constL2 c)).val
      ((n+1 : ℕ) : ℤ)=0
    rw [fourierCoeff_hardyProjection_nonneg,fourierCoeff_constL2,
      ite_eq_right (by omega : ((n+1 : ℕ) : ℤ)≠0),mul_zero]
  calc
    _ = ∑' n : ℕ,diskTaylorCoeff (hardyWeightedPairingKernel G) n*w.val^n :=
      (hasSum_diskTaylorCoeff _ (analyticOnNhd_hardyWeightedPairingKernel G) w.property).tsum_eq.symm
    _ = 0 := by simp only [hCoef,zero_mul,tsum_zero]

theorem cauchyWeightedHardyKernel_add (f g : BoundaryL2) (w : Disk) :
    cauchyWeightedHardyKernel (f+g) w.val=
      cauchyWeightedHardyKernel f w.val+cauchyWeightedHardyKernel g w.val := by
  rw [(cauchyWeightedHardyKernel_integral (f+g) w).2,
    (cauchyWeightedHardyKernel_integral f w).2,(cauchyWeightedHardyKernel_integral g w).2]
  have hAE : (fun t => (f+g) t*cauchyWeightedBoundaryKernel w t)=ᵐ[circleMeasure]
      fun t => f t*cauchyWeightedBoundaryKernel w t+g t*cauchyWeightedBoundaryKernel w t := by
    filter_upwards [Lp.coeFn_add f g] with t ht
    change (f+g) t=f t+g t at ht
    rw [ht,add_mul]
  rw [integral_congr_ae hAE,integral_add (cauchyWeightedHardyKernel_integral f w).1
    (cauchyWeightedHardyKernel_integral g w).1]

theorem cauchyWeightedHardyKernel_sub (f g : BoundaryL2) (w : Disk) :
    cauchyWeightedHardyKernel (f-g) w.val=
      cauchyWeightedHardyKernel f w.val-cauchyWeightedHardyKernel g w.val := by
  rw [(cauchyWeightedHardyKernel_integral (f-g) w).2,
    (cauchyWeightedHardyKernel_integral f w).2,(cauchyWeightedHardyKernel_integral g w).2]
  have hAE : (fun t => (f-g) t*cauchyWeightedBoundaryKernel w t)=ᵐ[circleMeasure]
      fun t => f t*cauchyWeightedBoundaryKernel w t-g t*cauchyWeightedBoundaryKernel w t := by
    filter_upwards [Lp.coeFn_sub f g] with t ht
    change (f-g) t=f t-g t at ht
    rw [ht,sub_mul]
  rw [integral_congr_ae hAE,integral_sub (cauchyWeightedHardyKernel_integral f w).1
    (cauchyWeightedHardyKernel_integral g w).1]

theorem cauchyWeightedHardyKernel_sub_const (f : BoundaryL2) (c : ℂ) (w : Disk) :
    cauchyWeightedHardyKernel (f-constL2 c) w.val=cauchyWeightedHardyKernel f w.val := by
  rw [cauchyWeightedHardyKernel_sub,cauchyWeightedHardyKernel_constL2,sub_zero]

end TTO.Paper.Proved
