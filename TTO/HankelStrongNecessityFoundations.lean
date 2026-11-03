/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BesovWeightFoundations
public import TTO.CauchyDerivativeFoundations
public import TTO.HankelDerivativePairingFoundations

/-! Genuine finite-corner limits and strong-p necessity for classical Hankel operators. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem finiteSequenceInclusion_single (N : ℕ) (j : Fin N) :
    finiteSequenceInclusion N (EuclideanSpace.single j (1 : ℂ))=
      lp.single 2 j.val (1 : ℂ) := by
  apply lp.ext
  funext i
  by_cases hi : i<N
  · rw [finiteSequenceInclusion_at N _ ⟨i,hi⟩]
    simp only [PiLp.single_apply,lp.single_apply,Pi.single_apply,Fin.ext_iff]
  · change finiteAnalysis (EuclideanSpace.basisFun (Fin N) ℂ)
      (EuclideanSpace.single j (1 : ℂ)) i=((lp.single 2 j.val (1 : ℂ) : SequenceL2)) i
    rw [finiteAnalysis_outside _ _ i (by omega)]
    simp only [lp.single_apply,Pi.single_apply,ite_eq_right (by omega : i≠j.val)]

theorem finiteSequenceInclusion_adjoint_at (N : ℕ) (x : SequenceL2) (i : Fin N) :
    (finiteSequenceInclusion N).adjoint x i=x i.val := by
  simpa only [finiteSequenceInclusion_single,EuclideanSpace.inner_single_left,
    lp.inner_single_left,map_one,one_mul,RCLike.inner_apply,mul_one] using
    ContinuousLinearMap.adjoint_inner_right (finiteSequenceInclusion N)
      (EuclideanSpace.single i (1 : ℂ)) x

theorem finiteHankelCoefficientMatrix_eq_compression (N : ℕ) (a : ℕ→ℂ)
    (Z : SequenceOperator)
    (hZ : ∀ i j : ℕ,Z (lp.single 2 j (1 : ℂ)) i=a (i+j)) :
    finiteHankelCoefficientMatrix N a=
      (finiteSequenceInclusion N).adjoint ∘L Z ∘L finiteSequenceInclusion N := by
  classical
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.ext
  intro j
  change finiteHankelCoefficientMatrix N a ((EuclideanSpace.basisFun (Fin N) ℂ) j)=_
  rw [EuclideanSpace.basisFun_apply]
  ext i
  simpa only [ContinuousLinearMap.coe_coe,OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply,ContinuousLinearMap.comp_apply,finiteSequenceInclusion_single,
    finiteSequenceInclusion_adjoint_at,finiteHankelCoefficientMatrix_entry] using (hZ i.val j.val).symm

theorem finiteHankelCoefficientMatrix_schatten_le (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    {p : ℝ} (hS : Schatten p H) (N : ℕ) :
    Schatten p (finiteHankelCoefficientMatrix N (fun n => fourierCoeff g (n : ℤ))) ∧
      schattenNorm p (finiteHankelCoefficientMatrix N (fun n => fourierCoeff g (n : ℤ)))≤
        schattenNorm p H := by
  let Z := (hankelSequenceOperator H).adjoint
  have hE (i j : ℕ) : Z (lp.single 2 j (1 : ℂ)) i=fourierCoeff g ((i+j : ℕ) : ℤ) := by
    rw [sequenceAdjoint_single_entry,hankelSequenceOperator_coefficient g H hH]
    simp only [starRingEnd_self_apply]
    rw [Nat.add_comm]
  have hSeq := schatten_hankelSequenceOperator H hS
  have hZ : Schatten p Z := (schatten_adjoint_iff _ p).mpr hSeq.1
  rw [finiteHankelCoefficientMatrix_eq_compression N _ Z hE]
  have h := schatten_contracting_composition hZ (finiteSequenceInclusion N).adjoint
    (finiteSequenceInclusion N)
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le (norm_finiteSequenceInclusion_le_one N))
    (norm_finiteSequenceInclusion_le_one N)
  exact ⟨h.1,h.2.trans ((schattenNorm_adjoint_eq _ p).trans_le hSeq.2)⟩

theorem summable_hankelAntidiagonal_terms (g : BoundaryL2) (z : Disk) :
    Summable (fun ij : ℕ×ℕ => fourierCoeff g ((ij.1+ij.2 : ℕ) : ℤ)*z.val^(ij.1+ij.2)) := by
  have hc : Summable (fun n : ℕ => ‖z.val‖^n) :=
    (hasSum_geometric_of_norm_lt_one
      (by simpa only [Real.norm_of_nonneg (norm_nonneg z.val)] using (show ‖z.val‖<1 from z.property))).summable
  have hp : Summable (fun ij : ℕ×ℕ => ‖z.val‖^ij.1*‖z.val‖^ij.2) :=
    hc.mul_of_nonneg hc (fun n => pow_nonneg (norm_nonneg z.val) n)
      (fun n => pow_nonneg (norm_nonneg z.val) n)
  refine Summable.of_norm_bounded (hp.mul_left ‖g‖) ?_
  intro ij
  simp only [norm_mul,norm_pow,pow_add]
  exact mul_le_mul_of_nonneg_right (norm_fourierCoeff_le g _)
    (mul_nonneg (pow_nonneg (norm_nonneg z.val) _) (pow_nonneg (norm_nonneg z.val) _))

theorem tsum_hankelAntidiagonal_terms (g : BoundaryL2) (z : Disk) :
    (∑' ij : ℕ×ℕ,fourierCoeff g ((ij.1+ij.2 : ℕ) : ℤ)*z.val^(ij.1+ij.2))=
      derivativeSzegoValue g z.val := by
  rw [(summable_hankelAntidiagonal_terms g z).tsum_prod,
    tsum_antidiagonal_of_summable _ (summable_hankelAntidiagonal_terms g z)]
  unfold derivativeSzegoValue
  apply tsum_congr
  intro n
  calc
    _ = ∑ ij ∈ Finset.antidiagonal n,fourierCoeff g (n : ℤ)*z.val^n := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [Finset.mem_antidiagonal.mp hij]
    _ = _ := by
      simp only [Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      ring

theorem tendsto_square_finset_range :
    Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro m n hmn
    exact Finset.product_subset_product (Finset.range_mono hmn) (Finset.range_mono hmn)
  · intro ij
    refine ⟨max ij.1 ij.2+1,?_⟩
    simp only [Finset.mem_product,Finset.mem_range]
    omega

theorem tendsto_finiteAntiDiagonalHankel (g : BoundaryL2) (z : Disk) :
    Tendsto (fun N : ℕ => finiteAntiDiagonalValue N
      (finiteHankelCoefficientMatrix N (fun n => fourierCoeff g (n : ℤ))) z.val)
        atTop (𝓝 (derivativeSzegoValue g z.val)) := by
  have h := (summable_hankelAntidiagonal_terms g z).hasSum.comp tendsto_square_finset_range
  rw [tsum_hankelAntidiagonal_terms g z] at h
  dsimp only [Function.comp_def] at h
  simpa only [Finset.sum_product,Finset.sum_range,finiteAntiDiagonalValue,
    finiteHankelCoefficientMatrix_entry] using h

theorem derivativeSzegoValue_eq_coordinate_deriv (g : BoundaryL2) (z : Disk) :
    derivativeSzegoValue g z.val=deriv (analyticValue (multiply coordinate g)) z.val := by
  have h := derivativeSzegoValue_backwardShift (multiply coordinate g) z
  rwa [multiply_star_cancel coordinate coordinate_unimodular] at h

theorem hankel_coordinate_derivative_energy_le (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    (∫⁻ z,ENNReal.ofReal
      (‖deriv (analyticValue (multiply coordinate g)) z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)≤
        ENNReal.ofReal (pellerStrongConstant p*schattenNorm p H^p) := by
  let A := fun N => finiteHankelCoefficientMatrix N (fun n => fourierCoeff g (n : ℤ))
  let W := fun N => finiteAntiDiagonalValue N (A N)
  let G := deriv (analyticValue (multiply coordinate g))
  let Φ := fun N x => ENNReal.ofReal (‖pellerLift (W N) x‖^p)
  have hG : AnalyticOnNhd ℂ G disk :=
    fun z hz => (analyticOnNhd_analyticValue (multiply coordinate g) z hz).deriv
  have hMeas (N : ℕ) : AEMeasurable (Φ N) pellerPolarMeasure :=
    ((memLp_pellerLift_finiteAntiDiagonal N (A N) p hp).aestronglyMeasurable.norm.aemeasurable.pow_const p).ennreal_ofReal
  have hLim : ∀ᵐ x ∂pellerPolarMeasure,
      Tendsto (fun N => pellerLift (W N) x) atTop (𝓝 (pellerLift G x)) := by
    filter_upwards [ae_radial_mem_pellerPolarMeasure] with x hx
    have hz : pellerPolarPoint x∈disk := by
      change ‖pellerPolarPoint x‖<1
      rw [norm_pellerPolarPoint x hx.1.le]
      exact hx.2
    have h := tendsto_finiteAntiDiagonalHankel g ⟨pellerPolarPoint x,hz⟩
    rw [derivativeSzegoValue_eq_coordinate_deriv] at h
    exact tendsto_const_nhds.mul h
  have hEq : (fun x => liminf (fun N => Φ N x) atTop)=ᵐ[pellerPolarMeasure]
      (fun x => ENNReal.ofReal (‖pellerLift G x‖^p)) := by
    filter_upwards [hLim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (hx.norm.rpow_const (Or.inr (lt_trans zero_lt_one hp).le))).liminf_eq
  have hFatou := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hMeas
  rw [lintegral_congr_ae hEq] at hFatou
  have hBound (N : ℕ) : (∫⁻ x,Φ N x ∂pellerPolarMeasure)≤
      ENNReal.ofReal (pellerStrongConstant p*schattenNorm p H^p) := by
    have h := lintegral_pellerLift_finiteAntiDiagonal_le N (A N) p hp
    change (∫⁻ x,Φ N x ∂pellerPolarMeasure)≤
      ENNReal.ofReal (pellerStrongConstant p*schattenNorm p (A N)^p) at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (pellerStrongConstant_pos p hp).le
    exact Real.rpow_le_rpow (schattenNorm_nonneg p (A N))
      (finiteHankelCoefficientMatrix_schatten_le g H hH hS N).2
      (lt_trans zero_lt_one hp).le
  have h := hFatou.trans
    (liminf_le_of_frequently_le' (Eventually.of_forall hBound).frequently)
  rw [lintegral_pellerLift_rpow G (aestronglyMeasurable_analytic_disk G hG) p] at h
  exact h

theorem hankel_homogeneousBesov_energy_le (g : BoundaryL2) (hg : g∈hardy)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    homogeneousBesovEnergy p (fun z => z*analyticValue g z)≤
      ENNReal.ofReal ((2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p) := by
  rw [homogeneousBesovEnergy_coordinate_of_one_lt ⟨g,hg⟩ p hp]
  let G := deriv (analyticValue (multiply coordinate g))
  calc
    _ ≤ ENNReal.ofReal (2^|p-2|)*
        ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea :=
      lintegral_frozenDiskWeight_le (fun z => ‖G z‖^p)
        (fun z _ => Real.rpow_nonneg (norm_nonneg (G z)) p) (p-2)
    _ ≤ ENNReal.ofReal (2^|p-2|)*
        ENNReal.ofReal (pellerStrongConstant p*schattenNorm p H^p) :=
      mul_le_mul_right (hankel_coordinate_derivative_energy_le g H hH p hp hS) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0≤(2 : ℝ)^|p-2|)]
      congr 1
      ring

theorem hankel_homogeneousBesov_necessity (g : BoundaryL2) (hg : g∈hardy)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 1<p) (hS : Schatten p H) :
    homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞ ∧
      homogeneousBesovNorm p (fun z => z*analyticValue g z)≤
        (2^|p-2| *pellerStrongConstant p)^(1/p)*schattenNorm p H := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hK : 0≤2^|p-2| *pellerStrongConstant p :=
    mul_nonneg (by positivity) (pellerStrongConstant_pos p hp).le
  have hEnergy := hankel_homogeneousBesov_energy_le g hg H hH p hp hS
  refine ⟨hEnergy.trans_lt ENNReal.ofReal_lt_top,?_⟩
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEnergy
  rw [ENNReal.toReal_ofReal
    (mul_nonneg hK (Real.rpow_nonneg (schattenNorm_nonneg p H) p))] at hReal
  unfold homogeneousBesovNorm
  calc
    _ ≤ ((2^|p-2| *pellerStrongConstant p)*schattenNorm p H^p)^(1/p) :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg hReal (one_div_pos.mpr hp0).le
    _ = _ := by
      rw [Real.mul_rpow hK (Real.rpow_nonneg (schattenNorm_nonneg p H) p),
        one_div,Real.rpow_rpow_inv (schattenNorm_nonneg p H) hp0.ne']

theorem classicalHankel_schatten_gt_one_homogeneous (p : ℝ) (hp : 1<p)
    (g : BoundaryL2) (hg : g∈hardy) :
    HasSchattenHankel p (star (multiply coordinate g)) ↔
      homogeneousBesovEnergy p (fun z => z*analyticValue g z)<∞ := by
  constructor
  · rintro ⟨H,hH,hS⟩
    exact (hankel_homogeneousBesov_energy_le g hg H hH p hp hS).trans_lt
      ENNReal.ofReal_lt_top
  · intro hE
    obtain ⟨H,hH,hS,_⟩ := exists_schattenHankel_of_homogeneousBesov_gt_one
      g hg p (Real.conjExponent p) (Real.HolderConjugate.conjExponent hp) hE
    exact ⟨H,hH,hS⟩

end TTO.Paper.Proved
