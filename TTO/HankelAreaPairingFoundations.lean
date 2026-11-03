/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.FiniteHankelInterpolationFoundations
public import TTO.TriangularBoundFoundations
public import TTO.WeightedBergmanFoundations
public import TTO.WeightedPolarFoundations

/-! Actual unweighted analytic area moments and finite Hankel pairings for p>1. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem integral_radial_monomial_unweighted (n : ℕ) :
    (∫ r : ℝ,r^(2*n) ∂diskRadialMeasure)=1/((n : ℝ)+1) := by
  rw [integral_diskRadialMeasure]
  have he (r : ℝ) : (2*r) • r^(2*n)=2*r^(2*n+1) := by
    simp only [smul_eq_mul,pow_succ]
    ring
  simp_rw [he]
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul,integral_pow_zero_one]
  push_cast
  have hn : (n : ℝ)+1≠0 := by positivity
  field_simp
  ring

theorem integrable_analytic_disk_moment (F : ℂ → ℂ) (hf : Integrable F diskArea) (n : ℕ) :
    Integrable (fun z => conj z^n*F z) diskArea := by
  apply hf.bdd_mul (by fun_prop : Continuous (fun z : ℂ => conj z^n)).aestronglyMeasurable
  filter_upwards [ae_mem_diskArea] with z hz
  rw [norm_pow,Complex.norm_conj]
  exact pow_le_one₀ (norm_nonneg z) hz.le

/-- Exact normalized-area coefficient recovery, with actual ordinary integrability. -/
theorem analytic_disk_moment_of_integrable (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F disk) (n : ℕ)
    (hI : Integrable (fun z => conj z^n*F z) diskArea) :
    (∫ z,conj z^n*F z ∂diskArea)=diskTaylorCoeff F n/((n : ℂ)+1) := by
  rw [integral_diskArea_polar _ hI]
  calc
    _ = ∫ r : ℝ,diskTaylorCoeff F n*((r^(2*n) : ℝ) : ℂ) ∂diskRadialMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_mem_diskRadialMeasure] with r hr
      have he (t : Boundary) :
          conj ((r : ℂ)*fourier (T:=1) 1 t)^n*F ((r : ℂ)*fourier (T:=1) 1 t)=
          (r : ℂ)^n*(conj (fourier (T:=1) 1 t)^n*F ((r : ℂ)*fourier (T:=1) 1 t)) := by
        simp only [map_mul,Complex.conj_ofReal,mul_pow]
        ring
      simp_rw [he]
      rw [integral_const_mul,analytic_radial_circle_coefficient F hF r hr.1.le hr.2 n]
      push_cast
      rw [pow_mul]
      ring
    _ = _ := by
      rw [integral_const_mul,integral_complex_ofReal,integral_radial_monomial_unweighted]
      push_cast
      ring

theorem analytic_disk_moment (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (hf : Integrable F diskArea) (n : ℕ) :
    (∫ z,conj z^n*F z ∂diskArea)=diskTaylorCoeff F n/((n : ℂ)+1) :=
  analytic_disk_moment_of_integrable F hF n (integrable_analytic_disk_moment F hf n)

/-- The derivative coefficient cancels the area moment denominator exactly. -/
theorem analytic_deriv_disk_moment (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (hf : Integrable (deriv F) diskArea) (n : ℕ) :
    (∫ z,conj z^n*deriv F z ∂diskArea)=diskTaylorCoeff F (n+1) := by
  rw [analytic_disk_moment _ (fun z hz => (hF z hz).deriv) hf n,diskTaylorCoeff_deriv]
  push_cast
  have hn : (n : ℂ)+1≠0 := by exact_mod_cast (show (n : ℝ)+1≠0 by positivity)
  field_simp


/-- The literal positive-coefficient finite Hankel matrix, using Mathlib's matrix representation. -/
def finiteHankelCoefficientMatrix (N : ℕ) (a : ℕ → ℂ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Matrix.toEuclideanLin (fun i j : Fin N => a (i.val+j.val))).toContinuousLinearMap

theorem finiteHankelCoefficientMatrix_apply (N : ℕ) (a : ℕ → ℂ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    finiteHankelCoefficientMatrix N a x i=∑ j : Fin N,a (i.val+j.val)*x j := rfl

theorem finiteHankelCoefficientMatrix_entry (N : ℕ) (a : ℕ → ℂ) (i j : Fin N) :
    finiteHankelCoefficientMatrix N a (EuclideanSpace.single j (1 : ℂ)) i=a (i.val+j.val) := by
  change (∑ k : Fin N,a (i.val+k.val)*Pi.single (M:=fun _ : Fin N => ℂ) j (1 : ℂ) k)=_
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]

theorem finiteHSPair_eq_euclidean_sum (N : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) ℂ
      (EuclideanSpace ℂ (Fin N)))
    (T A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    finiteHSPair b T A=
      ∑ j : Fin N,inner ℂ (T (EuclideanSpace.single j (1 : ℂ)))
        (A (EuclideanSpace.single j (1 : ℂ))) := by
  let e : Fin N ≃ Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))) :=
    finCongr (by simp)
  rw [finiteHSPair_independent b ((EuclideanSpace.basisFun (Fin N) ℂ).reindex e)]
  simpa only [finiteHSPair,OrthonormalBasis.reindex_apply,EuclideanSpace.basisFun_apply] using
    e.symm.sum_comp (fun j : Fin N =>
      inner ℂ (T (EuclideanSpace.single j (1 : ℂ))) (A (EuclideanSpace.single j (1 : ℂ))))

theorem finiteHSPair_hankelCoefficientMatrix (N : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) ℂ
      (EuclideanSpace ℂ (Fin N)))
    (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (a : ℕ → ℂ) :
    finiteHSPair b T (finiteHankelCoefficientMatrix N a)=
      ∑ j : Fin N,∑ i : Fin N,conj (T (EuclideanSpace.single j (1 : ℂ)) i)*a (i.val+j.val) := by
  rw [finiteHSPair_eq_euclidean_sum]
  simp only [PiLp.inner_apply,RCLike.inner_apply,finiteHankelCoefficientMatrix_entry,mul_comm]


/-- Actual finite Hankel pairing with an integrable analytic area function.
The moment hypotheses are scalar integrals, with no Schatten conclusion hidden in them. -/
theorem finiteHSPair_of_disk_moments (N : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) ℂ
      (EuclideanSpace ℂ (Fin N)))
    (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (G : ℂ → ℂ) (hG : Integrable G diskArea) (a : ℕ → ℂ)
    (hMom : ∀ n : ℕ,(∫ z,conj z^n*G z ∂diskArea)=a n) :
    Integrable (fun z => G z*conj (finiteAntiDiagonalValue N T z)) diskArea ∧
      finiteHSPair b T (finiteHankelCoefficientMatrix N a)=
        ∫ z,G z*conj (finiteAntiDiagonalValue N T z) ∂diskArea := by
  let J := fun (i j : Fin N) (z : ℂ) =>
    conj (T (EuclideanSpace.single j (1 : ℂ)) i)*(conj z^(i.val+j.val)*G z)
  have hJ (i j : Fin N) : Integrable (J i j) diskArea :=
    (integrable_analytic_disk_moment G hG (i.val+j.val)).const_mul _
  have hSum : Integrable (fun z => ∑ i : Fin N,∑ j : Fin N,J i j z) diskArea :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hJ i j))
  have he (z : ℂ) : (∑ i : Fin N,∑ j : Fin N,J i j z)=
      G z*conj (finiteAntiDiagonalValue N T z) := by
    simp only [finiteAntiDiagonalValue,map_sum,map_mul,map_pow,Finset.mul_sum,J]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hInt : (∫ z,∑ i : Fin N,∑ j : Fin N,J i j z ∂diskArea)=
      ∑ i : Fin N,∑ j : Fin N,conj (T (EuclideanSpace.single j (1 : ℂ)) i)*a (i.val+j.val) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hJ i j))]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_finsetSum _ (fun j _ => hJ i j)]
    apply Finset.sum_congr rfl
    intro j _hj
    change (∫ z,conj (T (EuclideanSpace.single j (1 : ℂ)) i)*
      (conj z^(i.val+j.val)*G z) ∂diskArea)=_
    rw [integral_const_mul,hMom]
  refine ⟨hSum.congr (Eventually.of_forall he),?_⟩
  rw [finiteHSPair_hankelCoefficientMatrix,Finset.sum_comm,← hInt]
  exact integral_congr_ae (Eventually.of_forall he)

theorem finiteHSPair_analytic_area (N : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) ℂ
      (EuclideanSpace ℂ (Fin N)))
    (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) (hI : Integrable G diskArea) :
    Integrable (fun z => G z*conj (finiteAntiDiagonalValue N T z)) diskArea ∧
      finiteHSPair b T (finiteHankelCoefficientMatrix N
        (fun n => diskTaylorCoeff G n/((n : ℂ)+1)))=
        ∫ z,G z*conj (finiteAntiDiagonalValue N T z) ∂diskArea :=
  finiteHSPair_of_disk_moments N b T G hI _ (analytic_disk_moment G hG hI)

theorem finiteHSPair_analytic_deriv_area (N : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) ℂ
      (EuclideanSpace ℂ (Fin N)))
    (T : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk) (hI : Integrable (deriv F) diskArea) :
    Integrable (fun z => deriv F z*conj (finiteAntiDiagonalValue N T z)) diskArea ∧
      finiteHSPair b T (finiteHankelCoefficientMatrix N (fun n => diskTaylorCoeff F (n+1)))=
        ∫ z,deriv F z*conj (finiteAntiDiagonalValue N T z) ∂diskArea :=
  finiteHSPair_of_disk_moments N b T (deriv F) hI _ (analytic_deriv_disk_moment F hF hI)


/-- The angle-first base measure used by the already proved strong-p estimate. -/
def pellerPolarBase : Measure (ℝ × ℝ) :=
  (volume.restrict (Ico (0 : ℝ) 1)).prod diskRadialMeasure

def pellerPolarPoint (x : ℝ × ℝ) : ℂ := polarMap x.swap

def pellerAreaDensity (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1-‖z‖)^2)⁻¹)

def pellerAreaMeasure : Measure ℂ := diskArea.withDensity pellerAreaDensity

theorem measurable_pellerAreaDensity : Measurable pellerAreaDensity := by
  unfold pellerAreaDensity
  fun_prop

theorem continuous_pellerPolarPoint : Continuous pellerPolarPoint :=
  continuous_polarMap.comp continuous_swap

theorem pellerPolarBase_measurePreserving :
    MeasurePreserving pellerPolarPoint pellerPolarBase diskArea :=
  realPolar_measurePreserving.comp Measure.measurePreserving_swap

theorem ae_radial_mem_pellerPolarBase :
    ∀ᵐ x ∂pellerPolarBase,x.2∈Ioo (0 : ℝ) 1 :=
  (Measure.quasiMeasurePreserving_snd
    (μ:=volume.restrict (Ico (0 : ℝ) 1)) (ν:=diskRadialMeasure)).ae ae_mem_diskRadialMeasure

theorem norm_pellerPolarPoint (x : ℝ × ℝ) (hx : 0≤x.2) :
    ‖pellerPolarPoint x‖=x.2 := by
  simp only [pellerPolarPoint,polarMap,Prod.fst_swap,Prod.snd_swap,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg hx,
    show ‖fourier (T:=1) 1 (x.1 : Boundary)‖=1 by simp,mul_one]

theorem pellerRadialMeasure_eq_density :
    pellerRadialMeasure=diskRadialMeasure.withDensity
      (fun r : ℝ => ENNReal.ofReal (((1-r)^2)⁻¹)) := by
  rw [diskRadialMeasure,← withDensity_mul _ (by fun_prop) (by fun_prop),pellerRadialMeasure]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  change ENNReal.ofReal (2*r/(1-r)^2)=
    ENNReal.ofReal (2*r)*ENNReal.ofReal (((1-r)^2)⁻¹)
  exact ENNReal.ofReal_mul (mul_nonneg (by norm_num) hr.1.le)

theorem pellerPolarMeasure_eq_density :
    pellerPolarMeasure=pellerPolarBase.withDensity (pellerAreaDensity ∘ pellerPolarPoint) := by
  rw [pellerPolarMeasure,pellerRadialMeasure_eq_density,
    prod_withDensity_right (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_radial_mem_pellerPolarBase] with x hx
  change ENNReal.ofReal (((1-x.2)^2)⁻¹)=pellerAreaDensity (pellerPolarPoint x)
  rw [pellerAreaDensity,norm_pellerPolarPoint x hx.1.le]

/-- Exact pushforward of the singular radial weight; it is valid before any Lp finiteness. -/
theorem pellerAreaMeasure_eq_map :
    pellerAreaMeasure=Measure.map pellerPolarPoint pellerPolarMeasure := by
  symm
  rw [pellerPolarMeasure_eq_density]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map' hf.aemeasurable continuous_pellerPolarPoint.measurable.aemeasurable]
  calc
    _ = ∫⁻ x,pellerAreaDensity (pellerPolarPoint x)*f (pellerPolarPoint x) ∂pellerPolarBase := by
      simpa only [Function.comp_def,Pi.mul_apply] using
        lintegral_withDensity_eq_lintegral_mul pellerPolarBase
          (measurable_pellerAreaDensity.comp continuous_pellerPolarPoint.measurable)
          (hf.comp continuous_pellerPolarPoint.measurable)
    _ = ∫⁻ z,pellerAreaDensity z*f z ∂diskArea :=
      pellerPolarBase_measurePreserving.lintegral_comp (measurable_pellerAreaDensity.mul hf)
    _ = _ := by
      simpa only [pellerAreaMeasure,Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul diskArea measurable_pellerAreaDensity hf).symm


/-- Literal multiplication by the boundary distance in disk and polar variables. -/
def pellerDiskLift (G : ℂ → ℂ) (z : ℂ) : ℂ := ((1-‖z‖ : ℝ) : ℂ)*G z

def pellerLift (G : ℂ → ℂ) (x : ℝ × ℝ) : ℂ := ((1-x.2 : ℝ) : ℂ)*G (pellerPolarPoint x)

theorem aestronglyMeasurable_analytic_disk (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk) :
    AEStronglyMeasurable G diskArea := by
  rw [diskArea]
  exact (hG.continuousOn.aestronglyMeasurable
    (isOpen_lt continuous_norm continuous_const).measurableSet).smul_measure _

theorem aestronglyMeasurable_pellerDiskLift (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) :
    AEStronglyMeasurable (pellerDiskLift G) diskArea :=
  (by fun_prop : Continuous (fun z : ℂ => ((1-‖z‖ : ℝ) : ℂ))).aestronglyMeasurable.mul hG

theorem pellerLift_ae_diskLift (G : ℂ → ℂ) :
    pellerLift G =ᵐ[pellerPolarMeasure] pellerDiskLift G ∘ pellerPolarPoint := by
  filter_upwards [ae_radial_mem_pellerPolarMeasure] with x hx
  simp only [pellerLift,Function.comp_def,pellerDiskLift,norm_pellerPolarPoint x hx.1.le]

/-- The singular density converts the lifted Lp integral to the actual derivative area weight.
No finiteness assumption is used, so infinite energy remains infinite. -/
theorem lintegral_pellerDiskLift_rpow (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) :
    (∫⁻ z,ENNReal.ofReal (‖pellerDiskLift G z‖^p) ∂pellerAreaMeasure)=
      ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea := by
  have hL := aestronglyMeasurable_pellerDiskLift G hG
  have hZ : AEMeasurable (fun z => ENNReal.ofReal (‖pellerDiskLift G z‖^p)) diskArea :=
    (hL.norm.aemeasurable.pow_const p).ennreal_ofReal
  rw [pellerAreaMeasure,lintegral_withDensity_eq_lintegral_mul₀
    measurable_pellerAreaDensity.aemeasurable hZ]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_diskArea] with z hz
  have hd : 0<1-‖z‖ := by exact sub_pos.mpr hz
  change ENNReal.ofReal (((1-‖z‖)^2)⁻¹)*
    ENNReal.ofReal (‖pellerDiskLift G z‖^p)=_
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
  congr 1
  rw [pellerDiskLift,norm_mul,Complex.norm_real,Real.norm_of_nonneg hd.le,
    Real.mul_rpow hd.le (norm_nonneg _),Real.rpow_sub hd,Real.rpow_two]
  ring

theorem lintegral_pellerLift_rpow (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) :
    (∫⁻ x,ENNReal.ofReal (‖pellerLift G x‖^p) ∂pellerPolarMeasure)=
      ∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea := by
  have hL : AEStronglyMeasurable (pellerDiskLift G) pellerAreaMeasure :=
    (aestronglyMeasurable_pellerDiskLift G hG).mono_ac (withDensity_absolutelyContinuous _ _)
  have hZ : AEMeasurable (fun z => ENNReal.ofReal (‖pellerDiskLift G z‖^p))
      (Measure.map pellerPolarPoint pellerPolarMeasure) := by
    rw [← pellerAreaMeasure_eq_map]
    exact (hL.norm.aemeasurable.pow_const p).ennreal_ofReal
  calc
    _ = ∫⁻ x,ENNReal.ofReal (‖pellerDiskLift G (pellerPolarPoint x)‖^p)
        ∂pellerPolarMeasure := by
      apply lintegral_congr_ae
      exact (pellerLift_ae_diskLift G).mono fun x hx =>
        congrArg (fun v : ℂ => ENNReal.ofReal (‖v‖^p)) hx
    _ = ∫⁻ z,ENNReal.ofReal (‖pellerDiskLift G z‖^p) ∂pellerAreaMeasure := by
      rw [pellerAreaMeasure_eq_map,
        lintegral_map' hZ continuous_pellerPolarPoint.measurable.aemeasurable]
    _ = _ := lintegral_pellerDiskLift_rpow G hG p


theorem aestronglyMeasurable_pellerLift (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) :
    AEStronglyMeasurable (pellerLift G) pellerPolarMeasure := by
  have hL : AEStronglyMeasurable (pellerDiskLift G)
      (Measure.map pellerPolarPoint pellerPolarMeasure) := by
    rw [← pellerAreaMeasure_eq_map]
    exact (aestronglyMeasurable_pellerDiskLift G hG).mono_ac
      (withDensity_absolutelyContinuous _ _)
  exact (hL.comp_measurable continuous_pellerPolarPoint.measurable).congr
    (pellerLift_ae_diskLift G).symm

/-- Finite genuine derivative energy supplies native Lp on the actual singular polar measure. -/
theorem memLp_pellerLift_of_energy (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) (hp : 0<p)
    (hE : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞) :
    MemLp (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure := by
  have hL := aestronglyMeasurable_pellerLift G hG
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top hL).mpr
  have he (x : ℝ × ℝ) :
      ‖pellerLift G x‖ₑ^(ENNReal.ofReal p).toReal=
        ENNReal.ofReal (‖pellerLift G x‖^p) := by
    rw [ENNReal.toReal_ofReal hp.le,← ofReal_norm]
    exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (pellerLift G x)) hp.le
  rw [lintegral_congr he,lintegral_pellerLift_rpow G hG p]
  exact hE

theorem lintegral_pellerLift_finiteAntiDiagonal_le (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℝ) (hp : 1<p) :
    (∫⁻ x,ENNReal.ofReal (‖pellerLift (finiteAntiDiagonalValue N A) x‖^p)
      ∂pellerPolarMeasure)≤
      ENNReal.ofReal (2621440*p*2^(p-1)/(p-1)*schattenNorm p A^p) := by
  have he :
      (fun x => ENNReal.ofReal (‖pellerLift (finiteAntiDiagonalValue N A) x‖^p)) =ᵐ[pellerPolarMeasure]
      (fun x : ℝ × ℝ => ENNReal.ofReal (((1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖)^p)) := by
    filter_upwards [ae_radial_mem_pellerPolarMeasure] with x hx
    rw [pellerLift,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by linarith [hx.2])]
    rfl
  rw [lintegral_congr_ae he]
  exact finiteAntiDiagonal_strong_p N A p hp

theorem memLp_pellerLift_finiteAntiDiagonal (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℝ) (hp : 1<p) :
    MemLp (pellerLift (finiteAntiDiagonalValue N A)) (ENNReal.ofReal p) pellerPolarMeasure := by
  have hM := (continuous_finiteAntiDiagonalValue N A).aestronglyMeasurable (μ:=diskArea)
  apply memLp_pellerLift_of_energy _ hM p (lt_trans zero_lt_one hp)
  rw [← lintegral_pellerLift_rpow _ hM p]
  exact (lintegral_pellerLift_finiteAntiDiagonal_le N A p hp).trans_lt ENNReal.ofReal_lt_top


/-- Hölder first establishes ordinary integrability; the exact density then cancels.
Neither factor is assumed unweighted L1. -/
theorem pellerLift_pairing {p q : ℝ} (hpq : p.HolderConjugate q)
    (G W : ℂ → ℂ) (hG : AEStronglyMeasurable G diskArea)
    (hW : AEStronglyMeasurable W diskArea)
    (hLG : MemLp (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure)
    (hLW : MemLp (pellerLift W) (ENNReal.ofReal q) pellerPolarMeasure) :
    Integrable (fun z => G z*conj (W z)) diskArea ∧
      (∫ x,pellerLift G x*conj (pellerLift W x) ∂pellerPolarMeasure)=
        ∫ z,G z*conj (W z) ∂diskArea := by
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := hpq.ennrealOfReal
  let J := fun z : ℂ => pellerDiskLift G z*conj (pellerDiskLift W z)
  have hI : Integrable (fun x => pellerLift G x*conj (pellerLift W x)) pellerPolarMeasure :=
    hLG.integrable_mul hLW.star
  have he : (fun x => pellerLift G x*conj (pellerLift W x)) =ᵐ[pellerPolarMeasure]
      J ∘ pellerPolarPoint :=
    (pellerLift_ae_diskLift G).mul ((pellerLift_ae_diskLift W).fun_comp conj)
  have hJM : AEStronglyMeasurable J pellerAreaMeasure :=
    ((aestronglyMeasurable_pellerDiskLift G hG).mul
      (aestronglyMeasurable_pellerDiskLift W hW).star).mono_ac
        (withDensity_absolutelyContinuous _ _)
  have hJMap : AEStronglyMeasurable J (Measure.map pellerPolarPoint pellerPolarMeasure) := by
    rw [← pellerAreaMeasure_eq_map]
    exact hJM
  have hJ : Integrable J pellerAreaMeasure := by
    rw [pellerAreaMeasure_eq_map]
    exact (integrable_map_measure hJMap continuous_pellerPolarPoint.measurable.aemeasurable).mpr
      (hI.congr he)
  have hDTop : ∀ᵐ z ∂diskArea,pellerAreaDensity z<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hDJ : Integrable (fun z => (pellerAreaDensity z).toReal • J z) diskArea :=
    (integrable_withDensity_iff_integrable_smul' measurable_pellerAreaDensity hDTop).mp hJ
  have hCancel : (fun z => (pellerAreaDensity z).toReal • J z) =ᵐ[diskArea]
      (fun z => G z*conj (W z)) := by
    filter_upwards [ae_mem_diskArea] with z hz
    have hd : 0<1-‖z‖ := sub_pos.mpr hz
    have hc : (1-(‖z‖ : ℂ))≠0 := by exact_mod_cast hd.ne'
    dsimp only [J,pellerDiskLift,pellerAreaDensity]
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _)),
      RCLike.real_smul_eq_coe_mul,map_mul,Complex.conj_ofReal]
    push_cast
    field_simp [hc]
    ring!
  refine ⟨hDJ.congr hCancel,?_⟩
  calc
    _ = ∫ x,J (pellerPolarPoint x) ∂pellerPolarMeasure := integral_congr_ae he
    _ = ∫ z,J z ∂pellerAreaMeasure := by
      rw [pellerAreaMeasure_eq_map,
        integral_map continuous_pellerPolarPoint.measurable.aemeasurable hJMap]
    _ = ∫ z,(pellerAreaDensity z).toReal • J z ∂diskArea :=
      integral_withDensity_eq_integral_toReal_smul measurable_pellerAreaDensity hDTop J
    _ = _ := integral_congr_ae hCancel

theorem norm_area_pairing_le_pellerLp {p q : ℝ} (hpq : p.HolderConjugate q)
    (G W : ℂ → ℂ) (hG : AEStronglyMeasurable G diskArea)
    (hW : AEStronglyMeasurable W diskArea)
    (hLG : MemLp (pellerLift G) (ENNReal.ofReal p) pellerPolarMeasure)
    (hLW : MemLp (pellerLift W) (ENNReal.ofReal q) pellerPolarMeasure) :
    ‖∫ z,G z*conj (W z) ∂diskArea‖≤
      (∫ x,‖pellerLift G x‖^p ∂pellerPolarMeasure)^(1/p)*
      (∫ x,‖pellerLift W x‖^q ∂pellerPolarMeasure)^(1/q) := by
  rw [← (pellerLift_pairing hpq G W hG hW hLG hLW).2]
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,Complex.norm_conj] using
    integral_mul_norm_le_Lp_mul_Lq hpq hLG hLW


theorem finiteAntiDiagonalValue_one (z : ℂ) :
    finiteAntiDiagonalValue 1 (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) z=1 := by
  simp [finiteAntiDiagonalValue]

/-- For p>1 the genuine weighted energy implies ordinary area L1.
This discharges the explicit L1 premise in the analytic moment lemmas. -/
theorem integrable_of_peller_energy (G : ℂ → ℂ)
    (hG : AEStronglyMeasurable G diskArea) (p : ℝ) (hp : 1<p)
    (hE : (∫⁻ z,ENNReal.ofReal (‖G z‖^p*(1-‖z‖)^(p-2)) ∂diskArea)<∞) :
    Integrable G diskArea := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hLG := memLp_pellerLift_of_energy G hG p hpq.pos hE
  have hLW := memLp_pellerLift_finiteAntiDiagonal 1
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) q hpq.symm.lt
  have hConst : finiteAntiDiagonalValue 1
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))=(fun _ : ℂ => (1 : ℂ)) :=
    funext finiteAntiDiagonalValue_one
  rw [hConst] at hLW
  obtain ⟨hI,_⟩ := pellerLift_pairing hpq G (fun _ => 1) hG
    (by fun_prop : Continuous (fun _ : ℂ => (1 : ℂ))).aestronglyMeasurable hLG hLW
  simpa only [map_one,mul_one] using hI

end TTO.Paper.Proved
