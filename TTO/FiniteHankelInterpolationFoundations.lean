/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SchattenCutoffBoundsFoundations
public import TTO.PolarCarlesonFoundations
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Actual finite antidiagonal averaging for the p>1 Hankel argument. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The actual finite geometric evaluation vector. -/
def finitePowerVector (N : ℕ) (z : ℂ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i : Fin N => z^i.val)

theorem finitePowerVector_sum (N : ℕ) (z : ℂ) :
    finitePowerVector N z=∑ i : Fin N,z^i.val • EuclideanSpace.single i (1 : ℂ) := by
  simpa only [EuclideanSpace.basisFun_repr,finitePowerVector,PiLp.toLp_apply,
    EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin N) ℂ).sum_repr (finitePowerVector N z)).symm

/-- The coefficient at degree n is the sum of the actual matrix entries on antidiagonal n. -/
def finiteAntiDiagonalValue (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (z : ℂ) : ℂ :=
  ∑ i : Fin N,∑ j : Fin N,A (EuclideanSpace.single j (1 : ℂ)) i*z^(i.val+j.val)

theorem finiteAntiDiagonalValue_eq_inner (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (z : ℂ) :
    finiteAntiDiagonalValue N A z=
      inner ℂ (finitePowerVector N (conj z)) (A (finitePowerVector N z)) := by
  rw [finitePowerVector_sum N z,map_sum,inner_sum]
  simp only [map_smul,inner_smul_right,PiLp.inner_apply,RCLike.inner_apply,finitePowerVector,
    map_pow,starRingEnd_self_apply]
  rw [finiteAntiDiagonalValue,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_add]
  ring

theorem finitePowerVector_norm_conj (N : ℕ) (z : ℂ) :
    ‖finitePowerVector N (conj z)‖=‖finitePowerVector N z‖ := by
  simp only [EuclideanSpace.norm_eq,finitePowerVector,norm_pow,Complex.norm_conj]

theorem finitePowerVector_norm_sq_le (N : ℕ) (z : ℂ) (hz : ‖z‖<1) :
    ‖finitePowerVector N z‖^2≤(1-‖z‖^2)⁻¹ := by
  have hn : ‖(‖z‖^2 : ℝ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z‖)]
    nlinarith [norm_nonneg z]
  have hsum := (hasSum_geometric_of_norm_lt_one hn).summable.sum_le_tsum (Finset.range N)
    (fun i _hi => pow_nonneg (sq_nonneg ‖z‖) i)
  rw [tsum_geometric_of_norm_lt_one hn] at hsum
  rw [EuclideanSpace.norm_sq_eq]
  simp only [finitePowerVector,PiLp.toLp_apply,norm_pow]
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  simpa only [← pow_mul,Nat.mul_comm] using hsum

theorem norm_finiteAntiDiagonalValue_le (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (z : ℂ) (hz : ‖z‖<1) :
    ‖finiteAntiDiagonalValue N A z‖≤‖A‖/(1-‖z‖^2) := by
  rw [finiteAntiDiagonalValue_eq_inner]
  calc
    _ ≤ ‖finitePowerVector N (conj z)‖*‖A (finitePowerVector N z)‖ := norm_inner_le_norm _ _
    _ ≤ ‖finitePowerVector N (conj z)‖*(‖A‖*‖finitePowerVector N z‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = ‖A‖*‖finitePowerVector N z‖^2 := by rw [finitePowerVector_norm_conj]; ring
    _ ≤ ‖A‖*((1-‖z‖^2)⁻¹) :=
      mul_le_mul_of_nonneg_left (finitePowerVector_norm_sq_le N z hz) (norm_nonneg A)
    _ = _ := rfl

/-- The genuine operator-norm endpoint is uniform in the matrix dimension. -/
theorem finiteAntiDiagonal_operator_endpoint (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (z : ℂ) (hz : ‖z‖<1) :
    (1-‖z‖)*‖finiteAntiDiagonalValue N A z‖≤‖A‖ := by
  have hd : 0<1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have hc : 1-‖z‖≤1-‖z‖^2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ (1-‖z‖)*(‖A‖/(1-‖z‖^2)) :=
      mul_le_mul_of_nonneg_left (norm_finiteAntiDiagonalValue_le N A z hz) (by linarith)
    _ = ‖A‖*((1-‖z‖)/(1-‖z‖^2)) := by ring
    _ ≤ ‖A‖*1 := mul_le_mul_of_nonneg_left ((div_le_one hd).mpr hc) (norm_nonneg A)
    _ = _ := mul_one _

theorem continuous_finiteAntiDiagonalValue (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    Continuous (finiteAntiDiagonalValue N A) := by
  unfold finiteAntiDiagonalValue
  fun_prop


/-- Exact finite synthesis into the native Hardy space, retaining the constant coefficient. -/
def finiteHardyVector (N : ℕ) (u : EuclideanSpace ℂ (Fin N)) : Hardy :=
  ∑ i : Fin N,u i • hardyBasis i.val

theorem finiteHardyVector_norm (N : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖finiteHardyVector N u‖=‖u‖ := by
  have ho : Orthonormal ℂ (fun i : Fin N => hardyBasis i.val) :=
    hardyBasis.orthonormal.comp (fun i : Fin N => i.val) Fin.val_injective
  have hi : inner ℂ (finiteHardyVector N u) (finiteHardyVector N u)=inner ℂ u u := by
    rw [finiteHardyVector,ho.inner_sum]
    simp only [PiLp.inner_apply,RCLike.inner_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hsq := congrArg (RCLike.re : ℂ → ℝ) hi
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (finiteHardyVector N u),norm_nonneg u]

theorem analyticValue_finiteHardyVector (N : ℕ) (u : EuclideanSpace ℂ (Fin N)) (z : Disk) :
    analyticValue (finiteHardyVector N u).val z.val=∑ i : Fin N,u i*z.val^i.val := by
  change hardyEvaluation z (finiteHardyVector N u)=_
  rw [finiteHardyVector,map_sum]
  simp only [map_smul,hardyEvaluation_apply,hardyBasis_apply,hardyMode,
    analyticValue_fourierBasis,smul_eq_mul]

/-- Coefficientwise conjugation in the actual finite Hilbert carrier. -/
def finiteConjVector (N : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (fun i : Fin N => conj (v i))

theorem finiteConjVector_norm (N : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    ‖finiteConjVector N v‖=‖v‖ := by
  simp only [EuclideanSpace.norm_eq,finiteConjVector,Complex.norm_conj]

/-- Native rank-one orientation produces two genuine analytic Hardy polynomials. -/
theorem finiteAntiDiagonalValue_rankOne (N : ℕ)
    (u v : EuclideanSpace ℂ (Fin N)) (z : Disk) :
    finiteAntiDiagonalValue N (InnerProductSpace.rankOne ℂ u v) z.val=
      analyticValue (finiteHardyVector N u).val z.val*
        analyticValue (finiteHardyVector N (finiteConjVector N v)).val z.val := by
  rw [analyticValue_finiteHardyVector,analyticValue_finiteHardyVector,
    finiteAntiDiagonalValue,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  simp only [InnerProductSpace.rankOne_apply,EuclideanSpace.inner_single_right,
    PiLp.smul_apply,smul_eq_mul,one_mul,finiteConjVector]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [pow_add]
  ring

theorem finiteAntiDiagonalValue_finsetSum {ι : Type*} (N : ℕ) (s : Finset ι)
    (A : ι → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (z : ℂ) :
    finiteAntiDiagonalValue N (∑ i∈s,A i) z=∑ i∈s,finiteAntiDiagonalValue N (A i) z := by
  simp only [finiteAntiDiagonalValue_eq_inner,sum_apply,inner_sum]

/-- Unnormalized Gram columns avoid every zero-singular-value normalization issue. -/
theorem finiteOperator_eq_sum_gram_rankOne (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    A=∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      InnerProductSpace.rankOne ℂ (A (gramBasis A i)) (gramBasis A i) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sum_apply,InnerProductSpace.rankOne_apply]
  simpa only [map_sum,map_smul] using congrArg A ((gramBasis A).sum_repr' x).symm

theorem schattenNorm_one_eq_gram_sum (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    schattenNorm 1 A=∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),‖A (gramBasis A i)‖ := by
  simpa only [schattenNorm,one_div_one,Real.rpow_one] using finiteGram_power_sum A 1 (by norm_num)

theorem lintegral_hardy_maximal_mul_le_of_norm_le_one (u v : BoundaryL2) (hu : ‖u‖≤1) (hv : ‖v‖≤1) :
    (∫⁻ x : ℝ,TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff u) x*
      TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff v) x)≤160 := by
  let M := fun f : BoundaryL2 => TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff f)
  have hM (f : BoundaryL2) : Measurable (M f) := TTO.RealAnalysis.measurable_realMaximal _
  have hb (f : BoundaryL2) (hf : ‖f‖≤1) : (∫⁻ x : ℝ,(M f x)^(2 : ℝ))≤160 := by
    have hs : ENNReal.ofReal (‖f‖^2)≤1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg f])
    have hh := (lintegral_maximal_hardyPeriodicCutoff_sq f).trans
      (mul_le_mul' (le_refl (160 : ℝ≥0∞)) hs)
    simpa only [ENNReal.rpow_two,mul_one] using hh
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    Real.HolderConjugate.two_two (hM u).aemeasurable (hM v).aemeasurable
  apply hh.trans
  calc
    _ ≤ (160 : ℝ≥0∞)^(1/(2 : ℝ))*(160 : ℝ≥0∞)^(1/(2 : ℝ)) := by
      exact mul_le_mul' (ENNReal.rpow_le_rpow (hb u hu) (by norm_num))
        (ENNReal.rpow_le_rpow (hb v hv) (by norm_num))
    _ = 160 := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

theorem finiteAntiDiagonalValue_smul (N : ℕ)
    (c : ℂ) (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (z : ℂ) :
    finiteAntiDiagonalValue N (c • A) z=c*finiteAntiDiagonalValue N A z := by
  simp only [finiteAntiDiagonalValue_eq_inner,smul_apply,inner_smul_right]

theorem finiteOperator_eq_sum_normalized_gram_rankOne (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    A=∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      (‖A (gramBasis A i)‖ : ℂ) •
        InnerProductSpace.rankOne ℂ (NormedSpace.normalize (A (gramBasis A i))) (gramBasis A i) := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [sum_apply,smul_apply,InnerProductSpace.rankOne_apply,
    smul_smul,mul_comm] using gramBasis_expansion A x

theorem norm_normalize_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E) :
    ‖NormedSpace.normalize u‖≤1 := by
  by_cases hu : u=0
  · subst u
    simp only [NormedSpace.normalize_zero_eq_zero,norm_zero,zero_le_one]
  · exact (NormedSpace.norm_normalize hu).le


/-- A measurable angular majorant built from the actual normalized Gram rank-one factors. -/
def finiteAntiDiagonalMajorant (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (θ : ℝ) : ℝ≥0∞ :=
  4096*∑ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
    ENNReal.ofReal ‖A (gramBasis A j)‖*
      TTO.RealAnalysis.realMaximal
        (hardyPeriodicCutoff (finiteHardyVector N (NormedSpace.normalize (A (gramBasis A j)))).val) θ*
      TTO.RealAnalysis.realMaximal
        (hardyPeriodicCutoff (finiteHardyVector N (finiteConjVector N (gramBasis A j))).val) θ

theorem measurable_finiteAntiDiagonalMajorant (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    Measurable (finiteAntiDiagonalMajorant N A) := by
  unfold finiteAntiDiagonalMajorant
  exact measurable_const.mul (Finset.measurable_sum _ (fun j _hj =>
    (measurable_const.mul (TTO.RealAnalysis.measurable_realMaximal _)).mul
      (TTO.RealAnalysis.measurable_realMaximal _)))

theorem lintegral_finiteAntiDiagonalMajorant_le (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    (∫⁻ θ,finiteAntiDiagonalMajorant N A θ)≤655360*ENNReal.ofReal (schattenNorm 1 A) := by
  let u := fun j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))) =>
    (finiteHardyVector N (NormedSpace.normalize (A (gramBasis A j)))).val
  let v := fun j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))) =>
    (finiteHardyVector N (finiteConjVector N (gramBasis A j))).val
  let M := fun f : BoundaryL2 => TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff f)
  have hM (f : BoundaryL2) : Measurable (M f) := TTO.RealAnalysis.measurable_realMaximal _
  have hb (j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) :
      (∫⁻ θ,M (u j) θ*M (v j) θ)≤160 := by
    apply lintegral_hardy_maximal_mul_le_of_norm_le_one
    · change ‖finiteHardyVector N _‖≤1
      rw [finiteHardyVector_norm]
      exact norm_normalize_le_one _
    · change ‖finiteHardyVector N _‖≤1
      rw [finiteHardyVector_norm,finiteConjVector_norm,(gramBasis A).norm_eq_one]
  change (∫⁻ θ,(4096 : ℝ≥0∞)*∑ j,ENNReal.ofReal ‖A (gramBasis A j)‖*
    M (u j) θ*M (v j) θ)≤_
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ (by norm_num)]
  have hA (j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) :
      Measurable (fun θ => ENNReal.ofReal ‖A (gramBasis A j)‖*(M (u j) θ*M (v j) θ)) :=
    measurable_const.mul ((hM _).mul (hM _))
  rw [lintegral_finsetSum _ (fun j _ => hA j)]
  have hint (j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N)))) :
      (∫⁻ θ,ENNReal.ofReal ‖A (gramBasis A j)‖*(M (u j) θ*M (v j) θ))=
        ENNReal.ofReal ‖A (gramBasis A j)‖*(∫⁻ θ,M (u j) θ*M (v j) θ) :=
    lintegral_const_mul' _ (fun θ => M (u j) θ*M (v j) θ) ENNReal.ofReal_ne_top
  simp_rw [hint]
  calc
    _ ≤ 4096*∑ j,ENNReal.ofReal ‖A (gramBasis A j)‖*160 := by
      gcongr with j
      exact hb j
    _ = 655360*ENNReal.ofReal (schattenNorm 1 A) := by
      rw [schattenNorm_one_eq_gram_sum,ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _),
        ← Finset.sum_mul]
      ring


/-- Every radial value is controlled by one integrable angular function, uniformly in r. -/
theorem finiteAntiDiagonalValue_le_majorant (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (r θ : ℝ) (hr : 0≤r) (hr1 : r<1) (hθ : θ∈Icc (0 : ℝ) 1) :
    ENNReal.ofReal ‖finiteAntiDiagonalValue N A
      ((r : ℂ)*fourier (T:=1) 1 (θ : Boundary))‖≤finiteAntiDiagonalMajorant N A θ := by
  let z : Disk := ⟨(r : ℂ)*fourier (T:=1) 1 (θ : Boundary),by
    change ‖(r : ℂ)*fourier (T:=1) 1 (θ : Boundary)‖<1
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr,
      fourier_apply,Circle.norm_coe,mul_one] using hr1⟩
  let u := fun j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))) =>
    finiteHardyVector N (NormedSpace.normalize (A (gramBasis A j)))
  let v := fun j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))) =>
    finiteHardyVector N (finiteConjVector N (gramBasis A j))
  let M := fun f : Hardy => TTO.RealAnalysis.realMaximal (hardyPeriodicCutoff f.val) θ
  have hval : finiteAntiDiagonalValue N A z.val=
      ∑ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
        (‖A (gramBasis A j)‖ : ℂ)*(analyticValue (u j).val z.val*analyticValue (v j).val z.val) := by
    conv_lhs => rw [finiteOperator_eq_sum_normalized_gram_rankOne N A]
    rw [finiteAntiDiagonalValue_finsetSum]
    simp_rw [finiteAntiDiagonalValue_smul,finiteAntiDiagonalValue_rankOne]
    rfl
  have hm (f : Hardy) : ENNReal.ofReal ‖analyticValue f.val z.val‖≤64*M f :=
    hardy_value_le_centered_maximal64 f r θ θ hr hr1 hθ hθ (by
      simp only [sub_self,abs_zero]
      linarith)
  change ENNReal.ofReal ‖finiteAntiDiagonalValue N A z.val‖≤_
  rw [hval]
  calc
    _ ≤ ENNReal.ofReal (∑ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      ‖(‖A (gramBasis A j)‖ : ℂ)*
        (analyticValue (u j).val z.val*analyticValue (v j).val z.val)‖) :=
      ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ = ∑ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
        ENNReal.ofReal ‖A (gramBasis A j)‖*
          ENNReal.ofReal ‖analyticValue (u j).val z.val‖*
          ENNReal.ofReal ‖analyticValue (v j).val z.val‖ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
        ENNReal.ofReal_mul (norm_nonneg _),ENNReal.ofReal_mul (norm_nonneg _)]
      ring
    _ ≤ ∑ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
        ENNReal.ofReal ‖A (gramBasis A j)‖*(64*M (u j))*(64*M (v j)) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul' (mul_le_mul' le_rfl (hm (u j))) (hm (v j))
    _ = finiteAntiDiagonalMajorant N A θ := by
      change _=4096*∑ j,ENNReal.ofReal ‖A (gramBasis A j)‖*M (u j)*M (v j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

theorem lintegral_radial_inverse_sq (b : ℝ) (hb0 : 0≤b) (hb1 : b<1) :
    (∫⁻ r in Ioo (0 : ℝ) b,ENNReal.ofReal (2/(1-r)^2))=
      ENNReal.ofReal (2/(1-b)-2) := by
  have hc : ContinuousOn (fun r : ℝ => 2/(1-r)^2) (Icc 0 b) :=
    continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun r hr => pow_ne_zero _ (by linarith [hr.2]))
  have hi : IntegrableOn (fun r : ℝ => 2/(1-r)^2) (Ioo 0 b) volume :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards with r
    positivity)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb0]
  have hd : ∀ r∈uIcc (0 : ℝ) b,HasDerivAt (fun x : ℝ => 2/(1-x)) (2/(1-r)^2) r := by
    intro r hr
    rw [uIcc_of_le hb0] at hr
    have hn : 1-r≠0 := by linarith [hr.2]
    convert (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).inv hn).const_mul 2 using 1 <;>
      dsimp <;> ring_nf
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hb0)

/-- The literal radial density for the weak trace-class antidiagonal estimate. -/
def pellerRadialMeasure : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
    (fun r => ENNReal.ofReal (2*r/(1-r)^2))

theorem ae_mem_pellerRadialMeasure :
    ∀ᵐ r ∂pellerRadialMeasure,r∈Ioo (0 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem pellerRadialMeasure_Ioo_le (b : ℝ) (hb0 : 0≤b) (hb1 : b<1) :
    pellerRadialMeasure (Ioo (0 : ℝ) b)≤ENNReal.ofReal (2/(1-b)-2) := by
  have hs : Ioo (0 : ℝ) b⊆Ioo (0 : ℝ) 1 := fun r hr => ⟨hr.1,hr.2.trans hb1⟩
  rw [pellerRadialMeasure,withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr hs]
  calc
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) b,ENNReal.ofReal (2/(1-r)^2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by linarith [hr.2]) (sq_nonneg _)
    _ = _ := lintegral_radial_inverse_sq b hb0 hb1

theorem pellerRadialMeasure_level_le (B t : ℝ) (hB : 0≤B) (ht : 0<t) :
    pellerRadialMeasure {r : ℝ | t<(1-r)*B}≤ENNReal.ofReal (2*B/t) := by
  by_cases hsmall : B≤t
  · have he : pellerRadialMeasure {r : ℝ | t<(1-r)*B}=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ae_mem_pellerRadialMeasure] with r hr
      nlinarith [mul_nonneg hr.1.le hB]
    rw [he]
    exact bot_le
  · have hBl : t<B := lt_of_not_ge hsmall
    have hBp : 0<B := ht.trans hBl
    let b : ℝ := 1-t/B
    have hq0 : 0<t/B := div_pos ht hBp
    have hq1 : t/B<1 := (div_lt_one hBp).mpr hBl
    have hb0 : 0≤b := by dsimp [b]; linarith
    have hb1 : b<1 := by dsimp [b]; linarith
    have hs : pellerRadialMeasure {r : ℝ | t<(1-r)*B}≤
        pellerRadialMeasure (Ioo (0 : ℝ) b) := by
      apply measure_mono_ae
      filter_upwards [ae_mem_pellerRadialMeasure] with r hr hlevel
      refine ⟨hr.1,?_⟩
      change t<(1-r)*B at hlevel
      dsimp [b]
      have hq : t/B*B=t := div_mul_cancel₀ t hBp.ne'
      nlinarith
    apply hs.trans ((pellerRadialMeasure_Ioo_le b hb0 hb1).trans _)
    apply ENNReal.ofReal_le_ofReal
    have he : 2/(1-b)=2*B/t := by
      dsimp [b]
      field_simp [hBp.ne',ht.ne']; ring
    rw [he]
    linarith

instance pellerRadialMeasure_sFinite : SFinite pellerRadialMeasure := by
  unfold pellerRadialMeasure
  infer_instance

/-- A pointwise angular majorant gives a radial weak bound, even at infinite majorant values. -/
theorem pellerRadialMeasure_level_le_of_majorant (f : ℝ → ℝ) (B : ℝ≥0∞)
    (h : ∀ r∈Ioo (0 : ℝ) 1,ENNReal.ofReal (f r)≤B) (t : ℝ) (ht : 0<t) :
    pellerRadialMeasure {r : ℝ | t<(1-r)*f r}≤ENNReal.ofReal (2/t)*B := by
  by_cases hB : B=∞
  · have hp : (0 : ℝ≥0∞)<ENNReal.ofReal (2/t) := ENNReal.ofReal_pos.mpr (by positivity)
    simp only [hB,ENNReal.mul_top hp.ne',le_top]
  · calc
      _ ≤ pellerRadialMeasure {r : ℝ | t<(1-r)*B.toReal} := by
        apply measure_mono_ae
        filter_upwards [ae_mem_pellerRadialMeasure] with r hr hlevel
        have hf : f r≤B.toReal := (ENNReal.ofReal_le_iff_le_toReal hB).mp (h r hr)
        exact hlevel.trans_le (mul_le_mul_of_nonneg_left hf (by linarith [hr.2]))
      _ ≤ ENNReal.ofReal (2*B.toReal/t) :=
        pellerRadialMeasure_level_le _ _ ENNReal.toReal_nonneg ht
      _ = ENNReal.ofReal (2/t)*B := by
        rw [show 2*B.toReal/t=(2/t)*B.toReal by ring,
          ENNReal.ofReal_mul (by positivity : 0≤2/t),ENNReal.ofReal_toReal hB]

/-- The actual product of the unit angular window and the weighted radial measure. -/
def pellerPolarMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ico (0 : ℝ) 1)).prod pellerRadialMeasure

/-- Genuine weak type (1,1) for antidiagonal averaging, uniformly in the finite dimension. -/
theorem finiteAntiDiagonal_weak_one (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (t : ℝ) (ht : 0<t) :
    pellerPolarMeasure {x : ℝ × ℝ |
      t<(1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖}≤
      ENNReal.ofReal (1310720/t*schattenNorm 1 A) := by
  have hz : Continuous (fun x : ℝ × ℝ =>
      (x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary)) := by fun_prop
  have hv : Continuous (fun x : ℝ × ℝ =>
      (1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖) :=
    (continuous_const.sub continuous_snd).mul
      ((continuous_finiteAntiDiagonalValue N A).comp hz).norm
  rw [pellerPolarMeasure,Measure.prod_apply (isOpen_lt continuous_const hv).measurableSet]
  calc
    _ ≤ ∫⁻ θ in Ico (0 : ℝ) 1,
        ENNReal.ofReal (2/t)*finiteAntiDiagonalMajorant N A θ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with θ hθ
      apply pellerRadialMeasure_level_le_of_majorant _ _ _ t ht
      intro r hr
      exact finiteAntiDiagonalValue_le_majorant N A r θ hr.1.le hr.2 ⟨hθ.1,hθ.2.le⟩
    _ = ENNReal.ofReal (2/t)*(∫⁻ θ in Ico (0 : ℝ) 1,finiteAntiDiagonalMajorant N A θ) := by
      rw [lintegral_const_mul _ (measurable_finiteAntiDiagonalMajorant N A)]
    _ ≤ ENNReal.ofReal (2/t)*(∫⁻ θ,finiteAntiDiagonalMajorant N A θ) :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    _ ≤ ENNReal.ofReal (2/t)*(655360*ENNReal.ofReal (schattenNorm 1 A)) :=
      mul_le_mul' le_rfl (lintegral_finiteAntiDiagonalMajorant_le N A)
    _ = ENNReal.ofReal (2/t)*
        (ENNReal.ofReal (655360 : ℝ)*ENNReal.ofReal (schattenNorm 1 A)) := by norm_num
    _ = ENNReal.ofReal ((2/t)*(655360*schattenNorm 1 A)) := by
      rw [← ENNReal.ofReal_mul (by norm_num : 0≤(655360 : ℝ)),
        ← ENNReal.ofReal_mul (by positivity : 0≤2/t)]
    _ = _ := by congr 1; ring

theorem lintegral_spectral_piece (σ p : ℝ) (hσ : 0≤σ) (hp : 1<p) :
    (∫⁻ t in Ioi (0 : ℝ),ENNReal.ofReal (if t<2*σ then σ*t^(p-2) else 0))=
      ENNReal.ofReal (2^(p-1)/(p-1)*σ^p) := by
  rcases eq_or_lt_of_le hσ with rfl | hσ
  · simp [Real.zero_rpow (by linarith : p≠0)]
  have h2 : 0<2*σ := by positivity
  have he : (fun t : ℝ => ENNReal.ofReal (if t<2*σ then σ*t^(p-2) else 0))=
      (Iio (2*σ)).indicator (fun t : ℝ => ENNReal.ofReal (σ*t^(p-2))) := by
    funext t
    by_cases ht : t<2*σ <;> simp [ht]
  rw [he,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (2*σ)∩Ioi (0 : ℝ)=Ioo (0 : ℝ) (2*σ) := by
    ext t
    simp [and_comm]
  rw [hset]
  have hi : IntegrableOn (fun t : ℝ => σ*t^(p-2)) (Ioo (0 : ℝ) (2*σ)) volume :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff h2).mpr
      (by linarith : -1<p-2)).const_mul σ
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg hσ.le (Real.rpow_nonneg ht.1.le _))]
  congr 1
  rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le h2.le,
    integral_rpow (Or.inl (by linarith : -1<p-2)),
    show p-2+1=p-1 by ring,
    Real.zero_rpow (by linarith : p-1≠0),sub_zero,
    Real.mul_rpow (by norm_num : 0≤(2 : ℝ)) hσ.le]
  have hsPow : σ*σ^(p-1)=σ^p := by
    calc
      _ = σ^(1+(p-1)) := by rw [Real.rpow_add hσ,Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ = 2^(p-1)/(p-1)*(σ*σ^(p-1)) := by ring
    _ = _ := by rw [hsPow]

theorem finiteAntiDiagonalValue_add (N : ℕ)
    (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (z : ℂ) :
    finiteAntiDiagonalValue N (A+B) z=
      finiteAntiDiagonalValue N A z+finiteAntiDiagonalValue N B z := by
  simp only [finiteAntiDiagonalValue_eq_inner,add_apply,inner_add_right]

theorem ae_radial_mem_pellerPolarMeasure :
    ∀ᵐ x ∂pellerPolarMeasure,x.2∈Ioo (0 : ℝ) 1 := by
  rw [pellerPolarMeasure,Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)]
  exact Eventually.of_forall (fun _ => ae_mem_pellerRadialMeasure)

/-- Actual spectral truncation refines the weak endpoint to the retained singular-value tail. -/
theorem finiteAntiDiagonal_refined_level (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (t : ℝ) (ht : 0<t) :
    pellerPolarMeasure {x : ℝ × ℝ |
      t<(1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖}≤
      ENNReal.ofReal (2621440/t*
        ∑ i∈Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
          if t<2*‖finiteGramWeights A i‖ then ‖finiteGramWeights A i‖ else 0) := by
  let B := singularCutoff A (t/2)
  have hs : pellerPolarMeasure {x : ℝ × ℝ |
      t<(1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖}≤
      pellerPolarMeasure {x : ℝ × ℝ |
      t/2<(1-x.2)*‖finiteAntiDiagonalValue N B
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖} := by
    apply measure_mono_ae
    filter_upwards [ae_radial_mem_pellerPolarMeasure] with x hx hlevel
    let z : ℂ := (x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary)
    have hn : ‖z‖=x.2 := by
      simp only [z,norm_mul,Complex.norm_real,Real.norm_of_nonneg hx.1.le,
        fourier_apply,Circle.norm_coe,mul_one]
    have hres : (1-x.2)*‖finiteAntiDiagonalValue N (A-B) z‖≤t/2 := by
      have hh := (finiteAntiDiagonal_operator_endpoint N (A-B) z (by rw [hn]; exact hx.2)).trans
        (norm_sub_singularCutoff_le A (t/2) (by linarith))
      simpa only [hn] using hh
    have hsplit : finiteAntiDiagonalValue N A z=
        finiteAntiDiagonalValue N B z+finiteAntiDiagonalValue N (A-B) z := by
      rw [← finiteAntiDiagonalValue_add]
      congr 1
      abel
    have hnorm := norm_add_le (finiteAntiDiagonalValue N B z) (finiteAntiDiagonalValue N (A-B) z)
    rw [← hsplit] at hnorm
    have htotal := mul_le_mul_of_nonneg_left hnorm (by linarith [hx.2] : 0≤1-x.2)
    change t<(1-x.2)*‖finiteAntiDiagonalValue N A z‖ at hlevel
    change t/2<(1-x.2)*‖finiteAntiDiagonalValue N B z‖
    nlinarith
  apply hs.trans ((finiteAntiDiagonal_weak_one N B (t/2) (by linarith)).trans _)
  apply ENNReal.ofReal_le_ofReal
  have htrace := schattenNorm_one_singularCutoff_le A (t/2)
  have hsum : (∑ i∈Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      if t/2<‖finiteGramWeights A i‖ then ‖finiteGramWeights A i‖ else 0)=
      ∑ i∈Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      if t<2*‖finiteGramWeights A i‖ then ‖finiteGramWeights A i‖ else 0 := by
    apply Finset.sum_congr rfl
    intro i _hi
    have hi : (t/2<‖finiteGramWeights A i‖)↔(t<2*‖finiteGramWeights A i‖) := by
      constructor <;> intro h <;> linarith
    simp only [hi]
  rw [hsum] at htrace
  calc
    _ ≤ (1310720/(t/2))*
        ∑ i∈Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
          if t<2*‖finiteGramWeights A i‖ then ‖finiteGramWeights A i‖ else 0 :=
      mul_le_mul_of_nonneg_left htrace (by positivity)
    _ = _ := by congr 1; ring


/-- Scalar layer cake for a genuine finite spectral-tail distribution bound. -/
theorem lintegral_rpow_le_of_spectral_level {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf0 : 0≤ᵐ[μ] f) (hfm : AEMeasurable f μ)
    (s : Finset ι) (σ : ι → ℝ) (hσ : ∀ i,0≤σ i)
    (C p : ℝ) (hC : 0≤C) (hp : 1<p)
    (hlevel : ∀ t : ℝ,0<t →
      μ {a : α | t<f a}≤ENNReal.ofReal (C/t*∑ i∈s,if t<2*σ i then σ i else 0)) :
    (∫⁻ a,ENNReal.ofReal (f a^p) ∂μ)≤
      ENNReal.ofReal (C*p*2^(p-1)/(p-1)*∑ i∈s,σ i^p) := by
  classical
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hm (i : ι) : Measurable (fun t : ℝ =>
      ENNReal.ofReal (if t<2*σ i then σ i*t^(p-2) else 0)) := by
    apply Measurable.ennreal_ofReal
    exact (by fun_prop : Measurable (fun t : ℝ => σ i*t^(p-2))).ite
      (measurableSet_lt measurable_id measurable_const) measurable_const
  have hd : 0≤2^(p-1)/(p-1) := by positivity
  have hI (i : ι) := lintegral_spectral_piece (σ i) p (hσ i) hp
  have he (t : ℝ) (ht : 0<t) :
      ENNReal.ofReal (C/t*∑ i∈s,if t<2*σ i then σ i else 0)*
        ENNReal.ofReal (t^(p-1))=
      ENNReal.ofReal C*∑ i∈s,
        ENNReal.ofReal (if t<2*σ i then σ i*t^(p-2) else 0) := by
    have hs : 0≤∑ i∈s,if t<2*σ i then σ i else 0 :=
      Finset.sum_nonneg (fun i _ => by
        split_ifs
        · exact hσ i
        · exact le_rfl)
    rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hC ht.le) hs)]
    have htPow : t^(p-1)/t=t^(p-2) := by
      rw [← Real.rpow_sub_one ht.ne']
      congr 1
      ring
    have hr :
        (C/t*(∑ i∈s,if t<2*σ i then σ i else 0))*t^(p-1)=
        C*∑ i∈s,if t<2*σ i then σ i*t^(p-2) else 0 := by
      calc
        _ = C*∑ i∈s,(if t<2*σ i then σ i else 0)*t^(p-2) := by
          rw [← Finset.sum_mul,← htPow]
          ring
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          split_ifs <;> simp
    rw [hr,ENNReal.ofReal_mul hC,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        split_ifs
        · exact mul_nonneg (hσ i) (Real.rpow_nonneg ht.le _)
        · exact le_rfl)]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hf0 hfm hp0]
  calc
    _ ≤ ENNReal.ofReal p*∫⁻ t in Ioi (0 : ℝ),ENNReal.ofReal C*
        ∑ i∈s,ENNReal.ofReal (if t<2*σ i then σ i*t^(p-2) else 0) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (mul_le_mul' (hlevel t ht) le_rfl).trans_eq (he t ht)
    _ = ENNReal.ofReal p*(ENNReal.ofReal C*
        ∑ i∈s,ENNReal.ofReal (2^(p-1)/(p-1)*σ i^p)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum s (fun i _ => hm i)]
      simp_rw [hI]
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        mul_nonneg hd (Real.rpow_nonneg (hσ i) _)),
        ← ENNReal.ofReal_mul hC,← ENNReal.ofReal_mul hp0.le,← Finset.mul_sum]
      congr 1
      ring


/-- Uniform strong-p antidiagonal averaging for every p>1, from genuine finite spectral tails. -/
theorem finiteAntiDiagonal_strong_p (N : ℕ)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℝ) (hp : 1<p) :
    (∫⁻ x : ℝ × ℝ,ENNReal.ofReal
      (((1-x.2)*‖finiteAntiDiagonalValue N A
        ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖)^p) ∂pellerPolarMeasure)≤
      ENNReal.ofReal (2621440*p*2^(p-1)/(p-1)*schattenNorm p A^p) := by
  let f := fun x : ℝ × ℝ => (1-x.2)*‖finiteAntiDiagonalValue N A
    ((x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary))‖
  have hf0 : 0≤ᵐ[pellerPolarMeasure] f := by
    filter_upwards [ae_radial_mem_pellerPolarMeasure] with x hx
    exact mul_nonneg (by linarith [hx.2]) (norm_nonneg _)
  have hz : Continuous (fun x : ℝ × ℝ =>
      (x.2 : ℂ)*fourier (T:=1) 1 (x.1 : Boundary)) := by fun_prop
  have hfc : Continuous f := (continuous_const.sub continuous_snd).mul
    ((continuous_finiteAntiDiagonalValue N A).comp hz).norm
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hpow : (∑ i∈Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
      ‖finiteGramWeights A i‖^p)=schattenNorm p A^p := by
    calc
      _ = ∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
          ‖finiteGramWeights A i.val‖^p := (Fin.sum_univ_eq_sum_range _ _).symm
      _ = ∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))),
          ‖A (gramBasis A i)‖^p := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [finiteGramWeights_at,Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg (A (gramBasis A i)))]
      _ = _ := (finiteGram_power_sum A p hp0).symm.trans (schattenNorm_rpow hp0).symm
  have h := lintegral_rpow_le_of_spectral_level pellerPolarMeasure f hf0 hfc.measurable.aemeasurable
    (Finset.range (Module.finrank ℂ (EuclideanSpace ℂ (Fin N))))
    (fun i => ‖finiteGramWeights A i‖) (fun i => norm_nonneg _) 2621440 p (by norm_num) hp
    (fun t ht => finiteAntiDiagonal_refined_level N A t ht)
  rw [hpow] at h
  exact h

end TTO.Paper.Proved
