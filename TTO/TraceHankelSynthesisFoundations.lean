/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeightedBergmanFoundations
public import TTO.TraceIntegralFoundations
public import TTO.SzegoRankOneFoundations

/-! Actual trace-class Hankel-tail synthesis from the analytic L¹ second derivative.
The all-p Peller obligation is not assumed or asserted. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

-- These aliases pin the native operator-norm instances before operator-valued integration.
local instance traceSzegoOperatorNormed : NormedAddCommGroup (Hardy →L[ℂ] Hardy) := inferInstance
local instance traceSzegoOperatorNormedSpace : NormedSpace ℂ (Hardy →L[ℂ] Hardy) := inferInstance

/-- Ordinary operator-norm Bochner synthesis of the literal rank-one kernel. -/
def szegoTraceIntegral (F : ℂ → ℂ) : Hardy →L[ℂ] Hardy :=
  ∫ z,weightedSzegoRankOneZero F z ∂diskArea

/-- Only disk continuity and genuine L¹ integrability are needed for this nuclear integral. -/
theorem szegoTraceIntegral_schatten_one (F : ℂ → ℂ) (hF : ContinuousOn F disk)
    (hInt : Integrable F diskArea) :
    Integrable (weightedSzegoRankOneZero F) diskArea ∧
      Schatten 1 (szegoTraceIntegral F) ∧
      schattenNorm 1 (szegoTraceIntegral F)≤∫ z,‖F z‖ ∂diskArea := by
  let b : ℂ → ℝ := Function.extend (Subtype.val : Disk → ℂ)
    (fun w => ‖F w.val‖) (fun _ => 0)
  have hbOn (w : Disk) : b w.val=‖F w.val‖ := Subtype.val_injective.extend_apply _ _ w
  have hbOff (z : ℂ) (hz : z ∉ disk) : b z=0 := by
    apply Function.extend_apply'
    rintro ⟨w,he⟩
    exact hz (he ▸ w.property)
  have hbM : Measurable b :=
    ((MeasurableEmbedding.subtype_coe
      (isOpen_lt continuous_norm continuous_const).measurableSet).stronglyMeasurable_extend
        hF.domRestrict.norm.stronglyMeasurable stronglyMeasurable_const).measurable
  have hbAE : b=ᵐ[diskArea] fun z => ‖F z‖ := by
    filter_upwards [ae_mem_diskArea] with z hz
    exact hbOn ⟨z,hz⟩
  have hbI : Integrable b diskArea := hInt.norm.congr hbAE.symm
  have hb0 (z : ℂ) : 0≤b z := by
    by_cases hz : z∈disk
    · rw [hbOn ⟨z,hz⟩]
      exact norm_nonneg _
    · rw [hbOff z hz]
  have hB (z : ℂ) : schattenNorm 1 (weightedSzegoRankOneZero F z)≤b z := by
    by_cases hz : z∈disk
    · rw [hbOn ⟨z,hz⟩]
      exact (weightedSzegoRankOneZero_schatten_one F z).2
    · rw [hbOff z hz,weightedSzegoRankOneZero_off F z hz,schattenNorm_zero 1 (by norm_num)]
  obtain ⟨hTi,hS,hN⟩ := traceClass_integral_dominated diskArea (weightedSzegoRankOneZero F)
    (stronglyMeasurable_weightedSzegoRankOneZero F hF) b hbM hbI hb0
    (fun z => (weightedSzegoRankOneZero_schatten_one F z).1) hB
  exact ⟨hTi,hS,hN.trans_eq (integral_congr_ae hbAE)⟩

/-- Literal matrix entries, obtained by ordinary continuous-linear Bochner evaluation. -/
theorem szegoTraceIntegral_matrix (F : ℂ → ℂ) (hF : ContinuousOn F disk)
    (hInt : Integrable F diskArea) (i j : ℕ) :
    inner ℂ (hardyBasis i) (szegoTraceIntegral F (hardyBasis j)) =
      ∫ z, (F z*((1-‖z‖^2 : ℝ) : ℂ))*z^(i+j) ∂diskArea := by
  have hTi := (szegoTraceIntegral_schatten_one F hF hInt).1
  let L := innerSL ℂ (hardyBasis i) ∘L ContinuousLinearMap.apply ℂ Hardy (hardyBasis j)
  have he := L.integral_comp_comm hTi
  change (∫ z,inner ℂ (hardyBasis i) (weightedSzegoRankOneZero F z (hardyBasis j)) ∂diskArea) =
    inner ℂ (hardyBasis i) (szegoTraceIntegral F (hardyBasis j)) at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [ae_mem_diskArea] with z hz
  rw [weightedSzegoRankOneZero_on F ⟨z,hz⟩,smul_apply,
    inner_smul_right,normalizedSzegoRankOne_matrix]
  ring

/-- The analytic second derivative synthesizes the twice-backshifted Hankel matrix. -/
def traceHankelTailEndo (g : BoundaryL2) : Hardy →L[ℂ] Hardy :=
  szegoTraceIntegral (fun z => conj (deriv (deriv (analyticValue g)) z))

theorem traceHankelTailEndo_schatten (g : BoundaryL2) (hg : besovEnergy 1 (analyticValue g)<∞) :
    Schatten 1 (traceHankelTailEndo g) ∧ schattenNorm 1 (traceHankelTailEndo g) ≤
      ∫ z,‖deriv (deriv (analyticValue g)) z‖ ∂diskArea := by
  have hF : ContinuousOn (fun z => conj (deriv (deriv (analyticValue g)) z)) disk :=
    Complex.continuous_conj.comp_continuousOn
      (show ContinuousOn (deriv (deriv (analyticValue g))) disk from
        (show AnalyticOnNhd ℂ (deriv (deriv (analyticValue g))) disk from
          fun z hz => ((analyticOnNhd_analyticValue g z hz).deriv).deriv).continuousOn)
  have hInt := ((RCLike.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (integrable_second_derivative_of_besov_one g hg))
  obtain ⟨_,hS,hN⟩ := szegoTraceIntegral_schatten_one _ hF hInt
  exact ⟨hS,by simpa only [traceHankelTailEndo,Complex.norm_conj] using hN⟩

theorem traceHankelTailEndo_matrix (g : BoundaryL2) (hg : besovEnergy 1 (analyticValue g)<∞)
    (i j : ℕ) :
    inner ℂ (hardyBasis i) (traceHankelTailEndo g (hardyBasis j)) =
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ)) := by
  have hF : ContinuousOn (fun z => conj (deriv (deriv (analyticValue g)) z)) disk :=
    Complex.continuous_conj.comp_continuousOn
      (show AnalyticOnNhd ℂ (deriv (deriv (analyticValue g))) disk from
        fun z hz => ((analyticOnNhd_analyticValue g z hz).deriv).deriv).continuousOn
  rw [traceHankelTailEndo,szegoTraceIntegral_matrix _ hF
    ((RCLike.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (integrable_second_derivative_of_besov_one g hg)),
    second_derivative_weighted_moment_of_besov_one g hg]

/-- Actual positive-to-negative Fourier coordinate unitary. -/
def hardyNegativeEquiv : Hardy ≃ₗᵢ[ℂ] ↥hardy.orthogonal :=
  hardyBasis.repr.trans negativeBasis.repr.symm

def traceHankelTail (g : BoundaryL2) : HankelOperator :=
  hardyNegativeEquiv.toContinuousLinearEquiv.toContinuousLinearMap ∘L traceHankelTailEndo g

theorem traceHankelTail_schatten (g : BoundaryL2) (hg : besovEnergy 1 (analyticValue g)<∞) :
    Schatten 1 (traceHankelTail g) ∧ schattenNorm 1 (traceHankelTail g) ≤
      ∫ z,‖deriv (deriv (analyticValue g)) z‖ ∂diskArea := by
  obtain ⟨hS,hN⟩ := traceHankelTailEndo_schatten g hg
  refine ⟨(schatten_unitary_comp_iff hardyNegativeEquiv _ 1).mpr hS,?_⟩
  simpa only [traceHankelTail,schattenNorm,approximationNumber_unitary_comp] using hN

theorem traceHankelTail_matrix (g : BoundaryL2) (hg : besovEnergy 1 (analyticValue g)<∞)
    (i j : ℕ) :
    inner ℂ (negativeBasis i) (traceHankelTail g (hardyBasis j)) =
      conj (fourierCoeff g ((i+j+2 : ℕ) : ℤ)) := by
  rw [← negativeBasis.repr_apply_apply]
  simpa only [traceHankelTail,hardyNegativeEquiv,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,
    hardyBasis.repr_apply_apply] using traceHankelTailEndo_matrix g hg i j

end TTO.Paper.Proved
