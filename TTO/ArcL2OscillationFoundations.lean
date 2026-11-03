/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ContinuousVMOAFoundations
public import TTO.ArcMeanFoundations

/-! Actual normalized Haar L² control of literal real-arc integrals and oscillations. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem boundaryL2_integral_norm_sq (f : BoundaryL2) :
    (∫ t, ‖f t‖^2 ∂circleMeasure)=‖f‖^2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h.symm
  · exact L2.integrable_inner f f

theorem arc_integral_norm_sq_le (f : BoundaryL2) (a b : ℝ) (hLen : b-a ≤ 1) :
    IntegrableOn (fun t : ℝ => ‖f (t : Boundary)‖^2) (Ioc a b) ∧
      (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)‖^2) ≤ ‖f‖^2 := by
  have hp : MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ioc a (a+1))) circleMeasure := by
    rw [circleMeasure_eq_volume]
    exact AddCircle.measurePreserving_mk 1 a
  have hW : MemLp (fun t : ℝ => f (t : Boundary)) 2 (volume.restrict (Ioc a (a+1))) :=
    (Lp.memLp f).comp_measurePreserving hp
  have hWI : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)‖^2) (Ioc a (a+1)) :=
    hW.integrable_norm_pow (by norm_num : (2 : ℕ)≠0)
  have hSub : Ioc a b ⊆ Ioc a (a+1) :=
    fun t ht => ⟨ht.1,ht.2.trans (by linarith)⟩
  refine ⟨hWI.mono_set hSub,?_⟩
  calc
    _ ≤ ∫ t : ℝ in Ioc a (a+1), ‖f (t : Boundary)‖^2 :=
      setIntegral_mono_set hWI (Eventually.of_forall fun t => sq_nonneg ‖f (t : Boundary)‖)
        (Eventually.of_forall fun t ht => hSub ht)
    _ = ∫ t : Boundary, ‖f t‖^2 := by
      simpa only using! AddCircle.integral_preimage 1 a (fun t : Boundary => ‖f t‖^2)
    _ = ‖f‖^2 := by rw [← circleMeasure_eq_volume,boundaryL2_integral_norm_sq]

theorem arc_integral_norm_le_sqrt_length (f : BoundaryL2) (a b : ℝ)
    (hab : a < b) (hLen : b-a ≤ 1) :
    (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)‖) ≤ Real.sqrt (b-a)*‖f‖ := by
  have hFin : volume (Ioc a b)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hSquared := arc_integral_norm_sq_le f a b hLen
  have hFM : AEStronglyMeasurable (fun t : ℝ => ‖f (t : Boundary)‖)
      (volume.restrict (Ioc a b)) :=
    (boundaryL2_integrableOn_lift_Ioc f a b hLen).aestronglyMeasurable.norm
  have hF : MemLp (fun t : ℝ => ‖f (t : Boundary)‖) 2 (volume.restrict (Ioc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm hFM).mpr
    simpa only [norm_norm] using! hSquared.1
  have hG : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_const).mpr
    simpa only [norm_one,one_pow] using!
      (integrableOn_const hFin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc a b))
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun t : ℝ => norm_nonneg (f (t : Boundary)))
    (Eventually.of_forall fun _ : ℝ => (show (0 : ℝ)≤1 by norm_num))
    (by simpa only [ENNReal.ofReal_ofNat] using hF)
    (by simpa only [ENNReal.ofReal_ofNat] using hG)
  simp only [mul_one,Real.rpow_two,one_pow] at hCS
  rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),smul_eq_mul,mul_one,
    ← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hCS
  calc
    _ ≤ Real.sqrt (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)‖^2)*Real.sqrt (b-a) := hCS
    _ ≤ Real.sqrt (‖f‖^2)*Real.sqrt (b-a) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hSquared.2) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_sq_eq_abs,abs_norm,mul_comm]

theorem meanOscillation_le_l2 (f : BoundaryL2) (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1) :
    meanOscillation f a b ≤ 2*‖f‖/Real.sqrt (b-a) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hs : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr hd
  have hM := meanOscillation_le_centeredIntegral f a b hab
    (boundaryL2_integrableOn_lift_Ioc f a b hLen) 0
  simp only [sub_zero] at hM
  have hI := arc_integral_norm_le_sqrt_length f a b hab hLen
  calc
    _ ≤ 2*(b-a)⁻¹*(Real.sqrt (b-a)*‖f‖) :=
      hM.trans (mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num) (inv_nonneg.mpr hd.le)))
    _ = _ := by
      have hSq := Real.sq_sqrt hd.le
      field_simp
      rw [hSq]



theorem arc_integral_centered_norm_le_sqrt_energy (f : BoundaryL2) (a b : ℝ)
    (hab : a < b) (hLen : b-a ≤ 1) (c : ℂ) :
    (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖) ≤
      Real.sqrt (b-a)*Real.sqrt (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖^2) := by
  have : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp⟩
  have hBase : MemLp (fun t : ℝ => f (t : Boundary)) 2 (volume.restrict (Ioc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (boundaryL2_integrableOn_lift_Ioc f a b hLen).aestronglyMeasurable).mpr
    exact (arc_integral_norm_sq_le f a b hLen).1
  have hF : MemLp (fun t : ℝ => ‖f (t : Boundary)-c‖) 2
      (volume.restrict (Ioc a b)) := (hBase.sub (memLp_const c)).norm
  have hG : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc a b)) := memLp_const 1
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun t : ℝ => norm_nonneg (f (t : Boundary)-c))
    (Eventually.of_forall fun _ : ℝ => (show (0 : ℝ)≤1 by norm_num))
    (by simpa only [ENNReal.ofReal_ofNat] using hF)
    (by simpa only [ENNReal.ofReal_ofNat] using hG)
  simp only [mul_one,Real.rpow_two,one_pow] at hCS
  rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),smul_eq_mul,mul_one,
    ← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hCS
  simpa only [mul_comm] using hCS

theorem meanOscillation_le_centered_l2 (f : BoundaryL2) (a b : ℝ)
    (hab : a < b) (hLen : b-a ≤ 1) (c : ℂ) :
    meanOscillation f a b ≤ 2/Real.sqrt (b-a)*
      Real.sqrt (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖^2) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hs : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr hd
  have hM := meanOscillation_le_centeredIntegral f a b hab
    (boundaryL2_integrableOn_lift_Ioc f a b hLen) c
  have hI := arc_integral_centered_norm_le_sqrt_energy f a b hab hLen c
  calc
    _ ≤ 2*(b-a)⁻¹*(Real.sqrt (b-a)*
        Real.sqrt (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖^2)) :=
      hM.trans (mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num) (inv_nonneg.mpr hd.le)))
    _ = _ := by
      have hSq := Real.sq_sqrt hd.le
      field_simp
      rw [hSq]

end TTO.Paper.Proved
