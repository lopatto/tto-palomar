/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BesovTwoFoundations

/-! Continuous Hardy boundary classes satisfy the literal real-arc VMOA definition.
All representative changes are justified by Haar-to-real-window measure preservation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem circle_ae_lift_Ioc {P : Boundary → Prop}
    (hP : ∀ᵐ t ∂circleMeasure, P t) (a b : ℝ) (hLen : b-a ≤ 1) :
    ∀ᵐ (t : ℝ) ∂(volume.restrict (Ioc a b)), P (t : Boundary) := by
  have hp : MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ioc a (a+1))) circleMeasure := by
    rw [circleMeasure_eq_volume]
    exact AddCircle.measurePreserving_mk 1 a
  have hw := hp.quasiMeasurePreserving.ae hP
  rw [ae_restrict_iff' measurableSet_Ioc] at hw ⊢
  filter_upwards [hw] with t ht hts
  exact ht ⟨hts.1,hts.2.trans (by linarith)⟩

theorem boundaryL2_integrableOn_lift_Ioc (f : BoundaryL2) (a b : ℝ) (hLen : b-a ≤ 1) :
    IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ioc a b) := by
  have hp : MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ioc a (a+1))) circleMeasure := by
    rw [circleMeasure_eq_volume]
    exact AddCircle.measurePreserving_mk 1 a
  have hI := hp.integrable_comp_of_integrable ((Lp.memLp f).integrable (by norm_num))
  have hJ : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ioc a (a+1)) := hI
  exact hJ.mono_set (fun t ht => ⟨ht.1,ht.2.trans (by linarith)⟩)

theorem dist_real_coe_circle_le (s t : ℝ) :
    dist (s : Boundary) (t : Boundary) ≤ dist s t := by
  rw [dist_eq_norm,dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem continuous_lift (c : C(Boundary,ℂ)) :
    Continuous (fun t : ℝ => c (t : Boundary)) := by fun_prop

theorem uniformContinuous_lift (c : C(Boundary,ℂ)) :
    UniformContinuous (fun t : ℝ => c (t : Boundary)) :=
  (CompactSpace.uniformContinuous_of_continuous c.continuous).comp
    ((show LipschitzWith 1 (fun t : ℝ => (t : Boundary)) from by
      have hLip := LipschitzWith.of_dist_le' (K := 1) (fun s t : ℝ => by
        simpa only [one_mul] using dist_real_coe_circle_le s t)
      simpa only [Real.toNNReal_one] using hLip).uniformContinuous)

/-- A continuous comparison controls the literal real-arc mean, with all representative
changes made on the actual restricted Lebesgue measure. -/
theorem arcMean_sub_const_le (f : BoundaryL2) (c : C(Boundary,ℂ))
    (hfc : f =ᵐ[circleMeasure] c) (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1)
    (k : ℂ) (M : ℝ) (hOsc : ∀ t ∈ Ioc a b, ‖c (t : Boundary)-k‖ ≤ M) :
    ‖arcMean f a b-k‖ ≤ M := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hD : ((b-a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hPull := circle_ae_lift_Ioc hfc a b hLen
  have hcI : IntegrableOn (fun t : ℝ => c (t : Boundary)) (Ioc a b) :=
    (continuous_lift c).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hkI : IntegrableOn (fun _ : ℝ => k) (Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hVol : volume.real (Ioc a b) = b-a := by
    rw [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal hd.le]
  have hConst : (∫ t : ℝ in Ioc a b, k) = ((b-a : ℝ) : ℂ)*k := by
    rw [setIntegral_const,hVol,Complex.real_smul]
  have hMean : arcMean f a b = ((b-a : ℝ) : ℂ)⁻¹*
      ∫ t : ℝ in Ioc a b, c (t : Boundary) := by
    unfold arcMean
    rw [integral_congr_ae hPull]
  have hId : ((b-a : ℝ) : ℂ)⁻¹*
      (∫ t : ℝ in Ioc a b, c (t : Boundary)-k) = arcMean f a b-k := by
    rw [integral_sub hcI hkI,hConst,hMean]
    field_simp
  have hI : ‖∫ t : ℝ in Ioc a b, c (t : Boundary)-k‖ ≤ M*(b-a) := by
    have hh := norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hOsc
    simpa only [hVol] using hh
  rw [← hId,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hd.le]
  calc
    _ ≤ (b-a)⁻¹*(M*(b-a)) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hd.le)
    _ = M := by field_simp

theorem meanOscillation_le_of_continuous_comparison (f : BoundaryL2) (c : C(Boundary,ℂ))
    (hfc : f =ᵐ[circleMeasure] c) (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1)
    (k : ℂ) (M : ℝ) (hOsc : ∀ t ∈ Ioc a b, ‖c (t : Boundary)-k‖ ≤ M) :
    meanOscillation f a b ≤ 2*M := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hPull := circle_ae_lift_Ioc hfc a b hLen
  have hMean := arcMean_sub_const_le f c hfc a b hab hLen k M hOsc
  have hBound : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioc a b),
      ‖f (t : Boundary)-arcMean f a b‖ ≤ 2*M := by
    filter_upwards [hPull,ae_restrict_mem measurableSet_Ioc] with t ht hts
    rw [ht]
    calc
      _ ≤ ‖c (t : Boundary)-k‖+‖arcMean f a b-k‖ := by
        simpa only [dist_eq_norm,norm_sub_rev (arcMean f a b) k] using
          dist_triangle (c (t : Boundary)) k (arcMean f a b)
      _ ≤ M+M := add_le_add (hOsc t hts) hMean
      _ = _ := by ring
  have hI : Integrable (fun t : ℝ => ‖f (t : Boundary)-arcMean f a b‖)
      (volume.restrict (Ioc a b)) :=
    ((boundaryL2_integrableOn_lift_Ioc f a b hLen).sub
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))).norm
  have hInt := integral_mono_ae hI (integrable_const (2*M)) hBound
  rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal hd.le,smul_eq_mul] at hInt
  unfold meanOscillation
  calc
    _ ≤ (b-a)⁻¹*((b-a)*(2*M)) :=
      mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr hd.le)
    _ = _ := by field_simp

/-- An a.e. continuous Hardy boundary class lies in the frozen real-arc VMOA space. -/
theorem inVMOA_of_continuous_ae (f : BoundaryL2) (hf : f ∈ hardy)
    (c : C(Boundary,ℂ)) (hfc : f =ᵐ[circleMeasure] c) : InVMOA f := by
  refine ⟨hf,?_⟩
  intro ε hε
  obtain ⟨η,hη,hUniform⟩ := Metric.uniformContinuous_iff.mp (uniformContinuous_lift c)
    (ε/4) (by linarith)
  refine ⟨η/2,by linarith,?_⟩
  intro a b hab hLen
  have h1 : b-a ≤ 1 := hLen.trans (min_le_right _ _)
  have hηLen : b-a ≤ η/2 := hLen.trans (min_le_left _ _)
  have hOsc (t : ℝ) (ht : t ∈ Ioc a b) : ‖c (t : Boundary)-c (a : Boundary)‖ ≤ ε/4 := by
    have hdist : dist t a < η := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      linarith [ht.2]
    have hh := hUniform hdist
    simpa only [dist_eq_norm] using hh.le
  exact (meanOscillation_le_of_continuous_comparison f c hfc a b hab h1
    (c (a : Boundary)) (ε/4) hOsc).trans_lt (by linarith)

theorem continuous_toLp_inVMOA (c : C(Boundary,ℂ))
    (hc : ContinuousMap.toLp 2 circleMeasure ℂ c ∈ hardy) :
    InVMOA (ContinuousMap.toLp 2 circleMeasure ℂ c) :=
  inVMOA_of_continuous_ae _ hc c (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure c)


end TTO.Paper.Proved
