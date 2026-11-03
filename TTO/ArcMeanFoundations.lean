/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.Definitions
public import TTO.ContinuousVMOAFoundations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Literal real-interval mean oscillation estimates for the VMOA definition. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved


theorem arcMean_sub_const_integral (f : BoundaryL2) (a b : ℝ) (hab : a<b)
    (hF : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ioc a b)) (c : ℂ) :
    arcMean f a b-c=((b-a : ℝ) : ℂ)⁻¹ * ∫ t in Ioc a b,f (t : Boundary)-c := by
  have hne : ((b-a : ℝ) : ℂ)≠0 := by exact_mod_cast (sub_pos.mpr hab).ne'
  have hFin : volume (Ioc a b)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  rw [integral_sub hF (integrableOn_const hFin),setIntegral_const,
    Real.volume_real_Ioc_of_le hab.le,Complex.real_smul]
  unfold arcMean
  field_simp

theorem norm_arcMean_sub_const_le_centeredIntegral (f : BoundaryL2) (a b : ℝ) (hab : a<b)
    (hF : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ioc a b)) (c : ℂ) :
    ‖arcMean f a b-c‖≤(b-a)⁻¹ * ∫ t in Ioc a b,‖f (t : Boundary)-c‖ := by
  rw [arcMean_sub_const_integral f a b hab hF c,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hab)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr (sub_nonneg.mpr hab.le))


theorem meanOscillation_le_centeredIntegral (f : BoundaryL2) (a b : ℝ) (hab : a<b)
    (hF : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ioc a b)) (c : ℂ) :
    meanOscillation f a b≤2*(b-a)⁻¹ * ∫ t in Ioc a b,‖f (t : Boundary)-c‖ := by
  have hFin : volume (Ioc a b)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hC : IntegrableOn (fun _ : ℝ => c) (Ioc a b) := integrableOn_const hFin
  have hM : IntegrableOn (fun _ : ℝ => arcMean f a b) (Ioc a b) := integrableOn_const hFin
  have hN : IntegrableOn (fun _ : ℝ => ‖arcMean f a b-c‖) (Ioc a b) := integrableOn_const hFin
  have hG : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c‖) (Ioc a b) := (hF.sub hC).norm
  have hI : (∫ t in Ioc a b,‖f (t : Boundary)-arcMean f a b‖)≤
      (∫ t in Ioc a b,‖f (t : Boundary)-c‖)+(b-a)*‖arcMean f a b-c‖ := by
    calc
      _ ≤ ∫ t in Ioc a b,‖f (t : Boundary)-c‖+‖arcMean f a b-c‖ := by
        apply integral_mono_ae (hF.sub hM).norm (hG.add hN)
        exact Filter.Eventually.of_forall (fun t => by
          change ‖f (t : Boundary)-arcMean f a b‖≤‖f (t : Boundary)-c‖+‖arcMean f a b-c‖
          have he : f (t : Boundary)-arcMean f a b=
              (f (t : Boundary)-c)+(c-arcMean f a b) := by abel
          rw [he]
          simpa only [norm_sub_rev c (arcMean f a b)] using
            norm_add_le (f (t : Boundary)-c) (c-arcMean f a b))
      _ = _ := by rw [integral_add hG hN,setIntegral_const,
        Real.volume_real_Ioc_of_le hab.le,smul_eq_mul]
  have hAvg := norm_arcMean_sub_const_le_centeredIntegral f a b hab hF c
  have hAvg' : (b-a)*‖arcMean f a b-c‖≤∫ t in Ioc a b,‖f (t : Boundary)-c‖ := by
    have hm := mul_le_mul_of_nonneg_left hAvg (sub_nonneg.mpr hab.le)
    simpa only [← mul_assoc,mul_inv_cancel₀ (sub_pos.mpr hab).ne',one_mul] using hm
  unfold meanOscillation
  calc
    _ ≤ (b-a)⁻¹*((∫ t in Ioc a b,‖f (t : Boundary)-c‖)+
        (∫ t in Ioc a b,‖f (t : Boundary)-c‖)) :=
      mul_le_mul_of_nonneg_left (hI.trans (add_le_add le_rfl hAvg'))
        (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = _ := by ring


theorem arcMean_add (f g : BoundaryL2) (a b : ℝ) (hLen : b-a≤1) :
    arcMean (f+g) a b=arcMean f a b+arcMean g a b := by
  have he := circle_ae_lift_Ioc (Lp.coeFn_add f g) a b hLen
  unfold arcMean
  rw [integral_congr_ae he]
  simp only [Pi.add_apply]
  rw [integral_add (boundaryL2_integrableOn_lift_Ioc f a b hLen)
    (boundaryL2_integrableOn_lift_Ioc g a b hLen)]
  ring

theorem arcMean_smul (c : ℂ) (f : BoundaryL2) (a b : ℝ) (hLen : b-a≤1) :
    arcMean (c • f) a b=c*arcMean f a b := by
  have he := circle_ae_lift_Ioc (Lp.coeFn_smul c f) a b hLen
  unfold arcMean
  rw [integral_congr_ae he]
  simp only [Pi.smul_apply]
  rw [integral_smul]
  simp only [smul_eq_mul]
  ring


theorem meanOscillation_add_le (f g : BoundaryL2) (a b : ℝ)
    (hab : a<b) (hLen : b-a≤1) :
    meanOscillation (f+g) a b≤meanOscillation f a b+meanOscillation g a b := by
  have hFin : volume (Ioc a b)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hFI := boundaryL2_integrableOn_lift_Ioc f a b hLen
  have hGI := boundaryL2_integrableOn_lift_Ioc g a b hLen
  have hSI := boundaryL2_integrableOn_lift_Ioc (f+g) a b hLen
  have hFn : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-arcMean f a b‖) (Ioc a b) :=
    (hFI.sub (integrableOn_const hFin)).norm
  have hGn : IntegrableOn (fun t : ℝ => ‖g (t : Boundary)-arcMean g a b‖) (Ioc a b) :=
    (hGI.sub (integrableOn_const hFin)).norm
  have hSn : IntegrableOn (fun t : ℝ => ‖(f+g) (t : Boundary)-arcMean (f+g) a b‖) (Ioc a b) :=
    (hSI.sub (integrableOn_const hFin)).norm
  have he := circle_ae_lift_Ioc (Lp.coeFn_add f g) a b hLen
  have hAE : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioc a b),
      ‖(f+g) (t : Boundary)-arcMean (f+g) a b‖≤
        ‖f (t : Boundary)-arcMean f a b‖+‖g (t : Boundary)-arcMean g a b‖ := by
    filter_upwards [he] with t ht
    rw [ht,arcMean_add f g a b hLen]
    change ‖(f (t : Boundary)+g (t : Boundary))-(arcMean f a b+arcMean g a b)‖≤_
    have hId : f (t : Boundary)+g (t : Boundary)-(arcMean f a b+arcMean g a b)=
      (f (t : Boundary)-arcMean f a b)+(g (t : Boundary)-arcMean g a b) := by abel
    rw [hId]
    exact norm_add_le _ _
  have hI := integral_mono_ae hSn (hFn.add hGn) hAE
  simp only [Pi.add_apply] at hI
  rw [integral_add hFn hGn] at hI
  unfold meanOscillation
  exact (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (sub_nonneg.mpr hab.le))).trans_eq (by ring)

theorem meanOscillation_smul (c : ℂ) (f : BoundaryL2) (a b : ℝ) (hLen : b-a≤1) :
    meanOscillation (c • f) a b=‖c‖*meanOscillation f a b := by
  have he := circle_ae_lift_Ioc (Lp.coeFn_smul c f) a b hLen
  have hAE : (fun t : ℝ => ‖(c • f) (t : Boundary)-arcMean (c • f) a b‖)=ᵐ[volume.restrict (Ioc a b)]
      (fun t : ℝ => ‖c‖*‖f (t : Boundary)-arcMean f a b‖) := by
    filter_upwards [he] with t ht
    rw [ht,arcMean_smul c f a b hLen]
    change ‖c*f (t : Boundary)-c*arcMean f a b‖=_
    rw [← mul_sub,norm_mul]
  unfold meanOscillation
  rw [integral_congr_ae hAE,integral_const_mul]
  ring


theorem inVMOA_add (f g : BoundaryL2) (hf : InVMOA f) (hg : InVMOA g) :
    InVMOA (f+g) := by
  refine ⟨hardy.add_mem hf.1 hg.1,?_⟩
  intro ε hε
  obtain ⟨δf,hδf,hfOsc⟩ := hf.2 (ε/2) (by linarith)
  obtain ⟨δg,hδg,hgOsc⟩ := hg.2 (ε/2) (by linarith)
  refine ⟨min δf δg,lt_min hδf hδg,?_⟩
  intro a b hab hLen
  have h1 : b-a≤1 := hLen.trans (min_le_right _ _)
  have hδ : b-a≤min δf δg := hLen.trans (min_le_left _ _)
  have hF := hfOsc a b hab (le_min (hδ.trans (min_le_left _ _)) h1)
  have hG := hgOsc a b hab (le_min (hδ.trans (min_le_right _ _)) h1)
  exact (meanOscillation_add_le f g a b hab h1).trans_lt (by linarith)

theorem inVMOA_smul (c : ℂ) (f : BoundaryL2) (hf : InVMOA f) : InVMOA (c • f) := by
  refine ⟨hardy.smul_mem c hf.1,?_⟩
  intro ε hε
  have hDen : 0<‖c‖+1 := by positivity
  obtain ⟨δ,hδ,hOsc⟩ := hf.2 (ε/(‖c‖+1)) (div_pos hε hDen)
  refine ⟨δ,hδ,?_⟩
  intro a b hab hLen
  calc
    _ = ‖c‖*meanOscillation f a b := meanOscillation_smul c f a b (hLen.trans (min_le_right _ _))
    _ ≤ ‖c‖*(ε/(‖c‖+1)) := mul_le_mul_of_nonneg_left (hOsc a b hab hLen).le (norm_nonneg c)
    _ = (‖c‖*ε)/(‖c‖+1) := by ring
    _ < ε := (div_lt_iff₀ hDen).mpr (by nlinarith)

theorem inVMOA_neg (f : BoundaryL2) (hf : InVMOA f) : InVMOA (-f) := by
  simpa only [neg_one_smul] using inVMOA_smul (-1 : ℂ) f hf

theorem inVMOA_sub (f g : BoundaryL2) (hf : InVMOA f) (hg : InVMOA g) : InVMOA (f-g) := by
  simpa only [sub_eq_add_neg] using inVMOA_add f (-g) hf (inVMOA_neg g hg)


theorem inVMOA_of_uniform_meanOscillation_approximation (f : BoundaryL2) (hf : f∈hardy)
    (g : ℕ → BoundaryL2) (hg : ∀ n,InVMOA (g n))
    (hApprox : ∀ ε : ℝ,0<ε → ∃ n : ℕ,∀ a b : ℝ,a<b → b-a≤1 →
      meanOscillation (f-g n) a b<ε) : InVMOA f := by
  refine ⟨hf,?_⟩
  intro ε hε
  obtain ⟨n,hn⟩ := hApprox (ε/2) (by linarith)
  obtain ⟨δ,hδ,hOsc⟩ := (hg n).2 (ε/2) (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro a b hab hLen
  have h1 : b-a≤1 := hLen.trans (min_le_right _ _)
  have hF := hn a b hab h1
  have hG := hOsc a b hab hLen
  have hSum := meanOscillation_add_le (f-g n) (g n) a b hab h1
  rw [sub_add_cancel] at hSum
  exact hSum.trans_lt (by linarith)

end TTO.Paper.Proved
