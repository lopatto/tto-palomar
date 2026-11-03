/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SingularBoundaryFoundations
public import TTO.ArcL2OscillationFoundations

/-! Literal Poisson lower bounds for every real arc of length at most one. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The midpoint radial disk point attached to the actual real arc `(a,b]`. -/
def arcDiskPoint (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1) : Disk :=
  singularRadialPoint (((a+b)/2 : ℝ) : Boundary) (1-(b-a))
    (by linarith) (by linarith)

@[simp] theorem arcDiskPoint_val (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1) :
    (arcDiskPoint a b hab hLen).val =
      ((1-(b-a) : ℝ) : ℂ)*fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary) := rfl

@[simp] theorem norm_arcDiskPoint (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1) :
    ‖(arcDiskPoint a b hab hLen).val‖ = 1-(b-a) := by
  exact norm_singularRadialPoint _ _ _ _

theorem arc_midpoint_chord_le (a b t : ℝ) (ht : t ∈ Ioc a b) :
    ‖fourier (T := 1) 1 (t : Boundary)-
      fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary)‖ ≤ Real.pi*(b-a) := by
  have hMid : ‖t-(a+b)/2‖ ≤ (b-a)/2 := by
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [ht.1,ht.2]
  rw [circleCharacter_chord_eq]
  have hSub : (t : Boundary)-(((a+b)/2 : ℝ) : Boundary) =
      ((t-(a+b)/2 : ℝ) : Boundary) := rfl
  rw [hSub]
  calc
    _ ≤ 2*Real.pi*‖t-(a+b)/2‖ := norm_circleCharacter_coe_sub_one_le _
    _ ≤ 2*Real.pi*((b-a)/2) := mul_le_mul_of_nonneg_left hMid (by positivity)
    _ = _ := by ring

theorem arcDiskPoint_denominator_le (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1)
    (t : ℝ) (ht : t ∈ Ioc a b) :
    ‖fourier (T := 1) 1 (t : Boundary)-(arcDiskPoint a b hab hLen).val‖ ≤
      (Real.pi+1)*(b-a) := by
  have hr : ‖fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary)-
      (arcDiskPoint a b hab hLen).val‖ = b-a := by
    rw [arcDiskPoint_val]
    rw [show fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary)-
      ((1-(b-a) : ℝ) : ℂ)*fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary) =
      ((b-a : ℝ) : ℂ)*fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary) by push_cast; ring]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hab.le),
      show ‖fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary)‖=1 by simp,mul_one]
  have hD := dist_triangle (fourier (T := 1) 1 (t : Boundary))
    (fourier (T := 1) 1 (((a+b)/2 : ℝ) : Boundary)) (arcDiskPoint a b hab hLen).val
  simp only [dist_eq_norm] at hD
  rw [hr] at hD
  have hChord := arc_midpoint_chord_le a b t ht
  nlinarith

theorem arc_poisson_lower (a b : ℝ) (hab : a < b) (hLen : b-a ≤ 1)
    (t : ℝ) (ht : t ∈ Ioc a b) :
    1/((Real.pi+1)^2*(b-a)) ≤
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hNum : b-a ≤ 1-‖(arcDiskPoint a b hab hLen).val‖^2 := by
    rw [norm_arcDiskPoint]
    nlinarith
  have hDen := arcDiskPoint_denominator_le a b hab hLen t ht
  have hPos : 0 < ‖fourier (T := 1) 1 (t : Boundary)-
      (arcDiskPoint a b hab hLen).val‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
      (circlePoint_sub_disk_ne_zero (t : Boundary) (arcDiskPoint a b hab hLen)))
  change _ ≤ (1-‖(arcDiskPoint a b hab hLen).val‖^2)/
    ‖fourier (T := 1) 1 (t : Boundary)-(arcDiskPoint a b hab hLen).val‖^2
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (Real.pi+1)^2*(b-a)) hPos).mpr
  calc
    _ ≤ ((Real.pi+1)*(b-a))^2 := by
      simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg _) hDen 2
    _ = (b-a)*((Real.pi+1)^2*(b-a)) := by ring
    _ ≤ (1-‖(arcDiskPoint a b hab hLen).val‖^2)*((Real.pi+1)^2*(b-a)) :=
      mul_le_mul_of_nonneg_right hNum (by positivity)



theorem arc_centered_energy_le_poisson (f : BoundaryL2) (a b : ℝ)
    (hab : a < b) (hLen : b-a ≤ 1) (c : ℂ)
    (hI : Integrable (fun t => ‖f t-c‖^2*
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val t) circleMeasure) :
    (∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖^2) ≤
      (Real.pi+1)^2*(b-a)*(∫ t, ‖f t-c‖^2*
        atomicPoissonKernel (arcDiskPoint a b hab hLen).val t ∂circleMeasure) := by
  have hp : MeasurePreserving (fun t : ℝ => (t : Boundary))
      (volume.restrict (Ioc a (a+1))) circleMeasure := by
    rw [circleMeasure_eq_volume]
    exact AddCircle.measurePreserving_mk 1 a
  have hF : Integrable (fun t : Boundary => ‖f t-c‖^2) circleMeasure := by
    simpa only using! ((Lp.memLp f).sub (memLp_const c)).integrable_norm_pow
      (by norm_num : (2 : ℕ)≠0)
  have hFW : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c‖^2) (Ioc a (a+1)) := by
    simpa only [Function.comp_def] using! hp.integrable_comp_of_integrable hF
  have hIW : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c‖^2*
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary)) (Ioc a (a+1)) := by
    simpa only [Function.comp_def] using! hp.integrable_comp_of_integrable hI
  have hSub : Ioc a b ⊆ Ioc a (a+1) :=
    fun t ht => ⟨ht.1,ht.2.trans (by linarith)⟩
  have hC : 0 < (Real.pi+1)^2*(b-a) := by positivity
  have hFN (t : Boundary) : 0 ≤ ‖f t-c‖^2*
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val t :=
    mul_nonneg (sq_nonneg _) (singular_poisson_nonneg _ _)
  calc
    _ ≤ ∫ t : ℝ in Ioc a b, ((Real.pi+1)^2*(b-a))*
        (‖f (t : Boundary)-c‖^2*
          atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary)) := by
      apply setIntegral_mono_on (hFW.mono_set hSub)
        ((hIW.mono_set hSub).const_mul _) measurableSet_Ioc
      intro t ht
      have hP : 1 ≤ atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary)*
          ((Real.pi+1)^2*(b-a)) :=
        (div_le_iff₀ hC).mp (arc_poisson_lower a b hab hLen t ht)
      have hh := mul_le_mul_of_nonneg_left hP (sq_nonneg ‖f (t : Boundary)-c‖)
      nlinarith
    _ = ((Real.pi+1)^2*(b-a))*(∫ t : ℝ in Ioc a b, ‖f (t : Boundary)-c‖^2*
          atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary)) := by
      rw [integral_const_mul]
    _ ≤ ((Real.pi+1)^2*(b-a))*(∫ t : ℝ in Ioc a (a+1), ‖f (t : Boundary)-c‖^2*
          atomicPoissonKernel (arcDiskPoint a b hab hLen).val (t : Boundary)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact setIntegral_mono_set hIW (Eventually.of_forall fun t => hFN (t : Boundary))
        (Eventually.of_forall fun t ht => hSub ht)
    _ = _ := by
      congr 1
      simpa only [← circleMeasure_eq_volume] using! AddCircle.integral_preimage 1 a (fun t : Boundary => ‖f t-c‖^2*
        atomicPoissonKernel (arcDiskPoint a b hab hLen).val t)



theorem meanOscillation_le_poisson_energy (f : BoundaryL2) (a b : ℝ)
    (hab : a < b) (hLen : b-a ≤ 1) (c : ℂ)
    (hI : Integrable (fun t => ‖f t-c‖^2*
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val t) circleMeasure) :
    meanOscillation f a b ≤ 2*(Real.pi+1)*Real.sqrt (∫ t, ‖f t-c‖^2*
      atomicPoissonKernel (arcDiskPoint a b hab hLen).val t ∂circleMeasure) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hs : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr hd
  have hCS := meanOscillation_le_centered_l2 f a b hab hLen c
  have hE := arc_centered_energy_le_poisson f a b hab hLen c hI
  calc
    _ ≤ (2/Real.sqrt (b-a))*Real.sqrt ((Real.pi+1)^2*(b-a)*
        (∫ t, ‖f t-c‖^2*atomicPoissonKernel (arcDiskPoint a b hab hLen).val t ∂circleMeasure)) :=
      hCS.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity))
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (Real.pi+1)^2*(b-a)),
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (by positivity : 0 < Real.pi+1)]
      field_simp

end TTO.Paper.Proved
