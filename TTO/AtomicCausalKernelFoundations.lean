/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicPWTransportFoundations
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Literal causal/coanalytic inputs, a genuine one-sided smooth mollifier, and smoothed kernels.
No convenient kernel is identified with a boundary-defined manuscript distribution by definition. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace TTO.Paper.Proved

def atomicMollifierBump : ContDiffBump ((1 : ℝ) / 2) :=
  ⟨1 / 8,1 / 4,by norm_num,by norm_num⟩

/-- A chosen real nonnegative C_c^∞(0,1) function of integral one. -/
def atomicMollifier : ℝ → ℝ := atomicMollifierBump.normed (volume : Measure ℝ)

theorem atomicMollifier_contDiff : ContDiff ℝ ∞ atomicMollifier :=
  atomicMollifierBump.contDiff_normed

theorem atomicMollifier_hasCompactSupport : HasCompactSupport atomicMollifier :=
  atomicMollifierBump.hasCompactSupport_normed

theorem atomicMollifier_nonneg (t : ℝ) : 0 ≤ atomicMollifier t :=
  atomicMollifierBump.nonneg_normed t

theorem atomicMollifier_integral : (∫ t : ℝ, atomicMollifier t) = 1 :=
  atomicMollifierBump.integral_normed

theorem atomicMollifier_tsupport : tsupport atomicMollifier ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  change t ∈ tsupport (atomicMollifierBump.normed (volume : Measure ℝ)) at ht
  rw [atomicMollifierBump.tsupport_normed_eq] at ht
  have hh : |t - 1 / 2| ≤ (1 : ℝ) / 4 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,atomicMollifierBump] using ht
  have ha := abs_le.mp hh
  constructor <;> linarith

def scaledAtomicMollifier (ε : ℝ) (t : ℝ) : ℝ := ε⁻¹ * atomicMollifier (t / ε)

def scaledAtomicMollifierDeriv (ε : ℝ) (t : ℝ) : ℝ :=
  (ε ^ 2)⁻¹ * deriv atomicMollifier (t / ε)

theorem scaledAtomicMollifier_contDiff (ε : ℝ) : ContDiff ℝ ∞ (scaledAtomicMollifier ε) :=
  contDiff_const.mul (atomicMollifier_contDiff.comp (contDiff_id.div_const ε))

theorem scaledAtomicMollifier_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ scaledAtomicMollifier ε t :=
  mul_nonneg (inv_nonneg.mpr hε.le) (atomicMollifier_nonneg _)

theorem scaledAtomicMollifier_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, scaledAtomicMollifier ε t) = 1 := by
  change (∫ t : ℝ, ε⁻¹ * atomicMollifier (t / ε)) = 1
  rw [integral_const_mul,Measure.integral_comp_div,atomicMollifier_integral]
  simp only [smul_eq_mul,abs_of_pos hε,mul_one,inv_mul_cancel₀ hε.ne']

/-- These are literal supported representatives of the PW-coordinate L² inputs. -/
def atomicPositiveInput (g : HalfLineL2) (t : ℝ) : ℂ := (Ioi (0 : ℝ)).indicator g t

def atomicNegativeInput (g : HalfLineL2) (t : ℝ) : ℂ :=
  (Iio (0 : ℝ)).indicator (fun t => conj (g (-t))) t

theorem memLp_atomicPositiveInput (g : HalfLineL2) : MemLp (atomicPositiveInput g) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr (Lp.memLp g)

/-- The constants and derivative signs match the proved analytic and coanalytic form actions. -/
def atomicSmoothedPlus (ε : ℝ) (g : HalfLineL2) (y : ℝ) : ℂ :=
  (Complex.I / (Real.sqrt 2 : ℂ)) *
    ∫ t : ℝ, atomicPositiveInput g t *
      ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) + (scaledAtomicMollifier ε (y - t) : ℂ))

def atomicSmoothedMinus (ε : ℝ) (g : HalfLineL2) (y : ℝ) : ℂ :=
  (Complex.I / (Real.sqrt 2 : ℂ)) *
    ∫ t : ℝ, atomicNegativeInput g t *
      ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) - (scaledAtomicMollifier ε (y - t) : ℂ))

def atomicSmoothedKernel (ε : ℝ) (g h : HalfLineL2) (y : ℝ) : ℂ :=
  atomicSmoothedPlus ε g y + atomicSmoothedMinus ε h y

def atomicCrossingScalar (ε : ℝ) (h : HalfLineL2) : ℂ :=
  ∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε h y

theorem hasDerivAt_scaledAtomicMollifier (ε t : ℝ) :
    HasDerivAt (scaledAtomicMollifier ε) (scaledAtomicMollifierDeriv ε t) t := by
  have hd := ((((atomicMollifier_contDiff.differentiable (by simp)) (t / ε)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const ε)).const_mul ε⁻¹
  have he : (fun y => ε⁻¹ * (atomicMollifier ∘ fun x : ℝ => id x / ε) y) =
      scaledAtomicMollifier ε := by funext y; rfl
  rw [he] at hd
  simpa only [scaledAtomicMollifierDeriv,inv_pow,pow_two,mul_inv_rev,one_div,mul_assoc,mul_left_comm,mul_comm] using! hd

theorem deriv_scaledAtomicMollifier (ε : ℝ) :
    deriv (scaledAtomicMollifier ε) = scaledAtomicMollifierDeriv ε :=
  funext fun t => (hasDerivAt_scaledAtomicMollifier ε t).deriv

theorem scaledAtomicMollifierDeriv_contDiff (ε : ℝ) :
    ContDiff ℝ ∞ (scaledAtomicMollifierDeriv ε) := by
  rw [← deriv_scaledAtomicMollifier]
  exact (contDiff_infty_iff_deriv.mp (scaledAtomicMollifier_contDiff ε)).2

theorem scaledAtomicMollifier_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaledAtomicMollifier ε) := by
  let D : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ ε⁻¹ (inv_ne_zero hε.ne')
  have hd : HasCompactSupport (atomicMollifier ∘ D) :=
    atomicMollifier_hasCompactSupport.comp_homeomorph D
  have hs : scaledAtomicMollifier ε = (fun r : ℝ => ε⁻¹ * r) ∘ (atomicMollifier ∘ D) := by
    funext t
    simp only [scaledAtomicMollifier,Function.comp_apply,D,Homeomorph.coe_mulRight₀,div_eq_mul_inv]
  rw [hs]
  exact hd.comp_left (by simp)

theorem scaledAtomicMollifier_tsupport {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaledAtomicMollifier ε) ⊆ Ioo (0 : ℝ) ε := by
  let D : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ ε⁻¹ (inv_ne_zero hε.ne')
  have hs : scaledAtomicMollifier ε = (fun r : ℝ => ε⁻¹ * r) ∘ (atomicMollifier ∘ D) := by
    funext t
    simp only [scaledAtomicMollifier,Function.comp_apply,D,Homeomorph.coe_mulRight₀,div_eq_mul_inv]
  intro t ht
  rw [hs] at ht
  have hd : t ∈ tsupport (atomicMollifier ∘ D) :=
    tsupport_comp_subset (g := fun r : ℝ => ε⁻¹ * r) (by simp) (atomicMollifier ∘ D) ht
  rw [tsupport_comp_eq_preimage] at hd
  have hm := atomicMollifier_tsupport hd
  have hm' : 0 < t / ε ∧ t / ε < 1 := by
    simpa only [D,Homeomorph.coe_mulRight₀,Set.mem_Ioo,div_eq_mul_inv] using hm
  constructor
  · have hp := mul_lt_mul_of_pos_right hm'.1 hε
    simpa only [zero_mul,div_mul_cancel₀ t hε.ne'] using hp
  · have hp := mul_lt_mul_of_pos_right hm'.2 hε
    simpa only [one_mul,div_mul_cancel₀ t hε.ne'] using hp

theorem scaledAtomicMollifierDeriv_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaledAtomicMollifierDeriv ε) := by
  rw [← deriv_scaledAtomicMollifier]
  exact (scaledAtomicMollifier_hasCompactSupport hε).deriv

theorem scaledAtomicMollifierDeriv_tsupport {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaledAtomicMollifierDeriv ε) ⊆ Ioo (0 : ℝ) ε := by
  rw [← deriv_scaledAtomicMollifier]
  exact tsupport_deriv_subset.trans (scaledAtomicMollifier_tsupport hε)

theorem scaledAtomicMollifier_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaledAtomicMollifier ε) :=
  (scaledAtomicMollifier_contDiff ε).continuous.integrable_of_hasCompactSupport
    (scaledAtomicMollifier_hasCompactSupport hε)

theorem scaledAtomicMollifierDeriv_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaledAtomicMollifierDeriv ε) :=
  (scaledAtomicMollifierDeriv_contDiff ε).continuous.integrable_of_hasCompactSupport
    (scaledAtomicMollifierDeriv_hasCompactSupport hε)

theorem atomicNegativeInput_eq_reflect (g : HalfLineL2) (t : ℝ) :
    atomicNegativeInput g t = conj (atomicPositiveInput g (-t)) := by
  by_cases ht : t ∈ Iio (0 : ℝ)
  · have hn : -t ∈ Ioi (0 : ℝ) := by simpa only [Set.mem_Ioi,Set.mem_Iio,neg_pos] using! ht
    simp only [atomicNegativeInput,atomicPositiveInput,indicator_of_mem ht,indicator_of_mem hn]
  · have hn : -t ∉ Ioi (0 : ℝ) := by
      simpa only [Set.mem_Ioi,Set.mem_Iio,neg_pos] using ht
    simp only [atomicNegativeInput,atomicPositiveInput,indicator_of_notMem ht,indicator_of_notMem hn,map_zero]

theorem memLp_atomicNegativeInput (g : HalfLineL2) : MemLp (atomicNegativeInput g) 2 volume := by
  have hm := (memLp_atomicPositiveInput g).comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hs : MemLp (fun t : ℝ => conj (atomicPositiveInput g (-t))) 2 volume := by
    simpa only [Function.comp_def] using! hm.star
  exact hs.ae_eq (Eventually.of_forall fun t => (atomicNegativeInput_eq_reflect g t).symm)

theorem pwCorrelation_conj_swap (a b : ℝ → ℂ) (t : ℝ) :
    conj (pwCorrelation b a t) = pwCorrelation a b (-t) := by
  rw [pwCorrelation,← integral_conj,pwCorrelation]
  simp only [map_mul,Complex.conj_conj]
  calc
    _ = ∫ s : ℝ, (fun r : ℝ => a r * conj (b (r - t))) (s + t) := by
      congr 1
      funext s
      simp only [add_sub_cancel_right,mul_comm]
    _ = ∫ s : ℝ, a s * conj (b (s - t)) := by
      simpa only using! (integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun r : ℝ => a r * conj (b (r - t))) t)
    _ = _ := by simp only [sub_eq_add_neg]

theorem pwCorrelation_conj_deriv_swap {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) (t : ℝ) :
    conj (deriv (pwCorrelation b a) t) = -deriv (pwCorrelation a b) (-t) := by
  have he : (fun r : ℝ => conj (pwCorrelation b a r)) =
      fun r : ℝ => pwCorrelation a b (-r) := funext (pwCorrelation_conj_swap a b)
  have hL : HasDerivAt (fun r : ℝ => conj (pwCorrelation b a r))
      (conj (deriv (pwCorrelation b a) t)) t := by
    have hd := (hasDerivAt_const (x := t) (Complex.conjCLE.toContinuousLinearMap)).clm_apply
      ((hasDerivAt_pwCorrelation_left hb ha t).differentiableAt.hasDerivAt)
    simpa using! hd
  have hR : HasDerivAt (fun r : ℝ => pwCorrelation a b (-r))
      (-deriv (pwCorrelation a b) (-t)) t := by
    have hd := ((hasDerivAt_pwCorrelation_left ha hb (-t)).differentiableAt.hasDerivAt).scomp t
      (hasDerivAt_neg t)
    simpa only [Function.comp_def,neg_smul,one_smul] using! hd
  rw [he] at hL
  exact hL.unique hR

theorem integral_Ioi_eq_Iio_reflect (F : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), F t) = ∫ t in Iio (0 : ℝ), F (-t) := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Iio]
  have he : (fun t : ℝ => (Ioi (0 : ℝ)).indicator F (-t)) =
      (Iio (0 : ℝ)).indicator (fun t => F (-t)) := by
    funext t
    by_cases ht : t ∈ Iio (0 : ℝ)
    · have hn : -t ∈ Ioi (0 : ℝ) := by simpa only [Set.mem_Ioi,Set.mem_Iio,neg_pos] using! ht
      rw [indicator_of_mem hn,indicator_of_mem ht]
    · have hn : -t ∉ Ioi (0 : ℝ) := by
        simpa only [Set.mem_Ioi,Set.mem_Iio,neg_pos] using ht
      rw [indicator_of_notMem hn,indicator_of_notMem ht]
  rw [← he]
  exact (integral_neg_eq_self ((Ioi (0 : ℝ)).indicator F) (volume : Measure ℝ)).symm

/-- Conjugating the already proved analytic form gives the literal negative-side derivative action. -/
theorem coanalytic_coreForm_of_causal (ℓ : ℝ) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy)
    (hA : ∀ (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          ∫ t in Ioi (0 : ℝ), (H.symm φ) t * (-deriv (pwCorrelation a b) t + pwCorrelation a b t))
    (ψ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b)
    (haBound : IsBounded (U (smoothIntervalL2 ℓ a ha)).val) :
    coreForm (star ψ.val) (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t in Iio (0 : ℝ), conj ((H.symm ψ) (-t)) *
          (-deriv (pwCorrelation a b) t - pwCorrelation a b t) := by
  rw [coreForm_star _ _ _ haBound,hA ψ b a hb ha,map_mul]
  have hc : conj (Complex.I / (Real.sqrt 2 : ℂ)) = -(Complex.I / (Real.sqrt 2 : ℂ)) := by
    simp
    ring
  rw [hc,← integral_conj,integral_Ioi_eq_Iio_reflect]
  calc
    _ = (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t in Iio (0 : ℝ),
          -(conj ((H.symm ψ) (-t) * (-deriv (pwCorrelation b a) (-t) + pwCorrelation b a (-t)))) := by
      rw [integral_neg]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        simp only [map_mul,map_add,map_neg,pwCorrelation_conj_deriv_swap ha hb (-t),
          pwCorrelation_conj_swap a b (-t),neg_neg]
        ring

/-- The same actual maps work for every analytic and coanalytic symbol, without a symbol-dependent
choice of coordinates. -/
theorem exists_singleAtomPWBothForms (u : BoundaryLInf) (hu : IsInner u)
    (ζ : Boundary) (hζ : SingleAtom u ζ) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u,
      ∃ H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy,
        Dense (pwSmoothModelCore U : Set (Model u)) ∧
        (∀ f ∈ pwSmoothModelCore U, IsBounded f.val) ∧
        (∀ (φ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
          (hb : IntervalSmoothCompact ℓ b),
          coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
            (Complex.I / (Real.sqrt 2 : ℂ)) *
              ∫ t in Ioi (0 : ℝ), (H.symm φ) t *
                (-deriv (pwCorrelation a b) t + pwCorrelation a b t)) ∧
        ∀ (ψ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
          (hb : IntervalSmoothCompact ℓ b),
          coreForm (star ψ.val) (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val =
            (Complex.I / (Real.sqrt 2 : ℂ)) *
              ∫ t in Iio (0 : ℝ), conj ((H.symm ψ) (-t)) *
                (-deriv (pwCorrelation a b) t - pwCorrelation a b t) := by
  obtain ⟨ℓ,hℓ,U,H,_hU,_hH,hd,hbd,hA⟩ := exists_singleAtomPWTransport u hu ζ hζ
  refine ⟨ℓ,hℓ,U,H,hd,hbd,hA,?_⟩
  intro ψ a b ha hb
  exact coanalytic_coreForm_of_causal ℓ u U H hA ψ a b ha hb
    (hbd _ ((mem_pwSmoothModelCore_iff ℓ u U _).mpr ⟨a,ha,rfl⟩))

theorem atomicSmoothedPlus_contDiff {ε : ℝ} (hε : 0 < ε) (g : HalfLineL2) :
    ContDiff ℝ ∞ (atomicSmoothedPlus ε g) := by
  let k : ℝ → ℂ := fun t =>
    (scaledAtomicMollifierDeriv ε t : ℂ) + (scaledAtomicMollifier ε t : ℂ)
  have hkC : ContDiff ℝ ∞ k :=
    (Complex.ofRealCLM.contDiff.comp (scaledAtomicMollifierDeriv_contDiff ε)).add
      (Complex.ofRealCLM.contDiff.comp (scaledAtomicMollifier_contDiff ε))
  have hkS : HasCompactSupport k :=
    ((scaledAtomicMollifierDeriv_hasCompactSupport hε).comp_left (g := fun t : ℝ => (t : ℂ)) (by rfl)).add
      ((scaledAtomicMollifier_hasCompactSupport hε).comp_left (g := fun t : ℝ => (t : ℂ)) (by rfl))
  have hc := hkS.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) (n := ⊤)
    ((memLp_atomicPositiveInput g).locallyIntegrable (by norm_num)) hkC
  simpa only [atomicSmoothedPlus,convolution_def,k] using!
    (contDiff_const.mul hc : ContDiff ℝ ∞ (fun y => (Complex.I / (Real.sqrt 2 : ℂ)) * _))

theorem atomicSmoothedMinus_contDiff {ε : ℝ} (hε : 0 < ε) (g : HalfLineL2) :
    ContDiff ℝ ∞ (atomicSmoothedMinus ε g) := by
  let k : ℝ → ℂ := fun t =>
    (scaledAtomicMollifierDeriv ε t : ℂ) - (scaledAtomicMollifier ε t : ℂ)
  have hkC : ContDiff ℝ ∞ k :=
    (Complex.ofRealCLM.contDiff.comp (scaledAtomicMollifierDeriv_contDiff ε)).sub
      (Complex.ofRealCLM.contDiff.comp (scaledAtomicMollifier_contDiff ε))
  have hkS : HasCompactSupport k :=
    ((scaledAtomicMollifierDeriv_hasCompactSupport hε).comp_left (g := fun t : ℝ => (t : ℂ)) (by rfl)).sub
      ((scaledAtomicMollifier_hasCompactSupport hε).comp_left (g := fun t : ℝ => (t : ℂ)) (by rfl))
  have hc := hkS.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) (n := ⊤)
    ((memLp_atomicNegativeInput g).locallyIntegrable (by norm_num)) hkC
  simpa only [atomicSmoothedMinus,convolution_def,k] using!
    (contDiff_const.mul hc : ContDiff ℝ ∞ (fun y => (Complex.I / (Real.sqrt 2 : ℂ)) * _))

theorem atomicSmoothedKernel_contDiff {ε : ℝ} (hε : 0 < ε) (g h : HalfLineL2) :
    ContDiff ℝ ∞ (atomicSmoothedKernel ε g h) :=
  (atomicSmoothedPlus_contDiff hε g).add (atomicSmoothedMinus_contDiff hε h)

theorem scaledAtomicMollifier_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ∉ Ioo (0 : ℝ) ε) :
    scaledAtomicMollifier ε x = 0 := by
  by_contra hn
  exact hx (scaledAtomicMollifier_tsupport hε (subset_tsupport _ hn))

theorem scaledAtomicMollifierDeriv_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ∉ Ioo (0 : ℝ) ε) :
    scaledAtomicMollifierDeriv ε x = 0 := by
  by_contra hn
  exact hx (scaledAtomicMollifierDeriv_tsupport hε (subset_tsupport _ hn))

theorem atomicSmoothedPlus_eq_zero {ε y : ℝ} (hε : 0 < ε) (g : HalfLineL2) (hy : y ≤ 0) :
    atomicSmoothedPlus ε g y = 0 := by
  unfold atomicSmoothedPlus
  have hz : (∫ t : ℝ, atomicPositiveInput g t *
      ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) + (scaledAtomicMollifier ε (y - t) : ℂ))) = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => by
      change atomicPositiveInput g t * ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) +
        (scaledAtomicMollifier ε (y - t) : ℂ)) = 0
      by_cases ht : 0 < t
      · have hn : y - t ∉ Ioo (0 : ℝ) ε := fun h => by linarith [h.1]
        rw [scaledAtomicMollifierDeriv_eq_zero hε hn,scaledAtomicMollifier_eq_zero hε hn]
        simp
      · have hn : t ∉ Ioi (0 : ℝ) := ht
        simp only [atomicPositiveInput,indicator_of_notMem hn,zero_mul]
  rw [hz,mul_zero]

theorem atomicSmoothedMinus_eq_zero {ε y : ℝ} (hε : 0 < ε) (g : HalfLineL2) (hy : ε ≤ y) :
    atomicSmoothedMinus ε g y = 0 := by
  unfold atomicSmoothedMinus
  have hz : (∫ t : ℝ, atomicNegativeInput g t *
      ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) - (scaledAtomicMollifier ε (y - t) : ℂ))) = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => by
      change atomicNegativeInput g t * ((scaledAtomicMollifierDeriv ε (y - t) : ℂ) -
        (scaledAtomicMollifier ε (y - t) : ℂ)) = 0
      by_cases ht : t < 0
      · have hn : y - t ∉ Ioo (0 : ℝ) ε := fun h => by linarith [h.2]
        rw [scaledAtomicMollifierDeriv_eq_zero hε hn,scaledAtomicMollifier_eq_zero hε hn]
        simp
      · have hn : t ∉ Iio (0 : ℝ) := ht
        simp only [atomicNegativeInput,indicator_of_notMem hn,zero_mul]
  rw [hz,mul_zero]

/-- The crossing scalar is an honest finite integral of a smooth function. -/
theorem integrableOn_atomicSmoothedMinus {ε : ℝ} (hε : 0 < ε) (g : HalfLineL2) :
    IntegrableOn (atomicSmoothedMinus ε g) (Ioo (0 : ℝ) ε) :=
  ((atomicSmoothedMinus_contDiff hε g).continuous.integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- A native L² small-interval estimate used only for the crossing remainder. -/
theorem lineL2_normIntegral_Ioo_le (f : LineL2) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Ioo a b, ‖f t‖) ≤ ‖f‖ * Real.sqrt (b - a) := by
  let e : LineL2 := indicatorConstLp (μ := (volume : Measure ℝ)) (s := Ioo a b) 2 measurableSet_Ioo (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (1 : ℂ)
  have he : e =ᵐ[volume] (Ioo a b).indicator (fun _ : ℝ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hn : ‖e‖ = Real.sqrt (b - a) := by
    dsimp only [e]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul,
      Real.volume_real_Ioo,max_eq_left (sub_nonneg.mpr hab)]
    norm_num only [ENNReal.toReal_ofNat]
    exact (Real.sqrt_eq_rpow _).symm
  have hi : (∫ t in Ioo a b, ‖f t‖) = ∫ t : ℝ, ‖f t‖ * ‖e t‖ := by
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [he] with t ht
    rw [ht]
    by_cases hm : t ∈ Ioo a b
    · simp only [indicator_of_mem hm,norm_one,mul_one]
    · simp only [indicator_of_notMem hm,norm_zero,mul_zero]
  rw [hi,← hn]
  exact lineL2_normPairIntegral_le f e

def atomicNegativeL2 (g : HalfLineL2) : LineL2 :=
  (memLp_atomicNegativeInput g).toLp (atomicNegativeInput g)

theorem atomicNegativeL2_ae (g : HalfLineL2) :
    atomicNegativeL2 g =ᵐ[volume] atomicNegativeInput g :=
  (memLp_atomicNegativeInput g).coeFn_toLp

theorem atomicNegativeInput_normIntegral_le (g : HalfLineL2) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioo (-ε) (0 : ℝ), ‖atomicNegativeInput g t‖) ≤
      ‖atomicNegativeL2 g‖ * Real.sqrt ε := by
  have hi : (∫ t in Ioo (-ε) (0 : ℝ), ‖atomicNegativeInput g t‖) =
      ∫ t in Ioo (-ε) (0 : ℝ), ‖(atomicNegativeL2 g) t‖ := by
    apply integral_congr_ae
    exact ((atomicNegativeL2_ae g).filter_mono (ae_restrict_le)).symm.fun_comp norm
  rw [hi]
  simpa only [sub_neg_eq_add,zero_add] using
    lineL2_normIntegral_Ioo_le (atomicNegativeL2 g) (a := -ε) (b := 0) (by linarith)

theorem atomicMollifier_bounds :
    ∃ M₀ M₁ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧
      (∀ t, ‖atomicMollifier t‖ ≤ M₀) ∧ (∀ t, ‖deriv atomicMollifier t‖ ≤ M₁) := by
  have hc₀ := atomicMollifier_contDiff.continuous.norm
  have hc₁ := (atomicMollifier_contDiff.continuous_deriv (by simp)).norm
  have hs₀ := atomicMollifier_hasCompactSupport.norm
  have hs₁ := atomicMollifier_hasCompactSupport.deriv.norm
  obtain ⟨M₀,hM₀⟩ := hc₀.bddAbove_range_of_hasCompactSupport hs₀
  obtain ⟨M₁,hM₁⟩ := hc₁.bddAbove_range_of_hasCompactSupport hs₁
  refine ⟨max M₀ 0,max M₁ 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro t
    exact (hM₀ ⟨t,rfl⟩).trans (le_max_left _ _)
  · intro t
    exact (hM₁ ⟨t,rfl⟩).trans (le_max_left _ _)

theorem scaledAtomicMollifier_norm_le {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ t, ‖atomicMollifier t‖ ≤ M) (t : ℝ) :
    ‖(scaledAtomicMollifier ε t : ℂ)‖ ≤ ε⁻¹ * M := by
  rw [Complex.norm_real,scaledAtomicMollifier,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr hε.le)

theorem scaledAtomicMollifierDeriv_norm_le {ε M : ℝ} (_hε : 0 < ε)
    (hM : ∀ t, ‖deriv atomicMollifier t‖ ≤ M) (t : ℝ) :
    ‖(scaledAtomicMollifierDeriv ε t : ℂ)‖ ≤ (ε^2)⁻¹ * M := by
  rw [Complex.norm_real,scaledAtomicMollifierDeriv,norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ε))]
  exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr (sq_nonneg ε))

theorem atomicSmoothedMinus_crossing_integral {ε y : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (hy : y ∈ Ioo (0 : ℝ) ε) :
    atomicSmoothedMinus ε g y = (Complex.I / (Real.sqrt 2 : ℂ)) *
      ∫ t in Ioo (-ε) (0 : ℝ), atomicNegativeInput g t *
        ((scaledAtomicMollifierDeriv ε (y-t) : ℂ) - (scaledAtomicMollifier ε (y-t) : ℂ)) := by
  unfold atomicSmoothedMinus
  congr 1
  rw [← integral_indicator measurableSet_Ioo]
  congr 1
  funext t
  by_cases ht : t ∈ Ioo (-ε) (0 : ℝ)
  · simp only [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    by_cases ht0 : t < 0
    · have hn : y-t ∉ Ioo (0 : ℝ) ε := fun h => by
        have hneg : t ≤ -ε := by
          by_contra hn
          exact ht ⟨lt_of_not_ge hn,ht0⟩
        linarith [hy.1,h.2]
      rw [scaledAtomicMollifierDeriv_eq_zero hε hn,scaledAtomicMollifier_eq_zero hε hn]
      simp
    · have hn : t ∉ Iio (0 : ℝ) := by simpa only [Set.mem_Iio] using! ht0
      simp only [atomicNegativeInput,indicator_of_notMem hn,zero_mul]

theorem atomicSmoothedMinus_crossing_bound {ε y M₀ M₁ : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (hy : y ∈ Ioo (0 : ℝ) ε)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hη : ∀ t, ‖atomicMollifier t‖ ≤ M₀)
    (hηD : ∀ t, ‖deriv atomicMollifier t‖ ≤ M₁) :
    ‖atomicSmoothedMinus ε g y‖ ≤ ‖Complex.I / (Real.sqrt 2 : ℂ)‖ *
      ((ε^2)⁻¹ * M₁ + ε⁻¹ * M₀) * (‖atomicNegativeL2 g‖ * Real.sqrt ε) := by
  let B := (ε^2)⁻¹ * M₁ + ε⁻¹ * M₀
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg ε)) hM₁)
    (mul_nonneg (inv_nonneg.mpr hε.le) hM₀)
  have hJ : IntegrableOn (fun t => ‖atomicNegativeInput g t‖) (Ioo (-ε) (0 : ℝ)) :=
    ((memLp_atomicNegativeInput g).norm.restrict _).integrable (by norm_num)
  have hi : ‖∫ t in Ioo (-ε) (0 : ℝ), atomicNegativeInput g t *
      ((scaledAtomicMollifierDeriv ε (y-t) : ℂ) - (scaledAtomicMollifier ε (y-t) : ℂ))‖ ≤
      B * (‖atomicNegativeL2 g‖ * Real.sqrt ε) := by
    calc
      _ ≤ ∫ t in Ioo (-ε) (0 : ℝ), B * ‖atomicNegativeInput g t‖ := by
        apply norm_integral_le_of_norm_le (hJ.const_mul B)
        exact Eventually.of_forall fun t => by
          rw [norm_mul,mul_comm B]
          exact mul_le_mul_of_nonneg_left
            ((norm_sub_le _ _).trans (add_le_add (scaledAtomicMollifierDeriv_norm_le hε hηD _)
              (scaledAtomicMollifier_norm_le hε hη _))) (norm_nonneg _)
      _ = B * ∫ t in Ioo (-ε) (0 : ℝ), ‖atomicNegativeInput g t‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (atomicNegativeInput_normIntegral_le g hε) hB
  rw [atomicSmoothedMinus_crossing_integral hε g hy,norm_mul]
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (by dsimp only [B]; ring)

def atomicCrossingError (ε : ℝ) (g : HalfLineL2) (q : ℝ → ℂ) : ℂ :=
  ∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε g y * (q y - q 0)

theorem atomicCrossingError_bound {ε M₀ M₁ D : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (_hD : 0 ≤ D)
    (hη : ∀ t, ‖atomicMollifier t‖ ≤ M₀)
    (hηD : ∀ t, ‖deriv atomicMollifier t‖ ≤ M₁)
    (hq : ∀ y ∈ Ioo (0 : ℝ) ε, ‖q y - q 0‖ ≤ D * ε) :
    ‖atomicCrossingError ε g q‖ ≤ ‖Complex.I / (Real.sqrt 2 : ℂ)‖ *
      ‖atomicNegativeL2 g‖ * D * (M₁ + ε * M₀) * Real.sqrt ε := by
  let C := ‖Complex.I / (Real.sqrt 2 : ℂ)‖ *
    ((ε^2)⁻¹ * M₁ + ε⁻¹ * M₀) * (‖atomicNegativeL2 g‖ * Real.sqrt ε)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hi : ‖atomicCrossingError ε g q‖ ≤ (C * (D * ε)) * volume.real (Ioo (0 : ℝ) ε) := by
    apply norm_setIntegral_le_of_norm_le_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    intro y hy
    rw [norm_mul]
    exact mul_le_mul (atomicSmoothedMinus_crossing_bound hε g hy hM₀ hM₁ hη hηD)
      (hq y hy) (norm_nonneg _) hC
  refine hi.trans_eq ?_
  rw [Real.volume_real_Ioo,sub_zero,max_eq_left hε.le]
  dsimp only [C]
  field_simp

theorem norm_sub_le_epsilon_of_deriv_bound {q : ℝ → ℂ} (hq : ContDiff ℝ 1 q)
    {D ε : ℝ} (hD : 0 ≤ D) (_hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hBound : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv q t‖ ≤ D) :
    ∀ y ∈ Ioo (0 : ℝ) ε, ‖q y - q 0‖ ≤ D * ε := by
  have hd : ∀ x ∈ Icc (0 : ℝ) ε, HasDerivWithinAt q (deriv q x) (Icc (0 : ℝ) ε) x :=
    fun x _ => ((hq.differentiable (by norm_num)) x).hasDerivAt.hasDerivWithinAt
  have hb : ∀ x ∈ Ico (0 : ℝ) ε, ‖deriv q x‖ ≤ D :=
    fun x hx => hBound x ⟨hx.1,(le_of_lt hx.2).trans hε₁⟩
  intro y hy
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb y
    (show y ∈ Icc (0 : ℝ) ε from ⟨hy.1.le,hy.2.le⟩)
  exact hh.trans (by simpa only [sub_zero] using mul_le_mul_of_nonneg_left hy.2.le hD)

theorem atomicCrossingError_tendsto (g : HalfLineL2) (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) :
    Tendsto (fun ε : ℝ => atomicCrossingError ε g q) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨M₀,M₁,hM₀,hM₁,hη,hηD⟩ := atomicMollifier_bounds
  have hder : Continuous (fun t => ‖deriv q t‖) := (hq.continuous_deriv_one).norm
  obtain ⟨D,hDb⟩ := isCompact_Icc.bddAbove_image hder.continuousOn
  let D' := max D 0
  have hD : 0 ≤ D' := le_max_right _ _
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv q t‖ ≤ D' := fun t ht =>
    (hDb ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  let B : ℝ → ℝ := fun ε => ‖Complex.I / (Real.sqrt 2 : ℂ)‖ *
    ‖atomicNegativeL2 g‖ * D' * (M₁ + ε * M₀) * Real.sqrt ε
  have hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous B := by dsimp only [B]; fun_prop
    simpa only [B,zero_mul,add_zero,Real.sqrt_zero,mul_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hB
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds] with ε hε hε₁
  exact atomicCrossingError_bound hε g q hM₀ hM₁ hD hη hηD
    (norm_sub_le_epsilon_of_deriv_bound hq hD hε hε₁.le hb)

theorem pwCorrelation_contDiff {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    ContDiff ℝ ∞ (pwCorrelation a b) := by
  rw [pwCorrelation_eq_convolution]
  have hca : ContDiff ℝ ∞ (fun s : ℝ => a (-s)) := ha.1.comp contDiff_neg
  have hcb : LocallyIntegrable (fun s : ℝ => conj (b s)) volume :=
    hb.1.continuous.star.locallyIntegrable
  exact (ha.2.1.comp_homeomorph (Homeomorph.neg ℝ)).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ) (n := ⊤) hca hcb

theorem pwCorrelation_hasCompactSupport {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    HasCompactSupport (pwCorrelation a b) := by
  rw [pwCorrelation_eq_convolution]
  exact (ha.2.1.comp_homeomorph (Homeomorph.neg ℝ)).convolution
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (hb.2.1.comp_left (g := conj) (map_zero _))

theorem atomicCrossingError_pwCorrelation_tendsto {ℓ : ℝ} (g : HalfLineL2)
    {a b : ℝ → ℂ} (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    Tendsto (fun ε : ℝ => atomicCrossingError ε g (pwCorrelation a b))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  atomicCrossingError_tendsto g _ ((pwCorrelation_contDiff ha hb).of_le (by simp))

/-- The one-sided scaled support shrinks to zero in the native small-set filter. -/
theorem scaledAtomicMollifier_support_tendsto :
    Tendsto (fun ε : ℝ => Function.support (scaledAtomicMollifier ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro s hs
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hs
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hδ).filter_mono
    nhdsWithin_le_nhds] with ε hε hεδ
  intro t ht
  apply hsub
  have hh := scaledAtomicMollifier_tsupport hε (subset_tsupport _ ht)
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh.1] using hh.2.trans hεδ

def atomicMollifiedValue (ε : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, scaledAtomicMollifier ε r • F r

/-- This is native approximate-identity convergence, applied to the actual one-sided mollifier. -/
theorem atomicMollifiedValue_tendsto (F : ℝ → ℂ) (hF : Continuous F) :
    Tendsto (fun ε : ℝ => atomicMollifiedValue ε F) (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hcg : Tendsto (fun p : ℝ × ℝ => F (-p.2))
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ))) (𝓝 (F 0)) := by
    simpa only [neg_zero,Function.comp_def] using
      ((hF.comp continuous_neg).tendsto 0).comp tendsto_snd
  have hh := convolution_tendsto_right (μ := (volume : Measure ℝ))
    (φ := fun ε : ℝ => scaledAtomicMollifier ε) (g := fun _ r : ℝ => F (-r))
    (k := fun _ : ℝ => (0 : ℝ))
    (show ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ x, 0 ≤ scaledAtomicMollifier ε x from
      hpos.mono fun ε hε x => scaledAtomicMollifier_nonneg hε x)
    (show ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (∫ x : ℝ, scaledAtomicMollifier ε x) = 1 from
      hpos.mono fun ε hε => scaledAtomicMollifier_integral hε)
    scaledAtomicMollifier_support_tendsto
    (Eventually.of_forall fun _ => (hF.comp continuous_neg).aestronglyMeasurable)
    hcg tendsto_const_nhds
  simpa only [atomicMollifiedValue,convolution_def,ContinuousLinearMap.lsmul_apply,
    zero_sub,neg_neg] using! hh

/-- A literal function version of the already proved native L¹/L²/L² absolute Fubini estimate. -/
theorem integrable_rawL1L2_pairing (k f q : ℝ → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 volume) (hq : MemLp q 2 volume) :
    Integrable (fun p : ℝ × ℝ => k p.1 * (f p.2 * q (p.2+p.1))) (volume.prod volume) := by
  let F : LineL2 := hf.toLp f
  let B : LineL2 := hq.star.toLp (fun t => conj (q t))
  have hFa : F =ᵐ[volume] f := hf.coeFn_toLp
  have hBa : B =ᵐ[volume] fun t => conj (q t) := hq.star.coeFn_toLp
  have hFp := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := volume)).ae hFa
  have hBp := (quasiMeasurePreserving_add_swap (volume : Measure ℝ) volume).ae hBa
  apply (integrable_lineBochner_pairing k hk F B).congr
  filter_upwards [hFp,hBp] with p hF hB
  simp only [hF,hB,Complex.conj_conj]

/-- The exact raw convolution pairing, with every change of order justified in L¹. -/
theorem integral_rawConvolution_pairing (k f q : ℝ → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 volume) (hq : MemLp q 2 volume) :
    (∫ y : ℝ, (∫ t : ℝ, f t * k (y-t)) * q y) =
      ∫ t : ℝ, f t * ∫ r : ℝ, k r * q (t+r) := by
  have hI := integrable_rawL1L2_pairing k f q hk hf hq
  have hP := (measurePreserving_sub_prod (volume : Measure ℝ) volume).integrable_comp_of_integrable hI
  have hJ : Integrable (fun p : ℝ × ℝ => k (p.1-p.2) * (f p.2 * q p.1))
      (volume.prod volume) := by
    apply hP.congr
    exact Eventually.of_forall fun p => by
      simp only [Function.comp_def,add_sub_cancel]
  calc
    _ = ∫ y : ℝ, ∫ t : ℝ, k (y-t) * (f t * q y) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (∫ t : ℝ, f t * k (y-t)) * q y = ∫ t : ℝ, k (y-t) * (f t * q y)
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Eventually.of_forall fun t => by ring
    _ = ∫ t : ℝ, ∫ y : ℝ, k (y-t) * (f t * q y) := integral_integral_swap hJ
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        calc
          _ = ∫ r : ℝ, k r * (f t * q (t+r)) := by
            have he := integral_add_right_eq_self (μ := (volume : Measure ℝ))
              (fun y : ℝ => k (y-t) * (f t * q y)) t
            calc
              _ = ∫ r : ℝ, k (r+t-t) * (f t * q (r+t)) := he.symm
              _ = _ := by
                congr 1
                funext r
                rw [add_sub_cancel_right,add_comm r t]
          _ = _ := by
            change (∫ r : ℝ, k r * (f t * q (t+r))) = f t * (∫ r : ℝ, k r * q (t+r))
            rw [← integral_const_mul]
            apply integral_congr_ae
            exact Eventually.of_forall fun r => by ring

theorem integral_rawL1L2_pairing_swap (k f q : ℝ → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 volume) (hq : MemLp q 2 volume) :
    (∫ t : ℝ, f t * ∫ r : ℝ, k r * q (t+r)) =
      ∫ r : ℝ, k r * ∫ t : ℝ, f t * q (t+r) := by
  calc
    _ = ∫ t : ℝ, ∫ r : ℝ, k r * (f t * q (t+r)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change f t * (∫ r : ℝ, k r * q (t+r)) = ∫ r : ℝ, k r * (f t * q (t+r))
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun r => by ring
    _ = ∫ r : ℝ, ∫ t : ℝ, k r * (f t * q (t+r)) :=
      (integral_integral_swap (integrable_rawL1L2_pairing k f q hk hf hq)).symm
    _ = _ := by simp only [integral_const_mul]

theorem hasDerivAt_complexScaledAtomicMollifier (ε r : ℝ) :
    HasDerivAt (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ))
      (scaledAtomicMollifierDeriv ε r : ℂ) r := by
  have hd := (hasDerivAt_const (x := r) Complex.ofRealCLM).clm_apply
    (hasDerivAt_scaledAtomicMollifier ε r)
  simpa using! hd

/-- Actual compact-support integration by parts, with the derivative and shift signs explicit. -/
theorem atomicMollifier_derivative_pairing {ε : ℝ} (hε : 0 < ε)
    (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) (t : ℝ) :
    (∫ r : ℝ, (scaledAtomicMollifierDeriv ε r : ℂ) * q (t+r)) =
      -(∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * deriv q (t+r)) := by
  have hη : Continuous (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ)) :=
    Complex.continuous_ofReal.comp (scaledAtomicMollifier_contDiff ε).continuous
  have hηD : Continuous (fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ)) :=
    Complex.continuous_ofReal.comp (scaledAtomicMollifierDeriv_contDiff ε).continuous
  have hsη : HasCompactSupport (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ)) :=
    (scaledAtomicMollifier_hasCompactSupport hε).comp_left (g := fun r : ℝ => (r : ℂ)) (by rfl)
  have hsηD : HasCompactSupport (fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ)) :=
    (scaledAtomicMollifierDeriv_hasCompactSupport hε).comp_left (g := fun r : ℝ => (r : ℂ)) (by rfl)
  have hqC : Continuous (fun r : ℝ => q (t+r)) :=
    hq.continuous.comp (continuous_const.add continuous_id)
  have hqD : Continuous (fun r : ℝ => deriv q (t+r)) :=
    hq.continuous_deriv_one.comp (continuous_const.add continuous_id)
  have hqd (r : ℝ) : HasDerivAt (fun r : ℝ => q (t+r)) (deriv q (t+r)) r := by
    have hd := (((hq.differentiable (by norm_num)) (t+r)).hasDerivAt).scomp r
      ((hasDerivAt_id r).const_add t)
    simpa only [Function.comp_def,one_smul] using! hd
  have hx := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun r : ℝ => q (t+r)) (u' := fun r : ℝ => deriv q (t+r))
    (v := fun r : ℝ => (scaledAtomicMollifier ε r : ℂ))
    (v' := fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ))
    (fun r _ => hqd r) (fun r _ => hasDerivAt_complexScaledAtomicMollifier ε r)
    ((hqC.mul hηD).integrable_of_hasCompactSupport hsηD.mul_left)
    ((hqD.mul hη).integrable_of_hasCompactSupport hsη.mul_left)
    ((hqC.mul hη).integrable_of_hasCompactSupport hsη.mul_left)
  simpa only [mul_comm] using! hx

/-- The derivative convolution acts on a test by the literal distribution derivative, for either
sign of the zeroth-order term. This is an equality of ordinary integrals. -/
theorem atomicMollifier_full_pairing {ε : ℝ} (hε : 0 < ε)
    (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) (σ : ℂ) (t : ℝ) :
    (∫ r : ℝ, ((scaledAtomicMollifierDeriv ε r : ℂ) +
      σ * (scaledAtomicMollifier ε r : ℂ)) * q (t+r)) =
    ∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * (-deriv q (t+r) + σ * q (t+r)) := by
  have hη : Continuous (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ)) :=
    Complex.continuous_ofReal.comp (scaledAtomicMollifier_contDiff ε).continuous
  have hηD : Continuous (fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ)) :=
    Complex.continuous_ofReal.comp (scaledAtomicMollifierDeriv_contDiff ε).continuous
  have hsη : HasCompactSupport (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ)) :=
    (scaledAtomicMollifier_hasCompactSupport hε).comp_left (g := fun r : ℝ => (r : ℂ)) (by rfl)
  have hsηD : HasCompactSupport (fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ)) :=
    (scaledAtomicMollifierDeriv_hasCompactSupport hε).comp_left (g := fun r : ℝ => (r : ℂ)) (by rfl)
  have hqC : Continuous (fun r : ℝ => q (t+r)) :=
    hq.continuous.comp (continuous_const.add continuous_id)
  have hqD : Continuous (fun r : ℝ => deriv q (t+r)) :=
    hq.continuous_deriv_one.comp (continuous_const.add continuous_id)
  have hi₁ : Integrable (fun r : ℝ => (scaledAtomicMollifierDeriv ε r : ℂ) * q (t+r)) :=
    (hηD.mul hqC).integrable_of_hasCompactSupport hsηD.mul_right
  have hi₀ : Integrable (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ) * q (t+r)) :=
    (hη.mul hqC).integrable_of_hasCompactSupport hsη.mul_right
  have hiD : Integrable (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ) * deriv q (t+r)) :=
    (hη.mul hqD).integrable_of_hasCompactSupport hsη.mul_right
  calc
    _ = (∫ r : ℝ, (scaledAtomicMollifierDeriv ε r : ℂ) * q (t+r)) +
        σ * ∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * q (t+r) := by
      rw [← integral_const_mul,← integral_add hi₁ (hi₀.const_mul σ)]
      congr 1
      funext r
      ring
    _ = -(∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * deriv q (t+r)) +
        σ * ∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * q (t+r) := by
      rw [atomicMollifier_derivative_pairing hε q hq t]
    _ = _ := by
      rw [← integral_neg,← integral_const_mul]
      have hadd := integral_add hiD.neg (hi₀.const_mul σ)
      simp only [Pi.neg_apply] at hadd
      rw [← hadd]
      congr 1
      funext r
      ring

/-- Raw smoothed kernel action equals mollification of its proved derivative action.
The sign σ=1 gives the analytic part and σ=−1 the coanalytic part. -/
theorem integral_atomicSmoothed_raw {ε : ℝ} (hε : 0 < ε)
    (f q : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) (σ : ℂ) :
    (∫ y : ℝ, ((Complex.I / (Real.sqrt 2 : ℂ)) *
      ∫ t : ℝ, f t * ((scaledAtomicMollifierDeriv ε (y-t) : ℂ) +
        σ * (scaledAtomicMollifier ε (y-t) : ℂ))) * q y) =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        atomicMollifiedValue ε (fun r => ∫ t : ℝ, f t *
          (-deriv q (t+r) + σ * q (t+r))) := by
  let k : ℝ → ℂ := fun r => (scaledAtomicMollifierDeriv ε r : ℂ) +
    σ * (scaledAtomicMollifier ε r : ℂ)
  let P : ℝ → ℂ := fun t => -deriv q t + σ * q t
  have hk : Integrable k := by
    exact ((Complex.ofRealCLM.integrable_comp (scaledAtomicMollifierDeriv_integrable hε)).add
      ((Complex.ofRealCLM.integrable_comp (scaledAtomicMollifier_integrable hε)).const_mul σ))
  have hqLp : MemLp q 2 volume := hq.continuous.memLp_of_hasCompactSupport hsq
  have hPC : Continuous P := hq.continuous_deriv_one.neg.add (continuous_const.mul hq.continuous)
  have hPS : HasCompactSupport P := hsq.deriv.neg.add hsq.mul_left
  have hPLp : MemLp P 2 volume := hPC.memLp_of_hasCompactSupport hPS
  have hη : Integrable (fun r : ℝ => (scaledAtomicMollifier ε r : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (scaledAtomicMollifier_integrable hε)
  calc
    _ = (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ y : ℝ, (∫ t : ℝ, f t * k (y-t)) * q y := by
      rw [← integral_const_mul]
      congr 1
      funext y
      dsimp only [k]
      ring
    _ = (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t : ℝ, f t * ∫ r : ℝ, k r * q (t+r) := by
      rw [integral_rawConvolution_pairing k f q hk hf hqLp]
    _ = (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t : ℝ, f t * ∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * P (t+r) := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change f t * (∫ r : ℝ, ((scaledAtomicMollifierDeriv ε r : ℂ) +
          σ * (scaledAtomicMollifier ε r : ℂ)) * q (t+r)) = _
        rw [atomicMollifier_full_pairing hε q hq σ t]
    _ = (Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ r : ℝ, (scaledAtomicMollifier ε r : ℂ) * ∫ t : ℝ, f t * P (t+r) := by
      rw [integral_rawL1L2_pairing_swap _ f P hη hf hPLp]
    _ = _ := by simp only [atomicMollifiedValue,Complex.real_smul,P]

theorem continuous_rawL2_shift_pairing (f q : ℝ → ℂ)
    (hf : MemLp f 2 volume) (hq : MemLp q 2 volume) :
    Continuous (fun r : ℝ => ∫ t : ℝ, f t * q (t+r)) := by
  let F : LineL2 := hf.toLp f
  let B : LineL2 := hq.star.toLp (fun t => conj (q t))
  have hFa : F =ᵐ[volume] f := hf.coeFn_toLp
  have hBa : B =ᵐ[volume] fun t => conj (q t) := hq.star.coeFn_toLp
  have he (r : ℝ) : inner ℂ B (lineTranslate r F) = ∫ t : ℝ, f t * q (t+r) := by
    rw [inner_lineTranslate_integral]
    apply integral_congr_ae
    have hB := (measurePreserving_add_right (volume : Measure ℝ) r).quasiMeasurePreserving.ae hBa
    filter_upwards [hFa,hB] with t hF hBt
    simp only [hF,hBt,Complex.conj_conj]
  have hc : Continuous (fun r : ℝ => inner ℂ B (lineTranslate r F)) :=
    continuous_const.inner (continuous_lineTranslate F)
  simpa only [he] using hc

theorem integral_atomicSmoothed_raw_tendsto
    (f q : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) (σ : ℂ) :
    Tendsto (fun ε : ℝ => ∫ y : ℝ, ((Complex.I / (Real.sqrt 2 : ℂ)) *
      ∫ t : ℝ, f t * ((scaledAtomicMollifierDeriv ε (y-t) : ℂ) +
        σ * (scaledAtomicMollifier ε (y-t) : ℂ))) * q y)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t : ℝ, f t * (-deriv q t + σ * q t))) := by
  let P : ℝ → ℂ := fun t => -deriv q t + σ * q t
  have hPC : Continuous P := hq.continuous_deriv_one.neg.add (continuous_const.mul hq.continuous)
  have hPS : HasCompactSupport P := hsq.deriv.neg.add hsq.mul_left
  have hPLp : MemLp P 2 volume := hPC.memLp_of_hasCompactSupport hPS
  have hh := (tendsto_const_nhds (x := Complex.I / (Real.sqrt 2 : ℂ))).mul (atomicMollifiedValue_tendsto
    (fun r : ℝ => ∫ t : ℝ, f t * P (t+r)) (continuous_rawL2_shift_pairing f P hf hPLp))
  have he : (fun ε : ℝ => (Complex.I / (Real.sqrt 2 : ℂ)) *
      atomicMollifiedValue ε (fun r => ∫ t : ℝ, f t * P (t+r))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => ∫ y : ℝ, ((Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t : ℝ, f t * ((scaledAtomicMollifierDeriv ε (y-t) : ℂ) +
          σ * (scaledAtomicMollifier ε (y-t) : ℂ))) * q y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_atomicSmoothed_raw hε f q hf hq hsq σ).symm
  simpa only [P,add_zero] using! hh.congr' he

theorem integral_atomicPositiveInput_mul (g : HalfLineL2) (q : ℝ → ℂ) :
    (∫ t : ℝ, atomicPositiveInput g t * q t) = ∫ t in Ioi (0 : ℝ), g t * q t := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [atomicPositiveInput,indicator_of_mem ht]
  · simp only [atomicPositiveInput,indicator_of_notMem ht,zero_mul]

theorem integral_atomicNegativeInput_mul (g : HalfLineL2) (q : ℝ → ℂ) :
    (∫ t : ℝ, atomicNegativeInput g t * q t) =
      ∫ t in Iio (0 : ℝ), conj (g (-t)) * q t := by
  rw [← integral_indicator measurableSet_Iio]
  congr 1
  funext t
  by_cases ht : t ∈ Iio (0 : ℝ)
  · simp only [atomicNegativeInput,indicator_of_mem ht]
  · simp only [atomicNegativeInput,indicator_of_notMem ht,zero_mul]

theorem integral_atomicSmoothedPlus_pairing {ε : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) :
    (∫ y : ℝ, atomicSmoothedPlus ε g y * q y) =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        atomicMollifiedValue ε (fun r => ∫ t in Ioi (0 : ℝ), g t *
          (-deriv q (t+r) + q (t+r))) := by
  simpa only [one_mul,atomicSmoothedPlus,integral_atomicPositiveInput_mul] using!
    integral_atomicSmoothed_raw hε (atomicPositiveInput g) q
      (memLp_atomicPositiveInput g) hq hsq 1

theorem integral_atomicSmoothedMinus_pairing {ε : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) :
    (∫ y : ℝ, atomicSmoothedMinus ε g y * q y) =
      (Complex.I / (Real.sqrt 2 : ℂ)) *
        atomicMollifiedValue ε (fun r => ∫ t in Iio (0 : ℝ), conj (g (-t)) *
          (-deriv q (t+r) - q (t+r))) := by
  simpa only [neg_one_mul,← sub_eq_add_neg,atomicSmoothedMinus,integral_atomicNegativeInput_mul] using!
    integral_atomicSmoothed_raw hε (atomicNegativeInput g) q
      (memLp_atomicNegativeInput g) hq hsq (-1)

theorem integral_atomicSmoothedPlus_eq_Ioi {ε : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) :
    (∫ y : ℝ, atomicSmoothedPlus ε g y * q y) =
      ∫ y in Ioi (0 : ℝ), atomicSmoothedPlus ε g y * q y := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext y
  by_cases hy : y ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hy]
  · have hy' : y ≤ 0 := le_of_not_gt hy
    simp only [indicator_of_notMem hy,atomicSmoothedPlus_eq_zero hε g hy',zero_mul]

theorem atomicSmoothedPlus_test_tendsto (g : HalfLineL2) (q : ℝ → ℂ)
    (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) :
    Tendsto (fun ε : ℝ => ∫ y in Ioi (0 : ℝ), atomicSmoothedPlus ε g y * q y)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Complex.I / (Real.sqrt 2 : ℂ)) *
        ∫ t in Ioi (0 : ℝ), g t * (-deriv q t + q t))) := by
  have hh := integral_atomicSmoothed_raw_tendsto
    (atomicPositiveInput g) q (memLp_atomicPositiveInput g) hq hsq 1
  have he : (fun ε : ℝ => ∫ y : ℝ, atomicSmoothedPlus ε g y * q y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => ∫ y in Ioi (0 : ℝ), atomicSmoothedPlus ε g y * q y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_atomicSmoothedPlus_eq_Ioi hε g q
  simp only [one_mul] at hh
  change Tendsto (fun ε : ℝ => ∫ y : ℝ, atomicSmoothedPlus ε g y * q y)
    (𝓝[>] (0 : ℝ)) (𝓝 ((Complex.I / (Real.sqrt 2 : ℂ)) *
      ∫ t : ℝ, atomicPositiveInput g t * (-deriv q t + q t))) at hh
  simpa only [integral_atomicPositiveInput_mul] using! hh.congr' he

theorem integral_atomicSmoothedMinus_eq_crossing {ε : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) :
    (∫ y in Ioi (0 : ℝ), atomicSmoothedMinus ε g y * q y) =
      ∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε g y * q y := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioo]
  congr 1
  funext y
  by_cases hy : 0 < y
  · have hyI : y ∈ Ioi (0 : ℝ) := by simpa only [Set.mem_Ioi] using! hy
    rw [indicator_of_mem hyI]
    by_cases hyε : y < ε
    · rw [indicator_of_mem (show y ∈ Ioo (0 : ℝ) ε from ⟨hy,hyε⟩)]
    · have hn : y ∉ Ioo (0 : ℝ) ε := fun h => hyε h.2
      rw [indicator_of_notMem hn,atomicSmoothedMinus_eq_zero hε g (le_of_not_gt hyε),zero_mul]
  · have hnI : y ∉ Ioi (0 : ℝ) := by simpa only [Set.mem_Ioi] using! hy
    have hn : y ∉ Ioo (0 : ℝ) ε := fun h => hy h.1
    rw [indicator_of_notMem hnI,indicator_of_notMem hn]

theorem atomicCrossingScalar_error_split {ε : ℝ} (hε : 0 < ε)
    (g : HalfLineL2) (q : ℝ → ℂ) (hq : Continuous q) :
    (∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε g y * q y) =
      atomicCrossingScalar ε g * q 0 + atomicCrossingError ε g q := by
  have hErr : IntegrableOn (fun y => atomicSmoothedMinus ε g y * (q y-q 0)) (Ioo (0 : ℝ) ε) :=
    (((atomicSmoothedMinus_contDiff hε g).continuous.mul (hq.sub continuous_const)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hConst := (integrableOn_atomicSmoothedMinus hε g).mul_const (q 0)
  calc
    _ = ∫ y in Ioo (0 : ℝ) ε,
        atomicSmoothedMinus ε g y * (q y-q 0) + atomicSmoothedMinus ε g y * q 0 := by
      congr 1
      funext y
      ring
    _ = (∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε g y * (q y-q 0)) +
        ∫ y in Ioo (0 : ℝ) ε, atomicSmoothedMinus ε g y * q 0 :=
      integral_add hErr hConst
    _ = _ := by rw [integral_mul_const]; change atomicCrossingError ε g q +
      atomicCrossingScalar ε g * q 0 = _; ring

theorem integral_atomicSmoothedKernel_positive_split {ε : ℝ} (hε : 0 < ε)
    (g h : HalfLineL2) (q : ℝ → ℂ) (hq : Continuous q) (hsq : HasCompactSupport q) :
    (∫ y in Ioi (0 : ℝ), atomicSmoothedKernel ε g h y * q y) =
      (∫ y : ℝ, atomicSmoothedPlus ε g y * q y) +
        atomicCrossingScalar ε h * q 0 + atomicCrossingError ε h q := by
  have hPlus : Integrable (fun y => atomicSmoothedPlus ε g y * q y) :=
    ((atomicSmoothedPlus_contDiff hε g).continuous.mul hq).integrable_of_hasCompactSupport hsq.mul_left
  have hMinus : Integrable (fun y => atomicSmoothedMinus ε h y * q y) :=
    ((atomicSmoothedMinus_contDiff hε h).continuous.mul hq).integrable_of_hasCompactSupport hsq.mul_left
  simp_rw [atomicSmoothedKernel,add_mul]
  rw [integral_add hPlus.integrableOn hMinus.integrableOn,
    ← integral_atomicSmoothedPlus_eq_Ioi hε g q,integral_atomicSmoothedMinus_eq_crossing hε h q,
    atomicCrossingScalar_error_split hε h q hq]
  ring

/-- The actual scalar-sequence asymptotic behind the single-atom splitting reduction. -/
theorem atomicSmoothedKernel_positive_test_tendsto (g h : HalfLineL2) (q : ℝ → ℂ)
    (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) :
    Tendsto (fun ε : ℝ =>
      (∫ y in Ioi (0 : ℝ), atomicSmoothedKernel ε g h y * q y) -
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          (∫ t in Ioi (0 : ℝ), g t * (-deriv q t+q t)) -
        atomicCrossingScalar ε h * q 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hPlus := (atomicSmoothedPlus_test_tendsto g q hq hsq).sub
    (tendsto_const_nhds (x := (Complex.I / (Real.sqrt 2 : ℂ)) *
      ∫ t in Ioi (0 : ℝ), g t * (-deriv q t+q t)))
  have hh := hPlus.add (atomicCrossingError_tendsto h q hq)
  have he : (fun ε : ℝ =>
      (∫ y in Ioi (0 : ℝ), atomicSmoothedPlus ε g y * q y) -
        (Complex.I / (Real.sqrt 2 : ℂ)) * (∫ t in Ioi (0 : ℝ), g t * (-deriv q t+q t)) +
        atomicCrossingError ε h q) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ =>
      (∫ y in Ioi (0 : ℝ), atomicSmoothedKernel ε g h y * q y) -
        (Complex.I / (Real.sqrt 2 : ℂ)) * (∫ t in Ioi (0 : ℝ), g t * (-deriv q t+q t)) -
        atomicCrossingScalar ε h * q 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_atomicSmoothedKernel_positive_split hε g h q hq.continuous hsq,
      integral_atomicSmoothedPlus_eq_Ioi hε g q]
    ring
  simpa only [sub_self,zero_add] using! hh.congr' he

theorem pwCorrelation_zero_eq_inner {ℓ : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b) :
    pwCorrelation a b 0 = inner ℂ (smoothIntervalL2 ℓ b hb) (smoothIntervalL2 ℓ a ha) := by
  rw [pwCorrelation]
  simp only [add_zero]
  calc
    _ = ∫ t in Ioo (0 : ℝ) ℓ, a t * conj (b t) := by
      rw [← integral_indicator measurableSet_Ioo]
      congr 1
      funext t
      by_cases ht : t ∈ Ioo (0 : ℝ) ℓ
      · simp only [indicator_of_mem ht]
      · have ha0 : a t = 0 := by
          by_contra hn
          exact ht (ha.2.2 (subset_tsupport _ hn))
        simp only [indicator_of_notMem ht,ha0,zero_mul]
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [smoothIntervalL2_ae ℓ a ha,smoothIntervalL2_ae ℓ b hb] with t hA hB
      rw [hA,hB,RCLike.inner_apply]

/-- Source equations (6)--(7) for the genuine model coordinates, all Hardy symbols and all smooth
core tests. The scalar depends only on the coanalytic symbol, never on the test pair. -/
theorem exists_singleAtom_scalarAsymptotic (u : BoundaryLInf) (hu : IsInner u)
    (ζ : Boundary) (hζ : SingleAtom u ζ) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u,
      ∃ H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy,
        Dense (pwSmoothModelCore U : Set (Model u)) ∧
        (∀ f ∈ pwSmoothModelCore U, IsBounded f.val) ∧
        ∀ (φ ψ : Hardy) (a b : ℝ → ℂ) (ha : IntervalSmoothCompact ℓ a)
          (hb : IntervalSmoothCompact ℓ b),
          Tendsto (fun ε : ℝ =>
            (∫ y in Ioi (0 : ℝ), atomicSmoothedKernel ε (H.symm φ) (H.symm ψ) y *
              pwCorrelation a b y) -
            coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val -
            atomicCrossingScalar ε (H.symm ψ) *
              inner ℂ (U (smoothIntervalL2 ℓ b hb)) (U (smoothIntervalL2 ℓ a ha)))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨ℓ,hℓ,U,H,hd,hbd,hA,_hC⟩ := exists_singleAtomPWBothForms u hu ζ hζ
  refine ⟨ℓ,hℓ,U,H,hd,hbd,?_⟩
  intro φ ψ a b ha hb
  have hh := atomicSmoothedKernel_positive_test_tendsto (H.symm φ) (H.symm ψ)
    (pwCorrelation a b) ((pwCorrelation_contDiff ha hb).of_le (by simp))
    (pwCorrelation_hasCompactSupport ha hb)
  rw [← hA φ a b ha hb,pwCorrelation_zero_eq_inner ha hb,← U.inner_map_map] at hh
  exact hh

end TTO.Paper.Proved
