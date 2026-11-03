/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.DyadicCubeFoundations
public import TTO.DyadicTailL2Foundations
public import TTO.ArcL2OscillationFoundations

/-! Homogeneous square-oscillation bounds toward the literal all-arc BMO estimate. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open TTO.DyadicAnalysis

theorem dyadic_square_oscillation_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : (Fin 1 → ℝ) → E)
    (hF : StronglyMeasurable f) (q₀ : ℤ × (Fin 1 → ℤ)) (M : ℝ≥0)
    (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hMO : ∀ q : ℤ × (Fin 1 → ℤ),dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 →
      ⨍⁻ x in dyadicCube q.1 q.2,‖f x-⨍ y in dyadicCube q.1 q.2,f y ∂volume‖ₑ ∂volume≤M) :
    IntegrableOn (fun x => ‖f x-⨍ y in dyadicCube q₀.1 q₀.2,f y ∂volume‖^2)
      (dyadicCube q₀.1 q₀.2) ∧
    (∫ x in dyadicCube q₀.1 q₀.2,‖f x-⨍ y in dyadicCube q₀.1 q₀.2,f y ∂volume‖^2)≤
      192*(M : ℝ)^2*volume.real (dyadicCube q₀.1 q₀.2) := by
  let Q := dyadicCube q₀.1 q₀.2
  let c := ⨍ y in Q,f y ∂volume
  rcases eq_or_ne M 0 with rfl | hM
  · have hZero := hMO q₀ le_rfl
    have hm : AEMeasurable (fun x => ‖f x-c‖ₑ) (volume.restrict Q) :=
      (hF.sub stronglyMeasurable_const).aestronglyMeasurable.enorm
    rw [ENNReal.coe_zero,nonpos_iff_eq_zero,setLAverage_eq,ENNReal.div_eq_zero_iff,
      or_iff_left (volume_dyadicCube_ne_top _ _),lintegral_eq_zero_iff' hm] at hZero
    have hSq : (fun x => ‖f x-c‖^2)=ᵐ[volume.restrict Q] fun _ => (0 : ℝ) := by
      filter_upwards [hZero] with x hx
      have hsub : f x-c=0 := enorm_eq_zero.mp hx
      simp [hsub]
    refine ⟨(integrable_congr hSq).mpr (integrable_zero _ _ _),?_⟩
    change (∫ x in Q,‖f x-c‖^2)≤_
    rw [integral_congr_ae hSq,integral_zero]
    simp
  have hPos : 0<(M : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hM)
  have hTail : ∀ n : ℕ,volume (Q∩{x | 4*(n : ℝ)*(M : ℝ)<‖f x-c‖})≤
      (2⁻¹ : ℝ≥0∞)^n*volume Q := by
    intro n
    have h := volume_lt_enorm_sub_setAverage_le_inv_two_pow hf hMO n
    have hCast : ENNReal.ofReal (4*(n : ℝ)*(M : ℝ))=(4 : ℝ≥0∞)*n*M := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast,ENNReal.ofReal_coe_nnreal]
    have hSet : Q∩{x | 4*(n : ℝ)*(M : ℝ)<‖f x-c‖}=
        {x∈Q | (4 : ℝ≥0∞)*n*M<‖f x-c‖ₑ} := by
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq]
      rw [← hCast,← ofReal_norm,ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
    rw [hSet]
    simpa only [Fintype.card_fin,show 2^(1+1)=(4 : ℝ≥0∞) by norm_num] using h
  exact integrable_sq_le_of_dyadic_tail volume Q (measurableSet_dyadicCube _ _)
    (volume_dyadicCube_ne_top _ _).lt_top (fun x => ‖f x-c‖)
    (hF.sub stronglyMeasurable_const).norm.aemeasurable
    (Eventually.of_forall fun x => norm_nonneg _) M hPos hTail


theorem arcMean_eq_real_setAverage (f : BoundaryL2) (a b : ℝ) (hab : a<b) :
    arcMean f a b=⨍ t in Ico a b,f (t : Boundary) := by
  rw [arcMean,setAverage_eq,measureReal_def,Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),integral_Ico_eq_integral_Ioc]
  simp only [Complex.real_smul,Complex.ofReal_inv]

theorem shifted_dyadic_setAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a : ℝ) (k : ℤ) (m : Fin 1 → ℤ) :
    (⨍ x in dyadicCube k m,f (a+x 0))=
      ⨍ t in Ico (a+(m 0 : ℝ)*2^k) (a+(m 0+1)*2^k),f t := by
  rw [setAverage_dyadicCube_fin_one (fun t => f (a+t)) k m]
  simp only [setAverage_eq,measureReal_def,Real.volume_Ico]
  rw [setIntegral_Ico_add_left]
  have hLen : (a+(m 0+1)*2^k)-(a+(m 0 : ℝ)*2^k)=
      ((m 0+1)*2^k)-(m 0 : ℝ)*2^k := by ring
  rw [hLen]

theorem ofReal_meanOscillation_eq_setLAverage (f : BoundaryL2) (a b : ℝ)
    (hab : a<b) (hLen : b-a≤1) :
    ENNReal.ofReal (meanOscillation f a b)=
      ⨍⁻ t in Ico a b,‖f (t : Boundary)-⨍ s in Ico a b,f (s : Boundary)‖ₑ ∂volume := by
  have hf : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ico a b) :=
    (integrableOn_congr_set_ae Ico_ae_eq_Ioc).mpr (boundaryL2_integrableOn_lift_Ioc f a b hLen)
  have hFin : volume (Ico a b)≠∞ := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hConst : IntegrableOn (fun _ : ℝ => arcMean f a b) (Ico a b) := integrableOn_const hFin
  have hNorm : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-arcMean f a b‖) (Ico a b) :=
    (hf.sub hConst).norm
  have hAvg : meanOscillation f a b=
      ⨍ t in Ico a b,‖f (t : Boundary)-arcMean f a b‖ := by
    rw [meanOscillation,setAverage_eq,measureReal_def,Real.volume_Ico,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),smul_eq_mul,integral_Ico_eq_integral_Ioc]
  rw [hAvg,ofReal_setAverage hNorm (Eventually.of_forall fun t => norm_nonneg _)]
  simp only [ofReal_norm,arcMean_eq_real_setAverage f a b hab,setLAverage_eq]

/-! The following real-inner-product mean-minimization proofs are adapted from
TauCetiProject/TauCeti commit d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad,
`TauCeti/MeasureTheory/Integral/Average.lean`, Apache-2.0.
Copyright (c) 2026 The Tau Ceti contributors; adapted by Patrick Lopatto. -/
section InnerProduct

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F] {s : Set X} {f : X → F}

/-- In a real inner product space, the square mean oscillation of `f` on a set `s` of finite
measure about a constant `c` splits orthogonally:
`∫_s ‖f - c‖² = ∫_s ‖f - f_s‖² + μ s ‖f_s - c‖²`. -/
theorem setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add (hs : μ s ≠ ⊤)
    (hf : IntegrableOn f s μ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - c‖ ^ 2 ∂μ =
      ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ + μ.real s * ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 := by
  set m := ⨍ y in s, f y ∂μ
  have hfm : Integrable (fun x ↦ f x - m) (μ.restrict s) := hf.sub (integrableOn_const hs)
  -- The cross term vanishes, since `∫_s (f - m) = 0`.
  have hcross : ∫ x in s, ⟪f x - m, m - c⟫_ℝ ∂μ = 0 := by
    simp_rw [real_inner_comm (m - c)]
    rw [integral_inner hfm, integral_sub hf (integrableOn_const hs), setIntegral_const,
      measure_smul_setAverage f hs, sub_self, inner_zero_right]
  have hint : Integrable (fun x ↦ ⟪f x - m, m - c⟫_ℝ) (μ.restrict s) := hfm.inner_const _
  -- Pointwise, `‖f - m‖² = ‖f - c‖² - 2 ⟪f - m, m - c⟫ - ‖m - c‖²`.
  have hpt : ∀ x, ‖f x - m‖ ^ 2 = ‖f x - c‖ ^ 2 - 2 * ⟪f x - m, m - c⟫_ℝ - ‖m - c‖ ^ 2 :=
    fun x ↦ by
      have := norm_add_sq_real (f x - m) (m - c)
      rw [sub_add_sub_cancel] at this
      linarith
  have h2 : Integrable (fun x ↦ ‖f x - c‖ ^ 2 - 2 * ⟪f x - m, m - c⟫_ℝ) (μ.restrict s) :=
    hfc.sub (hint.const_mul 2)
  simp_rw [hpt]
  rw [integral_sub h2 (integrableOn_const hs), integral_sub hfc (hint.const_mul 2),
    integral_const_mul, hcross, setIntegral_const, smul_eq_mul]
  ring

/-- In a real inner product space, the average of `f` over a set `s` of finite measure minimizes
the square mean oscillation: `∫_s ‖f - f_s‖² ≤ ∫_s ‖f - c‖²` for every constant `c`. -/
theorem setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq (hs : μ s ≠ ⊤)
    (hf : IntegrableOn f s μ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ ≤ ∫ x in s, ‖f x - c‖ ^ 2 ∂μ := by
  rw [setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add hs hf hfc]
  exact le_add_of_nonneg_right (by positivity)

end InnerProduct


theorem shifted_dyadic_setLAverage (f : ℝ → ℝ≥0∞) (a : ℝ) (k : ℤ) (m : Fin 1 → ℤ) :
    (⨍⁻ x in dyadicCube k m,f (a+x 0) ∂volume)=
      ⨍⁻ t in Ico (a+(m 0 : ℝ)*2^k) (a+(m 0+1)*2^k),f t ∂volume := by
  rw [setLAverage_dyadicCube_fin_one (fun t => f (a+t)) k m]
  simp only [setLAverage_eq,Real.volume_Ico]
  rw [setLIntegral_Ico_add_left]
  have hLen : (a+(m 0+1)*2^k)-(a+(m 0 : ℝ)*2^k)=
      ((m 0+1)*2^k)-(m 0 : ℝ)*2^k := by ring
  rw [hLen]

theorem dyadic_side_le_of_subset {j k : ℤ} {m n : Fin 1 → ℤ}
    (hSub : dyadicCube j m ⊆ dyadicCube k n) : (2 : ℝ)^j≤2^k := by
  have h := ENNReal.toReal_mono (volume_dyadicCube_ne_top k n) (measure_mono hSub)
  simpa only [volume_dyadicCube,Fintype.card_fin,pow_one,
    ENNReal.toReal_ofReal (by positivity : 0≤(2 : ℝ)^j),
    ENNReal.toReal_ofReal (by positivity : 0≤(2 : ℝ)^k)] using h

theorem shifted_dyadic_square_bound (f : BoundaryL2) (B : ℝ≥0)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a : ℝ) (k : ℤ) (hSide : (2 : ℝ)^k≤1) :
    (∫ t in Ico a (a+2^k),‖f (t : Boundary)-arcMean f a (a+2^k)‖^2)≤
      192*(B : ℝ)^2*2^k := by
  let L : ℝ := 2^k
  have hL : 0<L := zpow_pos two_pos k
  let Q := dyadicCube k (0 : Fin 1 → ℤ)
  let F : (Fin 1 → ℝ) → ℂ := fun x => f ((a+x 0 : ℝ) : Boundary)
  have hCont : Continuous (fun x : Fin 1 → ℝ => ((a+x 0 : ℝ) : Boundary)) := by fun_prop
  have hF : StronglyMeasurable F := (Lp.stronglyMeasurable f).comp_measurable hCont.measurable
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := (MeasurableEquiv.funUnique (Fin 1) ℝ).trans
    (MeasurableEquiv.addLeft a)
  have hp : MeasurePreserving e volume volume :=
    (measurePreserving_add_left volume a).comp (volume_preserving_funUnique (Fin 1) ℝ)
  have hQ : Q=e ⁻¹' Ico a (a+L) := by
    ext x
    change x∈dyadicCube k 0 ↔ x∈e ⁻¹' Ico a (a+L)
    rw [dyadicCube_fin_one]
    simp only [Pi.zero_apply,Int.cast_zero,zero_mul,zero_add,one_mul]
    change (0≤x 0 ∧ x 0<L) ↔ (a≤a+x 0 ∧ a+x 0<a+L)
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have hInt : IntegrableOn (fun t : ℝ => f (t : Boundary)) (Ico a (a+L)) :=
    (integrableOn_congr_set_ae Ico_ae_eq_Ioc).mpr
      (boundaryL2_integrableOn_lift_Ioc f a (a+L) (by linarith))
  have hFI : IntegrableOn F Q := by
    change Integrable ((fun t : ℝ => f (t : Boundary)) ∘ e) (volume.restrict Q)
    rw [hQ]
    exact ((hp.restrict_preimage_emb e.measurableEmbedding _).integrable_comp_emb
      e.measurableEmbedding).mpr hInt
  have hMean : (⨍ x in Q,F x)=arcMean f a (a+L) := by
    change (⨍ x in dyadicCube k 0,f ((a+x 0 : ℝ) : Boundary))=_
    rw [shifted_dyadic_setAverage (fun t : ℝ => f (t : Boundary)) a k 0]
    simpa only [Pi.zero_apply,Int.cast_zero,zero_mul,zero_add,add_zero,one_mul] using
      (arcMean_eq_real_setAverage f a (a+L) (by linarith)).symm
  have hDyadic : ∀ q : ℤ × (Fin 1 → ℤ),dyadicCube q.1 q.2 ⊆ Q →
      ⨍⁻ x in dyadicCube q.1 q.2,‖F x-⨍ y in dyadicCube q.1 q.2,F y‖ₑ ∂volume≤B := by
    intro q hq
    have hqL : (2 : ℝ)^q.1≤1 := (dyadic_side_le_of_subset hq).trans hSide
    let l : ℝ := a+(q.2 0 : ℝ)*2^q.1
    let r : ℝ := a+(q.2 0+1)*2^q.1
    have hDiff : r-l=(2 : ℝ)^q.1 := by dsimp [l,r]; ring
    have hab : l<r := by rw [← sub_pos,hDiff]; positivity
    have hLen : r-l≤1 := hDiff.trans_le hqL
    have hAvg : (⨍ y in dyadicCube q.1 q.2,F y)=arcMean f l r := by
      rw [shifted_dyadic_setAverage (fun t : ℝ => f (t : Boundary)) a q.1 q.2]
      exact (arcMean_eq_real_setAverage f l r hab).symm
    rw [hAvg]
    change (⨍⁻ x in dyadicCube q.1 q.2,
      (fun t : ℝ => ‖f (t : Boundary)-arcMean f l r‖ₑ) (a+x 0) ∂volume)≤B
    rw [shifted_dyadic_setLAverage (fun t : ℝ => ‖f (t : Boundary)-arcMean f l r‖ₑ) a q.1 q.2]
    change (⨍⁻ t in Ico l r,‖f (t : Boundary)-arcMean f l r‖ₑ ∂volume)≤B
    rw [arcMean_eq_real_setAverage f l r hab,
      ← ofReal_meanOscillation_eq_setLAverage f l r hab hLen]
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hMO l r hab hLen)
  have hD := (dyadic_square_oscillation_bound F hF (k,0) B hFI hDyadic).2
  change (∫ x in Q,‖F x-⨍ y in Q,F y‖^2)≤_ at hD
  rw [hMean] at hD
  change (∫ x in dyadicCube k 0,
    (fun t : ℝ => ‖f ((a+t : ℝ) : Boundary)-arcMean f a (a+L)‖^2) (x 0))≤_ at hD
  rw [setIntegral_dyadicCube_fin_one
    (fun t : ℝ => ‖f ((a+t : ℝ) : Boundary)-arcMean f a (a+L)‖^2) k 0] at hD
  simp only [Pi.zero_apply,Int.cast_zero,zero_mul,zero_add,one_mul] at hD
  rw [setIntegral_Ico_add_left a 0 L
    (fun t : ℝ => ‖f (t : Boundary)-arcMean f a (a+L)‖^2)] at hD
  simpa only [Pi.zero_apply,Int.cast_zero,zero_mul,zero_add,add_zero,measureReal_def,
    volume_dyadicCube,Fintype.card_fin,pow_one,
    ENNReal.toReal_ofReal (by positivity : 0≤(2 : ℝ)^k)] using hD


theorem arc_centered_square_integrable_Ico (f : BoundaryL2) (a b : ℝ)
    (hLen : b-a≤1) (c : ℂ) :
    IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c‖^2) (Ico a b) := by
  have hFin : volume (Ico a b)<∞ := by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict (Ico a b)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hFin⟩
  have hCont : Continuous (fun t : ℝ => (t : Boundary)) := by fun_prop
  have hMeas := (Lp.stronglyMeasurable f).comp_measurable hCont.measurable
  have hSq : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)‖^2) (Ico a b) :=
    (integrableOn_congr_set_ae Ico_ae_eq_Ioc).mpr (arc_integral_norm_sq_le f a b hLen).1
  have hL2 : MemLp (fun t : ℝ => f (t : Boundary)) 2 (volume.restrict (Ico a b)) :=
    (memLp_two_iff_integrable_sq_norm hMeas.aestronglyMeasurable).mpr hSq
  have hC : MemLp (fun _ : ℝ => c) 2 (volume.restrict (Ico a b)) := memLp_const c
  simpa only [IntegrableOn,Pi.sub_apply] using! (hL2.sub hC).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)

/-- A homogeneous square-mean estimate on EVERY literal real arc, including B=0. -/
theorem arc_square_oscillation_le_of_meanOscillation_bound (f : BoundaryL2)
    (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a b : ℝ) (hab : a<b) (hLen : b-a≤1) :
    (∫ t in Ioc a b,‖f (t : Boundary)-arcMean f a b‖^2)≤384*B^2*(b-a) := by
  obtain ⟨n,hLow,hHigh⟩ := exists_nat_pow_near_of_lt_one (sub_pos.mpr hab) hLen
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1)
  let k : ℤ := -(n : ℤ)
  have hPow : (2 : ℝ)^k=(1/2 : ℝ)^n := by simp [k,zpow_neg,one_div,inv_pow]
  have hSide : (2 : ℝ)^k≤1 := by rw [hPow]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hCover : b≤a+(2 : ℝ)^k := by rw [hPow]; linarith
  have hUpper : (2 : ℝ)^k≤2*(b-a) := by
    rw [hPow]
    rw [pow_succ] at hLow
    linarith
  have hBigLen : (a+(2 : ℝ)^k)-a≤1 := by linarith
  let c := arcMean f a (a+(2 : ℝ)^k)
  have hSub : Ico a b ⊆ Ico a (a+(2 : ℝ)^k) :=
    fun t ht => ⟨ht.1,ht.2.trans_le hCover⟩
  have hIntBig := arc_centered_square_integrable_Ico f a (a+(2 : ℝ)^k) hBigLen c
  have hIntSmall := (integrableOn_congr_set_ae Ico_ae_eq_Ioc).mpr
    (boundaryL2_integrableOn_lift_Ioc f a b hLen)
  have hFin : volume (Ico a b)≠∞ := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hCenter := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
    (f := fun t : ℝ => f (t : Boundary)) hFin hIntSmall (hIntBig.mono_set hSub)
  rw [← arcMean_eq_real_setAverage f a b hab] at hCenter
  have hMon : (∫ t in Ico a b,‖f (t : Boundary)-c‖^2)≤
      ∫ t in Ico a (a+(2 : ℝ)^k),‖f (t : Boundary)-c‖^2 :=
    setIntegral_mono_set hIntBig (Eventually.of_forall fun t => sq_nonneg _)
      (Eventually.of_forall fun t ht => hSub ht)
  rw [← integral_Ico_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Ico a b,‖f (t : Boundary)-c‖^2 := hCenter
    _ ≤ ∫ t in Ico a (a+(2 : ℝ)^k),‖f (t : Boundary)-c‖^2 := hMon
    _ ≤ 192*B^2*2^k := shifted_dyadic_square_bound f ⟨B,hB⟩ hMO a k hSide
    _ ≤ 192*B^2*(2*(b-a)) := mul_le_mul_of_nonneg_left hUpper (by positivity)
    _ = 384*B^2*(b-a) := by ring


theorem arcMean_unit_eq_fourierCoeff_zero (f : BoundaryL2) :
    arcMean f 0 1=fourierCoeff f 0 := by
  simp only [arcMean,sub_zero,Complex.ofReal_one,inv_one,one_mul,fourierCoeff,neg_zero,
    fourier_zero,one_smul]
  have h := AddCircle.integral_preimage 1 0 (fun t : Boundary => f t)
  have hm := congrArg (fun μ : Measure Boundary => ∫ t : Boundary,f t ∂μ)
    circleMeasure_eq_volume
  simp only [zero_add] at h
  exact h.trans hm.symm

theorem norm_sub_constant_sq_le_of_meanOscillation_bound (f : BoundaryL2)
    (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B) :
    ‖f-constL2 (fourierCoeff f 0)‖^2≤384*B^2 := by
  let c := fourierCoeff f 0
  have hArc := arc_square_oscillation_le_of_meanOscillation_bound f B hB hMO
    0 1 zero_lt_one (by norm_num)
  rw [arcMean_unit_eq_fourierCoeff_zero] at hArc
  have hPre := AddCircle.integral_preimage 1 0 (fun t : Boundary => ‖f t-c‖^2)
  have hμ := congrArg (fun μ : Measure Boundary => ∫ t : Boundary,‖f t-c‖^2 ∂μ)
    circleMeasure_eq_volume
  have hEqual : (∫ t : Boundary,‖(f-constL2 c) t‖^2 ∂circleMeasure)=
      ∫ t : Boundary,‖f t-c‖^2 ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f (constL2 c),(memLp_const c).coeFn_toLp] with t ht hc
    rw [ht]
    change ‖f t-(constL2 c) t‖^2=_
    change (constL2 c) t=c at hc
    rw [hc]
  rw [← boundaryL2_integral_norm_sq,hEqual,hμ]
  rw [← hPre]
  simpa only [zero_add,sub_zero,mul_one] using hArc

end TTO.Paper.Proved
