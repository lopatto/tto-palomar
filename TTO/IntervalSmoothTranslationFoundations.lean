/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.IntervalAverageFoundations
public import TTO.AtomicCausalKernelFoundations

/-! Actual compact smooth shifted interval tests and translation-average form identities. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology ContDiff
namespace TTO.Paper.Proved
open Reduction

def intervalTestShift (r : ℝ) (a : ℝ → ℂ) (t : ℝ) : ℂ := a (t-r)

theorem intervalSmoothCompact_mono {d ℓ : ℝ} (hd : d ≤ ℓ) {a : ℝ → ℂ}
    (ha : IntervalSmoothCompact d a) : IntervalSmoothCompact ℓ a :=
  ⟨ha.1,ha.2.1,fun _ ht => ⟨(ha.2.2 ht).1,(ha.2.2 ht).2.trans_le hd⟩⟩

theorem intervalTestShift_smooth {d ℓ r : ℝ} (hr : 0 ≤ r) (hEnd : d+r ≤ ℓ)
    {a : ℝ → ℂ} (ha : IntervalSmoothCompact d a) :
    IntervalSmoothCompact ℓ (intervalTestShift r a) := by
  refine ⟨ha.1.comp (contDiff_id.sub contDiff_const),?_,?_⟩
  · change HasCompactSupport (a ∘ Homeomorph.subRight r)
    exact ha.2.1.comp_homeomorph (Homeomorph.subRight r)
  · have hs := tsupport_comp_subset_preimage a (f := fun t : ℝ => t-r) (continuous_id.sub continuous_const)
    intro t ht
    have htr : t-r∈tsupport a := hs ht
    have hd := ha.2.2 htr
    exact ⟨by linarith [hd.1],by linarith [hd.2]⟩

/-- Translation of an actual smooth test class agrees with the literal translated test.
Both smooth-test premises concern explicit whole-line functions, not arbitrary L² representatives. -/
theorem intervalTranslate_smoothIntervalL2_of_eq (ℓ r : ℝ) (a b : ℝ → ℂ)
    (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b)
    (hab : ∀ t, b t=a (t-r)) :
    intervalTranslate ℓ r (smoothIntervalL2 ℓ a ha)=smoothIntervalL2 ℓ b hb := by
  apply Lp.ext
  have hA := (ae_restrict_iff' measurableSet_Ioo).mp (smoothIntervalL2_ae ℓ a ha)
  have hShift := (measurePreserving_sub_const_line r).quasiMeasurePreserving.ae hA
  filter_upwards [intervalTranslate_ae ℓ r (smoothIntervalL2 ℓ a ha),
    smoothIntervalL2_ae ℓ b hb,ae_restrict_of_ae hShift] with t hTr hB hA
  rw [hTr,hB,hab]
  by_cases ht : t-r∈Ioo (0 : ℝ) ℓ
  · rw [indicator_of_mem ht,hA ht]
  · rw [indicator_of_notMem ht,ha.eq_zero_of_not_mem ht]

/-- The whole-line correlation has the literal translated argument, with no sign ambiguity. -/
theorem pwCorrelation_testShifts (a b : ℝ → ℂ) (r s t : ℝ) :
    pwCorrelation (intervalTestShift r a) (intervalTestShift s b) t=
      pwCorrelation a b (t+r-s) := by
  rw [pwCorrelation,pwCorrelation]
  calc
    _ = ∫ x : ℝ, (fun y => a y * conj (b (y+(t+r-s)))) (x-r) := by
      congr 1
      funext x
      dsimp only [intervalTestShift]
      rw [show x+t-s=(x-r)+(t+r-s) by ring]
    _ = _ := by
      simpa only using! (integral_sub_right_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ => a y * conj (b (y+(t+r-s)))) r)

theorem pwCorrelation_regularization_shift (a b : ℝ → ℂ) (ε r t : ℝ) :
    pwCorrelation (intervalTestShift ε a) (intervalTestShift (ε-r) b) t=
      pwCorrelation a b (t+r) := by
  rw [pwCorrelation_testShifts]
  congr 1
  ring

theorem intervalTestShift_short_smooth {ℓ ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : IntervalSmoothCompact (ℓ-ε) a) :
    IntervalSmoothCompact ℓ (intervalTestShift ε a) :=
  intervalTestShift_smooth hε (by linarith) ha

theorem intervalTestShift_short_difference_smooth {ℓ ε r : ℝ} (hr : 0 ≤ r) (hrε : r ≤ ε)
    {a : ℝ → ℂ} (ha : IntervalSmoothCompact (ℓ-ε) a) :
    IntervalSmoothCompact ℓ (intervalTestShift (ε-r) a) :=
  intervalTestShift_smooth (by linarith) (by linarith) ha

theorem intervalTranslate_short_test {ℓ ε : ℝ} (hε : 0 ≤ ε)
    (a : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε) a) :
    intervalTranslate ℓ ε (smoothIntervalL2 ℓ a (intervalSmoothCompact_mono (by linarith) ha))=
      smoothIntervalL2 ℓ (intervalTestShift ε a) (intervalTestShift_short_smooth hε ha) := by
  apply intervalTranslate_smoothIntervalL2_of_eq
  intro t
  rfl

theorem intervalTranslate_adjoint_short_test {ℓ ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrε : r ≤ ε)
    (b : ℝ → ℂ) (hb : IntervalSmoothCompact (ℓ-ε) b) :
    (intervalTranslate ℓ r).adjoint
      (intervalTranslate ℓ ε (smoothIntervalL2 ℓ b (intervalSmoothCompact_mono (by linarith) hb)))=
      smoothIntervalL2 ℓ (intervalTestShift (ε-r) b)
        (intervalTestShift_short_difference_smooth hr hrε hb) := by
  rw [adjoint_intervalTranslate,intervalTranslate_short_test hε b hb]
  apply intervalTranslate_smoothIntervalL2_of_eq
  intro t
  dsimp only [intervalTestShift]
  congr 1
  ring

theorem inner_intervalTranslatedSandwich (ℓ ε r : ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ) (a b : IntervalL2 ℓ) :
    inner ℂ b (intervalTranslatedSandwich ℓ ε A r a)=
      inner ℂ ((intervalTranslate ℓ r).adjoint (intervalTranslate ℓ ε b))
        (A (intervalTranslate ℓ ε a)) := by
  unfold intervalTranslatedSandwich
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (ContinuousLinearMap.adjoint_inner_left (intervalTranslate ℓ r)
    (A (intervalTranslate ℓ ε a)) (intervalTranslate ℓ ε b)).symm

/-- The exact two shifted test vectors in manuscript Step 1. -/
theorem intervalTranslatedSandwich_short_test_pair {ℓ ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrε : r ≤ ε)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ)
    (a b : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε) a) (hb : IntervalSmoothCompact (ℓ-ε) b) :
    inner ℂ (smoothIntervalL2 ℓ b (intervalSmoothCompact_mono (by linarith) hb))
      (intervalTranslatedSandwich ℓ ε A r
        (smoothIntervalL2 ℓ a (intervalSmoothCompact_mono (by linarith) ha)))=
      inner ℂ (smoothIntervalL2 ℓ (intervalTestShift (ε-r) b)
        (intervalTestShift_short_difference_smooth hr hrε hb))
        (A (smoothIntervalL2 ℓ (intervalTestShift ε a) (intervalTestShift_short_smooth hε ha))) := by
  rw [inner_intervalTranslatedSandwich,intervalTranslate_short_test hε a ha,
    intervalTranslate_adjoint_short_test hε hr hrε b hb]

theorem deriv_pwCorrelation_regularization_shift {d : ℝ} {a b : ℝ → ℂ}
    (ha : IntervalSmoothCompact d a) (hb : IntervalSmoothCompact d b) (ε r t : ℝ) :
    deriv (pwCorrelation (intervalTestShift ε a) (intervalTestShift (ε-r) b)) t=
      deriv (pwCorrelation a b) (t+r) := by
  have he : pwCorrelation (intervalTestShift ε a) (intervalTestShift (ε-r) b)=
      fun x => pwCorrelation a b (x+r) :=
    funext (pwCorrelation_regularization_shift a b ε r)
  rw [he]
  have hd : HasDerivAt (pwCorrelation a b) (deriv (pwCorrelation a b) (t+r)) (t+r) :=
    ((pwCorrelation_contDiff ha hb).differentiable (by simp) (t+r)).hasDerivAt
  have hx : HasDerivAt (fun x : ℝ => x+r) 1 t := (hasDerivAt_id t).add_const r
  simpa only [one_smul,Function.comp_def] using! (hd.scomp t hx).deriv

section UnitaryPairing
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_unitaryConjugate_symm (U : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) (a b : E) :
    inner ℂ b (unitaryConjugate U.symm A a)=inner ℂ (U b) (A (U a)) := by
  change inner ℂ b (U.symm (A (U a)))=inner ℂ (U b) (A (U a))
  simpa only [U.apply_symm_apply] using (U.inner_map_map b (U.symm (A (U a)))).symm

end UnitaryPairing

/-- The translated operator really has the transported original core form on the shifted tests. -/
theorem intervalTranslatedSandwich_short_coreForm {ℓ ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrε : r ≤ ε) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u)
    (hBound : ∀ f∈pwSmoothModelCore U, IsBounded f.val)
    (σ : BoundaryL2) (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A)
    (a b : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε) a) (hb : IntervalSmoothCompact (ℓ-ε) b) :
    inner ℂ (smoothIntervalL2 ℓ b (intervalSmoothCompact_mono (by linarith) hb))
      (intervalTranslatedSandwich ℓ ε (unitaryConjugate U.symm A) r
        (smoothIntervalL2 ℓ a (intervalSmoothCompact_mono (by linarith) ha)))=
      coreForm σ
        (U (smoothIntervalL2 ℓ (intervalTestShift ε a) (intervalTestShift_short_smooth hε ha))).val
        (U (smoothIntervalL2 ℓ (intervalTestShift (ε-r) b)
          (intervalTestShift_short_difference_smooth hr hrε hb))).val := by
  rw [intervalTranslatedSandwich_short_test_pair hε hr hrε (unitaryConjugate U.symm A) a b ha hb,
    inner_unitaryConjugate_symm]
  apply hA
  · exact hBound _ ((mem_pwSmoothModelCore_iff ℓ u U _).mpr
      ⟨intervalTestShift ε a,intervalTestShift_short_smooth hε ha,rfl⟩)
  · exact hBound _ ((mem_pwSmoothModelCore_iff ℓ u U _).mpr
      ⟨intervalTestShift (ε-r) b,intervalTestShift_short_difference_smooth hr hrε hb,rfl⟩)

/-- The literal positive and negative causal derivative actions on a translated test. -/
def atomicShiftedAction (g h : HalfLineL2) (q : ℝ → ℂ) (r : ℝ) : ℂ :=
  (Complex.I / (Real.sqrt 2 : ℂ)) *
      (∫ t in Ioi (0 : ℝ), g t * (-deriv q (t+r)+q (t+r))) +
    (Complex.I / (Real.sqrt 2 : ℂ)) *
      (∫ t in Iio (0 : ℝ), conj (h (-t)) * (-deriv q (t+r)-q (t+r)))

/-- Applying the actual PW core formulas to the shifted smooth tests gives the original causal action. -/
theorem intervalTranslatedSandwich_causal_pair {ℓ ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrε : r ≤ ε) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy)
    (hBound : ∀ f∈pwSmoothModelCore U, IsBounded f.val)
    (hAnalytic : ∀ (φ : Hardy) (a b : ℝ → ℂ)
      (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val=
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          ∫ t in Ioi (0 : ℝ), (H.symm φ) t *
            (-deriv (pwCorrelation a b) t+pwCorrelation a b t))
    (hCoanalytic : ∀ (ψ : Hardy) (a b : ℝ → ℂ)
      (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm (star ψ.val) (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val=
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          ∫ t in Iio (0 : ℝ), conj ((H.symm ψ) (-t)) *
            (-deriv (pwCorrelation a b) t-pwCorrelation a b t))
    (φ ψ : Hardy) (A : Model u →L[ℂ] Model u)
    (hA : RepresentsTTO u (splitSymbol φ.val ψ.val) A)
    (a b : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε) a) (hb : IntervalSmoothCompact (ℓ-ε) b) :
    inner ℂ (smoothIntervalL2 ℓ b (intervalSmoothCompact_mono (by linarith) hb))
      (intervalTranslatedSandwich ℓ ε (unitaryConjugate U.symm A) r
        (smoothIntervalL2 ℓ a (intervalSmoothCompact_mono (by linarith) ha)))=
      atomicShiftedAction (H.symm φ) (H.symm ψ) (pwCorrelation a b) r := by
  rw [intervalTranslatedSandwich_short_coreForm hε hr hrε u U hBound
    (splitSymbol φ.val ψ.val) A hA a b ha hb]
  have hba : IsBounded
      (U (smoothIntervalL2 ℓ (intervalTestShift ε a) (intervalTestShift_short_smooth hε ha))).val :=
    hBound _ ((mem_pwSmoothModelCore_iff ℓ u U _).mpr
      ⟨intervalTestShift ε a,intervalTestShift_short_smooth hε ha,rfl⟩)
  rw [splitSymbol,coreForm_add φ.val (star ψ.val) _ _ hba,
    hAnalytic φ (intervalTestShift ε a) (intervalTestShift (ε-r) b)
      (intervalTestShift_short_smooth hε ha) (intervalTestShift_short_difference_smooth hr hrε hb),
    hCoanalytic ψ (intervalTestShift ε a) (intervalTestShift (ε-r) b)
      (intervalTestShift_short_smooth hε ha) (intervalTestShift_short_difference_smooth hr hrε hb)]
  simp_rw [deriv_pwCorrelation_regularization_shift ha hb,pwCorrelation_regularization_shift]
  rfl

section OperatorIntegralPairing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A single explicit real continuous linear functional evaluates the actual operator integral. -/
theorem inner_integral_real_smul_operators (T : ℝ → H →L[ℂ] H) (k : ℝ → ℝ)
    (hInt : Integrable (fun r : ℝ => k r • T r)) (a b : H) :
    inner ℂ b ((∫ r : ℝ, k r • T r) a)=∫ r : ℝ, k r • inner ℂ b (T r a) := by
  let L : (H →L[ℂ] H) →L[ℝ] ℂ :=
    ((innerSL ℂ b) ∘L ContinuousLinearMap.apply ℂ H a).restrictScalars ℝ
  change L (∫ r : ℝ, k r • T r)=_
  rw [← L.integral_comp_comm hInt]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => L.map_smul (k r) (T r)

end OperatorIntegralPairing

theorem inner_intervalTranslatedAverage (ℓ ε : ℝ) (k : ℝ → ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ)
    (hInt : Integrable (fun r : ℝ => k r • intervalTranslatedSandwich ℓ ε A r))
    (a b : IntervalL2 ℓ) :
    inner ℂ b (intervalTranslatedAverage ℓ ε k A a)=
      ∫ r : ℝ, k r • inner ℂ b (intervalTranslatedSandwich ℓ ε A r a) := by
  unfold intervalTranslatedAverage
  exact inner_integral_real_smul_operators (intervalTranslatedSandwich ℓ ε A) k hInt a b

theorem intervalTranslatedAverage_pair_of_shifted_pair (ℓ ε : ℝ) (k : ℝ → ℝ)
    (A : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ)
    (hInt : Integrable (fun r : ℝ => k r • intervalTranslatedSandwich ℓ ε A r))
    (hk : Function.support k ⊆ Icc (0 : ℝ) ε) (a b : IntervalL2 ℓ) (F : ℝ → ℂ)
    (hPair : ∀ r∈Icc (0 : ℝ) ε, inner ℂ b (intervalTranslatedSandwich ℓ ε A r a)=F r) :
    inner ℂ b (intervalTranslatedAverage ℓ ε k A a)=∫ r : ℝ, k r • F r := by
  rw [inner_intervalTranslatedAverage ℓ ε k A hInt a b]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    dsimp only
    by_cases hr : k r=0
    · rw [hr,zero_smul,zero_smul]
    · rw [hPair r (hk hr)]

theorem continuous_rawDerivativeShiftAction (f q : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) (σ : ℂ) :
    Continuous (fun r : ℝ => ∫ t : ℝ, f t * (-deriv q (t+r)+σ*q (t+r))) := by
  let P : ℝ → ℂ := fun t => -deriv q t+σ*q t
  have hPC : Continuous P := hq.continuous_deriv_one.neg.add (continuous_const.mul hq.continuous)
  have hPS : HasCompactSupport P := hsq.deriv.neg.add hsq.mul_left
  exact continuous_rawL2_shift_pairing f P hf (hPC.memLp_of_hasCompactSupport hPS)

theorem integrable_atomicMollifiedValue {ε : ℝ} (hε : 0 < ε) (F : ℝ → ℂ) (hF : Continuous F) :
    Integrable (fun r : ℝ => scaledAtomicMollifier ε r • F r) :=
  ((scaledAtomicMollifier_contDiff ε).continuous.smul hF).integrable_of_hasCompactSupport
    (scaledAtomicMollifier_hasCompactSupport hε).smul_right

/-- The proved analytic and coanalytic smoothed pairings combine into the actual full kernel pairing. -/
theorem atomicShiftedAction_mollified_eq_kernel {ε : ℝ} (hε : 0 < ε)
    (g h : HalfLineL2) (q : ℝ → ℂ) (hq : ContDiff ℝ 1 q) (hsq : HasCompactSupport q) :
    atomicMollifiedValue ε (atomicShiftedAction g h q)=
      ∫ y : ℝ, atomicSmoothedKernel ε g h y * q y := by
  let c : ℂ := Complex.I/(Real.sqrt 2 : ℂ)
  let Fpos : ℝ → ℂ := fun r => ∫ t in Ioi (0 : ℝ), g t * (-deriv q (t+r)+q (t+r))
  let Fneg : ℝ → ℂ := fun r => ∫ t in Iio (0 : ℝ), conj (h (-t)) * (-deriv q (t+r)-q (t+r))
  have hFpos : Continuous Fpos := by
    simpa only [one_mul,integral_atomicPositiveInput_mul] using
      continuous_rawDerivativeShiftAction (atomicPositiveInput g) q (memLp_atomicPositiveInput g) hq hsq 1
  have hFneg : Continuous Fneg := by
    simpa only [neg_one_mul,← sub_eq_add_neg,integral_atomicNegativeInput_mul] using
      continuous_rawDerivativeShiftAction (atomicNegativeInput h) q (memLp_atomicNegativeInput h) hq hsq (-1)
  have hIpos := integrable_atomicMollifiedValue hε Fpos hFpos
  have hIneg := integrable_atomicMollifiedValue hε Fneg hFneg
  have hPlus : Integrable (fun y => atomicSmoothedPlus ε g y*q y) :=
    ((atomicSmoothedPlus_contDiff hε g).continuous.mul hq.continuous).integrable_of_hasCompactSupport hsq.mul_left
  have hMinus : Integrable (fun y => atomicSmoothedMinus ε h y*q y) :=
    ((atomicSmoothedMinus_contDiff hε h).continuous.mul hq.continuous).integrable_of_hasCompactSupport hsq.mul_left
  have hKernel : (∫ y : ℝ, atomicSmoothedKernel ε g h y*q y)=
      (∫ y : ℝ, atomicSmoothedPlus ε g y*q y)+(∫ y : ℝ, atomicSmoothedMinus ε h y*q y) := by
    simp_rw [atomicSmoothedKernel,add_mul]
    exact integral_add hPlus hMinus
  rw [hKernel,integral_atomicSmoothedPlus_pairing hε g q hq hsq,
    integral_atomicSmoothedMinus_pairing hε h q hq hsq]
  change (∫ r : ℝ, scaledAtomicMollifier ε r • (c*Fpos r+c*Fneg r))=
    c*(∫ r : ℝ, scaledAtomicMollifier ε r • Fpos r)+
      c*(∫ r : ℝ, scaledAtomicMollifier ε r • Fneg r)
  have he (r : ℝ) : scaledAtomicMollifier ε r • (c*Fpos r+c*Fneg r)=
      c*(scaledAtomicMollifier ε r • Fpos r)+c*(scaledAtomicMollifier ε r • Fneg r) := by
    simp only [Complex.real_smul]
    ring
  simp_rw [he]
  rw [integral_add (hIpos.const_mul c) (hIneg.const_mul c),integral_const_mul,integral_const_mul]

/-- The actual translated average has the literal smoothed causal kernel on every short smooth test pair. -/
theorem intervalTranslatedAverage_kernel_pair {ℓ ε : ℝ}
    (hε : 0 < ε) (u : BoundaryLInf)
    (U : IntervalL2 ℓ ≃ₗᵢ[ℂ] Model u) (H : HalfLineL2 ≃ₗᵢ[ℂ] Hardy)
    (hBound : ∀ f∈pwSmoothModelCore U, IsBounded f.val)
    (hAnalytic : ∀ (φ : Hardy) (a b : ℝ → ℂ)
      (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm φ.val (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val=
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          ∫ t in Ioi (0 : ℝ), (H.symm φ) t *
            (-deriv (pwCorrelation a b) t+pwCorrelation a b t))
    (hCoanalytic : ∀ (ψ : Hardy) (a b : ℝ → ℂ)
      (ha : IntervalSmoothCompact ℓ a) (hb : IntervalSmoothCompact ℓ b),
      coreForm (star ψ.val) (U (smoothIntervalL2 ℓ a ha)).val (U (smoothIntervalL2 ℓ b hb)).val=
        (Complex.I / (Real.sqrt 2 : ℂ)) *
          ∫ t in Iio (0 : ℝ), conj ((H.symm ψ) (-t)) *
            (-deriv (pwCorrelation a b) t-pwCorrelation a b t))
    (p : ℝ) (hp : 1 ≤ p) (φ ψ : Hardy) (A : Model u →L[ℂ] Model u)
    (hA : RepresentsTTO u (splitSymbol φ.val ψ.val) A) (hSp : Schatten p A)
    (a b : ℝ → ℂ) (ha : IntervalSmoothCompact (ℓ-ε) a) (hb : IntervalSmoothCompact (ℓ-ε) b) :
    inner ℂ (smoothIntervalL2 ℓ b (intervalSmoothCompact_mono (by linarith [hε.le]) hb))
      (intervalTranslatedAverage ℓ ε (scaledAtomicMollifier ε) (unitaryConjugate U.symm A)
        (smoothIntervalL2 ℓ a (intervalSmoothCompact_mono (by linarith [hε.le]) ha)))=
      ∫ y : ℝ, atomicSmoothedKernel ε (H.symm φ) (H.symm ψ) y * pwCorrelation a b y := by

  have hTransport : Schatten p (unitaryConjugate U.symm A) :=
    (unitaryIdealLaws.schatten U.symm A p).mpr hSp
  have hAverage := schatten_intervalTranslatedAverage ℓ ε p hp (unitaryConjugate U.symm A) hTransport
    (scaledAtomicMollifier ε) (scaledAtomicMollifier_contDiff ε).continuous
    (scaledAtomicMollifier_integrable hε) (scaledAtomicMollifier_nonneg hε)
    (scaledAtomicMollifier_integral hε)
  have hSupport : Function.support (scaledAtomicMollifier ε) ⊆ Icc (0 : ℝ) ε := by
    intro r hr
    exact Ioo_subset_Icc_self (scaledAtomicMollifier_tsupport hε (subset_tsupport _ hr))
  calc
    _ = atomicMollifiedValue ε (atomicShiftedAction (H.symm φ) (H.symm ψ) (pwCorrelation a b)) := by
      unfold atomicMollifiedValue
      apply intervalTranslatedAverage_pair_of_shifted_pair ℓ ε (scaledAtomicMollifier ε)
        (unitaryConjugate U.symm A) hAverage.1 hSupport
      intro r hr
      exact intervalTranslatedSandwich_causal_pair hε.le hr.1 hr.2 u U H hBound hAnalytic hCoanalytic
        φ ψ A hA a b ha hb
    _ = _ := atomicShiftedAction_mollified_eq_kernel hε (H.symm φ) (H.symm ψ) (pwCorrelation a b)
      ((pwCorrelation_contDiff ha hb).of_le (by simp)) (pwCorrelation_hasCompactSupport ha hb)

end TTO.Paper.Proved
