/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Function.L2Space

/-! A genuine scalar second-moment bound from geometric dyadic distribution tails. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
namespace TTO.Paper.Proved

theorem hasSum_dyadic_square_moment :
    HasSum (fun n : ℕ => ((n : ℝ)+1)^2*(1/2 : ℝ)^n) 12 := by
  have h : ‖(1/2 : ℝ)‖<1 := by norm_num
  have h0 : HasSum (fun n : ℕ => (1/2 : ℝ)^n) 2 := by
    convert hasSum_geometric_of_norm_lt_one h using 1; norm_num
  have h1 : HasSum (fun n : ℕ => (n : ℝ)*(1/2 : ℝ)^n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one h using 1; norm_num
  have h2 : HasSum (fun n : ℕ => (n : ℝ)^2*(1/2 : ℝ)^n) 6 := by
    convert hasSum_sq_mul_geometric_of_norm_lt_one h using 1; norm_num
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  · funext n
    ring
  · norm_num

/-- Each finite positive real lies in one successive threshold interval. -/
theorem exists_dyadic_tail_threshold (x M : ℝ) (hx : 0<x) (hM : 0<M) :
    ∃ n : ℕ, 4*(n : ℝ)*M<x ∧ x≤4*((n : ℝ)+1)*M := by
  have hex : ∃ n : ℕ,x≤4*((n : ℝ)+1)*M := by
    obtain ⟨n,hn⟩ := exists_nat_gt (x/(4*M))
    refine ⟨n,?_⟩
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ)<4*M)).mp hn
    nlinarith
  let n := Nat.find hex
  refine ⟨n,?_,Nat.find_spec hex⟩
  by_cases hn : n=0
  · simpa only [hn,Nat.cast_zero,mul_zero,zero_mul] using hx
  · by_contra h
    have hPrev : x≤4*((((n-1 : ℕ) : ℝ))+1)*M := by
      have hCast : ((n-1 : ℕ) : ℝ)+1=(n : ℝ) := by
        rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
        ring
      rw [hCast]
      exact le_of_not_gt h
    have hMin : n≤n-1 := Nat.find_min' hex hPrev
    omega



/-- A pointwise square is dominated by the sum of the literal strict tail indicators. -/
theorem dyadic_tail_square_majorant (x M : ℝ) (hM : 0<M) :
    ENNReal.ofReal x^2≤∑' n : ℕ,
      {y : ℝ | 4*(n : ℝ)*M<y}.indicator
        (fun _ => ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)) x := by
  by_cases hx : 0<x
  · obtain ⟨n,hLower,hUpper⟩ := exists_dyadic_tail_threshold x M hx hM
    have hSq : x^2≤16*M^2*((n : ℝ)+1)^2 := by
      nlinarith [sq_nonneg (x-4*((n : ℝ)+1)*M)]
    calc
      _ = ENNReal.ofReal (x^2) := (ENNReal.ofReal_pow hx.le 2).symm
      _ ≤ ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2) := ENNReal.ofReal_le_ofReal hSq
      _ = {y : ℝ | 4*(n : ℝ)*M<y}.indicator
          (fun _ => ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)) x := by
        rw [indicator_of_mem (show x∈{y : ℝ | 4*(n : ℝ)*M<y} from hLower)]
      _ ≤ _ := by
        simpa only using! ENNReal.le_tsum (f := fun k : ℕ =>
          {y : ℝ | 4*(k : ℝ)*M<y}.indicator
            (fun _ => ENNReal.ofReal (16*M^2*((k : ℝ)+1)^2)) x) n
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hx),zero_pow (by norm_num : 2≠0)]
    exact zero_le



theorem tsum_dyadic_square_coeff (M : ℝ) :
    (∑' n : ℕ,ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)*(2⁻¹ : ℝ≥0∞)^n)=
      ENNReal.ofReal (192*M^2) := by
  have h : HasSum (fun n : ℕ => 16*M^2*((n : ℝ)+1)^2*(1/2 : ℝ)^n)
      (192*M^2) := by
    convert hasSum_dyadic_square_moment.mul_left (16*M^2) using 1
    · funext n
      ring
    · ring
  have hEq (n : ℕ) : ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)*(2⁻¹ : ℝ≥0∞)^n=
      ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2*(1/2 : ℝ)^n) := by
    rw [ENNReal.ofReal_mul (p := 16*M^2*((n : ℝ)+1)^2) (by positivity),
      ENNReal.ofReal_pow (by norm_num : 0≤(1/2 : ℝ))]
    rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ)<2),ENNReal.ofReal_ofNat]
  simp_rw [hEq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable,h.tsum_eq]

/-- A geometric strict-tail estimate gives an actual second-moment bound.
The result also permits infinite Q; finite Q makes its right side finite. -/
theorem lintegral_sq_le_of_dyadic_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Q : Set α) (hQ : MeasurableSet Q) (F : α → ℝ)
    (hF : AEMeasurable F μ) (M : ℝ) (hM : 0<M)
    (hTail : ∀ n : ℕ,μ (Q∩{x | 4*(n : ℝ)*M<F x})≤(2⁻¹ : ℝ≥0∞)^n*μ Q) :
    (∫⁻ x in Q,ENNReal.ofReal (F x)^2 ∂μ)≤ENNReal.ofReal (192*M^2)*μ Q := by
  let T : ℕ → α → ℝ≥0∞ := fun n =>
    {x | 4*(n : ℝ)*M<F x}.indicator (fun _ => ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2))
  have hSet (n : ℕ) : NullMeasurableSet {x | 4*(n : ℝ)*M<F x} (μ.restrict Q) :=
    nullMeasurableSet_lt aemeasurable_const hF.restrict
  have hAE (n : ℕ) : AEMeasurable (T n) (μ.restrict Q) :=
    aemeasurable_const.indicator₀ (hSet n)
  have hMajor (x : α) : ENNReal.ofReal (F x)^2≤∑' n : ℕ,T n x := by
    simpa only [T,Set.indicator_apply,Set.mem_ofPred_eq] using! dyadic_tail_square_majorant (F x) M hM
  calc
    _ ≤ ∫⁻ x in Q,∑' n : ℕ,T n x ∂μ := lintegral_mono hMajor
    _ = ∑' n : ℕ,∫⁻ x in Q,T n x ∂μ := lintegral_tsum hAE
    _ = ∑' n : ℕ,ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)*
        μ (Q∩{x | 4*(n : ℝ)*M<F x}) := by
      congr 1
      funext n
      rw [show T n={x | 4*(n : ℝ)*M<F x}.indicator
        (fun _ => ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)) from rfl,
        lintegral_indicator_const₀ (hSet n),Measure.restrict_apply' hQ,inter_comm]
    _ ≤ ∑' n : ℕ,ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)*
        ((2⁻¹ : ℝ≥0∞)^n*μ Q) := by
      apply ENNReal.tsum_le_tsum
      intro n
      gcongr
      exact hTail n
    _ = (∑' n : ℕ,ENNReal.ofReal (16*M^2*((n : ℝ)+1)^2)*(2⁻¹ : ℝ≥0∞)^n)*μ Q := by
      simp_rw [← mul_assoc]
      exact ENNReal.tsum_mul_right
    _ = _ := by rw [tsum_dyadic_square_coeff]



/-- On a finite set, the genuine moment estimate gives ordinary real square integrability. -/
theorem integrable_sq_le_of_dyadic_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Q : Set α) (hQ : MeasurableSet Q) (hQfin : μ Q<∞)
    (F : α → ℝ) (hF : AEMeasurable F μ)
    (hNonneg : ∀ᵐ x ∂μ.restrict Q,0≤F x) (M : ℝ) (hM : 0<M)
    (hTail : ∀ n : ℕ,μ (Q∩{x | 4*(n : ℝ)*M<F x})≤(2⁻¹ : ℝ≥0∞)^n*μ Q) :
    IntegrableOn (fun x => F x^2) Q μ ∧
      (∫ x in Q,F x^2 ∂μ)≤192*M^2*μ.real Q := by
  have hMoment := lintegral_sq_le_of_dyadic_tail μ Q hQ F hF M hM hTail
  have hEq : (fun x => ENNReal.ofReal (F x^2))=ᵐ[μ.restrict Q]
      fun x => ENNReal.ofReal (F x)^2 := by
    filter_upwards [hNonneg] with x hx
    exact ENNReal.ofReal_pow hx 2
  have hMoment' : (∫⁻ x in Q,ENNReal.ofReal (F x^2) ∂μ)≤
      ENNReal.ofReal (192*M^2)*μ Q :=
    (lintegral_congr_ae hEq).trans_le hMoment
  have hRhs : ENNReal.ofReal (192*M^2)*μ Q<∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin
  have hFM : AEStronglyMeasurable (fun x => F x^2) (μ.restrict Q) :=
    (hF.restrict.pow_const 2).aestronglyMeasurable
  have hNN : ∀ᵐ x ∂μ.restrict Q,0≤F x^2 := Eventually.of_forall fun x => sq_nonneg (F x)
  have hInt : IntegrableOn (fun x => F x^2) Q μ :=
    ⟨hFM,(hasFiniteIntegral_iff_ofReal hNN).mpr (hMoment'.trans_lt hRhs)⟩
  refine ⟨hInt,?_⟩
  calc
    _ = (∫⁻ x in Q,ENNReal.ofReal (F x^2) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae hNN hFM
    _ ≤ (ENNReal.ofReal (192*M^2)*μ Q).toReal := ENNReal.toReal_mono hRhs.ne hMoment'
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]; rfl

/-- The same tail condition supplies actual native L² membership on the finite set. -/
theorem memLp_two_of_dyadic_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (Q : Set α) (hQ : MeasurableSet Q) (hQfin : μ Q<∞)
    (F : α → ℝ) (hF : AEMeasurable F μ)
    (hNonneg : ∀ᵐ x ∂μ.restrict Q,0≤F x) (M : ℝ) (hM : 0<M)
    (hTail : ∀ n : ℕ,μ (Q∩{x | 4*(n : ℝ)*M<F x})≤(2⁻¹ : ℝ≥0∞)^n*μ Q) :
    MemLp F 2 (μ.restrict Q) := by
  apply (memLp_two_iff_integrable_sq hF.restrict.aestronglyMeasurable).mpr
  exact (integrable_sq_le_of_dyadic_tail μ Q hQ hQfin F hF hNonneg M hM hTail).1

end TTO.Paper.Proved
