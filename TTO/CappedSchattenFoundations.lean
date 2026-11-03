/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SchattenNormFoundations
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Capped singular-value sums and actual finite-rank trace-norm budgets. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The literal finite sum of singular values capped at a real threshold. -/
def cappedSingularSum [FiniteDimensional ℂ E] (A : E →L[ℂ] F) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Module.finrank ℂ E),min (approximationNumber A i : ℝ) t

variable [FiniteDimensional ℂ E] [CompleteSpace F]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Every rank-k approximation gives a genuine trace-norm budget for the capped sum. -/
theorem cappedSingularSum_le_rank_budget (A R : E →L[ℂ] F) (t : ℝ) (ht : 0≤t)
    (k : ℕ) (hR : R.rank≤(k : Cardinal)) :
    cappedSingularSum A t≤(k : ℝ)*t+schattenNorm 1 (A-R) := by
  have hTrace : schattenNorm 1 (A-R)=
      ∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber (A-R) i : ℝ) := by
    simpa only [Real.rpow_one,one_div_one] using schattenNorm_finite_prefix (A-R) 1 (by norm_num)
  have hPrefix (n : ℕ) :
      (∑ i ∈ Finset.range n,min (approximationNumber A i : ℝ) t)≤(n : ℝ)*t := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n,t := Finset.sum_le_sum (fun i _hi => min_le_right _ _)
      _ = _ := by simp
  by_cases hk : Module.finrank ℂ E≤k
  · exact (hPrefix _).trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ht).trans
      (le_add_of_nonneg_right (schattenNorm_nonneg 1 (A-R))))
  · have hTail (i : ℕ) :
        min (approximationNumber A (k+i) : ℝ) t≤(approximationNumber (A-R) i : ℝ) := by
      apply (min_le_left _ _).trans
      have h := approximationNumber_add (A-R) R i k
      have hR0 : approximationNumber R k=0 := le_antisymm
        (by simpa only [sub_self,nnnorm_zero] using approximationNumber_le_nnnorm_sub R (n:=k) (R:=R) hR) bot_le
      rw [sub_add_cancel,hR0,add_zero] at h
      exact_mod_cast (show approximationNumber A (k+i)≤approximationNumber (A-R) i by
        simpa only [Nat.add_comm] using h)
    have hRem :
        (∑ i ∈ Finset.range (Module.finrank ℂ E-k),(approximationNumber (A-R) i : ℝ))≤
          schattenNorm 1 (A-R) := by
      rw [hTrace]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
        (fun i _hi _hnot => (approximationNumber (A-R) i).coe_nonneg)
    unfold cappedSingularSum
    rw [show Module.finrank ℂ E=k+(Module.finrank ℂ E-k) by omega,Finset.sum_range_add]
    exact add_le_add (hPrefix k) ((Finset.sum_le_sum (fun i _hi => hTail i)).trans hRem)

/-- The same cap sum in the actual Gram diagonal coordinates. -/
theorem cappedSingularSum_eq_gram (A : E →L[ℂ] F) (t : ℝ) :
    cappedSingularSum A t=∑ i ∈ Finset.range (Module.finrank ℂ E),min ‖finiteGramWeights A i‖ t := by
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i<Module.finrank ℂ E := Finset.mem_range.mp hi
  rw [show finiteGramWeights A i=(‖A (gramBasis A ⟨i,hin⟩)‖ : ℂ) by
    exact finiteGramWeights_at A ⟨i,hin⟩,Complex.norm_real,Real.norm_eq_abs,abs_norm]
  rw [← approximationNumber_gramBasis A ⟨i,hin⟩]

/-- The actual singular coordinates strictly above the threshold. -/
def singularCutoffSet (A : E →L[ℂ] F) (t : ℝ) : Finset ℕ :=
  (Finset.range (Module.finrank ℂ E)).filter (fun i => t<‖finiteGramWeights A i‖)

/-- Retain precisely those singular columns, through the actual Gram factorization. -/
def singularCutoff (A : E →L[ℂ] F) (t : ℝ) : E →L[ℂ] F :=
  (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint ∘L
    diagonalTruncation (finiteGramWeights A) (singularCutoffSet A t) ∘L
      finiteAnalysis (fun i => gramBasis A i)

/-- Its rank is at most the number of retained singular columns. -/
theorem singularCutoff_rank (A : E →L[ℂ] F) (t : ℝ) :
    (singularCutoff A t).rank≤((singularCutoffSet A t).card : Cardinal) := by
  unfold singularCutoff
  exact (LinearMap.rank_comp_le_right _ _).trans
    ((LinearMap.rank_comp_le_left _ _).trans (rank_diagonalTruncation_le _ _))

/-- Coefficients of the literal residual diagonal, not a new approximation operator. -/
def singularResidualWeights (A : E →L[ℂ] F) (t : ℝ) (i : ℕ) : ℂ :=
  if i∈singularCutoffSet A t then 0 else finiteGramWeights A i

theorem finiteGramDiagonal_sub_cutoff (A : E →L[ℂ] F) (t : ℝ) :
    finiteGramDiagonal A-diagonalTruncation (finiteGramWeights A) (singularCutoffSet A t)=
      diagonalTruncation (singularResidualWeights A t) (Finset.range (Module.finrank ℂ E)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  by_cases hi : i∈Finset.range (Module.finrank ℂ E)
  · by_cases hs : i∈singularCutoffSet A t
    · simp [finiteGramDiagonal,diagonalTruncation_apply,singularResidualWeights,hi,hs]
    · simp [finiteGramDiagonal,diagonalTruncation_apply,singularResidualWeights,hi,hs]
  · have hs : i∉singularCutoffSet A t := fun h => hi (Finset.mem_of_mem_filter i h)
    simp [finiteGramDiagonal,diagonalTruncation_apply,hi,hs]

theorem sub_singularCutoff_factorization (A : E →L[ℂ] F) (t : ℝ) :
    A-singularCutoff A t=
      (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint ∘L
        diagonalTruncation (singularResidualWeights A t) (Finset.range (Module.finrank ℂ E)) ∘L
          finiteAnalysis (fun i => gramBasis A i) := by
  calc
    _ = (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint ∘L
        (finiteGramDiagonal A-diagonalTruncation (finiteGramWeights A) (singularCutoffSet A t)) ∘L
          finiteAnalysis (fun i => gramBasis A i) := by
      rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
      exact congrArg (fun T => T-singularCutoff A t) (finiteGram_factorization A)
    _ = _ := by rw [finiteGramDiagonal_sub_cutoff]

/-- Exact trace norm of a finite coordinate diagonal. -/
theorem schattenNorm_one_diagonalTruncation (w : ℕ → ℂ) (N : ℕ) :
    schattenNorm 1 (diagonalTruncation w (Finset.range N))=∑ i ∈ Finset.range N,‖w i‖ := by
  unfold schattenNorm
  rw [one_div_one,Real.rpow_one,diagonalTruncation_power_sum w N 1 (by norm_num)]
  simp only [Real.rpow_one]

/-- The actual cutoff attains the capped rank/trace budget, without an infimum hypothesis. -/
theorem singularCutoff_budget (A : E →L[ℂ] F) (t : ℝ) :
    ((singularCutoffSet A t).card : ℝ)*t+schattenNorm 1 (A-singularCutoff A t)≤
      cappedSingularSum A t := by
  let N := Module.finrank ℂ E
  let D := diagonalTruncation (singularResidualWeights A t) (Finset.range N)
  have hD : Schatten 1 D := finiteRankSchatten D
    ⟨N,by simpa only [D,Finset.card_range] using (rank_diagonalTruncation_le
      (singularResidualWeights A t) (Finset.range N))⟩ 1 (by norm_num)
  have hR := (gramBasis_analysis_contractions A).1
  have hC := (ContinuousLinearMap.adjoint.norm_map
    (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i))))).trans_le
      (gramBasis_analysis_contractions A).2
  have hTrace : schattenNorm 1 (A-singularCutoff A t)≤∑ i ∈ Finset.range N,‖singularResidualWeights A t i‖ := by
    rw [sub_singularCutoff_factorization]
    calc
      _ ≤ (‖(finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint‖*
          ‖finiteAnalysis (fun i => gramBasis A i)‖)*schattenNorm 1 D := schattenNorm_comp_le hD _ _
      _ ≤ schattenNorm 1 D := by
        have hm := mul_le_mul hC hR (norm_nonneg _) zero_le_one
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (schattenNorm_nonneg 1 D)
      _ = _ := schattenNorm_one_diagonalTruncation _ _
  have hCount : (∑ i ∈ Finset.range N,if t<‖finiteGramWeights A i‖ then t else 0)=
      ((singularCutoffSet A t).card : ℝ)*t := by
    rw [← Finset.sum_filter]
    simp [singularCutoffSet,N]
  have hCost : ((singularCutoffSet A t).card : ℝ)*t+
      (∑ i ∈ Finset.range N,‖singularResidualWeights A t i‖)=cappedSingularSum A t := by
    rw [← hCount,← Finset.sum_add_distrib,cappedSingularSum_eq_gram]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i∈Finset.range (Module.finrank ℂ E) := hi
    by_cases ht : t<‖finiteGramWeights A i‖
    · simp [singularResidualWeights,singularCutoffSet,hiN,ht,min_eq_right ht.le]
    · simp [singularResidualWeights,singularCutoffSet,hiN,ht,min_eq_left (not_lt.mp ht)]
  exact (add_le_add_right hTrace _).trans_eq hCost

/-- The capped singular sum is subadditive, with the sharp constant one. -/
theorem cappedSingularSum_add_le (A B : E →L[ℂ] F) (t : ℝ) (ht : 0≤t) :
    cappedSingularSum (A+B) t≤cappedSingularSum A t+cappedSingularSum B t := by
  let kA := (singularCutoffSet A t).card
  let kB := (singularCutoffSet B t).card
  let R := singularCutoff A t+singularCutoff B t
  have hR : R.rank≤((kA+kB : ℕ) : Cardinal) := by
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le _ _).trans
      (add_le_add (singularCutoff_rank A t) (singularCutoff_rank B t))
  have hTrace : schattenNorm 1 (A+B-R)≤
      schattenNorm 1 (A-singularCutoff A t)+schattenNorm 1 (B-singularCutoff B t) := by
    have he : A+B-R=(A-singularCutoff A t)+(B-singularCutoff B t) := by dsimp [R]; abel
    rw [he]
    exact finiteSchattenTriangle E F 1 le_rfl _ _
  calc
    _ ≤ ((kA+kB : ℕ) : ℝ)*t+schattenNorm 1 (A+B-R) :=
      cappedSingularSum_le_rank_budget (A+B) R t ht (kA+kB) hR
    _ ≤ ((kA+kB : ℕ) : ℝ)*t+
        (schattenNorm 1 (A-singularCutoff A t)+schattenNorm 1 (B-singularCutoff B t)) :=
      add_le_add_right hTrace _
    _ = ((kA : ℝ)*t+schattenNorm 1 (A-singularCutoff A t))+
        ((kB : ℝ)*t+schattenNorm 1 (B-singularCutoff B t)) := by push_cast; ring
    _ ≤ _ := add_le_add (singularCutoff_budget A t) (singularCutoff_budget B t)

/-- Integrability of the Mellin kernel; both ends are treated before any ordinary integral. -/
theorem integrableOn_min_mul_rpow (x p : ℝ) (hx : 0≤x) (hp : 0<p) (hp1 : p<1) :
    IntegrableOn (fun t : ℝ => min x t*t^(p-2)) (Ioi 0) := by
  rcases eq_or_lt_of_le hx with rfl|hx
  · apply (integrable_zero ℝ ℝ (volume.restrict (Ioi 0))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [min_eq_left ht.le]
  · have hNear : IntegrableOn (fun t : ℝ => min x t*t^(p-2)) (Ioc 0 x) := by
      have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=x) (r:=p-1) (by linarith))
      apply h.congr_fun _ measurableSet_Ioc
      intro t ht
      change t^(p-1)=min x t*t^(p-2)
      rw [min_eq_right ht.2]
      calc
        _ = t^(1+(p-2)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add ht.1,Real.rpow_one]
    have hFar : IntegrableOn (fun t : ℝ => min x t*t^(p-2)) (Ioi x) := by
      have h : IntegrableOn (fun t : ℝ => x*t^(p-2)) (Ioi x) :=
        (integrableOn_Ioi_rpow_of_lt (a:=p-2) (by linarith) hx).const_mul x
      apply h.congr_fun _ measurableSet_Ioi
      intro t ht
      dsimp only
      rw [min_eq_left ht.le]
    rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact hNear.union hFar

/-- Elementary scalar Mellin representation, with its exact positive constant. -/
theorem rpow_eq_integral_min (x p : ℝ) (hx : 0≤x) (hp : 0<p) (hp1 : p<1) :
    x^p=(p*(1-p))*(∫ t : ℝ in Ioi 0,min x t*t^(p-2)) := by
  rcases eq_or_lt_of_le hx with rfl|hx
  · rw [Real.zero_rpow hp.ne']
    have hz : (∫ t : ℝ in Ioi 0,min 0 t*t^(p-2))=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [min_eq_left ht.le]
    rw [hz,mul_zero]
  · have hI := integrableOn_min_mul_rpow x p hx.le hp hp1
    have hNear : (∫ t : ℝ in (0 : ℝ)..x,min x t*t^(p-2))=x^p/p := by
      rw [intervalIntegral.integral_of_le hx.le]
      calc
        _ = ∫ t : ℝ in Ioc 0 x,t^(p-1) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          dsimp only
          rw [min_eq_right ht.2]
          calc
            _ = t^(1+(p-2)) := by rw [Real.rpow_add ht.1,Real.rpow_one]
            _ = _ := by congr 1; ring
        _ = ∫ t : ℝ in (0 : ℝ)..x,t^(p-1) := (intervalIntegral.integral_of_le hx.le).symm
        _ = _ := by
          rw [integral_rpow (Or.inl (by linarith : -1<p-1))]
          rw [show p-1+1=p by ring,Real.zero_rpow hp.ne',sub_zero]
    have hPow : x*x^(p-1)=x^p := by
      calc
        _ = x^(1+(p-1)) := by rw [Real.rpow_add hx,Real.rpow_one]
        _ = _ := by congr 1; ring
    have hFar : (∫ t : ℝ in Ioi x,min x t*t^(p-2))=x^p/(1-p) := by
      calc
        _ = ∫ t : ℝ in Ioi x,x*t^(p-2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          dsimp only
          rw [min_eq_left ht.le]
        _ = x*(-x^(p-1)/(p-1)) := by
          rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : p-2 < -1) hx]
          rw [show p-2+1=p-1 by ring]
        _ = (x*x^(p-1))/(1-p) := by field_simp [sub_ne_zero.mpr hp1.ne,(sub_pos.mpr hp1).ne']; ring
        _ = _ := by rw [hPow]
    rw [← intervalIntegral.integral_interval_add_Ioi hI
      (hI.mono_set (Ioi_subset_Ioi hx.le)),hNear,hFar]
    field_simp [hp.ne',(sub_pos.mpr hp1).ne']; ring

omit [CompleteSpace F] in
/-- Every finite capped singular sum has the required weighted integrability. -/
theorem integrableOn_cappedSingularSum_mul_rpow (A : E →L[ℂ] F) (p : ℝ)
    (hp : 0<p) (hp1 : p<1) :
    IntegrableOn (fun t : ℝ => cappedSingularSum A t*t^(p-2)) (Ioi 0) := by
  simp only [cappedSingularSum,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _hi =>
    integrableOn_min_mul_rpow (approximationNumber A i : ℝ) p (NNReal.coe_nonneg _) hp hp1)

omit [CompleteSpace F] in
/-- The scalar Mellin formula summed over the actual finite singular values. -/
theorem singular_power_sum_eq_integral_cap (A : E →L[ℂ] F) (p : ℝ)
    (hp : 0<p) (hp1 : p<1) :
    (∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber A i : ℝ)^p)=
      (p*(1-p))*(∫ t : ℝ in Ioi 0,cappedSingularSum A t*t^(p-2)) := by
  simp only [cappedSingularSum,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _hi =>
    integrableOn_min_mul_rpow (approximationNumber A i : ℝ) p (NNReal.coe_nonneg _) hp hp1),Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _hi =>
    rpow_eq_integral_min (approximationNumber A i : ℝ) p (NNReal.coe_nonneg _) hp hp1)

/-- Sharp low-p power-sum addition; the constant is independent of dimension and summand count. -/
theorem finite_singular_power_sum_add_le (A B : E →L[ℂ] F) (p : ℝ)
    (hp : 0<p) (hp1 : p<1) :
    (∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber (A+B) i : ℝ)^p)≤
      (∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber A i : ℝ)^p)+
        (∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber B i : ℝ)^p) := by
  rw [singular_power_sum_eq_integral_cap (A+B) p hp hp1,
    singular_power_sum_eq_integral_cap A p hp hp1,singular_power_sum_eq_integral_cap B p hp hp1,← mul_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.le (sub_pos.mpr hp1).le)
  rw [← integral_add (integrableOn_cappedSingularSum_mul_rpow A p hp hp1)
    (integrableOn_cappedSingularSum_mul_rpow B p hp hp1)]
  apply integral_mono_ae (integrableOn_cappedSingularSum_mul_rpow (A+B) p hp hp1)
    ((integrableOn_cappedSingularSum_mul_rpow A p hp hp1).add
      (integrableOn_cappedSingularSum_mul_rpow B p hp hp1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Pi.add_apply,add_mul] using mul_le_mul_of_nonneg_right
    (cappedSingularSum_add_le A B t ht.le) (Real.rpow_nonneg ht.le (p-2))

/-- Exact finite prefix after taking the pth power of the Schatten gauge. -/
theorem schattenNorm_finite_prefix_rpow (A : E →L[ℂ] F) (p : ℝ) (hp : 0<p) :
    schattenNorm p A^p=
      ∑ i ∈ Finset.range (Module.finrank ℂ E),(approximationNumber A i : ℝ)^p := by
  rw [schattenNorm_finite_prefix A p hp,one_div]
  exact Real.rpow_inv_rpow (Finset.sum_nonneg (fun i _hi => Real.rpow_nonneg (NNReal.coe_nonneg _) p)) hp.ne'

/-- Actual sharp finite Schatten p-power triangle throughout 0<p≤1. -/
theorem finite_schattenNorm_add_rpow_le (A B : E →L[ℂ] F) (p : ℝ)
    (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (A+B)^p≤schattenNorm p A^p+schattenNorm p B^p := by
  rcases lt_or_eq_of_le hp1 with hp1|rfl
  · rw [schattenNorm_finite_prefix_rpow (A+B) p hp,
      schattenNorm_finite_prefix_rpow A p hp,schattenNorm_finite_prefix_rpow B p hp]
    exact finite_singular_power_sum_add_le A B p hp hp1
  · simp only [Real.rpow_one]
    exact finiteSchattenTriangle E F 1 le_rfl A B

/-- The same constant one for any finite family, including the empty family. -/
theorem finite_schattenNorm_sum_rpow_le {ι : Type*} (s : Finset ι)
    (A : ι → E →L[ℂ] F) (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    schattenNorm p (∑ i ∈ s,A i)^p≤∑ i ∈ s,schattenNorm p (A i)^p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,schattenNorm_rpow hp,approximationNumber_zero,NNReal.coe_zero,
      Real.zero_rpow hp.ne',tsum_zero,le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (finite_schattenNorm_add_rpow_le (A i) (∑ j ∈ s,A j) p hp hp1).trans
      (add_le_add le_rfl ih)

section InfiniteLowPower
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Simultaneous actual source cuts preserve the sharp power budget. -/
theorem exists_schatten_sum_cut_rpow (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (A B : H →L[ℂ] H) (hA : Schatten p A) (hB : Schatten p B) (ε : ℝ) (hε : 0<ε) :
    ∃ C : H →L[ℂ] H,Schatten p C ∧
      schattenNorm p C^p≤schattenNorm p A^p+schattenNorm p B^p ∧ ‖(A+B)-C‖≤2*ε := by
  obtain ⟨M,hM,P,hP,hPJ,hEA,hEB⟩ := simultaneous_compact_source_cut A B hA.2.1 hB.2.1 ε hε
  let : FiniteDimensional ℂ M := hM
  let : CompleteSpace M := FiniteDimensional.complete ℂ M
  have hJ : ‖M.subtypeL‖≤1 := norm_isometry_clm_le_one M.subtypeₗᵢ
  let C : H →L[ℂ] H := ((A+B) ∘L M.subtypeL) ∘L P
  have hC : Schatten p C := by
    simpa only [C,ContinuousLinearMap.comp_assoc] using
      schatten_comp_right (schatten_add hA hB) (M.subtypeL ∘L P)
  have hbound (T : H →L[ℂ] H) (hT : Schatten p T) :
      schattenNorm p (T ∘L M.subtypeL)≤schattenNorm p T := by
    have ht := schattenNorm_le_of_approx_le hT 1 zero_le_one (fun n => by
      simpa only [one_mul] using NNReal.coe_le_coe.mpr
        (approximationNumber_comp_right_contraction T M.subtypeL hJ n))
    simpa only [one_mul] using ht
  refine ⟨C,hC,?_,?_⟩
  · calc
      schattenNorm p C^p=schattenNorm p ((A+B) ∘L M.subtypeL)^p :=
        congrArg (fun x : ℝ => x^p) (schattenNorm_comp_right_retract P M.subtypeL hP hJ hPJ _ p)
      _ = schattenNorm p ((A ∘L M.subtypeL)+(B ∘L M.subtypeL))^p := by
        rw [ContinuousLinearMap.add_comp]
      _ ≤ schattenNorm p (A ∘L M.subtypeL)^p+schattenNorm p (B ∘L M.subtypeL)^p :=
        finite_schattenNorm_add_rpow_le _ _ p hp hp1
      _ ≤ _ := add_le_add
        (Real.rpow_le_rpow (schattenNorm_nonneg p _) (hbound A hA) hp.le)
        (Real.rpow_le_rpow (schattenNorm_nonneg p _) (hbound B hB) hp.le)
  · have he : (A+B)-C=(A-A ∘L M.subtypeL ∘L P)+(B-B ∘L M.subtypeL ∘L P) := by
      simp only [C,ContinuousLinearMap.add_comp]
      abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)

/-- Sharp power triangle for actual Schatten operators, without finite dimension or separability. -/
theorem schattenNorm_add_rpow_le_sharp (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (A B : H →L[ℂ] H) (hA : Schatten p A) (hB : Schatten p B) :
    schattenNorm p (A+B)^p≤schattenNorm p A^p+schattenNorm p B^p := by
  have hex (n : ℕ) := exists_schatten_sum_cut_rpow p hp hp1 A B hA hB
    (1/((n : ℝ)+1)) (by positivity)
  choose C hCs hCB hCE using hex
  have hz : Tendsto (fun n : ℕ => 2*(1/((n : ℝ)+1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  have hnorm : Tendsto (fun n => ‖C n-(A+B)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => by simpa only [norm_sub_rev] using hCE n) hz
  have hlim : Tendsto C atTop (𝓝 (A+B)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_eq_norm] using hnorm
  have hPrefix (N : ℕ) :
      (∑ i ∈ Finset.range N,(approximationNumber (A+B) i : ℝ)^p)≤
        schattenNorm p A^p+schattenNorm p B^p := by
    have ht : Tendsto (fun n => ∑ i ∈ Finset.range N,(approximationNumber (C n) i : ℝ)^p)
        atTop (𝓝 (∑ i ∈ Finset.range N,(approximationNumber (A+B) i : ℝ)^p)) := by
      apply tendsto_finsetSum
      intro i _hi
      exact ((Real.continuous_rpow_const hp.le).comp (continuous_approximationNumber i)).continuousAt.tendsto.comp hlim
    apply le_of_tendsto' ht
    intro n
    have h := (hCs n).2.2.sum_le_tsum (Finset.range N)
      (fun i _hi => Real.rpow_nonneg (approximationNumber (C n) i).coe_nonneg p)
    rw [← schattenNorm_rpow hp] at h
    exact h.trans (hCB n)
  rw [schattenNorm_rpow hp]
  exact Real.tsum_le_of_sum_range_le (fun i => Real.rpow_nonneg (NNReal.coe_nonneg _) p) hPrefix

/-- The dimension-independent power bound for every finite family of actual Schatten operators. -/
theorem schattenNorm_sum_rpow_le_sharp {ι : Type*} (s : Finset ι)
    (A : ι → H →L[ℂ] H) (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hA : ∀ i∈s,Schatten p (A i)) :
    schattenNorm p (∑ i ∈ s,A i)^p≤∑ i ∈ s,schattenNorm p (A i)^p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,schattenNorm_rpow hp,approximationNumber_zero,NNReal.coe_zero,
      Real.zero_rpow hp.ne',tsum_zero,le_refl]
  | @insert i s hi ih =>
    have hAi := hA i (Finset.mem_insert_self i s)
    have hAs : ∀ j∈s,Schatten p (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (schattenNorm_add_rpow_le_sharp p hp hp1 (A i) (∑ j ∈ s,A j) hAi
      (schatten_sum s A p hp hAs)).trans (add_le_add le_rfl (ih hAs))

end InfiniteLowPower

end TTO.Paper.Proved
