/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.AngularFoundations
public import Mathlib.Analysis.Normed.Operator.Banach

/-! Norm-controlled native H∞ interpolation, a prerequisite for the Riesz kernel synthesis. -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

abbrev SequenceLInf := lp (fun _ : ℕ => ℂ) ∞

/-- The actual inclusion from boundary L∞ into L², using multiplication by one. -/
def boundaryInclusion : BoundaryLInf →L[ℂ] BoundaryL2 :=
  ((ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ 2 2).flip (constL2 1)

theorem boundaryInclusion_apply (g : BoundaryLInf) : boundaryInclusion g = toL2 g := by
  change multiply g (constL2 1) = toL2 g
  apply Lp.ext
  filter_upwards [multiply_ae g (constL2 1),(memLp_const (1 : ℂ)).coeFn_toLp,toL2_ae g] with t hm h1 hg
  change (constL2 1) t = 1 at h1
  rw [hm,h1,hg,mul_one]

def boundedHardy : Submodule ℂ BoundaryLInf := hardy.comap boundaryInclusion.toLinearMap

theorem boundedHardy_closed : IsClosed (boundedHardy : Set BoundaryLInf) :=
  (Submodule.isClosed_topologicalClosure _).preimage boundaryInclusion.continuous

instance boundedHardy_complete : CompleteSpace boundedHardy := boundedHardy_closed.completeSpace_coe

theorem boundedHardy_hardy (g : boundedHardy) : toL2 g.val ∈ hardy := by
  rw [← boundaryInclusion_apply]
  exact g.prop

def boundedHardyToHardy : boundedHardy →L[ℂ] Hardy :=
  (boundaryInclusion.comp boundedHardy.subtypeL).codRestrict hardy (fun g => g.prop)

theorem boundedHardyToHardy_val (g : boundedHardy) : (boundedHardyToHardy g).val = toL2 g.val :=
  boundaryInclusion_apply g.val

def interpolationValues (a : ℕ → Disk) (g : boundedHardy) : SequenceLInf :=
  ⟨fun n => hardyEvaluation (a n) (boundedHardyToHardy g),by
    apply memℓp_infty
    refine ⟨‖g.val‖,?_⟩
    rintro _ ⟨n,rfl⟩
    change ‖analyticValue (boundedHardyToHardy g).val (a n).val‖ ≤ ‖g.val‖
    rw [boundedHardyToHardy_val]
    exact norm_innerValue_le g.val (boundedHardy_hardy g) (a n)⟩

theorem interpolationValues_apply (a : ℕ → Disk) (g : boundedHardy) (n : ℕ) :
    interpolationValues a g n = innerValue g.val (a n).val := by
  change analyticValue (boundedHardyToHardy g).val (a n).val = _
  rw [boundedHardyToHardy_val]
  rfl

def interpolationLinear (a : ℕ → Disk) : boundedHardy →ₗ[ℂ] SequenceLInf where
  toFun := interpolationValues a
  map_add' g h := by
    apply lp.ext
    funext n
    change hardyEvaluation (a n) (boundedHardyToHardy (g+h)) =
      hardyEvaluation (a n) (boundedHardyToHardy g)+hardyEvaluation (a n) (boundedHardyToHardy h)
    rw [map_add,map_add]
  map_smul' c g := by
    apply lp.ext
    funext n
    change hardyEvaluation (a n) (boundedHardyToHardy (c • g)) =
      c • hardyEvaluation (a n) (boundedHardyToHardy g)
    rw [map_smul,map_smul]

theorem interpolationValues_norm_le (a : ℕ → Disk) (g : boundedHardy) :
    ‖interpolationValues a g‖ ≤ ‖g‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg g)
  intro n
  rw [interpolationValues_apply]
  exact norm_innerValue_le g.val (boundedHardy_hardy g) (a n)

def interpolationMap (a : ℕ → Disk) : boundedHardy →L[ℂ] SequenceLInf :=
  (interpolationLinear a).mkContinuous 1 (fun g => by
    change ‖interpolationValues a g‖ ≤ 1*‖g‖
    rw [one_mul]
    exact interpolationValues_norm_le a g)

theorem interpolationMap_surjective (a : ℕ → Disk) (ha : Interpolating a) : Function.Surjective (interpolationMap a) := by
  intro w
  obtain ⟨g,hg,hv⟩ := ha (fun n => w n) ⟨‖w‖,lp.norm_apply_le_norm ENNReal.top_ne_zero w⟩
  have hbg : g ∈ boundedHardy := by
    change boundaryInclusion g ∈ hardy
    rw [boundaryInclusion_apply]
    exact hg
  refine ⟨⟨g,hbg⟩,?_⟩
  apply lp.ext
  funext n
  change interpolationValues a ⟨g,hbg⟩ n = w n
  rw [interpolationValues_apply]
  exact hv n

/-- A single interpolation constant depends on the nodes, before all data and bounds. -/
theorem uniformInterpolation_linf (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SequenceLInf, ∃ g : BoundaryLInf,
      toL2 g ∈ hardy ∧ (∀ n, innerValue g (a n).val = w n) ∧ ‖g‖ ≤ C*‖w‖ := by
  obtain ⟨C,hC,hpre⟩ := (interpolationMap a).exists_preimage_norm_le (interpolationMap_surjective a ha)
  refine ⟨C,hC,fun w => ?_⟩
  obtain ⟨g,he,hg⟩ := hpre w
  refine ⟨g.val,boundedHardy_hardy g,fun n => ?_,hg⟩
  have hn := congrArg (fun v : SequenceLInf => v n) he
  change interpolationValues a g n = w n at hn
  exact (interpolationValues_apply a g n).symm.trans hn

/-- Raw bounded scalar data admit uniformly norm-controlled native H∞ interpolants. -/
theorem uniformInterpolation (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ → ℂ, ∀ M : ℝ, 0 ≤ M → (∀ n, ‖w n‖ ≤ M) →
      ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ (∀ n, innerValue g (a n).val = w n) ∧ ‖g‖ ≤ C*M := by
  obtain ⟨C,hC,hinterp⟩ := uniformInterpolation_linf a ha
  refine ⟨C,hC,fun w M hM hw => ?_⟩
  let v : SequenceLInf := ⟨w,memℓp_infty ⟨M,by rintro _ ⟨n,rfl⟩; exact hw n⟩⟩
  obtain ⟨g,hg,hv,hn⟩ := hinterp v
  refine ⟨g,hg,hv,hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (lp.norm_le_of_forall_le hM hw) hC.le


/-- The genuine adjoint Hardy multiplier has the Szegő kernels as eigenvectors. -/
theorem hardyMultiply_adjoint_szego (g : BoundaryLInf) (hg : toL2 g ∈ hardy) (w : Disk) :
    (hardyMultiply g hg).adjoint (szegoKernel w) = conj (innerValue g w.val) • szegoKernel w := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left,inner_smul_left (𝕜 := ℂ) (E := Hardy),Complex.conj_conj,
    inner_szegoKernel,inner_szegoKernel]
  exact analyticValue_multiply g hg f w

theorem hardyMultiply_adjoint_node (g : BoundaryLInf) (hg : toL2 g ∈ hardy) (w : Disk) :
    (hardyMultiply g hg).adjoint (hardyNodeVector w) = conj (innerValue g w.val) • hardyNodeVector w := by
  rw [hardyNodeVector,map_smul,hardyMultiply_adjoint_szego]
  simp only [smul_smul]
  congr 1
  exact mul_comm _ _

/-- Uniformly bounded scalar data act through actual bounded adjoint multipliers on the kernels. -/
theorem interpolatingKernelMultipliers (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ → ℂ, ∀ M : ℝ, 0 ≤ M → (∀ n, ‖w n‖ ≤ M) →
      ∃ A : Hardy →L[ℂ] Hardy, ‖A‖ ≤ C*M ∧
        ∀ n, A (hardyNodeVector (a n)) = conj (w n) • hardyNodeVector (a n) := by
  obtain ⟨C,hC,hinterp⟩ := uniformInterpolation a ha
  refine ⟨C,hC,fun w M hM hw => ?_⟩
  obtain ⟨g,hg,hv,hn⟩ := hinterp w M hM hw
  refine ⟨(hardyMultiply g hg).adjoint,?_,fun n => ?_⟩
  · rw [ContinuousLinearMap.adjoint.norm_map]
    exact (norm_hardyMultiply_le g hg).trans hn
  · rw [hardyMultiply_adjoint_node,hv]


section FiniteSigns
variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem signedSum_insert [DecidableEq I] (s : Finset I) (a : I) (ha : a ∉ s) (σ : I → ℂ) (r : ℂ) (v : I → H) :
    (∑ i ∈ insert a s, Function.update σ a r i • v i) = r • v a+∑ i ∈ s, σ i • v i := by
  classical
  rw [Finset.sum_insert ha,Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (show i≠a from fun he => ha (he ▸ hi))]

theorem sign_update [DecidableEq I] (σ : I → ℂ) (hσ : ∀ i, σ i=1 ∨ σ i= -1) (a : I) (r : ℂ)
    (hr : r=1 ∨ r= -1) : ∀ i, Function.update σ a r i=1 ∨ Function.update σ a r i= -1 := by
  classical
  intro i
  by_cases hi : i=a
  · subst i
    rw [Function.update_self]
    exact hr
  · rw [Function.update_of_ne hi]
    exact hσ i

theorem sign_step_le (x v : H) : ∃ r : ℂ, (r=1 ∨ r= -1) ∧ ‖r • v+x‖^2 ≤ ‖x‖^2+‖v‖^2 := by
  by_cases h : ‖x+v‖^2 ≤ ‖x‖^2+‖v‖^2
  · exact ⟨1,Or.inl rfl,by simpa only [one_smul,add_comm] using h⟩
  · have hp := parallelogram_law_with_norm ℂ x v
    have hn : ‖x-v‖^2 ≤ ‖x‖^2+‖v‖^2 := by linarith
    exact ⟨-1,Or.inr rfl,by simpa only [neg_one_smul,sub_eq_add_neg,add_comm] using hn⟩

theorem sign_step_ge (x v : H) : ∃ r : ℂ, (r=1 ∨ r= -1) ∧ ‖x‖^2+‖v‖^2 ≤ ‖r • v+x‖^2 := by
  by_cases h : ‖x‖^2+‖v‖^2 ≤ ‖x+v‖^2
  · exact ⟨1,Or.inl rfl,by simpa only [one_smul,add_comm] using h⟩
  · have hp := parallelogram_law_with_norm ℂ x v
    have hn : ‖x‖^2+‖v‖^2 ≤ ‖x-v‖^2 := by linarith
    exact ⟨-1,Or.inr rfl,by simpa only [neg_one_smul,sub_eq_add_neg,add_comm] using hn⟩

theorem exists_signs_norm_sq_le (s : Finset I) (v : I → H) :
    ∃ σ : I → ℂ, (∀ i, σ i=1 ∨ σ i= -1) ∧ ‖∑ i ∈ s, σ i • v i‖^2 ≤ ∑ i ∈ s, ‖v i‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨σ,hσ,hb⟩ := ih
    obtain ⟨r,hr,hn⟩ := sign_step_le (∑ i ∈ s, σ i • v i) (v a)
    refine ⟨Function.update σ a r,sign_update σ hσ a r hr,?_⟩
    rw [signedSum_insert s a ha,Finset.sum_insert ha]
    linarith

theorem exists_signs_norm_sq_ge (s : Finset I) (v : I → H) :
    ∃ σ : I → ℂ, (∀ i, σ i=1 ∨ σ i= -1) ∧ (∑ i ∈ s, ‖v i‖^2) ≤ ‖∑ i ∈ s, σ i • v i‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨σ,hσ,hb⟩ := ih
    obtain ⟨r,hr,hn⟩ := sign_step_ge (∑ i ∈ s, σ i • v i) (v a)
    refine ⟨Function.update σ a r,sign_update σ hσ a r hr,?_⟩
    rw [signedSum_insert s a ha,Finset.sum_insert ha]
    linarith

end FiniteSigns


theorem interpolatingKernelSignOperators (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℕ → ℂ, (∀ n, σ n=1 ∨ σ n= -1) →
      ∃ A : Hardy →L[ℂ] Hardy, ‖A‖ ≤ C ∧ ∀ n, A (hardyNodeVector (a n)) = σ n • hardyNodeVector (a n) := by
  obtain ⟨C,hC,hinterp⟩ := interpolatingKernelMultipliers a ha
  refine ⟨C,hC,fun σ hσ => ?_⟩
  have hb : ∀ n, ‖σ n‖ ≤ 1 := by
    intro n
    rcases hσ n with h | h <;> rw [h] <;> norm_num
  obtain ⟨A,hA,hAn⟩ := hinterp σ 1 zero_le_one hb
  refine ⟨A,by simpa only [mul_one] using hA,fun n => ?_⟩
  rw [hAn]
  have hc : conj (σ n) = σ n := by rcases hσ n with h | h <;> rw [h] <;> norm_num
  rw [hc]

/-- The full pair of finite Riesz bounds on the actual normalized Hardy kernels.
Completeness of their span for the specified Blaschke model is proved in BlaschkeFoundations. -/
theorem finiteRieszKernelBounds (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      (∑ n ∈ s, ‖c n‖^2) ≤ C^2*‖∑ n ∈ s, c n • hardyNodeVector (a n)‖^2 ∧
      ‖∑ n ∈ s, c n • hardyNodeVector (a n)‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2) := by
  obtain ⟨C,hC,hinterp⟩ := interpolatingKernelSignOperators a ha
  refine ⟨C,hC,fun s c => ?_⟩
  let v := fun n => c n • hardyNodeVector (a n)
  let x := ∑ n ∈ s, v n
  have henergy : (∑ n ∈ s, ‖v n‖^2) = ∑ n ∈ s, ‖c n‖^2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [show v n = c n • hardyNodeVector (a n) from rfl,norm_smul,norm_hardyNodeVector,mul_one]
  have hsums (σ : ℕ → ℂ) (hσ : ∀ n, σ n=1 ∨ σ n= -1) :
      ∃ A : Hardy →L[ℂ] Hardy, ‖A‖ ≤ C ∧
        A x = ∑ n ∈ s, σ n • v n ∧ A (∑ n ∈ s, σ n • v n) = x := by
    obtain ⟨A,hA,hAn⟩ := hinterp σ hσ
    refine ⟨A,hA,?_,?_⟩
    · dsimp only [x,v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [map_smul,hAn]
      simp only [smul_smul]
      congr 1
      exact mul_comm _ _
    · dsimp only [x,v]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [map_smul,map_smul,hAn]
      rcases hσ n with h | h
      · rw [h]
        simp only [one_smul]
      · rw [h]
        simp only [smul_smul]
        congr 1
        ring
  constructor
  · obtain ⟨σ,hσ,hs⟩ := exists_signs_norm_sq_ge s v
    obtain ⟨A,hA,hAx,_hAy⟩ := hsums σ hσ
    have hb : ‖∑ n ∈ s, σ n • v n‖ ≤ C*‖x‖ := by
      rw [← hAx]
      exact (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg x))
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow] at hsquare
    rw [henergy] at hs
    exact hs.trans hsquare
  · obtain ⟨σ,hσ,hs⟩ := exists_signs_norm_sq_le s v
    obtain ⟨A,hA,_hAx,hAy⟩ := hsums σ hσ
    have hb : ‖x‖ ≤ C*‖∑ n ∈ s, σ n • v n‖ := by
      rw [← hAy]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    have hsquare := pow_le_pow_left₀ (norm_nonneg x) hb 2
    rw [mul_pow] at hsquare
    rw [henergy] at hs
    exact hsquare.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg C))

section InfiniteSynthesis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sequenceL2_hasSum (c : SequenceL2) : HasSum (fun n => ‖c n‖^2) (‖c‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) c

/-- A uniform finite upper Riesz bound gives genuine unconditional synthesis. -/
theorem synthesis_summable (k : ℕ → H) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2)) (c : SequenceL2) :
    Summable (fun n => c n • k n) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hδ : 0 < ε^2/C^2 := div_pos (sq_pos_of_pos hε) (sq_pos_of_pos hC)
  obtain ⟨s,hs⟩ := summable_iff_vanishing_norm.mp (sequenceL2_hasSum c).summable (ε^2/C^2) hδ
  refine ⟨s,fun t ht => ?_⟩
  have he := hs t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun n _ => sq_nonneg ‖c n‖))] at he
  have hb' := hb t c
  have hmul := mul_lt_mul_of_pos_left he (sq_pos_of_pos hC)
  have hcancel : C^2*(ε^2/C^2) = ε^2 := by field_simp
  rw [hcancel] at hmul
  have hsq := hb'.trans_lt hmul
  nlinarith [norm_nonneg (∑ n ∈ t, c n • k n)]

/-- Both finite bounds pass to the actual infinite sum, with the identical constant. -/
theorem synthesis_bounds (k : ℕ → H) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      (∑ n ∈ s, ‖c n‖^2) ≤ C^2*‖∑ n ∈ s, c n • k n‖^2 ∧
      ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2)) (c : SequenceL2) :
    ‖c‖^2 ≤ C^2*‖∑' n, c n • k n‖^2 ∧
      ‖∑' n, c n • k n‖^2 ≤ C^2*‖c‖^2 := by
  have hs := (synthesis_summable k C hC (fun s c => (hb s c).2) c).hasSum
  have he := sequenceL2_hasSum c
  have hn := (hs.norm.pow 2)
  constructor
  · exact le_of_tendsto_of_tendsto he (tendsto_const_nhds.mul hn) (Filter.Eventually.of_forall (fun s => (hb s c).1))
  · exact le_of_tendsto_of_tendsto hn (tendsto_const_nhds.mul he) (Filter.Eventually.of_forall (fun s => (hb s c).2))

def synthesisLinear (k : ℕ → H) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2)) : SequenceL2 →ₗ[ℂ] H where
  toFun c := ∑' n, c n • k n
  map_add' c d := by
    change (∑' n, (c n+d n) • k n) = _
    simp_rw [add_smul]
    exact (synthesis_summable k C hC hb c).tsum_add (synthesis_summable k C hC hb d)
  map_smul' r c := by
    change (∑' n, (r • c n) • k n) = _
    calc
      (∑' n, (r • c n) • k n) = ∑' n, r • (c n • k n) := tsum_congr (fun n => by rw [smul_eq_mul,smul_smul])
      _ = r • ∑' n, c n • k n := (synthesis_summable k C hC hb c).tsum_const_smul r

theorem synthesis_norm_le (k : ℕ → H) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2)) (c : SequenceL2) :
    ‖synthesisLinear k C hC hb c‖ ≤ C*‖c‖ := by
  have hs := (synthesis_summable k C hC hb c).hasSum
  have he := sequenceL2_hasSum c
  have hn := hs.norm.pow 2
  have hsq := le_of_tendsto_of_tendsto hn (tendsto_const_nhds.mul he)
    (Filter.Eventually.of_forall (fun s => hb s c))
  change ‖∑' n, c n • k n‖ ≤ C*‖c‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg c))).mp
  simpa only [mul_pow] using hsq

def synthesisOperator (k : ℕ → H) (C : ℝ) (hC : 0 < C)
    (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2)) : SequenceL2 →L[ℂ] H :=
  (synthesisLinear k C hC hb).mkContinuous C (synthesis_norm_le k C hC hb)

variable (k : ℕ → H) (C : ℝ) (hC : 0 < C)
  (hb : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
    (∑ n ∈ s, ‖c n‖^2) ≤ C^2*‖∑ n ∈ s, c n • k n‖^2 ∧
    ‖∑ n ∈ s, c n • k n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2))

theorem synthesis_lower_bound (c : SequenceL2) :
    ‖c‖ ≤ C*‖synthesisOperator k C hC (fun s c => (hb s c).2) c‖ := by
  have hsq := (synthesis_bounds k C hC hb c).1
  change ‖c‖ ≤ C*‖∑' n, c n • k n‖
  apply (sq_le_sq₀ (norm_nonneg c) (mul_nonneg hC.le (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

theorem synthesis_antilipschitz : AntilipschitzWith (⟨C,hC.le⟩ : NNReal)
    (synthesisOperator k C hC (fun s c => (hb s c).2)) :=
  ContinuousLinearMap.antilipschitz_of_bound _ (synthesis_lower_bound k C hC hb)

theorem synthesis_single (n : ℕ) :
    synthesisOperator k C hC (fun s c => (hb s c).2) (lp.single 2 n (1 : ℂ)) = k n := by
  change (∑' m, (lp.single 2 n (1 : ℂ) : SequenceL2) m • k m) = k n
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    simp [lp.single_apply,hm]

/-- The actual synthesis range is exactly the closed span of the specified vectors. -/
theorem synthesis_range :
    (synthesisOperator k C hC (fun s c => (hb s c).2)).range =
      (Submodule.span ℂ (Set.range k)).topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    have hs := (synthesis_summable k C hC (fun s c => (hb s c).2) c).hasSum
    apply (Submodule.isClosed_topologicalClosure (Submodule.span ℂ (Set.range k))).mem_of_tendsto hs
    apply Filter.Eventually.of_forall
    intro s
    exact Submodule.sum_mem _ (fun n _ => Submodule.smul_mem _ _
      ((Submodule.le_topologicalClosure _) (Submodule.subset_span (Set.mem_range_self n))))
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      exact ⟨lp.single 2 n 1,synthesis_single k C hC hb n⟩
    · exact (synthesis_antilipschitz k C hC hb).isClosed_range (synthesisOperator k C hC (fun s c => (hb s c).2)).uniformContinuous

/-- No totality hypothesis is hidden: the codomain is explicitly the closed kernel span. -/
def synthesisEquiv : SequenceL2 ≃L[ℂ] (Submodule.span ℂ (Set.range k)).topologicalClosure :=
  ((synthesisOperator k C hC (fun s c => (hb s c).2)).equivRange
    (synthesis_antilipschitz k C hC hb).injective
    ((synthesis_antilipschitz k C hC hb).isClosed_range
      (synthesisOperator k C hC (fun s c => (hb s c).2)).uniformContinuous)).trans
    (LinearIsometryEquiv.ofEq _ _ (synthesis_range k C hC hb)).toContinuousLinearEquiv

theorem synthesisEquiv_single (n : ℕ) :
    (synthesisEquiv k C hC hb (lp.single 2 n (1 : ℂ))).val = k n := by
  change synthesisOperator k C hC (fun s c => (hb s c).2) (lp.single 2 n (1 : ℂ)) = k n
  exact synthesis_single k C hC hb n

end InfiniteSynthesis

/-- Native interpolating normalized kernels form a Riesz basis of their closed span.
Identifying this span with the full Blaschke model remains an analytic obligation. -/
theorem interpolatingClosedSpanSynthesis (a : ℕ → Disk) (ha : Interpolating a) :
    ∃ R : SequenceL2 ≃L[ℂ] (Submodule.span ℂ (Set.range (fun n => hardyNodeVector (a n)))).topologicalClosure,
      ∀ n, (R (lp.single 2 n (1 : ℂ))).val = hardyNodeVector (a n) := by
  obtain ⟨C,hC,hb⟩ := finiteRieszKernelBounds a ha
  exact ⟨synthesisEquiv (fun n => hardyNodeVector (a n)) C hC hb,synthesisEquiv_single _ C hC hb⟩

end TTO.Paper.Proved
