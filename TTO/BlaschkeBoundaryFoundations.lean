/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.MalmquistFoundations
public import TTO.AnalyticLiftFoundations
public import Mathlib.Data.Nat.Dist

/-! Actual boundary realization of summable Blaschke products. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem multiply_constL2_one (u : BoundaryLInf) : multiply u (constL2 1) = toL2 u := by
  apply Lp.ext
  filter_upwards [multiply_ae u (constL2 1),(memLp_const (1 : ℂ)).coeFn_toLp,
    toL2_ae u] with t hm hc hu
  change constL2 1 t = 1 at hc
  rw [hm,hc,mul_one,hu]

theorem norm_toL2_of_inner (u : BoundaryLInf) (hu : IsInner u) : ‖toL2 u‖ = 1 := by
  rw [← multiply_constL2_one]
  change ‖innerMultiplyIsometry u hu (constL2 1)‖ = 1
  rw [LinearIsometry.norm_map,constL2_fourier,one_smul]
  exact (fourierBasis (T := 1)).orthonormal.norm_eq_one 0

theorem blaschkeFactor_zero (a : Disk) : blaschkeFactor a 0 = (‖a.val‖ : ℂ) := by
  by_cases ha : a.val = 0
  · simp [blaschkeFactor,ha]
  · simp only [blaschkeFactor,ha,ite_false,sub_zero,mul_zero,sub_zero,div_one]
    field_simp

def blaschkeHardyPrefix (a : ℕ → Disk) (n : ℕ) : Hardy :=
  ⟨toL2 (blaschkePrefix a n),(blaschkePrefix_isInner a n).1⟩

theorem blaschkePrefix_inner_add (a : ℕ → Disk) (n k : ℕ) :
    inner ℂ (toL2 (blaschkePrefix a n)) (toL2 (blaschkePrefix a (n+k))) =
      ((∏ j ∈ Finset.range k, ‖(a (j+n)).val‖ : ℝ) : ℂ) := by
  rw [blaschkePrefix_add,toL2_multiplyInf,← multiply_constL2_one (blaschkePrefix a n)]
  change inner ℂ
    (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n) (constL2 1))
    (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n)
      (toL2 (blaschkePrefix (fun j => a (j+n)) k))) = _
  rw [LinearIsometry.inner_map_map,inner_constL2_left,map_one,one_mul,← analyticValue_at_zero]
  change innerValue (blaschkePrefix (fun j => a (j+n)) k) 0 = _
  rw [innerValue_blaschkePrefix _ _ (⟨0,by simp [disk]⟩ : Disk)]
  simp only [blaschkeFactor_zero]
  norm_cast

theorem blaschkePrefix_norm_sub_sq (a : ℕ → Disk) (n k : ℕ) :
    ‖toL2 (blaschkePrefix a n) - toL2 (blaschkePrefix a (n+k))‖^2 =
      2 * (1 - ∏ j ∈ Finset.range k, ‖(a (j+n)).val‖) := by
  rw [norm_sub_sq (𝕜 := ℂ),norm_toL2_of_inner _ (blaschkePrefix_isInner a n),
    norm_toL2_of_inner _ (blaschkePrefix_isInner a (n+k)),blaschkePrefix_inner_add]
  change (1 : ℝ)^2 - 2 * (((∏ j ∈ Finset.range k, ‖(a (j+n)).val‖ : ℝ) : ℂ).re) + 1^2 = _
  simp only [Complex.ofReal_re,one_pow]
  ring

theorem one_sub_prod_range_le (r : ℕ → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (n : ℕ) : 1 - ∏ i ∈ Finset.range n, r i ≤ ∑ i ∈ Finset.range n, (1-r i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP0 : 0 ≤ ∏ i ∈ Finset.range n, r i := Finset.prod_nonneg (fun i _ => hr0 i)
    have hP1 : (∏ i ∈ Finset.range n, r i) ≤ 1 := Finset.prod_le_one₀ (fun i _ => hr0 i) (fun i _ => hr1 i)
    rw [Finset.prod_range_succ,Finset.sum_range_succ]
    have hmul := mul_nonneg (sub_nonneg.mpr hP1) (sub_nonneg.mpr (hr1 n))
    nlinarith

theorem blaschkePrefix_norm_sub_sq_le (a : ℕ → Disk) (n k : ℕ) :
    ‖toL2 (blaschkePrefix a n) - toL2 (blaschkePrefix a (n+k))‖^2 ≤
      2 * ∑ j ∈ Finset.range k, (1-‖(a (j+n)).val‖) := by
  rw [blaschkePrefix_norm_sub_sq]
  exact mul_le_mul_of_nonneg_left
    (one_sub_prod_range_le (fun j => ‖(a (j+n)).val‖) (fun j => norm_nonneg _)
      (fun j => (a (j+n)).property.le) k) (by norm_num)

theorem blaschkeHardyPrefix_cauchy (a : ℕ → Disk)
    (ha : Summable (fun n => 1-‖(a n).val‖)) : CauchySeq (blaschkeHardyPrefix a) := by
  have hc : CauchySeq (fun n => ∑ i ∈ Finset.range n, (1-‖(a i).val‖)) :=
    ha.hasSum.tendsto_sum_nat.cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs := hN (N+k) (Nat.le_add_right N k)
  rw [dist_eq_norm,Real.norm_eq_abs,Finset.sum_range_add] at hs
  have ht : (∑ j ∈ Finset.range k, (1-‖(a (j+N)).val‖)) < ε^2/2 := by
    simpa only [Nat.add_comm,add_sub_cancel_left] using (le_abs_self _).trans_lt hs
  have hb := blaschkePrefix_norm_sub_sq_le a N k
  rw [dist_comm,dist_eq_norm]
  change ‖toL2 (blaschkePrefix a N)-toL2 (blaschkePrefix a (N+k))‖ < ε
  nlinarith [norm_nonneg (toL2 (blaschkePrefix a N)-toL2 (blaschkePrefix a (N+k)))]

/-- Summability of the actual zero defects produces a genuine unimodular Hardy
boundary function for the canonically normalized infinite product, with phase exactly one. -/
theorem exists_blaschkeInner (a : ℕ → Disk)
    (ha : Summable (fun n => 1-‖(a n).val‖)) :
    ∃ u : BoundaryLInf, IsInner u ∧ HasBlaschkeZeros u a ∧
      ∀ z ∈ disk, innerValue u z = ∏' n, blaschkeFactor (a n) z := by
  let f : Hardy := limUnder atTop (blaschkeHardyPrefix a)
  have ht : Tendsto (blaschkeHardyPrefix a) atTop (𝓝 f) :=
    (blaschkeHardyPrefix_cauchy a ha).tendsto_limUnder
  have hL : Tendsto (fun n => toL2 (blaschkePrefix a n)) atTop (𝓝 f.val) :=
    (hardy.subtypeL.continuous.tendsto f).comp ht
  obtain ⟨s,_hs,hsae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hp : ∀ᵐ t ∂circleMeasure, ∀ n, ‖toL2 (blaschkePrefix a n) t‖ = 1 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [toL2_ae (blaschkePrefix a n),(blaschkePrefix_isInner a n).2] with t he hn
    rw [he,hn]
  have hfunit : ∀ᵐ t ∂circleMeasure, ‖f.val t‖ = 1 := by
    filter_upwards [hsae,hp] with t ht hp
    have hn := ht.norm
    simp_rw [hp] at hn
    exact tendsto_nhds_unique hn tendsto_const_nhds
  have hfinf : MemLp f.val ∞ circleMeasure :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) 1 (hfunit.mono (fun _ h => h.le))
  let u : BoundaryLInf := hfinf.toLp f.val
  have hAE : u =ᵐ[circleMeasure] f.val := hfinf.coeFn_toLp
  have hL2 : toL2 u = f.val := Lp.ext ((toL2_ae u).trans hAE)
  have hu : IsInner u := by
    refine ⟨hL2.symm ▸ f.property,?_⟩
    filter_upwards [hAE,hfunit] with t he hn
    rw [he,hn]
  have hv : ∀ z ∈ disk, innerValue u z = ∏' n, blaschkeFactor (a n) z := by
    intro z hz
    change analyticValue (toL2 u) z = _
    rw [hL2]
    have he := ((hardyEvaluation ⟨z,hz⟩).continuous.tendsto f).comp ht
    change Tendsto (fun n => innerValue (blaschkePrefix a n) z) atTop (𝓝 (analyticValue f.val z)) at he
    have hev (n : ℕ) : innerValue (blaschkePrefix a n) z =
        ∏ j ∈ Finset.range n, blaschkeFactor (a j) z := innerValue_blaschkePrefix a n ⟨z,hz⟩
    simp_rw [hev] at he
    exact tendsto_nhds_unique he (blaschkeFactors_multipliable a ha ⟨z,hz⟩).tendsto_prod_tprod_nat
  exact ⟨u,hu,⟨ha,1,by simp,fun z hz => by simpa only [one_mul] using hv z hz⟩,hv⟩


def dyadicDefect (n : ℕ) : ℝ := (1/2 : ℝ)^(n+1)

theorem dyadicDefect_pos (n : ℕ) : 0 < dyadicDefect n := pow_pos (by norm_num) _

theorem dyadicDefect_le_half (n : ℕ) : dyadicDefect n ≤ 1/2 := by
  unfold dyadicDefect
  rw [pow_succ]
  have h : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem dyadicDefect_strictAnti : StrictAnti dyadicDefect := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hn := dyadicDefect_pos n
  unfold dyadicDefect at hn
  change (1/2 : ℝ)^((n+1)+1) < (1/2 : ℝ)^(n+1)
  rw [pow_succ]
  nlinarith

def dyadicNode (n : ℕ) : Disk :=
  ⟨((1 - dyadicDefect n : ℝ) : ℂ),by
    change ‖((1-dyadicDefect n : ℝ) : ℂ)‖ < 1
    rw [Complex.norm_real,Real.norm_of_nonneg (by have := dyadicDefect_le_half n; linarith)]
    linarith [dyadicDefect_pos n]⟩

theorem dyadicNode_norm (n : ℕ) : ‖(dyadicNode n).val‖ = 1 - dyadicDefect n := by
  change ‖((1-dyadicDefect n : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real,Real.norm_of_nonneg (by have := dyadicDefect_le_half n; linarith)]

theorem dyadicNode_eq (n : ℕ) : (dyadicNode n).val = 1-(2 : ℂ)^(-(n : ℤ)-1) := by
  change ((1-(1/2 : ℝ)^(n+1) : ℝ) : ℂ) = _
  have hz : -(n : ℤ)-1 = -((n+1 : ℕ) : ℤ) := by omega
  rw [hz,zpow_neg,zpow_natCast,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
  norm_num [div_pow,inv_pow]

theorem dyadicNode_injective : Function.Injective dyadicNode := by
  intro m n h
  have he := congrArg (fun z : Disk => z.val.re) h
  change 1-dyadicDefect m = 1-dyadicDefect n at he
  exact dyadicDefect_strictAnti.injective (by linarith)

theorem dyadicNode_summable : Summable (fun n => 1-‖(dyadicNode n).val‖) := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_right (1/2)
  simpa only [dyadicNode_norm,dyadicDefect,sub_sub_cancel,pow_succ] using hs

theorem nonconstant_of_inner_zero (u : BoundaryLInf) (hu : IsInner u)
    (w : Disk) (hw : innerValue u w.val = 0) : Nonconstant u := by
  rintro ⟨c,rfl⟩
  have hc : c = 0 := by
    change analyticValue (toL2 (constLInf c)) w.val = 0 at hw
    rw [toL2_constLInf,constL2_fourier,analyticValue_smul c (fourierBasis (T := 1) 0) w.property] at hw
    have hzero : analyticValue (fourierBasis (T := 1) 0) w.val = 1 := by
      simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 w.val
    simpa only [hzero,mul_one] using hw
  subst c
  have hn := norm_toL2_of_inner (constLInf 0) hu
  rw [toL2_constLInf,constL2_fourier,zero_smul,norm_zero] at hn
  norm_num at hn

/-- The geometric zero sequence in the logarithmic example has an actual
nonconstant inner boundary function, with exactly the prescribed node indexing. -/
theorem exists_dyadicBlaschkeInner :
    ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ HasBlaschkeZeros u dyadicNode := by
  obtain ⟨u,hu,hz,_hv⟩ := exists_blaschkeInner dyadicNode dyadicNode_summable
  exact ⟨u,hu,nonconstant_of_inner_zero u hu (dyadicNode 0)
    (blaschkeNodes_zero u dyadicNode hz 0),hz⟩


theorem finite_geometric_reindex_sum_le {I : Type*} (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset I) (f : I → ℕ) (hf : Set.InjOn f (s : Set I)) :
    (∑ i ∈ s, r^(f i)) ≤ (1-r)⁻¹ := by
  classical
  calc
    (∑ i ∈ s, r^(f i)) = ∑ k ∈ s.image f, r^k := (Finset.sum_image hf).symm
    _ ≤ ∑' k : ℕ, r^k := Summable.sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
      (summable_geometric_of_lt_one hr0 hr1)
    _ = (1-r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- The finite Hilbert-space Schur estimate uses only actual Gram row sums. -/
theorem finite_sum_norm_sq_le_of_gram_rows {I H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : I → H) (C : ℝ)
    (hrow : ∀ s : Finset I, ∀ i ∈ s, (∑ j ∈ s, ‖inner ℂ (k i) (k j)‖) ≤ C)
    (s : Finset I) (c : I → ℂ) :
    ‖∑ i ∈ s, c i • k i‖^2 ≤ C * ∑ i ∈ s, ‖c i‖^2 := by
  classical
  let g i j := ‖inner ℂ (k i) (k j)‖
  have hg : ∀ i j, g i j = g j i := fun i j => norm_inner_symm _ _
  have he : ‖∑ i ∈ s, c i • k i‖^2 ≤
      ∑ i ∈ s, ∑ j ∈ s, ‖c i‖*‖c j‖*g i j := by
    calc
      ‖∑ i ∈ s, c i • k i‖^2 =
          ‖inner ℂ (∑ i ∈ s, c i • k i) (∑ j ∈ s, c j • k j)‖ := by
        rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq]
      _ = ‖∑ i ∈ s, ∑ j ∈ s, conj (c i)*c j*inner ℂ (k i) (k j)‖ := by
        simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,mul_assoc]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖conj (c i)*c j*inner ℂ (k i) (k j)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ = ∑ i ∈ s, ∑ j ∈ s, ‖c i‖*‖c j‖*g i j := by
        simp only [norm_mul,Complex.norm_conj,g]
  have hcol : (∑ i ∈ s, ∑ j ∈ s, ‖c j‖^2*g i j) =
      ∑ i ∈ s, ‖c i‖^2 * ∑ j ∈ s, g i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hg j i]
  have hweighted : (∑ i ∈ s, ∑ j ∈ s, (‖c i‖^2+‖c j‖^2)*g i j) =
      2*(∑ i ∈ s, ‖c i‖^2 * ∑ j ∈ s, g i j) := by
    simp only [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have htwo : 2*(∑ i ∈ s, ∑ j ∈ s, ‖c i‖*‖c j‖*g i j) ≤
      ∑ i ∈ s, ∑ j ∈ s, (‖c i‖^2+‖c j‖^2)*g i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _hj
    calc
      2*(‖c i‖*‖c j‖*g i j) = (2*‖c i‖*‖c j‖)*g i j := by ring
      _ ≤ (‖c i‖^2+‖c j‖^2)*g i j :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖c i‖-‖c j‖)]) (norm_nonneg _)
  have hr : (∑ i ∈ s, ‖c i‖^2 * ∑ j ∈ s, g i j) ≤ C * ∑ i ∈ s, ‖c i‖^2 := by
    calc
      _ ≤ ∑ i ∈ s, ‖c i‖^2*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hrow s i hi) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [hweighted] at htwo
  linarith


theorem finite_geometric_nat_dist_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : Finset ℕ) (n : ℕ) :
    (∑ m ∈ s, r^(Nat.dist n m)) ≤ 2*(1-r)⁻¹ := by
  classical
  have hil : Set.InjOn (fun m : ℕ => n-m) ((s.filter (fun m => m ≤ n)) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change n-x = n-y at hxy
    omega
  have hir : Set.InjOn (fun m : ℕ => m-n) ((s.filter (fun m => ¬m ≤ n)) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change x-n = y-n at hxy
    omega
  have hl := finite_geometric_reindex_sum_le r hr0 hr1 (s.filter (fun m => m ≤ n)) (fun m => n-m) hil
  have hr := finite_geometric_reindex_sum_le r hr0 hr1 (s.filter (fun m => ¬m ≤ n)) (fun m => m-n) hir
  have hel : (∑ m ∈ s.filter (fun m => m ≤ n), r^(Nat.dist n m)) =
      ∑ m ∈ s.filter (fun m => m ≤ n), r^(n-m) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hm).2]
  have her : (∑ m ∈ s.filter (fun m => ¬m ≤ n), r^(Nat.dist n m)) =
      ∑ m ∈ s.filter (fun m => ¬m ≤ n), r^(m-n) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmn := (Finset.mem_filter.mp hm).2
    rw [Nat.dist_eq_sub_of_le (by omega : n ≤ m)]
  have he := Finset.sum_filter_add_sum_filter_not s (fun m => m ≤ n) (fun m => r^(Nat.dist n m))
  rw [hel,her] at he
  linarith

theorem dyadicDefect_add (n k : ℕ) :
    dyadicDefect (n+k) = dyadicDefect n * (1/2 : ℝ)^k := by
  unfold dyadicDefect
  rw [← pow_add]
  congr 1
  omega

theorem dyadic_denominator_pos (i j : ℕ) :
    0 < dyadicDefect i + dyadicDefect j - dyadicDefect i * dyadicDefect j := by
  have hi := dyadicDefect_pos i
  have hj := dyadicDefect_pos j
  have hi1 := dyadicDefect_le_half i
  have hm := mul_nonneg (show 0 ≤ 1-dyadicDefect i by linarith) hj.le
  nlinarith

theorem norm_blaschkeFactor_dyadic (i j : ℕ) :
    ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ =
      |dyadicDefect i-dyadicDefect j| /
        (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j) := by
  have hai : (dyadicNode i).val ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    change 1-dyadicDefect i = 0 at he
    linarith [dyadicDefect_le_half i]
  have hn : ‖(dyadicNode i).val‖ ≠ 0 := norm_ne_zero_iff.mpr hai
  have hnum : ‖(dyadicNode i).val-(dyadicNode j).val‖ =
      |dyadicDefect i-dyadicDefect j| := by
    change ‖((1-dyadicDefect i : ℝ) : ℂ)-((1-dyadicDefect j : ℝ) : ℂ)‖ = _
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have he : (1-dyadicDefect i)-(1-dyadicDefect j) = dyadicDefect j-dyadicDefect i := by ring
    rw [he,abs_sub_comm]
  have hden : ‖1-conj (dyadicNode i).val*(dyadicNode j).val‖ =
      dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j := by
    change ‖1-conj ((1-dyadicDefect i : ℝ) : ℂ)*((1-dyadicDefect j : ℝ) : ℂ)‖ = _
    rw [Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_of_nonneg (by nlinarith [dyadic_denominator_pos i j])]
    ring
  simp only [blaschkeFactor,hai,ite_false,norm_div,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg (dyadicNode i).val),div_self hn,one_mul,hnum,hden]


theorem dyadic_blaschke_bounds_of_lt (i j : ℕ) (hij : i < j) :
    1/3 ≤ ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ∧
    ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ≤ 1 ∧
    1-‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ≤ 2*(1/2 : ℝ)^(j-i) := by
  let s : ℝ := (1/2 : ℝ)^(j-i)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1/2 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hij))
    simpa only [s,hk,dyadicDefect] using dyadicDefect_le_half k
  have hrel : dyadicDefect j = dyadicDefect i*s := by
    have hji : i+(j-i) = j := by omega
    simpa only [hji,s] using dyadicDefect_add i (j-i)
  have hi := dyadicDefect_pos i
  have hj := dyadicDefect_pos j
  have hi1 := dyadicDefect_le_half i
  have hd := dyadic_denominator_pos i j
  have ht : 2*dyadicDefect j ≤ dyadicDefect i := by
    have hm := mul_le_mul_of_nonneg_left hs1 hi.le
    rw [← hrel] at hm
    linarith
  have hm0 := mul_nonneg hi.le hj.le
  have hD : dyadicDefect i ≤ dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j := by
    have hm := mul_nonneg (show 0 ≤ 1-dyadicDefect i by linarith) hj.le
    nlinarith
  have hsm := mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*s by positivity)
  have hsm' : 2*dyadicDefect j ≤
      2*s*(dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j) := by
    nlinarith [hrel]
  rw [norm_blaschkeFactor_dyadic,abs_of_pos (sub_pos.mpr (dyadicDefect_strictAnti hij))]
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_⟩
  · nlinarith
  · nlinarith
  · rw [one_sub_div hd.ne']
    apply (div_le_iff₀ hd).mpr
    change (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j) -
      (dyadicDefect i-dyadicDefect j) ≤
      2*s*(dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j)
    nlinarith

theorem norm_blaschkeFactor_dyadic_comm (i j : ℕ) :
    ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ =
      ‖blaschkeFactor (dyadicNode j) (dyadicNode i).val‖ := by
  rw [norm_blaschkeFactor_dyadic,norm_blaschkeFactor_dyadic,abs_sub_comm]
  congr 1
  ring

theorem dyadic_blaschke_bounds (i j : ℕ) (hij : i ≠ j) :
    1/3 ≤ ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ∧
    ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ≤ 1 ∧
    1-‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ ≤ 2*(1/2 : ℝ)^(Nat.dist i j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · simpa only [Nat.dist_eq_sub_of_le h.le] using dyadic_blaschke_bounds_of_lt i j h
  · rw [norm_blaschkeFactor_dyadic_comm i j,Nat.dist_comm i j]
    simpa only [Nat.dist_eq_sub_of_le h.le] using dyadic_blaschke_bounds_of_lt j i h

theorem dyadic_blaschke_log_lower (i j : ℕ) (hij : i ≠ j) :
    -6*(1/2 : ℝ)^(Nat.dist i j) ≤
      Real.log ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖ := by
  let r := ‖blaschkeFactor (dyadicNode i) (dyadicNode j).val‖
  obtain ⟨hr3,hr1,hrd⟩ := dyadic_blaschke_bounds i j hij
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hri : r⁻¹ ≤ 3 := (inv_le_iff_one_le_mul₀ hr0).mpr (by dsimp [r]; linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hr0
  have hm := mul_le_mul_of_nonneg_left hri (show 0 ≤ 1-r by dsimp [r]; linarith)
  have he : 1-r⁻¹ = -(1-r)*r⁻¹ := by
    rw [neg_mul,sub_mul,mul_inv_cancel₀ hr0.ne']
    ring
  rw [he] at hl
  change -6*(1/2 : ℝ)^(Nat.dist i j) ≤ Real.log r
  change 1-r ≤ 2*(1/2 : ℝ)^(Nat.dist i j) at hrd
  nlinarith


/-- A conservative uniform lower bound for every finite omitted zero product. -/
theorem dyadic_blaschke_finite_product_lower (n : ℕ) (s : Finset ℕ) (hn : n ∉ s) :
    Real.exp (-24) ≤ ∏ m ∈ s, ‖blaschkeFactor (dyadicNode m) (dyadicNode n).val‖ := by
  have hs : (∑ m ∈ s, (1/2 : ℝ)^(Nat.dist n m)) ≤ 4 := by
    convert finite_geometric_nat_dist_sum_le (1/2) (by norm_num) (by norm_num) s n using 1
    norm_num
  have hsum : -24 ≤ ∑ m ∈ s, -6*(1/2 : ℝ)^(Nat.dist n m) := by
    rw [← Finset.mul_sum]
    linarith
  calc
    Real.exp (-24) ≤ Real.exp (∑ m ∈ s, -6*(1/2 : ℝ)^(Nat.dist n m)) := Real.exp_le_exp.mpr hsum
    _ = ∏ m ∈ s, Real.exp (-6*(1/2 : ℝ)^(Nat.dist n m))  := Real.exp_sum s _
    _ ≤ ∏ m ∈ s, ‖blaschkeFactor (dyadicNode m) (dyadicNode n).val‖ := by
      apply Finset.prod_le_prod₀
      · intro m _hm
        exact (Real.exp_pos _).le
      · intro m hm
        have hmn : m ≠ n := fun h => hn (h ▸ hm)
        have hb := dyadic_blaschke_bounds m n hmn
        have hr : 0 < ‖blaschkeFactor (dyadicNode m) (dyadicNode n).val‖ := by linarith [hb.1]
        have hl := dyadic_blaschke_log_lower m n hmn
        rw [Nat.dist_comm m n] at hl
        exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log hr)

/-- The actual omitted product retains the same lower bound under any injective
enumeration of other indices; this includes the swap-and-tail used below. -/
theorem dyadic_blaschke_omitted_product_lower (n : ℕ) (f : ℕ → ℕ)
    (hf : Function.Injective f) (hn : ∀ k, f k ≠ n) :
    Real.exp (-24) ≤ ‖∏' k, blaschkeFactor (dyadicNode (f k)) (dyadicNode n).val‖ := by
  have ha : Summable (fun k => 1-‖(dyadicNode (f k)).val‖) := dyadicNode_summable.comp_injective hf
  have ht := (blaschkeFactors_multipliable (fun k => dyadicNode (f k)) ha (dyadicNode n)).tendsto_prod_tprod_nat.norm
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  apply Filter.Eventually.of_forall
  intro N
  change Real.exp (-24) ≤ ‖∏ k ∈ Finset.range N, blaschkeFactor (dyadicNode (f k)) (dyadicNode n).val‖
  rw [norm_prod]
  have hp : (∏ k ∈ Finset.range N, ‖blaschkeFactor (dyadicNode (f k)) (dyadicNode n).val‖) =
      ∏ m ∈ (Finset.range N).image f, ‖blaschkeFactor (dyadicNode m) (dyadicNode n).val‖ :=
    (Finset.prod_image (f := fun m => ‖blaschkeFactor (dyadicNode m) (dyadicNode n).val‖)
      (s := Finset.range N) (g := f) hf.injOn).symm
  rw [hp]
  apply dyadic_blaschke_finite_product_lower
  intro hmem
  obtain ⟨k,_hk,he⟩ := Finset.mem_image.mp hmem
  exact hn k he


theorem dyadic_denominator_norm (i j : ℕ) :
    ‖1-conj (dyadicNode i).val*(dyadicNode j).val‖ =
      dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j := by
  change ‖1-conj ((1-dyadicDefect i : ℝ) : ℂ)*((1-dyadicDefect j : ℝ) : ℂ)‖ = _
  rw [Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_of_nonneg (by nlinarith [dyadic_denominator_pos i j])]
  ring

theorem dyadic_nodeKernel_gram_norm (i j : ℕ) :
    ‖inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j))‖ =
      Real.sqrt (1-(1-dyadicDefect i)^2) * Real.sqrt (1-(1-dyadicDefect j)^2) /
        (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j) := by
  rw [inner_hardyNodeVector]
  change ‖(Real.sqrt (1-‖(dyadicNode i).val‖^2) : ℂ)*
    analyticValue ((Real.sqrt (1-‖(dyadicNode j).val‖^2) : ℂ) • (szegoKernel (dyadicNode j)).val) (dyadicNode i).val‖ = _
  rw [analyticValue_smul _ _ (dyadicNode i).property,analyticValue_szegoKernel _ (dyadicNode i).property]
  rw [norm_mul,norm_mul,norm_inv,dyadic_denominator_norm j i]
  rw [Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg (1-‖(dyadicNode i).val‖^2)),
    Real.norm_of_nonneg (Real.sqrt_nonneg (1-‖(dyadicNode j).val‖^2))]
  simp only [dyadicNode_norm]
  rw [div_eq_mul_inv]
  rw [show dyadicDefect j+dyadicDefect i-dyadicDefect j*dyadicDefect i =
    dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j by ring]
  ring

theorem dyadic_nodeKernel_gram_norm_sq (i j : ℕ) :
    ‖inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j))‖^2 =
      (dyadicDefect i*(2-dyadicDefect i)*(dyadicDefect j*(2-dyadicDefect j))) /
        (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j)^2 := by
  have hi : 0 ≤ 1-(1-dyadicDefect i)^2 := by
    have h0 := dyadicDefect_pos i
    have h1 := dyadicDefect_le_half i
    nlinarith
  have hj : 0 ≤ 1-(1-dyadicDefect j)^2 := by
    have h0 := dyadicDefect_pos j
    have h1 := dyadicDefect_le_half j
    nlinarith
  rw [dyadic_nodeKernel_gram_norm,div_pow,mul_pow,Real.sq_sqrt hi,Real.sq_sqrt hj]
  congr 1
  ring

theorem dyadic_nodeKernel_gram_norm_sq_le_of_le (i j : ℕ) (hij : i ≤ j) :
    ‖inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j))‖^2 ≤
      4*(1/2 : ℝ)^(j-i) := by
  have hi := dyadicDefect_pos i
  have hj := dyadicDefect_pos j
  have hi1 := dyadicDefect_le_half i
  have hj1 := dyadicDefect_le_half j
  have hd := dyadic_denominator_pos i j
  have hD : dyadicDefect i ≤ dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j := by
    have hm := mul_nonneg (show 0 ≤ 1-dyadicDefect i by linarith) hj.le
    nlinarith
  have hD2 : (dyadicDefect i)^2 ≤
      (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j)^2 := by nlinarith
  have hnum : dyadicDefect i*(2-dyadicDefect i)*(dyadicDefect j*(2-dyadicDefect j)) ≤
      4*dyadicDefect i*dyadicDefect j := by
    have hli : dyadicDefect i*(2-dyadicDefect i) ≤ 2*dyadicDefect i := by nlinarith
    have hlj : dyadicDefect j*(2-dyadicDefect j) ≤ 2*dyadicDefect j := by nlinarith
    have hlj0 : 0 ≤ dyadicDefect j*(2-dyadicDefect j) :=
      mul_nonneg hj.le (by linarith)
    have hm := mul_le_mul hli hlj hlj0 (by positivity : 0 ≤ 2*dyadicDefect i)
    nlinarith
  have hrel : dyadicDefect j = dyadicDefect i*(1/2 : ℝ)^(j-i) := by
    have hji : i+(j-i) = j := by omega
    simpa only [hji] using dyadicDefect_add i (j-i)
  rw [dyadic_nodeKernel_gram_norm_sq]
  calc
    _ ≤ (4*dyadicDefect i*dyadicDefect j) /
        (dyadicDefect i+dyadicDefect j-dyadicDefect i*dyadicDefect j)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ (4*dyadicDefect i*dyadicDefect j)/(dyadicDefect i)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hi) hD2
    _ = 4*(1/2 : ℝ)^(j-i) := by
      rw [hrel]
      field_simp

theorem dyadic_nodeKernel_gram_norm_le (i j : ℕ) :
    ‖inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j))‖ ≤
      2*(3/4 : ℝ)^(Nat.dist i j) := by
  have hsq : ∀ i j : ℕ, i ≤ j →
      ‖inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j))‖ ≤
        2*(3/4 : ℝ)^(j-i) := by
    intro i j hij
    have h := dyadic_nodeKernel_gram_norm_sq_le_of_le i j hij
    have hp : (1/2 : ℝ)^(j-i) ≤ ((3/4 : ℝ)^(j-i))^2 := by
      calc
        _ ≤ ((3/4 : ℝ)^2)^(j-i) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ = _ := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    have hn : 0 ≤ (3/4 : ℝ)^(j-i) := by positivity
    nlinarith [norm_nonneg (inner ℂ (hardyNodeVector (dyadicNode i)) (hardyNodeVector (dyadicNode j)))]
  rcases le_total i j with h | h
  · simpa only [Nat.dist_eq_sub_of_le h] using hsq i j h
  · rw [norm_inner_symm,Nat.dist_comm i j]
    simpa only [Nat.dist_eq_sub_of_le h] using hsq j i h

/-- The actual normalized Hardy kernels at the prescribed dyadic nodes have a
uniform finite Bessel bound, obtained from their literal Gram kernel. -/
theorem dyadic_nodeKernel_bessel (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ s, c i • hardyNodeVector (dyadicNode i)‖^2 ≤ 16*∑ i ∈ s, ‖c i‖^2 := by
  apply finite_sum_norm_sq_le_of_gram_rows _ 16 ?_ s c
  intro t i _hi
  have hr : (∑ j ∈ t, (3/4 : ℝ)^(Nat.dist i j)) ≤ 8 := by
    convert finite_geometric_nat_dist_sum_le (3/4) (by norm_num) (by norm_num) t i using 1
    norm_num
  calc
    _ ≤ ∑ j ∈ t, 2*(3/4 : ℝ)^(Nat.dist i j) :=
      Finset.sum_le_sum (fun j _ => dyadic_nodeKernel_gram_norm_le i j)
    _ = 2*∑ j ∈ t, (3/4 : ℝ)^(Nat.dist i j) := by rw [Finset.mul_sum]
    _ ≤ 16 := by linarith


/-- The conjugation for one actual Blaschke factor fixes its normalized kernel
up to precisely the unimodular factor phase. -/
theorem conjugation_blaschkeBoundary_node (a : Disk) :
    conjugation (blaschkeBoundary a) (hardyNodeVector a).val =
      blaschkePhase a • (hardyNodeVector a).val := by
  apply Lp.ext
  filter_upwards [conjugation_ae (blaschkeBoundary a) (hardyNodeVector a).val,
    blaschkeBoundary_ae a,nodeKernel_hardyNodeVector a,
    Lp.coeFn_smul (blaschkePhase a) (hardyNodeVector a).val] with t hc hb hk hs
  have hz : ‖fourier (T := 1) 1 t‖ = 1 := by simp
  have hd : 1-a.val*conj (fourier (T := 1) 1 t) ≠ 0 := by
    have hn : ‖a.val*conj (fourier (T := 1) 1 t)‖ < 1 := by
      have ha : ‖a.val‖ < 1 := a.property
      simpa only [norm_mul,Complex.norm_conj,hz,mul_one] using ha
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one] at he
    linarith
  have he : (fourier (T := 1) 1 t-a.val)*conj (fourier (T := 1) 1 t) =
      1-a.val*conj (fourier (T := 1) 1 t) := by
    rw [sub_mul,Complex.mul_conj',hz]
    norm_num
  change (blaschkePhase a • (hardyNodeVector a).val) t =
    blaschkePhase a * ((hardyNodeVector a).val t) at hs
  rw [hc,hb,hs,hk]
  simp only [div_eq_mul_inv,map_mul,map_inv₀,map_sub,map_one,Complex.conj_conj,Complex.conj_ofReal]
  calc
    _ = blaschkePhase a*(Real.sqrt (1-‖a.val‖^2) : ℂ)*
        (1-conj a.val*fourier (T := 1) 1 t)⁻¹*
        (((fourier (T := 1) 1 t-a.val)*conj (fourier (T := 1) 1 t))*
          (1-a.val*conj (fourier (T := 1) 1 t))⁻¹) := by ring
    _ = blaschkePhase a*(Real.sqrt (1-‖a.val‖^2) : ℂ)*
        (1-conj a.val*fourier (T := 1) 1 t)⁻¹ := by rw [he,mul_inv_cancel₀ hd,mul_one]
    _ = _ := by ring

theorem conjugation_factor_node (u v : BoundaryLInf) (a : Disk)
    (hfactor : u = multiplyInf (blaschkeBoundary a) v) :
    conjugation u (hardyNodeVector a).val =
      blaschkePhase a • multiply v (hardyNodeVector a).val := by
  change multiply u (multiply (star coordinate) (star (hardyNodeVector a).val)) = _
  rw [hfactor,multiplyInf_comm,← multiply_assoc]
  change multiply v (conjugation (blaschkeBoundary a) (hardyNodeVector a).val) = _
  rw [conjugation_blaschkeBoundary_node,map_smul]

/-- Literal model conjugation, bundled only with its already proved antiisometry. -/
def modelConjugationIsometry (u : BoundaryLInf) (hu : IsInner u) :
    Model u →ₗᵢ⋆[ℂ] Model u :=
  (conjugateModelUnitary u hu).toLinearIsometry.comp (modelStarIsometry u)

@[simp] theorem modelConjugationIsometry_val (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    (modelConjugationIsometry u hu f).val = conjugation u f.val := rfl


/-- Omitting one prescribed zero gives an actual inner quotient whose value at the
removed zero has the proved uniform lower bound. No derivative or boundary
factorization theorem is assumed. -/
theorem exists_dyadic_inner_factor (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (n : ℕ) :
    ∃ v : BoundaryLInf, IsInner v ∧
      u = multiplyInf (blaschkeBoundary (dyadicNode n)) v ∧
      Real.exp (-24) ≤ ‖innerValue v (dyadicNode n).val‖ := by
  classical
  let e : ℕ ≃ ℕ := Equiv.swap 0 n
  let tail : ℕ → Disk := fun k => dyadicNode (e (k+1))
  have he0 : e 0 = n := Equiv.swap_apply_left 0 n
  have hfi : Function.Injective (fun k : ℕ => e (k+1)) :=
    e.injective.comp (fun i j h => Nat.add_right_cancel h)
  have hfn : ∀ k : ℕ, e (k+1) ≠ n := by
    intro k h
    have he := e.injective (h.trans he0.symm)
    omega
  have ht : Summable (fun k => 1-‖(tail k).val‖) := dyadicNode_summable.comp_injective hfi
  obtain ⟨v₀,hv₀,_hvzeros,hvprod⟩ := exists_blaschkeInner tail ht
  obtain ⟨α,hα,huval⟩ := hz.2
  let v : BoundaryLInf := α • v₀
  have hv : IsInner v := by
    constructor
    · rw [malmquist_toL2_smul]
      exact hardy.smul_mem α hv₀.1
    · filter_upwards [Lp.coeFn_smul α v₀,hv₀.2] with t hs ht
      change (α • v₀) t = α*v₀ t at hs
      change ‖(α • v₀) t‖ = 1
      rw [hs,norm_mul,hα,ht,mul_one]
  have hval (z : Disk) : innerValue v z.val =
      α*∏' k, blaschkeFactor (dyadicNode (e (k+1))) z.val := by
    change analyticValue (toL2 (α • v₀)) z.val = _
    rw [malmquist_toL2_smul,analyticValue_smul α _ z.property]
    change α*innerValue v₀ z.val = _
    rw [hvprod _ z.property]
  have hfactor : u = multiplyInf (blaschkeBoundary (dyadicNode n)) v := by
    apply boundedHardy_boundary_ext _ _ hu.1
      (isInner_multiplyInf _ _ (blaschkeBoundary_isInner (dyadicNode n)) hv).1
    intro z
    rw [huval _ z.property]
    change _ = analyticValue (toL2 (multiplyInf (blaschkeBoundary (dyadicNode n)) v)) z.val
    rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkeBoundary_hardy (dyadicNode n)) ⟨toL2 v,hv.1⟩ z]
    change _ = innerValue (blaschkeBoundary (dyadicNode n)) z.val*innerValue v z.val
    rw [innerValue_blaschkeBoundary,hval]
    have hp := Multipliable.prod_mul_tprod_nat_mul'
      (f := fun k => blaschkeFactor (dyadicNode (e k)) z.val) (k := 1)
      (blaschkeFactors_multipliable tail ht z)
    simp only [Finset.prod_range_one,he0] at hp
    have he := e.tprod_eq (fun k => blaschkeFactor (dyadicNode k) z.val)
    rw [he] at hp
    rw [← hp]
    ring
  refine ⟨v,hv,hfactor,?_⟩
  rw [hval,norm_mul,hα,one_mul]
  exact dyadic_blaschke_omitted_product_lower n (fun k => e (k+1)) hfi hfn


theorem node_inner_multiply (a : Disk) (v : BoundaryLInf) (hv : toL2 v ∈ hardy) (f : Hardy) :
    inner ℂ (hardyNodeVector a).val (multiply v f.val) =
      innerValue v a.val * inner ℂ (hardyNodeVector a) f := by
  have hp := multiply_mem_hardy v hv f.val f.property
  change inner ℂ (hardyNodeVector a) (⟨multiply v f.val,hp⟩ : Hardy) = _
  rw [inner_hardyNodeVector,analyticValue_multiply v hv f a,inner_hardyNodeVector]
  ring

def dyadicConjugateNode (u : BoundaryLInf) (hu : IsInner u) (hz : HasBlaschkeZeros u dyadicNode)
    (n : ℕ) : Model u :=
  modelConjugationIsometry u hu (blaschkeNodeModel u hu dyadicNode hz n)

theorem dyadicConjugateNode_pairing (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (m n : ℕ) (v : BoundaryLInf)
    (hv : toL2 v ∈ hardy) (hf : u = multiplyInf (blaschkeBoundary (dyadicNode n)) v) :
    inner ℂ (blaschkeNodeModel u hu dyadicNode hz m) (dyadicConjugateNode u hu hz n) =
      blaschkePhase (dyadicNode n)*innerValue v (dyadicNode m).val*
        inner ℂ (blaschkeNodeModel u hu dyadicNode hz m) (blaschkeNodeModel u hu dyadicNode hz n) := by
  change inner ℂ (hardyNodeVector (dyadicNode m)).val
      (conjugation u (hardyNodeVector (dyadicNode n)).val) =
    blaschkePhase (dyadicNode n)*innerValue v (dyadicNode m).val*
      inner ℂ (hardyNodeVector (dyadicNode m)) (hardyNodeVector (dyadicNode n))
  rw [conjugation_factor_node u v _ hf,inner_smul_right,
    node_inner_multiply (dyadicNode m) v hv (hardyNodeVector (dyadicNode n))]
  ring

theorem dyadicConjugateNode_orthogonal (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (m n : ℕ) (hmn : m ≠ n) :
    inner ℂ (blaschkeNodeModel u hu dyadicNode hz m) (dyadicConjugateNode u hu hz n) = 0 := by
  obtain ⟨v,hv,hf,_hbound⟩ := exists_dyadic_inner_factor u hu hz n
  have hv0 : innerValue v (dyadicNode m).val = 0 := by
    have hzero := blaschkeNodes_zero u dyadicNode hz m
    rw [hf] at hzero
    change analyticValue (toL2 (multiplyInf (blaschkeBoundary (dyadicNode n)) v)) (dyadicNode m).val = 0 at hzero
    rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkeBoundary_hardy (dyadicNode n))
      ⟨toL2 v,hv.1⟩ (dyadicNode m),innerValue_blaschkeBoundary] at hzero
    change blaschkeFactor (dyadicNode n) (dyadicNode m).val * innerValue v (dyadicNode m).val = 0 at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (blaschkeFactor_ne_zero _ _
      (fun h => hmn (dyadicNode_injective h)))
  rw [dyadicConjugateNode_pairing u hu hz m n v hv.1 hf,hv0,mul_zero,zero_mul]

def dyadicNodeCoefficient (u : BoundaryLInf) (hu : IsInner u) (hz : HasBlaschkeZeros u dyadicNode)
    (n : ℕ) : ℂ :=
  inner ℂ (blaschkeNodeModel u hu dyadicNode hz n) (dyadicConjugateNode u hu hz n)

theorem dyadicNodeCoefficient_norm_lower (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (n : ℕ) :
    Real.exp (-24) ≤ ‖dyadicNodeCoefficient u hu hz n‖ := by
  obtain ⟨v,hv,hf,hbound⟩ := exists_dyadic_inner_factor u hu hz n
  have hk : ‖blaschkeNodeModel u hu dyadicNode hz n‖ = 1 := norm_hardyNodeVector (dyadicNode n)
  unfold dyadicNodeCoefficient
  rw [dyadicConjugateNode_pairing u hu hz n n v hv.1 hf,
    inner_self_eq_one_of_norm_eq_one hk,mul_one,norm_mul,blaschkePhase_norm,one_mul]
  exact hbound

theorem dyadicNodeCoefficient_ne_zero (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (n : ℕ) : dyadicNodeCoefficient u hu hz n ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt ((Real.exp_pos (-24)).trans_le (dyadicNodeCoefficient_norm_lower u hu hz n)))

def dyadicBiorthogonalNode (u : BoundaryLInf) (hu : IsInner u) (hz : HasBlaschkeZeros u dyadicNode)
    (n : ℕ) : Model u :=
  (dyadicNodeCoefficient u hu hz n)⁻¹ • dyadicConjugateNode u hu hz n

theorem dyadicBiorthogonalNode_pairing (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (m n : ℕ) :
    inner ℂ (blaschkeNodeModel u hu dyadicNode hz m) (dyadicBiorthogonalNode u hu hz n) =
      if m = n then 1 else 0 := by
  unfold dyadicBiorthogonalNode
  rw [inner_smul_right (blaschkeNodeModel u hu dyadicNode hz m) (dyadicConjugateNode u hu hz n)]
  by_cases h : m = n
  · subst m
    rw [ite_eq_left rfl]
    exact inv_mul_cancel₀ (dyadicNodeCoefficient_ne_zero u hu hz n)
  · rw [ite_eq_right h,dyadicConjugateNode_orthogonal u hu hz m n h,mul_zero]


theorem dyadic_modelNode_bessel (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ s, c i • blaschkeNodeModel u hu dyadicNode hz i‖^2 ≤ 16*∑ i ∈ s, ‖c i‖^2 := by
  have he : modelHardyIsometry u (∑ i ∈ s, c i • blaschkeNodeModel u hu dyadicNode hz i) =
      ∑ i ∈ s, c i • hardyNodeVector (dyadicNode i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smul]
    rfl
  have hn := congrArg norm he
  rw [LinearIsometry.norm_map] at hn
  rw [hn]
  exact dyadic_nodeKernel_bessel s c

theorem dyadicConjugateNode_bessel (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ s, c i • dyadicConjugateNode u hu hz i‖^2 ≤ 16*∑ i ∈ s, ‖c i‖^2 := by
  have he : modelConjugationIsometry u hu
      (∑ i ∈ s, conj (c i) • blaschkeNodeModel u hu dyadicNode hz i) =
      ∑ i ∈ s, c i • dyadicConjugateNode u hu hz i := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smulₛₗ,Complex.conj_conj]
    rfl
  have hn := congrArg norm he
  rw [LinearIsometry.norm_map] at hn
  rw [← hn]
  simpa only [Complex.norm_conj] using dyadic_modelNode_bessel u hu hz s (fun i => conj (c i))

theorem dyadicNodeCoefficient_inv_norm_le (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (n : ℕ) :
    ‖(dyadicNodeCoefficient u hu hz n)⁻¹‖ ≤ Real.exp 24 := by
  rw [norm_inv]
  calc
    _ ≤ (Real.exp (-24))⁻¹ := inv_anti₀ (Real.exp_pos _) (dyadicNodeCoefficient_norm_lower u hu hz n)
    _ = _ := by rw [← Real.exp_neg]; norm_num

theorem dyadicBiorthogonalNode_bessel (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ s, c i • dyadicBiorthogonalNode u hu hz i‖^2 ≤
      (4*Real.exp 24)^2 * ∑ i ∈ s, ‖c i‖^2 := by
  have hb := dyadicConjugateNode_bessel u hu hz s
    (fun i => c i*(dyadicNodeCoefficient u hu hz i)⁻¹)
  simp only [dyadicBiorthogonalNode,smul_smul]
  calc
    _ ≤ 16*∑ i ∈ s, ‖c i*(dyadicNodeCoefficient u hu hz i)⁻¹‖^2 := hb
    _ ≤ 16*∑ i ∈ s, ‖c i‖^2*(Real.exp 24)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (Real.exp_pos 24).le).mpr
          (dyadicNodeCoefficient_inv_norm_le u hu hz i)) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

open scoped Classical in
/-- Finite biorthogonality and an upper bound for the dual family give a lower
bound for the original family by ordinary Hilbert-space Cauchy–Schwarz. -/
theorem finite_lower_of_biorthogonal_bessel {I H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (k h : I → H) (C : ℝ) (hC : 0 ≤ C)
    (hbi : ∀ i j, inner ℂ (k i) (h j) = if i = j then 1 else 0)
    (hb : ∀ s : Finset I, ∀ c : I → ℂ, ‖∑ i ∈ s, c i • h i‖^2 ≤ C*∑ i ∈ s, ‖c i‖^2)
    (s : Finset I) (c : I → ℂ) :
    (∑ i ∈ s, ‖c i‖^2) ≤ C*‖∑ i ∈ s, c i • k i‖^2 := by
  classical
  have heval (i : I) (hi : i ∈ s) : inner ℂ (k i) (∑ j ∈ s, c j • h j) = c i := by
    simp [inner_sum,inner_smul_right,hbi,hi]
  have hpair : inner ℂ (∑ i ∈ s, c i • k i) (∑ i ∈ s, c i • h i) =
      ((∑ i ∈ s, ‖c i‖^2 : ℝ) : ℂ) := by
    calc
      _ = ∑ i ∈ s, conj (c i)*inner ℂ (k i) (∑ j ∈ s, c j • h j) := by
        simp only [sum_inner,inner_smul_left]
      _ = ∑ i ∈ s, conj (c i)*c i := Finset.sum_congr rfl (fun i hi => by rw [heval i hi])
      _ = _ := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Complex.conj_mul',Complex.ofReal_pow]
  have hsum : 0 ≤ ∑ i ∈ s, ‖c i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnorm := norm_inner_le_norm (𝕜 := ℂ) (∑ i ∈ s, c i • k i) (∑ i ∈ s, c i • h i)
  rw [hpair,Complex.norm_real,Real.norm_of_nonneg hsum] at hnorm
  have hsq := pow_le_pow_left₀ hsum hnorm 2
  rw [mul_pow] at hsq
  by_cases hs : (∑ i ∈ s, ‖c i‖^2) = 0
  · rw [hs]
    exact mul_nonneg hC (sq_nonneg _)
  · have hs0 : 0 < ∑ i ∈ s, ‖c i‖^2 := lt_of_le_of_ne hsum (Ne.symm hs)
    apply (mul_le_mul_iff_left₀ hs0).mp
    calc
      _ = (∑ i ∈ s, ‖c i‖^2)^2 := by ring
      _ ≤ ‖∑ i ∈ s, c i • k i‖^2 * ‖∑ i ∈ s, c i • h i‖^2 := hsq
      _ ≤ ‖∑ i ∈ s, c i • k i‖^2 * (C*∑ i ∈ s, ‖c i‖^2) :=
        mul_le_mul_of_nonneg_left (hb s c) (sq_nonneg _)
      _ = _ := by ring


theorem dyadic_finiteRieszModelBounds (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      (∑ i ∈ s, ‖c i‖^2) ≤ C^2*‖∑ i ∈ s, c i • blaschkeNodeModel u hu dyadicNode hz i‖^2 ∧
      ‖∑ i ∈ s, c i • blaschkeNodeModel u hu dyadicNode hz i‖^2 ≤ C^2*∑ i ∈ s, ‖c i‖^2 := by
  let C : ℝ := 4*Real.exp 24
  have hC : 0 < C := by dsimp [C]; positivity
  have hC16 : 16 ≤ C^2 := by
    have hM : 1 ≤ Real.exp (24 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp [C]
    nlinarith [Real.exp_pos (24 : ℝ)]
  refine ⟨C,hC,fun s c => ⟨?_,?_⟩⟩
  · exact finite_lower_of_biorthogonal_bessel
      (blaschkeNodeModel u hu dyadicNode hz) (dyadicBiorthogonalNode u hu hz)
      (C^2) (sq_nonneg C) (fun i j => by
        by_cases h : i = j
        · simpa only [ite_eq_left h] using dyadicBiorthogonalNode_pairing u hu hz i j
        · simpa only [ite_eq_right h] using dyadicBiorthogonalNode_pairing u hu hz i j)
      (dyadicBiorthogonalNode_bessel u hu hz) s c
  · exact (dyadic_modelNode_bessel u hu hz s c).trans
      (mul_le_mul_of_nonneg_right hC16 (Finset.sum_nonneg (fun i _ => sq_nonneg ‖c i‖)))

/-- The exact dyadic nodes have actual Riesz synthesis on their full Blaschke model,
proved without first assuming functional interpolation. -/
theorem dyadicRieszSynthesis (u : BoundaryLInf) (hu : IsInner u)
    (hz : HasBlaschkeZeros u dyadicNode) :
    ∃ R : SequenceL2 ≃L[ℂ] Model u, RieszSynthesis u dyadicNode R := by
  obtain ⟨C,hC,hb⟩ := dyadic_finiteRieszModelBounds u hu hz
  let k := blaschkeNodeModel u hu dyadicNode hz
  let S := synthesisOperator k C hC (fun s c => (hb s c).2)
  have hAnti := synthesis_antilipschitz k C hC hb
  have hRange : S.range = ⊤ := (synthesis_range k C hC hb).trans
    (Submodule.dense_iff_topologicalClosure_eq_top.mp
      (blaschkeNodes_dense_of_division blaschkeHardyDivision u hu dyadicNode dyadicNode_injective hz))
  let R := ContinuousLinearEquiv.ofBijective S (LinearMap.ker_eq_bot.mpr hAnti.injective) hRange
  refine ⟨R,fun n => ?_⟩
  change NodeKernel (dyadicNode n) (S (lp.single 2 n (1 : ℂ))).val
  rw [show S (lp.single 2 n (1 : ℂ)) = k n from synthesis_single k C hC hb n]
  exact blaschkeNodeModel_kernel u hu dyadicNode hz n

/-- Functional H∞ interpolation for precisely the geometric nodes in the paper,
derived from the actual Riesz family and the proved simple-Blaschke lift. -/
theorem dyadicNode_interpolating : Interpolating dyadicNode := by
  obtain ⟨u,hu,hn,hz⟩ := exists_dyadicBlaschkeInner
  obtain ⟨R,hR⟩ := dyadicRieszSynthesis u hu hz
  exact interpolating_of_riesz u hu hn dyadicNode dyadicNode_injective hz R hR

theorem exists_dyadicInterpolatingBlaschke :
    ∃ u : BoundaryLInf, IsInner u ∧ Nonconstant u ∧ HasBlaschkeZeros u dyadicNode ∧
      Interpolating dyadicNode := by
  obtain ⟨u,hu,hn,hz⟩ := exists_dyadicBlaschkeInner
  exact ⟨u,hu,hn,hz,dyadicNode_interpolating⟩


end TTO.Paper.Proved
