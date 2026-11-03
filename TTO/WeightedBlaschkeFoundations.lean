/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.BlaschkeBoundaryFoundations
public import TTO.SchattenAveragingFoundations

/-! Weighted trace-class synthesis over arbitrary infinite simple Blaschke zero sequences. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The source's omitted-factor separation product; the omitted index contributes the unit. -/
def blaschkeSeparationProduct (a : ℕ → Disk) (n : ℕ) : ℝ :=
  ∏' m : ℕ, if m=n then 1 else ‖blaschkeFactor (a m) (a n).val‖

section RankOne
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem schatten_one_of_rank_le_one (A : H →L[ℂ] H) (hRank : A.rank ≤ (1 : Cardinal)) :
    Schatten 1 A ∧ schattenNorm 1 A=‖A‖ := by
  refine ⟨finiteRankSchatten A ⟨1,hRank⟩ 1 (by norm_num),?_⟩
  unfold schattenNorm
  simp only [Real.rpow_one,one_div_one]
  rw [tsum_eq_single 0]
  · simp only [approximationNumber_index_zero,coe_nnnorm]
  · intro n hn
    have h1n : (1 : Cardinal) ≤ (n : Cardinal) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    rw [approximationNumber_eq_zero_of_rank_le A n (hRank.trans h1n),NNReal.coe_zero]

end RankOne

/-- An analytic creator vanishing at every simple node except one has rank at most one.
No Riesz or interpolation property is used. -/
theorem analytic_tto_rank_le_one_of_node_zeros
    (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk) (hi : Function.Injective a)
    (hz : HasBlaschkeZeros u a) (φ : Hardy) (A : Model u →L[ℂ] Model u)
    (hA : RepresentsTTO u φ.val A) (n : ℕ)
    (hZero : ∀ m, m≠n → analyticValue φ.val (a m).val=0) :
    A.rank ≤ (1 : Cardinal) := by
  let k := blaschkeNodeModel u hu a hz
  let V : Submodule ℂ (Model u) := Submodule.span ℂ ({k n} : Set (Model u))
  let W : Submodule ℂ (Model u) := V.comap A.adjoint.toLinearMap
  have hVclosed : IsClosed (V : Set (Model u)) := V.closed_of_finiteDimensional
  have hWclosed : IsClosed (W : Set (Model u)) := hVclosed.preimage A.adjoint.continuous
  have hSpan : Submodule.span ℂ (Set.range k) ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨m,rfl⟩
    change A.adjoint (k m)∈V
    rw [analytic_tto_node_adjoint u hu φ A hA (a m) (k m) (blaschkeNodeModel_kernel u hu a hz m)]
    by_cases hm : m=n
    · subst m
      exact V.smul_mem _ (Submodule.subset_span (Set.mem_singleton (k n)))
    · rw [hZero m hm,map_zero,zero_smul]
      exact V.zero_mem
  have hDense : Dense (Submodule.span ℂ (Set.range k) : Set (Model u)) :=
    blaschkeNodes_dense_of_division blaschkeHardyDivision u hu a hi hz
  have hTop : W=⊤ := by
    apply top_unique
    rw [← Submodule.dense_iff_topologicalClosure_eq_top.mp hDense]
    exact Submodule.topologicalClosure_minimal _ hSpan hWclosed
  have hRange : A.adjoint.range ≤ V := by
    rintro y ⟨x,rfl⟩
    have hx : x∈W := by rw [hTop]; exact Submodule.mem_top
    exact hx
  have hVrank : Module.rank ℂ V ≤ (1 : Cardinal) := by
    simpa only [V,Cardinal.mk_singleton] using rank_span_le ({k n} : Set (Model u))
  have hAdj : A.adjoint.rank ≤ (1 : Cardinal) := (Submodule.rank_mono hRange).trans hVrank
  simpa using rank_adjoint_le_of_rank_le A.adjoint hAdj

theorem norm_boundedSymbolOperator_inner_le_one (u v : BoundaryLInf) (hv : IsInner v) :
    ‖boundedSymbolOperator u v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(model u).orthogonalProjectionOnto (multiply v f.val)‖ ≤ 1*‖f‖
  calc
    _ ≤ ‖multiply v f.val‖ := ((model u).orthogonalProjectionOnto.le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (model u).orthogonalProjectionOnto_norm_le (norm_nonneg (multiply v f.val)))
    _ = ‖f‖ := (innerMultiplyIsometry v hv).norm_map f.val
    _ = _ := (one_mul ‖f‖).symm

/-- The actual omitted-inner-factor creator is trace class with gauge at most one. -/
theorem omittedInnerCreator_traceClass
    (u v : BoundaryLInf) (hu : IsInner u) (hv : IsInner v)
    (a : ℕ → Disk) (hi : Function.Injective a) (hz : HasBlaschkeZeros u a) (n : ℕ)
    (hFactor : u=multiplyInf (blaschkeBoundary (a n)) v) :
    Schatten 1 (boundedSymbolOperator u v) ∧ schattenNorm 1 (boundedSymbolOperator u v) ≤ 1 := by
  have hZero (m : ℕ) (hm : m≠n) : analyticValue (toL2 v) (a m).val=0 := by
    have hNode := blaschkeNodes_zero u a hz m
    rw [hFactor,innerValue_multiplyInf _ _ (blaschkeBoundary_hardy (a n)) hv.1 (a m),
      innerValue_blaschkeBoundary] at hNode
    exact (mul_eq_zero.mp hNode).resolve_left
      (blaschkeFactor_ne_zero (a n) (a m) (fun h => hm (hi h)))
  have hRank := analytic_tto_rank_le_one_of_node_zeros u hu a hi hz ⟨toL2 v,hv.1⟩
    (boundedSymbolOperator u v) (boundedSymbolOperator_represents u v) n hZero
  obtain ⟨hSp,hNorm⟩ := schatten_one_of_rank_le_one (boundedSymbolOperator u v) hRank
  exact ⟨hSp,hNorm.trans_le (norm_boundedSymbolOperator_inner_le_one u v hv)⟩


/-- The omitted factor is the unit at precisely the removed index. -/
def omittedBlaschkeFactor (a : ℕ → Disk) (n m : ℕ) (z : Disk) : ℂ :=
  if m=n then 1 else blaschkeFactor (a m) z.val

theorem omittedBlaschkeFactors_summable_deviation
    (a : ℕ → Disk) (ha : Summable (fun m => 1-‖(a m).val‖)) (n : ℕ) (z : Disk) :
    Summable (fun m => ‖1-omittedBlaschkeFactor a n m z‖) := by
  apply (ha.mul_left ((1+‖z.val‖)/(1-‖z.val‖))).of_nonneg_of_le (fun m => norm_nonneg _)
  intro m
  by_cases hm : m=n
  · simp only [omittedBlaschkeFactor,ite_eq_left hm,sub_self,norm_zero]
    exact mul_nonneg (div_nonneg (by positivity) (sub_nonneg.mpr z.property.le))
      (sub_nonneg.mpr (a m).property.le)
  · simpa only [omittedBlaschkeFactor,ite_eq_right hm] using blaschkeFactor_deviation (a m) z

theorem omittedBlaschkeFactors_multipliable
    (a : ℕ → Disk) (ha : Summable (fun m => 1-‖(a m).val‖)) (n : ℕ) (z : Disk) :
    Multipliable (fun m => omittedBlaschkeFactor a n m z) := by
  simpa only [sub_sub_cancel] using
    multipliable_one_sub_of_summable (omittedBlaschkeFactors_summable_deviation a ha n z)


theorem norm_tprod_of_multipliable {I : Type} (f : I → ℂ) (hf : Multipliable f) :
    ‖∏' i, f i‖=∏' i, ‖f i‖ := by
  have h : Tendsto (fun s : Finset I => ∏ i∈s, f i) atTop (𝓝 (∏' i, f i)) := hf.hasProd
  have hn : HasProd (fun i => ‖f i‖) ‖∏' i, f i‖ := by
    change Tendsto (fun s : Finset I => ∏ i∈s, ‖f i‖) atTop (𝓝 ‖∏' i, f i‖)
    simpa only [←norm_prod] using h.norm
  exact hn.tprod_eq.symm

theorem blaschkeSeparationProduct_pos
    (a : ℕ → Disk) (hi : Function.Injective a)
    (ha : Summable (fun m => 1-‖(a m).val‖)) (n : ℕ) :
    0 < blaschkeSeparationProduct a n := by
  have hs : Summable (fun m => ‖omittedBlaschkeFactor a n m (a n)-1‖) := by
    simpa only [norm_sub_rev] using omittedBlaschkeFactors_summable_deviation a ha n (a n)
  have hne (m : ℕ) : omittedBlaschkeFactor a n m (a n)≠0 := by
    unfold omittedBlaschkeFactor
    split_ifs with hm
    · exact one_ne_zero
    · exact blaschkeFactor_ne_zero (a m) (a n) (fun he => hm (hi he).symm)
  have heq : (fun m => 1+(omittedBlaschkeFactor a n m (a n)-1)) =
      (fun m => omittedBlaschkeFactor a n m (a n)) := by funext m; ring
  have hp := tprod_one_add_ne_zero_of_summable
    (f:=fun m => omittedBlaschkeFactor a n m (a n)-1)
    (by intro m; change (fun m => 1+(omittedBlaschkeFactor a n m (a n)-1)) m≠0; rw [heq]; exact hne m) hs
  change (∏' m, (fun m => 1+(omittedBlaschkeFactor a n m (a n)-1)) m)≠0 at hp
  rw [heq] at hp
  have hn := norm_pos_iff.mpr hp
  rw [norm_tprod_of_multipliable _ (omittedBlaschkeFactors_multipliable a ha n (a n))] at hn
  simpa only [blaschkeSeparationProduct,omittedBlaschkeFactor,apply_ite,norm_one] using hn

/-- The genuine omitted inner factor, with its exact value at the removed zero. -/
theorem exists_omitted_blaschke_inner
    (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk) (hz : HasBlaschkeZeros u a) (n : ℕ) :
    ∃ v : BoundaryLInf, IsInner v ∧ u=multiplyInf (blaschkeBoundary (a n)) v ∧
      ‖innerValue v (a n).val‖=blaschkeSeparationProduct a n := by
  classical
  let e : ℕ ≃ ℕ := Equiv.swap 0 n
  let tail : ℕ → Disk := fun k => a (e (k+1))
  have he0 : e 0=n := Equiv.swap_apply_left 0 n
  have hfi : Function.Injective (fun k : ℕ => e (k+1)) :=
    e.injective.comp (fun i j h => Nat.add_right_cancel h)
  have hfn : ∀ k : ℕ, e (k+1)≠n := by
    intro k h
    have he := e.injective (h.trans he0.symm)
    omega
  have ht : Summable (fun k => 1-‖(tail k).val‖) := hz.1.comp_injective hfi
  obtain ⟨v₀,hv₀,_hvzeros,hvprod⟩ := exists_blaschkeInner tail ht
  obtain ⟨α,hα,huval⟩ := hz.2
  let v : BoundaryLInf := α • v₀
  have hv : IsInner v := by
    constructor
    · rw [malmquist_toL2_smul]
      exact hardy.smul_mem α hv₀.1
    · filter_upwards [Lp.coeFn_smul α v₀,hv₀.2] with t hs ht
      change (α • v₀) t=α*v₀ t at hs
      change ‖(α • v₀) t‖=1
      rw [hs,norm_mul,hα,ht,mul_one]
  have hval (z : Disk) : innerValue v z.val=α*∏' k, blaschkeFactor (a (e (k+1))) z.val := by
    change analyticValue (toL2 (α • v₀)) z.val=_
    rw [malmquist_toL2_smul,analyticValue_smul α _ z.property]
    change α*innerValue v₀ z.val=_
    rw [hvprod _ z.property]
  have hfactor : u=multiplyInf (blaschkeBoundary (a n)) v := by
    apply boundedHardy_boundary_ext _ _ hu.1
      (isInner_multiplyInf _ _ (blaschkeBoundary_isInner (a n)) hv).1
    intro z
    rw [huval _ z.property]
    change _=analyticValue (toL2 (multiplyInf (blaschkeBoundary (a n)) v)) z.val
    rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkeBoundary_hardy (a n)) ⟨toL2 v,hv.1⟩ z]
    change _=innerValue (blaschkeBoundary (a n)) z.val*innerValue v z.val
    rw [innerValue_blaschkeBoundary,hval]
    have hp := Multipliable.prod_mul_tprod_nat_mul'
      (f:=fun k => blaschkeFactor (a (e k)) z.val) (k:=1)
      (blaschkeFactors_multipliable tail ht z)
    simp only [Finset.prod_range_one,he0] at hp
    have he := e.tprod_eq (fun k => blaschkeFactor (a k) z.val)
    rw [he] at hp
    rw [←hp]
    ring
  refine ⟨v,hv,hfactor,?_⟩
  rw [hval,norm_mul,hα,one_mul]
  have hp := Multipliable.prod_mul_tprod_nat_mul'
    (f:=fun k => omittedBlaschkeFactor a n (e k) (a n)) (k:=1)
    (by simpa [omittedBlaschkeFactor,hfn] using blaschkeFactors_multipliable tail ht (a n))
  have he := e.tprod_eq (fun k => omittedBlaschkeFactor a n k (a n))
  rw [he] at hp
  have heq : (∏' k, blaschkeFactor (a (e (k+1))) (a n).val) =
      ∏' k, omittedBlaschkeFactor a n k (a n) := by
    simpa [Finset.prod_range_one,omittedBlaschkeFactor,he0,hfn] using hp
  rw [heq,norm_tprod_of_multipliable _ (omittedBlaschkeFactors_multipliable a hz.1 n (a n))]
  simp only [blaschkeSeparationProduct,omittedBlaschkeFactor,apply_ite,norm_one]


/-- Actual compressed multiplication, linear and continuous in its bounded symbol. -/
def boundedSymbolMap (u : BoundaryLInf) :
    BoundaryLInf →L[ℂ] (Model u →L[ℂ] Model u) :=
  ContinuousLinearMap.postcomp (Model u) (model u).orthogonalProjectionOnto ∘L
    ContinuousLinearMap.precomp BoundaryL2 (model u).subtypeL ∘L
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL circleMeasure ∞ 2 2

@[simp] theorem boundedSymbolMap_apply (u a : BoundaryLInf) :
    boundedSymbolMap u a=boundedSymbolOperator u a := rfl

theorem norm_inner_LInf_le_one (v : BoundaryLInf) (hv : IsInner v) : ‖v‖≤1 := by
  have h := Lp.norm_le_of_ae_bound (f:=v) zero_le_one (hv.2.mono (fun _ ht => ht.le))
  simpa using h

/-- Ordinary operator-norm summation preserves a uniform trace-class bound.
No normed Schatten carrier is postulated. -/
theorem traceClass_tsum_of_summable
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℕ → H →L[ℂ] H) (s : ℕ → ℝ)
    (hs : Summable s) (hs0 : ∀ n,0≤s n) (hT : Summable T)
    (hSp : ∀ n,Schatten 1 (T n)) (hGauge : ∀ n,schattenNorm 1 (T n)≤s n) :
    Schatten 1 (∑' n,T n) ∧ schattenNorm 1 (∑' n,T n)≤∑' n,s n := by
  have hFinite (F : Finset ℕ) :
      Schatten 1 (∑ n∈F,T n) ∧ schattenNorm 1 (∑ n∈F,T n)≤∑ n∈F,s n := by
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨schatten_zero 1 (by norm_num), by rw [schattenNorm_zero 1 (by norm_num)]⟩
    | @insert n F hn ih =>
      rw [Finset.sum_insert hn,Finset.sum_insert hn]
      exact ⟨schatten_add (hSp n) ih.1,
        (schattenNorm_add_le_sharp 1 le_rfl _ _ (hSp n) ih.1).trans (add_le_add (hGauge n) ih.2)⟩
  apply (isClosed_schattenClosedBall (H:=H) 1 (by norm_num) (∑' n,s n)).mem_of_tendsto
    hT.hasSum.tendsto_sum_nat
  exact Eventually.of_forall (fun N => ⟨(hFinite (Finset.range N)).1,
    (hFinite (Finset.range N)).2.trans (hs.sum_le_tsum _ (fun n _ => hs0 n))⟩)


/-- Lemma 5 in the manuscript's infinite simple-zero context.  The literal separation
products are proved positive above; neither interpolation nor uniform separation is assumed. -/
theorem weightedBlaschke_traceClass
    (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk) (hi : Function.Injective a)
    (hz : HasBlaschkeZeros u a) (φ : Hardy)
    (hs : Summable (fun n => ‖analyticValue φ.val (a n).val‖/blaschkeSeparationProduct a n)) :
    ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u φ.val A ∧ Schatten 1 A ∧
      schattenNorm 1 A≤∑' n,‖analyticValue φ.val (a n).val‖/blaschkeSeparationProduct a n := by
  classical
  choose v hv hFactor hValue using fun n => exists_omitted_blaschke_inner u hu a hz n
  have hδ (n : ℕ) : 0<blaschkeSeparationProduct a n := blaschkeSeparationProduct_pos a hi hz.1 n
  have hvne (n : ℕ) : innerValue (v n) (a n).val≠0 := by
    apply norm_pos_iff.mp
    rw [hValue n]
    exact hδ n
  have hOther (n m : ℕ) (hm : m≠n) : innerValue (v n) (a m).val=0 := by
    have he := blaschkeNodes_zero u a hz m
    rw [hFactor n,innerValue_multiplyInf _ _ (blaschkeBoundary_hardy (a n)) (hv n).1 (a m),
      innerValue_blaschkeBoundary] at he
    exact (mul_eq_zero.mp he).resolve_left (blaschkeFactor_ne_zero (a n) (a m) (fun h => hm (hi h)))
  let V : ℕ → boundedHardy := fun n => ⟨v n,by
    change boundaryInclusion (v n)∈hardy
    rw [boundaryInclusion_apply]
    exact (hv n).1⟩
  let c : ℕ → ℂ := fun n => analyticValue φ.val (a n).val/innerValue (v n) (a n).val
  have hc (n : ℕ) : ‖c n‖=‖analyticValue φ.val (a n).val‖/blaschkeSeparationProduct a n := by
    dsimp only [c]
    rw [norm_div,hValue n]
  have hcSum : Summable (fun n => ‖c n‖) := by simpa only [hc] using hs
  let f : ℕ → boundedHardy := fun n => c n • V n
  have hfNorm : Summable (fun n => ‖f n‖) :=
    hcSum.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      change ‖c n • V n‖≤‖c n‖
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (norm_inner_LInf_le_one (v n) (hv n)) (norm_nonneg _)).trans_eq (mul_one _))
  have hf : Summable f := hfNorm.of_norm
  let γ : boundedHardy := ∑' n,f n
  have hEval (m : ℕ) : innerValue γ.val (a m).val=analyticValue φ.val (a m).val := by
    let E : boundedHardy →L[ℂ] ℂ := (hardyEvaluation (a m)).comp boundedHardyToHardy
    have he : innerValue γ.val (a m).val=∑' n,c n*innerValue (v n) (a m).val := by
      have heγ : E γ=innerValue γ.val (a m).val := by
        change analyticValue (boundedHardyToHardy γ).val (a m).val=_
        rw [boundedHardyToHardy_val]
        rfl
      rw [←heγ]
      change E (∑' n,f n)=_
      rw [E.map_tsum hf]
      congr 1
      funext n
      change E (c n • V n)=_
      rw [map_smul]
      change c n*analyticValue (boundedHardyToHardy (V n)).val (a m).val=_
      rw [boundedHardyToHardy_val]
      rfl
    rw [he,tsum_eq_single m]
    · exact div_mul_cancel₀ _ (hvne m)
    · intro n hnm
      rw [hOther n m (Ne.symm hnm),mul_zero]
  let T : ℕ → Model u →L[ℂ] Model u := fun n => c n • boundedSymbolOperator u (v n)
  have hTn (n : ℕ) : Schatten 1 (T n) ∧ schattenNorm 1 (T n)≤‖c n‖ := by
    obtain ⟨hSp,hN⟩ := omittedInnerCreator_traceClass u (v n) hu (hv n) a hi hz n (hFactor n)
    exact ⟨schatten_smul hSp (c n),
      (schattenNorm_smul_le hSp (c n)).trans ((mul_le_mul_of_nonneg_left hN (norm_nonneg _)).trans_eq (mul_one _))⟩
  let M : boundedHardy →L[ℂ] (Model u →L[ℂ] Model u) :=
    (boundedSymbolMap u).comp boundedHardy.subtypeL
  have hMf (n : ℕ) : M (f n)=T n := by
    change M (c n • V n)=_
    rw [map_smul]
    rfl
  have hMSum : HasSum T (M γ) := by
    simpa only [hMf] using M.hasSum hf.hasSum
  have hTSum : Summable T := hMSum.summable
  have hSp := traceClass_tsum_of_summable T (fun n => ‖c n‖) hcSum (fun n => norm_nonneg _)
    hTSum (fun n => (hTn n).1) (fun n => (hTn n).2)
  have hM : M γ=∑' n,T n := hMSum.tsum_eq.symm
  change Schatten 1 (∑' n,T n) ∧ schattenNorm 1 (∑' n,T n)≤∑' n,‖c n‖ at hSp
  rw [←hM] at hSp
  change Schatten 1 (boundedSymbolOperator u γ.val) ∧
    schattenNorm 1 (boundedSymbolOperator u γ.val)≤∑' n,‖c n‖ at hSp
  let γH : Hardy := boundedHardyToHardy γ
  have hzDiff (n : ℕ) : analyticValue (φ-γH).val (a n).val=0 := by
    change analyticValue (φ.val-(boundedHardyToHardy γ).val) (a n).val=0
    rw [boundedHardyToHardy_val,analyticValue_sub _ _ (a n).property]
    change analyticValue φ.val (a n).val-innerValue γ.val (a n).val=0
    rw [hEval n,sub_self]
  obtain ⟨q,hq⟩ := blaschkeHardyDivision u hu a hi hz (φ-γH) hzDiff
  change multiply u q.val=φ.val-(boundedHardyToHardy γ).val at hq
  rw [boundedHardyToHardy_val] at hq
  have hRep : RepresentsTTO u φ.val (boundedSymbolOperator u γ.val) := by
    have hσ : φ.val=toL2 γ.val+multiply u q.val := by rw [hq]; abel
    intro f g hf hg
    have hB := boundedSymbolOperator_represents u γ.val f g hf hg
    have hZ : coreForm (multiply u q.val) f.val g.val=0 := by
      have he := represents_inner_multiple_zero u q f g hf hg
      simpa only [zero_apply,inner_zero_right] using he.symm
    rw [hσ,coreForm_add _ _ _ _ hf,hZ,add_zero]
    exact hB
  exact ⟨boundedSymbolOperator u γ.val,hRep,hSp.1,by simpa only [hc] using hSp.2⟩

theorem weightedBlaschke_hasSchattenTTO
    (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk) (hi : Function.Injective a)
    (hz : HasBlaschkeZeros u a) (φ : Hardy)
    (hs : Summable (fun n => ‖analyticValue φ.val (a n).val‖/blaschkeSeparationProduct a n)) :
    HasSchattenTTO 1 u φ.val := by
  obtain ⟨A,hA,hS,_hN⟩ := weightedBlaschke_traceClass u hu a hi hz φ hs
  exact ⟨A,hA,hS⟩

end TTO.Paper.Proved
