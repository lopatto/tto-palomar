/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.BoundaryFoundations
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.Normed.Operator.Extend

/-! Natural adjoint-square operators and their closed graph forms. -/

@[expose] public section
noncomputable section
open Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The literal graph composition Q*Q, with its natural domain. -/
def adjointSquareGraph (Q : H →ₗ.[ℂ] K) : Submodule ℂ (H × H) where
  carrier := {p | ∃ v : K, (p.1,v) ∈ Q.graph ∧ (v,p.2) ∈ Q.adjoint.graph}
  zero_mem' := ⟨0,Q.graph.zero_mem,Q.adjoint.graph.zero_mem⟩
  add_mem' := by
    rintro p r ⟨v,hv,hw⟩ ⟨z,hz,ht⟩
    exact ⟨v+z,Q.graph.add_mem hv hz,Q.adjoint.graph.add_mem hw ht⟩
  smul_mem' := by
    rintro c p ⟨v,hv,hw⟩
    exact ⟨c • v,Q.graph.smul_mem c hv,Q.adjoint.graph.smul_mem c hw⟩

omit [CompleteSpace K] in
theorem adjointSquareGraph_single (Q : H →ₗ.[ℂ] K) :
    ∀ p ∈ adjointSquareGraph Q, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨v,hv,hw⟩ hp
  exact Q.adjoint.graph_fst_eq_zero_snd hw (Q.graph_fst_eq_zero_snd hv hp)

def adjointSquare (Q : H →ₗ.[ℂ] K) : H →ₗ.[ℂ] H := (adjointSquareGraph Q).toLinearPMap

omit [CompleteSpace K] in
theorem adjointSquare_graph (Q : H →ₗ.[ℂ] K) :
    (adjointSquare Q).graph = adjointSquareGraph Q :=
  (adjointSquareGraph Q).toLinearPMap_graph_eq (adjointSquareGraph_single Q)

omit [CompleteSpace K] in
theorem mem_adjointSquare_graph (Q : H →ₗ.[ℂ] K) (x y : H) :
    (x,y) ∈ (adjointSquare Q).graph ↔ ∃ v : K, (x,v) ∈ Q.graph ∧ (v,y) ∈ Q.adjoint.graph := by
  rw [adjointSquare_graph]
  rfl

omit [CompleteSpace K] in
theorem adjointSquare_form (Q : H →ₗ.[ℂ] K) (hQ : Dense (Q.domain : Set H)) (x y : H) :
    (x,y) ∈ (adjointSquare Q).graph ↔ ∃ hx : x ∈ Q.domain,
      ∀ γ : Q.domain, inner ℂ γ.val y = inner ℂ (Q γ) (Q ⟨x,hx⟩) := by
  rw [mem_adjointSquare_graph]
  constructor
  · rintro ⟨v,hx,hy⟩
    obtain ⟨a,ha,hqa⟩ := (Q.mem_graph_iff).mp hx
    obtain ⟨b,hb,hqb⟩ := (Q.adjoint.mem_graph_iff).mp hy
    change a.val = x at ha
    change Q a = v at hqa
    change b.val = v at hb
    change Q.adjoint b = y at hqb
    subst x
    refine ⟨a.prop,fun γ => ?_⟩
    have h := (Q.adjoint_isFormalAdjoint hQ).symm γ b
    simpa only [hb,hqb,hqa] using h.symm
  · rintro ⟨hx,hxy⟩
    have hy : Q ⟨x,hx⟩ ∈ Q.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y,fun γ => by
        rw [← inner_conj_symm,← inner_conj_symm (Q ⟨x,hx⟩),hxy γ]⟩
    have he : Q.adjoint ⟨Q ⟨x,hx⟩,hy⟩ = y :=
      LinearPMap.adjoint_apply_eq hQ _ (fun γ => by
        rw [← inner_conj_symm,← inner_conj_symm (Q ⟨x,hx⟩),hxy γ])
    refine ⟨Q ⟨x,hx⟩,Q.mem_graph ⟨x,hx⟩,?_⟩
    simpa only [he] using Q.adjoint.mem_graph ⟨Q ⟨x,hx⟩,hy⟩

omit [CompleteSpace K] in
theorem adjointSquare_quadratic (Q : H →ₗ.[ℂ] K) (hQ : Dense (Q.domain : Set H))
    (x : (adjointSquare Q).domain) :
    ∃ hx : x.val ∈ Q.domain,
      inner ℂ x.val (adjointSquare Q x) = inner ℂ (Q ⟨x.val,hx⟩) (Q ⟨x.val,hx⟩) := by
  obtain ⟨hx,hf⟩ := (adjointSquare_form Q hQ x.val (adjointSquare Q x)).mp
    ((adjointSquare Q).mem_graph x)
  exact ⟨hx,hf ⟨x.val,hx⟩⟩

omit [CompleteSpace K] in
theorem adjointSquare_symmetric (Q : H →ₗ.[ℂ] K) (hQ : Dense (Q.domain : Set H)) :
    (adjointSquare Q).IsFormalAdjoint (adjointSquare Q) := by
  intro x y
  obtain ⟨hx,hfx⟩ := (adjointSquare_form Q hQ x.val (adjointSquare Q x)).mp
    ((adjointSquare Q).mem_graph x)
  obtain ⟨hy,hfy⟩ := (adjointSquare_form Q hQ y.val (adjointSquare Q y)).mp
    ((adjointSquare Q).mem_graph y)
  rw [← inner_conj_symm, hfx ⟨y.val,hy⟩,inner_conj_symm]
  exact (hfy ⟨x.val,hx⟩).symm


omit [CompleteSpace K] in
theorem adjointSquare_bounded (Q : H →ₗ.[ℂ] K) (hQ : Dense (Q.domain : Set H)) (x : H) :
    x ∈ (adjointSquare Q).domain ↔ ∃ hx : x ∈ Q.domain,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : Q.domain,
        ‖inner ℂ (Q γ) (Q ⟨x,hx⟩)‖ ≤ C*‖γ.val‖ := by
  constructor
  · intro hx
    obtain ⟨hq,hf⟩ := (adjointSquare_form Q hQ x (adjointSquare Q ⟨x,hx⟩)).mp
      ((adjointSquare Q).mem_graph ⟨x,hx⟩)
    refine ⟨hq,‖adjointSquare Q ⟨x,hx⟩‖,norm_nonneg _,fun γ => ?_⟩
    rw [← hf γ,mul_comm]
    exact norm_inner_le_norm _ _
  · rintro ⟨hx,C,hC,hb⟩
    let F : Q.domain →ₗ[ℂ] ℂ := (innerₛₗ ℂ (Q ⟨x,hx⟩)).comp Q.toFun
    have hF : ∀ γ, ‖F γ‖ ≤ C*‖γ‖ := by
      intro γ
      change ‖inner ℂ (Q ⟨x,hx⟩) (Q γ)‖ ≤ _
      rw [norm_inner_symm]
      exact hb γ
    have hy : Q ⟨x,hx⟩ ∈ Q.adjoint.domain :=
      (Q.mem_adjoint_domain_iff _).mpr (F.mkContinuous C hF).continuous
    apply LinearPMap.mem_domain_of_mem_graph (y := Q.adjoint ⟨Q ⟨x,hx⟩,hy⟩)
    exact (mem_adjointSquare_graph Q _ _).mpr
      ⟨Q ⟨x,hx⟩,Q.mem_graph ⟨x,hx⟩,Q.adjoint.mem_graph ⟨Q ⟨x,hx⟩,hy⟩⟩


/-- The actual closed graph, with the sum-of-squares Hilbert norm. -/
def graphHilbert (Q : H →ₗ.[ℂ] K) : Submodule ℂ (WithLp 2 (H × K)) :=
  Q.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toLinearMap

instance graphHilbert_complete (Q : H →ₗ.[ℂ] K) [hc : Fact Q.IsClosed] :
    CompleteSpace (graphHilbert Q) := by
  let : IsClosed (graphHilbert Q : Set (WithLp 2 (H × K))) :=
    hc.out.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H K).continuous
  infer_instance

def graphFirst (Q : H →ₗ.[ℂ] K) : graphHilbert Q →L[ℂ] H :=
  (ContinuousLinearMap.fst ℂ H K).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap.comp (graphHilbert Q).subtypeL)

def graphSecond (Q : H →ₗ.[ℂ] K) : graphHilbert Q →L[ℂ] K :=
  (ContinuousLinearMap.snd ℂ H K).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap.comp (graphHilbert Q).subtypeL)

omit [CompleteSpace H] [CompleteSpace K] in
theorem graph_coordinates_mem (Q : H →ₗ.[ℂ] K) (v : graphHilbert Q) :
    (graphFirst Q v,graphSecond Q v) ∈ Q.graph := v.prop

def graphVector (Q : H →ₗ.[ℂ] K) (x : Q.domain) : graphHilbert Q :=
  ⟨WithLp.toLp 2 (x.val,Q x),Q.mem_graph x⟩

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphVector_first (Q : H →ₗ.[ℂ] K) (x : Q.domain) :
    graphFirst Q (graphVector Q x) = x.val := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem graphVector_second (Q : H →ₗ.[ℂ] K) (x : Q.domain) :
    graphSecond Q (graphVector Q x) = Q x := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem graph_inner (Q : H →ₗ.[ℂ] K) (v w : graphHilbert Q) :
    inner ℂ v w = inner ℂ (graphFirst Q v) (graphFirst Q w)+
      inner ℂ (graphSecond Q v) (graphSecond Q w) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem graph_norm_sq (Q : H →ₗ.[ℂ] K) (v : graphHilbert Q) :
    ‖v‖^2 = ‖graphFirst Q v‖^2+‖graphSecond Q v‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 v.val

omit [CompleteSpace H] [CompleteSpace K] in
theorem graphFirst_norm_le (Q : H →ₗ.[ℂ] K) : ‖graphFirst Q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := graph_norm_sq Q v
  have hn := norm_nonneg (graphSecond Q v)
  have hv := norm_nonneg v
  have hf := norm_nonneg (graphFirst Q v)
  simpa only [one_mul] using (show ‖graphFirst Q v‖ ≤ ‖v‖ by nlinarith [sq_nonneg ‖graphSecond Q v‖])

omit [CompleteSpace H] [CompleteSpace K] in
theorem graphFirst_injective (Q : H →ₗ.[ℂ] K) : Function.Injective (graphFirst Q) := by
  intro v w h
  have hs := Q.mem_graph_snd_inj (graph_coordinates_mem Q v) (graph_coordinates_mem Q w) h
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H K).injective
  exact Prod.ext h hs

omit [CompleteSpace H] [CompleteSpace K] in
theorem graphFirst_range (Q : H →ₗ.[ℂ] K) : LinearMap.range (graphFirst Q).toLinearMap = Q.domain := by
  apply le_antisymm
  · rintro x ⟨v,rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (graph_coordinates_mem Q v)
  · intro x hx
    exact ⟨graphVector Q ⟨x,hx⟩,rfl⟩

theorem adjointSquare_resolvent (Q : H →ₗ.[ℂ] K) (hc : Q.IsClosed)
    (hQ : Dense (Q.domain : Set H)) (h : H) :
    ∃ x : H, (x,h-x) ∈ (adjointSquare Q).graph := by
  let : Fact Q.IsClosed := ⟨hc⟩
  let v := (graphFirst Q).adjoint h
  let x := graphFirst Q v
  have hx : x ∈ Q.domain := LinearPMap.mem_domain_of_mem_graph (graph_coordinates_mem Q v)
  refine ⟨x,(adjointSquare_form Q hQ x (h-x)).mpr ⟨hx,fun γ => ?_⟩⟩
  have he := (graphFirst Q).adjoint_inner_right (graphVector Q γ) h
  change inner ℂ (graphVector Q γ) v = inner ℂ γ.val h at he
  rw [graph_inner,graphVector_first,graphVector_second] at he
  have hq : Q ⟨x,hx⟩ = graphSecond Q v :=
    Q.mem_graph_snd_inj (Q.mem_graph ⟨x,hx⟩) (graph_coordinates_mem Q v) rfl
  rw [hq,inner_sub_right]
  change inner ℂ γ.val h-inner ℂ γ.val (graphFirst Q v) = _
  linear_combination -he


omit [CompleteSpace K] in
theorem adjoint_graph_form (Q : H →ₗ.[ℂ] K) (hQ : Dense (Q.domain : Set H)) (v : K) (y : H) :
    (v,y) ∈ Q.adjoint.graph ↔ ∀ γ : Q.domain, inner ℂ γ.val y = inner ℂ (Q γ) v := by
  constructor
  · intro hv γ
    obtain ⟨a,ha,hqa⟩ := Q.adjoint.mem_graph_iff.mp hv
    have he := (Q.adjoint_isFormalAdjoint hQ).symm γ a
    change a.val = v at ha
    change Q.adjoint a = y at hqa
    simpa only [ha,hqa] using he.symm
  · intro hf
    have hv : v ∈ Q.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists v ⟨y,fun γ => by
        rw [← inner_conj_symm,← inner_conj_symm v,hf γ]⟩
    have he : Q.adjoint ⟨v,hv⟩ = y :=
      LinearPMap.adjoint_apply_eq hQ _ (fun γ => by
        rw [← inner_conj_symm,← inner_conj_symm v,hf γ])
    simpa only [he] using Q.adjoint.mem_graph ⟨v,hv⟩

theorem adjointSquare_dense (Q : H →ₗ.[ℂ] K) (hc : Q.IsClosed)
    (hQ : Dense (Q.domain : Set H)) : Dense ((adjointSquare Q).domain : Set H) := by
  have hb : (adjointSquare Q).domain.orthogonal = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro h hh
    obtain ⟨x,hx⟩ := adjointSquare_resolvent Q hc hQ h
    obtain ⟨hq,hf⟩ := (adjointSquare_form Q hQ x (h-x)).mp hx
    have ho := (Submodule.mem_orthogonal _ _).mp hh x
      (LinearPMap.mem_domain_of_mem_graph hx)
    have he := hf ⟨x,hq⟩
    rw [inner_sub_right,ho] at he
    have hre := congrArg Complex.re he
    have hpos := inner_self_nonneg (𝕜 := ℂ) (x := Q ⟨x,hq⟩)
    have hz : x = 0 := (re_inner_self_nonpos (𝕜 := ℂ)).mp (by
      simp only [zero_sub,Complex.neg_re] at hre
      change 0 ≤ (inner ℂ (Q ⟨x,hq⟩) (Q ⟨x,hq⟩)).re at hpos
      change (inner ℂ x x).re ≤ 0
      linarith)
    have hh0 : h = 0 := by
      have hv := (adjointSquare Q).graph_fst_eq_zero_snd hx hz
      simpa only [hz,sub_zero] using hv
    exact hh0
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,hb,Submodule.bot_orthogonal_eq_top]

theorem adjointSquare_selfAdjoint (Q : H →ₗ.[ℂ] K) (hc : Q.IsClosed)
    (hQ : Dense (Q.domain : Set H)) : IsSelfAdjoint (adjointSquare Q) := by
  let D := adjointSquare Q
  have hd : Dense (D.domain : Set H) := adjointSquare_dense Q hc hQ
  have hs : D.IsFormalAdjoint D := adjointSquare_symmetric Q hQ
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨y,z⟩ hyz
    have hf := (adjoint_graph_form D hd y z).mp hyz
    obtain ⟨x,hx⟩ := adjointSquare_resolvent Q hc hQ (y+z)
    have hxD : x ∈ D.domain := LinearPMap.mem_domain_of_mem_graph hx
    have hDx : D ⟨x,hxD⟩ = y+z-x := D.mem_graph_snd_inj (D.mem_graph ⟨x,hxD⟩) hx rfl
    have he : ∀ γ : D.domain, inner ℂ (γ.val+D γ) (y-x) = 0 := by
      intro γ
      have ha := hf γ
      have hb := hs γ ⟨x,hxD⟩
      rw [hDx,inner_sub_right,inner_add_right] at hb
      rw [inner_add_left,inner_sub_right,inner_sub_right]
      linear_combination -ha-hb
    obtain ⟨r,hr⟩ := adjointSquare_resolvent Q hc hQ (y-x)
    have hrD : r ∈ D.domain := LinearPMap.mem_domain_of_mem_graph hr
    have hDr : D ⟨r,hrD⟩ = y-x-r := D.mem_graph_snd_inj (D.mem_graph ⟨r,hrD⟩) hr rfl
    have her := he ⟨r,hrD⟩
    rw [hDr,add_sub_cancel] at her
    have hyx : y = x := sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp her)
    simpa only [hyx,add_sub_cancel_left] using hx
  · exact hs.le_adjoint hd

theorem adjointSquare_positive (Q : H →ₗ.[ℂ] K) (hc : Q.IsClosed)
    (hQ : Dense (Q.domain : Set H)) : PositiveSelfAdjoint (adjointSquare Q) := by
  refine ⟨adjointSquare_selfAdjoint Q hc hQ,fun x => ?_⟩
  obtain ⟨hx,he⟩ := adjointSquare_quadratic Q hQ x
  rw [he]
  exact ⟨inner_self_im (𝕜 := ℂ) (Q ⟨x.val,hx⟩),
    inner_self_nonneg (𝕜 := ℂ) (x := Q ⟨x.val,hx⟩)⟩


omit [CompleteSpace K] in
/-- A self-adjoint injective bounded operator has dense range, including in the zero space. -/
theorem denseRange_selfAdjoint_injective (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hi : Function.Injective A) : DenseRange A := by
  have hk : A.adjoint.ker = ⊥ := by
    change A.adjoint = A at hA
    rw [hA,LinearMap.ker_eq_bot]
    exact hi
  have ho : A.range.orthogonal = ⊥ := (A.orthogonal_range).trans hk
  change Dense (A.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure,ho,Submodule.bot_orthogonal_eq_top]

/-- The graph parameterization x=T a, Sx=B a used for the positive unbounded square root. -/
def transformGraph (T B : H →L[ℂ] H) : Submodule ℂ (H × H) := (T.prod B).range

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_transformGraph (T B : H →L[ℂ] H) (x y : H) :
    (x,y) ∈ transformGraph T B ↔ ∃ a, T a = x ∧ B a = y := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Prod.fst ha,congrArg Prod.snd ha⟩
  · rintro ⟨a,ha,hb⟩
    exact ⟨a,Prod.ext ha hb⟩

omit [CompleteSpace H] [CompleteSpace K] in
theorem transformGraph_single (T B : H →L[ℂ] H) (hi : Function.Injective T) :
    ∀ p ∈ transformGraph T B, p.1 = 0 → p.2 = 0 := by
  rintro ⟨x,y⟩ hp hx
  obtain ⟨a,ha,hb⟩ := (mem_transformGraph T B x y).mp hp
  change x = 0 at hx
  have hz : a = 0 := hi (by simpa only [hx,map_zero] using ha)
  simpa only [hz,map_zero] using hb.symm

def boundedTransform (T B : H →L[ℂ] H) : H →ₗ.[ℂ] H := (transformGraph T B).toLinearPMap

omit [CompleteSpace H] [CompleteSpace K] in
theorem boundedTransform_graph (T B : H →L[ℂ] H) (hi : Function.Injective T) :
    (boundedTransform T B).graph = transformGraph T B :=
  (transformGraph T B).toLinearPMap_graph_eq (transformGraph_single T B hi)

omit [CompleteSpace H] [CompleteSpace K] in
theorem transformGraph_equation (T B : H →L[ℂ] H) (hc : Commute T B)
    (hcircle : ∀ a, T (T a)+B (B a) = a) (x z : H) :
    (x,z) ∈ transformGraph T B ↔ B x = T z := by
  have hcomm : ∀ a, T (B a) = B (T a) := fun a => congrArg (fun C : H →L[ℂ] H => C a) hc.eq
  constructor
  · intro hp
    obtain ⟨a,rfl,rfl⟩ := (mem_transformGraph T B x z).mp hp
    exact (hcomm a).symm
  · intro he
    apply (mem_transformGraph T B x z).mpr
    refine ⟨T x+B z,?_,?_⟩
    · rw [map_add,hcomm,← he]
      exact hcircle x
    · rw [map_add,← hcomm,he]
      exact hcircle z

omit [CompleteSpace K] in
theorem boundedTransform_selfAdjoint (T B : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hB : IsSelfAdjoint B) (hc : Commute T B) (hi : Function.Injective T)
    (hcircle : ∀ a, T (T a)+B (B a) = a) : IsSelfAdjoint (boundedTransform T B) := by
  have hd : Dense ((boundedTransform T B).domain : Set H) := by
    have he : (boundedTransform T B).domain = T.range := by
      ext x
      rw [LinearPMap.mem_domain_iff,boundedTransform_graph T B hi]
      constructor
      · rintro ⟨y,hy⟩
        obtain ⟨a,ha,_⟩ := (mem_transformGraph T B x y).mp hy
        exact ⟨a,ha⟩
      · rintro ⟨a,ha⟩
        exact ⟨B a,(mem_transformGraph T B x (B a)).mpr ⟨a,ha,rfl⟩⟩
    rw [he]
    exact denseRange_selfAdjoint_injective T hT hi
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd,boundedTransform_graph T B hi]
  ext ⟨x,z⟩
  rw [transformGraph_equation T B hc hcircle,Submodule.mem_adjoint_iff]
  have ht : ∀ a b, inner ℂ (T a) b = inner ℂ a (T b) := hT.isSymmetric
  have hb : ∀ a b, inner ℂ (B a) b = inner ℂ a (B b) := hB.isSymmetric
  constructor
  · intro h
    have he : ∀ a, inner ℂ a (B x-T z) = 0 := by
      intro a
      have hp := h (T a) (B a) ((mem_transformGraph T B _ _).mpr ⟨a,rfl,rfl⟩)
      simpa only [hb,ht,inner_sub_right] using hp
    exact (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp (he (B x-T z)))).symm.symm
  · intro he a b hab
    obtain ⟨v,rfl,rfl⟩ := (mem_transformGraph T B a b).mp hab
    rw [hb,ht,he,sub_self]


/-- The positive contraction (I+Q*Q)⁻¹, constructed from the actual closed graph. -/
def graphResolvent (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] : H →L[ℂ] H :=
  (graphFirst Q).comp (graphFirst Q).adjoint

def graphRoot (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] : H →L[ℂ] H := CFC.sqrt (graphResolvent Q)

def graphComplementRoot (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] : H →L[ℂ] H :=
  CFC.sqrt (1-graphResolvent Q)

theorem graphResolvent_positive (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] :
    (graphResolvent Q).IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint (graphFirst Q)

theorem graphResolvent_complement_positive (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] :
    (1-graphResolvent Q).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(IsSelfAdjoint.one (H →L[ℂ] H)).sub (graphResolvent_positive Q).isSelfAdjoint,fun x => ?_⟩
  have hn : ‖(graphFirst Q).adjoint x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖(graphFirst Q).adjoint‖*‖x‖ := (graphFirst Q).adjoint.le_opNorm x
      _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.adjoint.norm_map (graphFirst Q)) ▸ graphFirst_norm_le Q) (norm_nonneg x)
      _ = _ := one_mul _
  change 0 ≤ RCLike.re (inner ℂ ((1-graphResolvent Q) x) x)
  change 0 ≤ RCLike.re (inner ℂ (x-graphFirst Q ((graphFirst Q).adjoint x)) x)
  rw [inner_sub_left]
  rw [← (graphFirst Q).adjoint_inner_right]
  change 0 ≤ (inner ℂ x x-inner ℂ ((graphFirst Q).adjoint x) ((graphFirst Q).adjoint x)).re
  rw [Complex.sub_re]
  change 0 ≤ RCLike.re (inner ℂ x x)-RCLike.re
    (inner ℂ ((graphFirst Q).adjoint x) ((graphFirst Q).adjoint x))
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq]
  nlinarith [norm_nonneg x,norm_nonneg ((graphFirst Q).adjoint x)]

theorem graphRoot_positive (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] : (graphRoot Q).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)

theorem graphComplementRoot_positive (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] :
    (graphComplementRoot Q).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)

theorem graphRoot_square (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] (x : H) :
    graphRoot Q (graphRoot Q x) = graphResolvent Q x :=
  congrArg (fun C : H →L[ℂ] H => C x) (CFC.sqrt_mul_sqrt_self _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_positive Q)))

theorem graphComplementRoot_square (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] (x : H) :
    graphComplementRoot Q (graphComplementRoot Q x) = x-graphResolvent Q x :=
  congrArg (fun C : H →L[ℂ] H => C x) (CFC.sqrt_mul_sqrt_self _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_complement_positive Q)))

theorem graph_roots_commute (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] :
    Commute (graphRoot Q) (graphComplementRoot Q) := by
  have hc : Commute (graphResolvent Q) (1-graphResolvent Q) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  exact (hc.cfcₙ_nnreal NNReal.sqrt).symm.cfcₙ_nnreal NNReal.sqrt |>.symm

theorem graph_roots_circle (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] (x : H) :
    graphRoot Q (graphRoot Q x)+graphComplementRoot Q (graphComplementRoot Q x) = x := by
  rw [graphRoot_square,graphComplementRoot_square,add_sub_cancel]

theorem graphRoot_norm (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] (x : H) :
    ‖(graphFirst Q).adjoint x‖ = ‖graphRoot Q x‖ := by
  have he : inner ℂ (graphRoot Q x) (graphRoot Q x) =
      inner ℂ ((graphFirst Q).adjoint x) ((graphFirst Q).adjoint x) := by
    rw [(graphRoot_positive Q).inner_left_eq_inner_right,graphRoot_square]
    exact (graphFirst Q).adjoint_inner_left ((graphFirst Q).adjoint x) x |>.symm
  have hr := congrArg RCLike.re he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at hr
  nlinarith [norm_nonneg ((graphFirst Q).adjoint x),norm_nonneg (graphRoot Q x)]

theorem graphFirst_adjoint_injective (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : Function.Injective (graphFirst Q).adjoint := by
  intro x y h
  apply hQ.eq_of_inner_right ℂ
  intro z hz
  have hx := (graphFirst Q).adjoint_inner_right (graphVector Q ⟨z,hz⟩) x
  have hy := (graphFirst Q).adjoint_inner_right (graphVector Q ⟨z,hz⟩) y
  rw [h] at hx
  exact hx.symm.trans hy

theorem graphRoot_injective (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : Function.Injective (graphRoot Q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hn := graphRoot_norm Q x
  rw [hx,norm_zero] at hn
  exact (graphFirst_adjoint_injective Q hQ) (by simpa only [map_zero] using norm_eq_zero.mp hn)

theorem graphRoot_denseRange (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : DenseRange (graphRoot Q) :=
  denseRange_selfAdjoint_injective _ (graphRoot_positive Q).isSelfAdjoint (graphRoot_injective Q hQ)


theorem graphRoot_isometry (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) :
    ∃ U : H ≃ₗᵢ[ℂ] graphHilbert Q, ∀ x, graphFirst Q (U x) = graphRoot Q x := by
  let U₀ : H →ₗᵢ[ℂ] graphHilbert Q :=
    (graphFirst Q).adjoint.toLinearMap.extendOfIsometry (graphRoot_denseRange Q hQ) (graphRoot_norm Q)
  have hU : ∀ x, U₀ (graphRoot Q x) = (graphFirst Q).adjoint x := fun x =>
    LinearMap.extendOfIsometry_eq _ (graphRoot_denseRange Q hQ) (graphRoot_norm Q) x
  have hd : DenseRange (graphFirst Q).adjoint := by
    change Dense ((graphFirst Q).adjoint.range : Set (graphHilbert Q))
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    rw [← (graphFirst Q).orthogonal_ker,LinearMap.ker_eq_bot.mpr (graphFirst_injective Q),
      Submodule.bot_orthogonal_eq_top]
  have hu : Function.Surjective U₀ := by
    have hclosed : IsClosed (Set.range U₀) := U₀.isometry.isClosedEmbedding.isClosed_range
    have hle : Set.range (graphFirst Q).adjoint ⊆ Set.range U₀ := by
      rintro _ ⟨x,rfl⟩
      exact ⟨graphRoot Q x,hU x⟩
    have hc := closure_minimal hle hclosed
    rw [hd.closure_range] at hc
    exact fun v => hc (Set.mem_univ v)
  let U : H ≃ₗᵢ[ℂ] graphHilbert Q := LinearIsometryEquiv.ofSurjective U₀ hu
  refine ⟨U,fun x => ?_⟩
  have he : (fun a => graphFirst Q (U a)) = graphRoot Q :=
    (graphRoot_denseRange Q hQ).equalizer (by fun_prop) (graphRoot Q).continuous (by
      funext a
      change graphFirst Q (U₀ (graphRoot Q a)) = graphRoot Q (graphRoot Q a)
      rw [hU,graphRoot_square]
      rfl)
  exact congrFun he x

theorem graphRoot_range (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : (graphRoot Q).range = Q.domain := by
  obtain ⟨U,hU⟩ := graphRoot_isometry Q hQ
  rw [← graphFirst_range Q]
  apply le_antisymm
  · rintro x ⟨a,rfl⟩
    exact ⟨U a,hU a⟩
  · rintro x ⟨a,rfl⟩
    obtain ⟨v,rfl⟩ := U.surjective a
    exact ⟨v,(hU v).symm⟩

theorem graphRoot_form_norm (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) (a : H) (hx : graphRoot Q a ∈ Q.domain) :
    ‖Q ⟨graphRoot Q a,hx⟩‖^2 = ‖graphComplementRoot Q a‖^2 := by
  obtain ⟨U,hU⟩ := graphRoot_isometry Q hQ
  have hv : Q ⟨graphRoot Q a,hx⟩ = graphSecond Q (U a) :=
    Q.mem_graph_snd_inj (Q.mem_graph ⟨graphRoot Q a,hx⟩) (graph_coordinates_mem Q (U a)) (hU a).symm
  have hn := graph_norm_sq Q (U a)
  rw [U.norm_map,hU] at hn
  have hc := congrArg (fun v => (inner ℂ a v).re) (graph_roots_circle Q a)
  rw [inner_add_right,Complex.add_re,← (graphRoot_positive Q).inner_left_eq_inner_right,
    ← (graphComplementRoot_positive Q).inner_left_eq_inner_right] at hc
  change RCLike.re (inner ℂ (graphRoot Q a) (graphRoot Q a))+
    RCLike.re (inner ℂ (graphComplementRoot Q a) (graphComplementRoot Q a)) =
    RCLike.re (inner ℂ a a) at hc
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq,inner_self_eq_norm_sq] at hc
  rw [hv]
  linarith


omit [CompleteSpace K] in
theorem positive_mul_of_commute (T B : H →L[ℂ] H) (hT : T.IsPositive) (hB : B.IsPositive)
    (hc : Commute T B) : (T*B).IsPositive := by
  let C := CFC.sqrt T
  have hC : C.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)
  have hCa : C.adjoint = C := hC.isSelfAdjoint
  have hCC : ∀ a, C (C a) = T a := fun a => congrArg (fun D : H →L[ℂ] H => D a)
    (CFC.sqrt_mul_sqrt_self T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT))
  have hCB : ∀ a, C (B a) = B (C a) := fun a => congrArg (fun D : H →L[ℂ] H => D a)
    (hc.cfcₙ_nnreal NNReal.sqrt).eq
  have he : C.adjoint.comp (B.comp C) = T*B := by
    rw [hCa]
    ext a
    change C (B (C a)) = T (B a)
    rw [← hCB,hCC]
  rw [← he]
  exact hB.adjoint_conj C

omit [CompleteSpace K] in
theorem boundedTransform_positive (T B : H →L[ℂ] H) (hT : T.IsPositive) (hB : B.IsPositive)
    (hc : Commute T B) (hi : Function.Injective T)
    (hcircle : ∀ a, T (T a)+B (B a) = a) : PositiveSelfAdjoint (boundedTransform T B) := by
  have hS := boundedTransform_selfAdjoint T B hT.isSelfAdjoint hB.isSelfAdjoint hc hi hcircle
  refine ⟨hS,fun x => ?_⟩
  have hx := (boundedTransform T B).mem_graph x
  rw [boundedTransform_graph T B hi] at hx
  obtain ⟨a,ha,hb⟩ := (mem_transformGraph T B _ _).mp hx
  rw [← ha,← hb,hT.inner_left_eq_inner_right]
  have hp := positive_mul_of_commute T B hT hB hc
  have hreal := (ContinuousLinearMap.isPositive_iff_complex (T*B)).mp hp a
  have he : inner ℂ a (T (B a)) = inner ℂ ((T*B) a) a :=
    (hp.inner_left_eq_inner_right a a).symm
  rw [he]
  refine ⟨?_,hp.re_inner_nonneg_left a⟩
  have hm := congrArg Complex.im hreal.1
  simpa only [Complex.ofReal_im] using hm.symm

omit [CompleteSpace H] [CompleteSpace K] in
theorem transformGraph_square (T B : H →L[ℂ] H) (hc : Commute T B)
    (hcircle : ∀ a, T (T a)+B (B a) = a) (x z : H) :
    (∃ v, (x,v) ∈ transformGraph T B ∧ (v,z) ∈ transformGraph T B) ↔
      ∃ a, T (T a) = x ∧ B (B a) = z := by
  constructor
  · rintro ⟨v,hx,hz⟩
    obtain ⟨a,ha,hav⟩ := (mem_transformGraph T B x v).mp hx
    obtain ⟨b,hbv,hbz⟩ := (mem_transformGraph T B v z).mp hz
    have hp := (transformGraph_equation T B hc hcircle a b).mpr (hav.trans hbv.symm)
    obtain ⟨c,hca,hcb⟩ := (mem_transformGraph T B a b).mp hp
    exact ⟨c,by rw [hca,ha],by rw [hcb,hbz]⟩
  · rintro ⟨a,ha,hb⟩
    refine ⟨B (T a),(mem_transformGraph T B _ _).mpr ⟨T a,ha,rfl⟩,?_⟩
    apply (mem_transformGraph T B _ _).mpr
    exact ⟨B a,congrArg (fun D : H →L[ℂ] H => D a) hc.eq,hb⟩

theorem adjointSquare_resolvent_graph (Q : H →ₗ.[ℂ] K) [hc : Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) (x z : H) :
    (x,z) ∈ (adjointSquare Q).graph ↔ ∃ a, graphResolvent Q a = x ∧ a-graphResolvent Q a = z := by
  have hres : ∀ a, (graphResolvent Q a,a-graphResolvent Q a) ∈ (adjointSquare Q).graph := by
    intro a
    let v := (graphFirst Q).adjoint a
    let y := graphFirst Q v
    have hy : y ∈ Q.domain := LinearPMap.mem_domain_of_mem_graph (graph_coordinates_mem Q v)
    apply (adjointSquare_form Q hQ _ _).mpr
    refine ⟨hy,fun γ => ?_⟩
    have he := (graphFirst Q).adjoint_inner_right (graphVector Q γ) a
    change inner ℂ (graphVector Q γ) v = inner ℂ γ.val a at he
    rw [graph_inner,graphVector_first,graphVector_second] at he
    have hq : Q ⟨y,hy⟩ = graphSecond Q v :=
      Q.mem_graph_snd_inj (Q.mem_graph ⟨y,hy⟩) (graph_coordinates_mem Q v) rfl
    change inner ℂ γ.val (a-y) = inner ℂ (Q γ) (Q ⟨y,hy⟩)
    rw [hq,inner_sub_right]
    change inner ℂ γ.val a-inner ℂ γ.val (graphFirst Q v) = _
    linear_combination -he
  constructor
  · intro hxz
    let a := x+z
    have hr := hres a
    have hp := (adjointSquare Q).graph.sub_mem hxz hr
    have hf := (adjointSquare_form Q hQ _ _).mp hp
    obtain ⟨hx,hf⟩ := hf
    have he := hf ⟨x-graphResolvent Q a,hx⟩
    have hv : z-(a-graphResolvent Q a) = -(x-graphResolvent Q a) := by dsimp [a]; abel
    rw [hv,inner_neg_right] at he
    have hre := congrArg RCLike.re he
    rw [map_neg,inner_self_eq_norm_sq,inner_self_eq_norm_sq] at hre
    have hz : x-graphResolvent Q a = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x-graphResolvent Q a),sq_nonneg ‖Q ⟨x-graphResolvent Q a,hx⟩‖])
    refine ⟨a,(sub_eq_zero.mp hz).symm,?_⟩
    dsimp [a]
    rw [← sub_eq_zero.mp hz]
    abel
  · rintro ⟨a,rfl,rfl⟩
    exact hres a

/-- Literal positive square root of the natural Q*Q, with no additional hypothesis. -/
def graphSquareRoot (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed] : H →ₗ.[ℂ] H :=
  boundedTransform (graphRoot Q) (graphComplementRoot Q)

theorem graphSquareRoot_square (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : IsSquareRoot (adjointSquare Q) (graphSquareRoot Q) := by
  refine ⟨boundedTransform_positive _ _ (graphRoot_positive Q) (graphComplementRoot_positive Q)
    (graph_roots_commute Q) (graphRoot_injective Q hQ) (graph_roots_circle Q),fun x z => ?_⟩
  change (x,z) ∈ (adjointSquare Q).graph ↔
    ∃ v, (x,v) ∈ (boundedTransform (graphRoot Q) (graphComplementRoot Q)).graph ∧
      (v,z) ∈ (boundedTransform (graphRoot Q) (graphComplementRoot Q)).graph
  simp only [boundedTransform_graph (graphRoot Q) (graphComplementRoot Q) (graphRoot_injective Q hQ)]
  rw [transformGraph_square _ _ (graph_roots_commute Q) (graph_roots_circle Q),
    adjointSquare_resolvent_graph Q hQ]
  simp only [graphRoot_square,graphComplementRoot_square]


theorem graphSquareRoot_domain (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) : (graphSquareRoot Q).domain = Q.domain := by
  rw [← graphRoot_range Q hQ]
  ext x
  rw [LinearPMap.mem_domain_iff]
  change (∃ y, (x,y) ∈ (boundedTransform (graphRoot Q) (graphComplementRoot Q)).graph) ↔ _
  rw [boundedTransform_graph _ _ (graphRoot_injective Q hQ)]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha,_⟩ := (mem_transformGraph _ _ x y).mp hy
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨graphComplementRoot Q a,(mem_transformGraph _ _ _ _).mpr ⟨a,ha,rfl⟩⟩

theorem graphSquareRoot_norm (Q : H →ₗ.[ℂ] K) [Fact Q.IsClosed]
    (hQ : Dense (Q.domain : Set H)) (x : (graphSquareRoot Q).domain) (y : Q.domain)
    (hxy : x.val = y.val) : ‖graphSquareRoot Q x‖^2 = ‖Q y‖^2 := by
  have hx := (graphSquareRoot Q).mem_graph x
  change (x.val,graphSquareRoot Q x) ∈ (boundedTransform (graphRoot Q) (graphComplementRoot Q)).graph at hx
  rw [boundedTransform_graph _ _ (graphRoot_injective Q hQ)] at hx
  obtain ⟨a,ha,hb⟩ := (mem_transformGraph _ _ _ _).mp hx
  have hqa : graphRoot Q a ∈ Q.domain := (ha.trans hxy) ▸ y.prop
  have he : (⟨graphRoot Q a,hqa⟩ : Q.domain) = y := Subtype.ext (ha.trans hxy)
  have hn := graphRoot_form_norm Q hQ a hqa
  rw [he,hb] at hn
  exact hn.symm

/-- Generic closed densely-defined graph-form and square-root theorem, completely proved. -/
theorem graphForm : GraphFormObligation := by
  intro H K _ _ _ _ _ _ Q hc hQ
  let : Fact Q.IsClosed := ⟨hc⟩
  refine ⟨adjointSquare Q,graphSquareRoot Q,?_⟩
  exact {
    adjoint_square := mem_adjointSquare_graph Q
    positive := adjointSquare_positive Q hc hQ
    sqrt := graphSquareRoot_square Q hQ
    domain := graphSquareRoot_domain Q hQ
    norm := graphSquareRoot_norm Q hQ
    form := adjointSquare_form Q hQ
    bounded := adjointSquare_bounded Q hQ }

/-- The full principal Hilbert–Schmidt energy theorem, including natural graph and square root. -/
theorem hilbertSchmidtEnergyTheorem : HilbertSchmidtConclusion := hilbertSchmidtEnergy_of_graph graphForm

/-- The full principal differential realization and exact natural-domain theorem. -/
theorem differentialRealizationTheorem : DifferentialConclusion := differentialRealization_of_graph graphForm

end TTO.Paper.Proved
