/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! Exact unitary normal form modulo compact and Schatten kernel perturbations. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem diagonal_adjoint (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D) :
    Diagonal (fun n => conj (w n)) D.adjoint := by
  intro n
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,inner_smul_left,Complex.conj_conj]
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using diagonal_apply w D hd x n

def nodeValueDiagonal (a : ℕ → Disk) (φ : BoundaryLInf) (hφ : toL2 φ ∈ hardy) : SequenceOperator :=
  diagonalOperator (fun n => innerValue φ (a n).val) ‖φ‖ (norm_nonneg φ)
    (fun n => norm_innerValue_le φ hφ (a n))

theorem nodeValueDiagonal_diagonal (a : ℕ → Disk) (φ : BoundaryLInf) (hφ : toL2 φ ∈ hardy) :
    Diagonal (fun n => innerValue φ (a n).val) (nodeValueDiagonal a φ hφ) :=
  diagonalOperator_isDiagonal _ _ _ _

section UnitaryRemainder
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def basisValueOperator (e : HilbertBasis ℕ ℂ H) (a : ℕ → Disk) (φ : BoundaryLInf) (hφ : toL2 φ ∈ hardy) : H →L[ℂ] H :=
  unitaryConjugate e.repr.symm (nodeValueDiagonal a φ hφ)

theorem basisValueOperator_adjoint (e : HilbertBasis ℕ ℂ H) (a : ℕ → Disk)
    (φ : BoundaryLInf) (hφ : toL2 φ ∈ hardy) (n : ℕ) :
    (basisValueOperator e a φ hφ).adjoint (e n) = conj (innerValue φ (a n).val) • e n := by
  rw [basisValueOperator,← unitaryAlgebraLaws.adjoint]
  change e.repr.symm ((nodeValueDiagonal a φ hφ).adjoint (e.repr (e n))) = _
  rw [e.repr_self,diagonal_adjoint _ _ (nodeValueDiagonal_diagonal a φ hφ),map_smul,e.repr_symm_single]

/-- Pure bounded-operator algebra: no invertibility of V+Γ is required. -/
theorem unitary_kernel_remainder (V : H ≃ₗᵢ[ℂ] H) (Γ X Y B C : H →L[ℂ] H)
    (hX : X.adjoint ∘L ((V : H →L[ℂ] H)+Γ) = ((V : H →L[ℂ] H)+Γ) ∘L B.adjoint)
    (hY : Y.adjoint ∘L ((V : H →L[ℂ] H)+Γ) = ((V : H →L[ℂ] H)+Γ) ∘L C.adjoint) :
    X+Y.adjoint = unitaryConjugate V (B+C.adjoint)+
      ((V : H →L[ℂ] H) ∘L (B ∘L Γ.adjoint-Γ.adjoint ∘L X)+
        (Γ ∘L C.adjoint-Y.adjoint ∘L Γ) ∘L (V.symm : H →L[ℂ] H)) := by
  have hx := congrArg ContinuousLinearMap.adjoint hX
  simp only [ContinuousLinearMap.adjoint_comp,map_add,V.adjoint_eq_symm,ContinuousLinearMap.adjoint_adjoint] at hx
  have hx' : (V.symm : H →L[ℂ] H) ∘L X =
      B ∘L (V.symm : H →L[ℂ] H)+(B ∘L Γ.adjoint-Γ.adjoint ∘L X) := by
    rw [← add_sub_assoc]
    apply eq_sub_iff_add_eq.mpr
    simpa only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add] using hx
  have hy' : Y.adjoint ∘L (V : H →L[ℂ] H) =
      (V : H →L[ℂ] H) ∘L C.adjoint+(Γ ∘L C.adjoint-Y.adjoint ∘L Γ) := by
    rw [← add_sub_assoc]
    apply eq_sub_iff_add_eq.mpr
    simpa only [ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add] using hY
  have hxeq : X = unitaryConjugate V B+(V : H →L[ℂ] H) ∘L (B ∘L Γ.adjoint-Γ.adjoint ∘L X) := by
    calc
      X = (V : H →L[ℂ] H) ∘L ((V.symm : H →L[ℂ] H) ∘L X) := by ext x; simp
      _ = _ := by rw [hx',ContinuousLinearMap.comp_add]; rfl
  have hyeq : Y.adjoint = unitaryConjugate V C.adjoint+
      (Γ ∘L C.adjoint-Y.adjoint ∘L Γ) ∘L (V.symm : H →L[ℂ] H) := by
    calc
      Y.adjoint = (Y.adjoint ∘L (V : H →L[ℂ] H)) ∘L (V.symm : H →L[ℂ] H) := by ext x; simp
      _ = _ := by rw [hy',ContinuousLinearMap.add_comp]; rfl
  calc
    X+Y.adjoint = (unitaryConjugate V B+(V : H →L[ℂ] H) ∘L (B ∘L Γ.adjoint-Γ.adjoint ∘L X))+
      (unitaryConjugate V C.adjoint+(Γ ∘L C.adjoint-Y.adjoint ∘L Γ) ∘L (V.symm : H →L[ℂ] H)) := congrArg₂ (·+·) hxeq hyeq
    _ = _ := by rw [unitaryAlgebraLaws.add]; abel

end UnitaryRemainder
/-- The actual mixed TTO has a unitary diagonal normal form in any adjoint-stable two-sided ideal. -/
theorem kernel_remainder_in_ideal (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (a : ℕ → Disk) (φ ψ : BoundaryLInf) (hφ : toL2 φ ∈ hardy) (hψ : toL2 ψ ∈ hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) A)
    (I : Submodule ℂ (Model u →L[ℂ] Model u)) (hI : TwoSided u I)
    (e : HilbertBasis ℕ ℂ (Model u)) (V : Model u ≃ₗᵢ[ℂ] Model u)
    (Γ : Model u →L[ℂ] Model u) (hΓ : Γ ∈ I) (hΓstar : Γ.adjoint ∈ I)
    (hnode : ∀ n, NodeKernel (a n) (V (e n)+Γ (e n)).val) :
    ∃ S : SequenceL2 ≃L[ℂ] Model u, ∃ D : SequenceOperator,
      Diagonal (fun n => innerValue φ (a n).val+conj (innerValue ψ (a n).val)) D ∧
      ∃ K : Model u →L[ℂ] Model u, K ∈ I ∧ A = similarity S D+K := by
  let X := boundedSymbolOperator u φ
  let Y := boundedSymbolOperator u ψ
  let B := basisValueOperator e a φ hφ
  let C := basisValueOperator e a ψ hψ
  have hXrep : RepresentsTTO u (toL2 φ) X := boundedSymbolOperator_represents u φ
  have hYrep : RepresentsTTO u (toL2 ψ) Y := boundedSymbolOperator_represents u ψ
  have hX : X.adjoint ∘L ((V : Model u →L[ℂ] Model u)+Γ) =
      ((V : Model u →L[ℂ] Model u)+Γ) ∘L B.adjoint := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
    rintro _ ⟨n,rfl⟩
    change X.adjoint (V (e n)+Γ (e n)) = (V : Model u →L[ℂ] Model u) (B.adjoint (e n))+Γ (B.adjoint (e n))
    rw [analytic_tto_node_adjoint u hu ⟨toL2 φ,hφ⟩ X hXrep (a n) _ (hnode n),
      basisValueOperator_adjoint e a φ hφ n]
    simp only [map_smul,smul_add]
    rfl
  have hY : Y.adjoint ∘L ((V : Model u →L[ℂ] Model u)+Γ) =
      ((V : Model u →L[ℂ] Model u)+Γ) ∘L C.adjoint := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
    rintro _ ⟨n,rfl⟩
    change Y.adjoint (V (e n)+Γ (e n)) = (V : Model u →L[ℂ] Model u) (C.adjoint (e n))+Γ (C.adjoint (e n))
    rw [analytic_tto_node_adjoint u hu ⟨toL2 ψ,hψ⟩ Y hYrep (a n) _ (hnode n),
      basisValueOperator_adjoint e a ψ hψ n]
    simp only [map_smul,smul_add]
    rfl
  have hArep : RepresentsTTO u (splitSymbol (toL2 φ) (toL2 ψ)) (X+Y.adjoint) :=
    coreLaws.add u _ _ X Y.adjoint hXrep (coreLaws.adjoint u _ Y hYrep)
  have hAe : A = X+Y.adjoint := coreLaws.unique u hu hn _ A _ hA hArep
  let R1 := B ∘L Γ.adjoint-Γ.adjoint ∘L X
  let R2 := Γ ∘L C.adjoint-Y.adjoint ∘L Γ
  have hR1 : R1 ∈ I := by
    apply Submodule.sub_mem (R := ℂ) (M := Model u →L[ℂ] Model u) I
    · simpa using hI Γ.adjoint hΓstar B (ContinuousLinearMap.id ℂ (Model u))
    · simpa using hI Γ.adjoint hΓstar (ContinuousLinearMap.id ℂ (Model u)) X
  have hR2 : R2 ∈ I := by
    apply Submodule.sub_mem (R := ℂ) (M := Model u →L[ℂ] Model u) I
    · simpa using hI Γ hΓ (ContinuousLinearMap.id ℂ (Model u)) C.adjoint
    · simpa using hI Γ hΓ Y.adjoint (ContinuousLinearMap.id ℂ (Model u))
  let K := (V : Model u →L[ℂ] Model u) ∘L R1+R2 ∘L (V.symm : Model u →L[ℂ] Model u)
  have hK : K ∈ I := by
    apply I.add_mem
    · simpa using hI R1 hR1 (V : Model u →L[ℂ] Model u) (ContinuousLinearMap.id ℂ (Model u))
    · simpa using hI R2 hR2 (ContinuousLinearMap.id ℂ (Model u)) (V.symm : Model u →L[ℂ] Model u)
  let S := (e.repr.symm.trans V).toContinuousLinearEquiv
  let D := nodeValueDiagonal a φ hφ+(nodeValueDiagonal a ψ hψ).adjoint
  have hd : Diagonal (fun n => innerValue φ (a n).val+conj (innerValue ψ (a n).val)) D := by
    intro n
    change nodeValueDiagonal a φ hφ (lp.single 2 n (1 : ℂ))+
      (nodeValueDiagonal a ψ hψ).adjoint (lp.single 2 n (1 : ℂ)) = _
    rw [nodeValueDiagonal_diagonal a φ hφ n,diagonal_adjoint _ _ (nodeValueDiagonal_diagonal a ψ hψ) n,add_smul]
  have hNormal : unitaryConjugate V (B+C.adjoint) = similarity S D := by
    change unitaryConjugate V (unitaryConjugate e.repr.symm (nodeValueDiagonal a φ hφ)+
      (unitaryConjugate e.repr.symm (nodeValueDiagonal a ψ hψ)).adjoint) = _
    rw [← unitaryAlgebraLaws.adjoint,← unitaryAlgebraLaws.add]
    ext x
    rfl
  refine ⟨S,D,hd,K,hK,?_⟩
  calc
    A = X+Y.adjoint := hAe
    _ = unitaryConjugate V (B+C.adjoint)+K := unitary_kernel_remainder V Γ X Y B C hX hY
    _ = similarity S D+K := by rw [hNormal]

/-- The complete compact/all-positive-p remainder interface, with no open proof parameter. -/
theorem kernelRemainder : KernelRemainderObligation := by
  intro u hu hn a _hi _hz φ ψ hφ hψ A hA
  constructor
  · rintro ⟨e,V,Γ,hΓ,hnode⟩
    obtain ⟨I,hI,hmem⟩ := idealCarriers.compact u
    obtain ⟨S,D,hd,K,hK,he⟩ := kernel_remainder_in_ideal u hu hn a φ ψ hφ hψ A hA I hI e V Γ
      ((hmem Γ).mpr hΓ) ((hmem Γ.adjoint).mpr (compact_adjoint_of_compact Γ hΓ)) hnode
    exact ⟨S,D,hd,K,(hmem K).mp hK,he⟩
  · intro p hp
    rintro ⟨e,V,Γ,hΓ,hnode⟩
    obtain ⟨I,hI,hmem⟩ := idealCarriers.schatten u p hp
    obtain ⟨S,D,hd,K,hK,he⟩ := kernel_remainder_in_ideal u hu hn a φ ψ hφ hψ A hA I hI e V Γ
      ((hmem Γ).mpr hΓ) ((hmem Γ.adjoint).mpr ((schatten_adjoint_iff Γ p).mpr hΓ)) hnode
    exact ⟨S,D,hd,K,(hmem K).mp hK,he⟩

/-- Interpolating-symbol classification from an analytic bounded-symbol lift. -/
theorem perturbedKernelBasisClassification_of_lift (hL : AnalyticLiftObligation) : PerturbedBasisConclusion :=
  perturbedKernelBasisClassification hL kernelRemainder

section CompactPerturbation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The native Fredholm alternative gives an actual inverse, not an extra hypothesis. -/
theorem compact_add_one_isUnit (K : H →L[ℂ] H) (hK : IsCompactOperator K)
    (hinj : Function.Injective (1+K : H →L[ℂ] H)) : IsUnit (1+K) := by
  rcases hK.hasEigenvalue_or_mem_resolventSet (by norm_num : (-1 : ℂ) ≠ 0) with he | hr
  · obtain ⟨x,hx⟩ := he.exists_hasEigenvector
    have hz : (1+K : H →L[ℂ] H) x = 0 := by
      change x+K x = 0
      have heq : K x = (-1 : ℂ) • x := hx.apply_eq_smul
      rw [heq,neg_one_smul,add_neg_cancel]
    exact (hx.2 (hinj (hz.trans (map_zero _).symm))).elim
  · have hu := spectrum.mem_resolventSet_iff.mp hr
    have he : algebraMap ℂ (H →L[ℂ] H) (-1)-K = -(1+K) := by
      rw [Algebra.algebraMap_eq_smul_one,neg_one_smul]
      abel
    rw [he] at hu
    simpa only [neg_neg] using hu.neg

/-- Dense range suffices for a compact perturbation of a unitary to be invertible. -/
theorem unitary_add_compact_isUnit (V : H ≃ₗᵢ[ℂ] H) (Γ : H →L[ℂ] H)
    (hΓ : IsCompactOperator Γ) (hd : DenseRange ((V : H →L[ℂ] H)+Γ)) :
    IsUnit ((V : H →L[ℂ] H)+Γ) := by
  let F := (V : H →L[ℂ] H)+Γ
  have hrange : F.range.topologicalClosure = ⊤ := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mp
    change DenseRange F
    exact hd
  have hker : F.adjoint.ker = ⊥ := by
    rw [← F.orthogonal_range,← Submodule.orthogonal_closure,hrange]
    simp
  have hinj : Function.Injective F.adjoint := LinearMap.ker_eq_bot.mp hker
  let K := Γ.adjoint ∘L (V : H →L[ℂ] H)
  have hK : IsCompactOperator K := (compact_adjoint_of_compact Γ hΓ).comp_clm (V : H →L[ℂ] H)
  have hJ : (1+K : H →L[ℂ] H) = F.adjoint ∘L (V : H →L[ℂ] H) := by
    ext x
    simp [F,K,map_add,V.adjoint_eq_symm]
  have hJinj : Function.Injective (1+K : H →L[ℂ] H) := by
    rw [hJ]
    exact hinj.comp V.injective
  have hJsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp (compact_add_one_isUnit K hK hJinj)).2
  have hsurj : Function.Surjective F.adjoint := by
    intro y
    obtain ⟨x,hx⟩ := hJsurj y
    refine ⟨V x,?_⟩
    rw [hJ] at hx
    exact hx
  have hFu : IsUnit F.adjoint := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,hsurj⟩
  simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using hFu.star

end CompactPerturbation

/-- A U+compact kernel system is an actual Riesz synthesis, without assuming functional interpolation. -/
theorem perturbedKernelBasis_riesz (u : BoundaryLInf) (hu : IsInner u) (_hn : Nonconstant u)
    (a : ℕ → Disk) (hi : Function.Injective a) (hz : HasBlaschkeZeros u a)
    (hb : PerturbedKernelBasis u a {Γ | IsCompactOperator Γ}) :
    ∃ R : SequenceL2 ≃L[ℂ] Model u, RieszSynthesis u a R := by
  obtain ⟨e,V,Γ,hΓ,hnode⟩ := hb
  let F := (V : Model u →L[ℂ] Model u)+Γ
  have hcol (n : ℕ) : F (e n) = blaschkeNodeModel u hu a hz n := by
    apply Subtype.ext
    exact nodeKernel_eq_hardyNodeVector (a n) _ (hnode n)
  have hd : DenseRange F := by
    apply Dense.mono _ (blaschkeNodes_dense_of_division blaschkeHardyDivision u hu a hi hz)
    intro x hx
    have hsub : Submodule.span ℂ (Set.range (blaschkeNodeModel u hu a hz)) ≤ F.range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      exact ⟨e n,hcol n⟩
    exact hsub hx
  obtain ⟨w,hw⟩ := unitary_add_compact_isUnit V Γ hΓ hd
  let R := e.repr.symm.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.ofUnit w)
  refine ⟨R,fun n => ?_⟩
  have he : R (lp.single 2 n (1 : ℂ)) = F (e n) := by
    change (w : Model u →L[ℂ] Model u) (e.repr.symm (lp.single 2 n (1 : ℂ))) = F (e n)
    rw [e.repr_symm_single,hw]
  rw [he]
  exact hnode n

/-- Actual Riesz kernel synthesis supplies H² interpolants for bounded data by Blaschke summability. -/
theorem hardy_interpolate_of_riesz (u : BoundaryLInf) (a : ℕ → Disk) (hz : HasBlaschkeZeros u a)
    (R : SequenceL2 ≃L[ℂ] Model u) (hR : RieszSynthesis u a R)
    (w : ℕ → ℂ) (M : ℝ) (hw : ∀ n, ‖w n‖ ≤ M) :
    ∃ f : Hardy, ∀ n, analyticValue f.val (a n).val = w n := by
  let δ (n : ℕ) := Real.sqrt (1-‖(a n).val‖^2)
  have hdef (n : ℕ) : 0 < 1-‖(a n).val‖^2 := by
    have hn : ‖(a n).val‖ < 1 := (a n).property
    nlinarith [norm_nonneg (a n).val]
  have hsum : Summable (fun n => ‖(δ n : ℂ)*w n‖^2) := by
    apply (hz.1.mul_left (2*M^2)).of_nonneg_of_le (fun n => sq_nonneg _)
    intro n
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hdef n).le]
    have hw2 := pow_le_pow_left₀ (norm_nonneg (w n)) (hw n) 2
    have hsmall : 1-‖(a n).val‖^2 ≤ 2*(1-‖(a n).val‖) := by nlinarith [sq_nonneg (1-‖(a n).val‖)]
    calc
      (1-‖(a n).val‖^2)*‖w n‖^2 ≤ (1-‖(a n).val‖^2)*M^2 := mul_le_mul_of_nonneg_left hw2 (hdef n).le
      _ ≤ (2*(1-‖(a n).val‖))*M^2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg M)
      _ = _ := by ring
  let c : SequenceL2 := ⟨fun n => (δ n : ℂ)*w n,by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hsum⟩
  let f := dualSynthesis R c
  refine ⟨⟨f.val,f.property.1⟩,fun n => ?_⟩
  have hpair : inner ℂ (R (lp.single 2 n (1 : ℂ))) f = (δ n : ℂ)*w n := by
    rw [← dualSynthesis_coord]
    change ((dualSynthesis R).symm ((dualSynthesis R) c)) n = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  change inner ℂ (R (lp.single 2 n (1 : ℂ))).val f.val = _ at hpair
  rw [inner_nodeKernel (a n) _ (hR n) ⟨f.val,f.property.1⟩] at hpair
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hdef n)))) hpair

/-- H∞ interpolation from Riesz synthesis and an analytic-lift hypothesis. -/
theorem interpolating_of_riesz_and_lift (hL : AnalyticLiftObligation)
    (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (a : ℕ → Disk)
    (hi : Function.Injective a) (hz : HasBlaschkeZeros u a)
    (R : SequenceL2 ≃L[ℂ] Model u) (hR : RieszSynthesis u a R) : Interpolating a := by
  intro w hw
  obtain ⟨M,hM⟩ := hw
  obtain ⟨f,hf⟩ := hardy_interpolate_of_riesz u a hz R hR w M hM
  obtain ⟨S,_hS,_hnS,_hinS,hmodel⟩ := dualDiagonal u hu hn a hi hz R hR
  let D := diagonalOperator w M ((norm_nonneg (w 0)).trans (hM 0)) hM
  have hD : Diagonal (fun n => analyticValue f.val (a n).val) D := by
    simpa only [hf] using diagonalOperator_isDiagonal w M ((norm_nonneg (w 0)).trans (hM 0)) hM
  let A := similarity S D
  have hA : RepresentsTTO u f.val A := (hmodel f).2 D hD
  obtain ⟨g,hg,hgA⟩ := hL u hu hn f A hA
  refine ⟨g,hg,fun n => ?_⟩
  let k := R (lp.single 2 n (1 : ℂ))
  have hk : ‖k‖ = 1 := by
    change ‖k.val‖ = 1
    rw [nodeKernel_eq_hardyNodeVector (a n) _ (hR n)]
    exact norm_hardyNodeVector (a n)
  have hfE := analytic_tto_node_adjoint u hu f A hA (a n) k (hR n)
  have hgE := analytic_tto_node_adjoint u hu ⟨toL2 g,hg⟩ A hgA (a n) k (hR n)
  have he := congrArg (fun v => inner ℂ k v) (hgE.symm.trans hfE)
  rw [inner_smul_right (𝕜 := ℂ) (E := Model u),inner_smul_right (𝕜 := ℂ) (E := Model u),
    inner_self_eq_one_of_norm_eq_one hk,mul_one,mul_one] at he
  have hc := congrArg conj he
  simpa only [innerValue,Complex.conj_conj,hf] using hc

/-- No functional interpolation premise is added to the source's perturbed-kernel example. -/
theorem alternatingInterpolation_of_lift (hL : AnalyticLiftObligation) : AlternatingInterpolationObligation := by
  intro u hu hn a hi hz p _hp hb
  obtain ⟨e,V,Γ,hΓ,hnode⟩ := hb
  obtain ⟨R,hR⟩ := perturbedKernelBasis_riesz u hu hn a hi hz ⟨e,V,Γ,hΓ.2.1,hnode⟩
  apply interpolating_of_riesz_and_lift hL u hu hn a hi hz R hR alternatingValues
  refine ⟨1,fun n => ?_⟩
  unfold alternatingValues
  split_ifs <;> norm_num

theorem toL2_zero : toL2 (0 : BoundaryLInf) = 0 := by
  rw [← boundaryInclusion_apply,map_zero]

theorem toL2_sub (g h : BoundaryLInf) : toL2 (g-h) = toL2 g-toL2 h := by
  rw [← boundaryInclusion_apply,map_sub,boundaryInclusion_apply,boundaryInclusion_apply]

theorem toL2_neg (g : BoundaryLInf) : toL2 (-g) = -toL2 g := by
  rw [← boundaryInclusion_apply,map_neg,boundaryInclusion_apply]

/-- Actual scalar shifts of native bounded analytic symbols and their TTOs. -/
theorem shiftSymbolLaws : ShiftSymbolLaws where
  analytic_zero := by rw [toL2_zero]; exact hardy.zero_mem
  zero_value z _hz := by rw [innerValue,toL2_zero,analyticValue_zero]
  zero_split g := by
    have hz : star (0 : BoundaryL2) = 0 := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_star (0 : BoundaryL2),Lp.coeFn_zero (ℂ) 2 circleMeasure] with t hs h0
      change (star (0 : BoundaryL2)) t = conj ((0 : BoundaryL2) t) at hs
      change (0 : BoundaryL2) t = 0 at h0
      rw [hs,h0,map_zero]
    simp only [splitSymbol,toL2_zero,hz,add_zero]
  analytic_shift g hg c := by
    rw [toL2_sub,toL2_constLInf]
    exact hardy.sub_mem hg (constantCoreLaws.hardy c)
  shift_value g c z hz := by
    rw [innerValue,toL2_sub,toL2_constLInf,analyticValue_sub _ _ hz]
    change analyticValue (toL2 g) z-analyticValue (constL2 c) z = analyticValue (toL2 g) z-c
    rw [constL2_fourier,analyticValue_smul _ _ hz]
    have he : analyticValue (fourierBasis (T := 1) (0 : ℤ)) z = 1 := by
      simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z
    rw [he,mul_one]
  shift_operator u g c X hX := by
    rw [toL2_sub,toL2_constLInf]
    exact coreLaws.sub u _ _ X _ hX (constantCoreLaws.represents u c)
  unshift_operator u g c X hX := by
    have he := coreLaws.add u _ _ X _ hX (constantCoreLaws.represents u c)
    rw [toL2_sub,toL2_constLInf,sub_add_cancel] at he
    exact he
  negative_l2 := toL2_neg
  negative_value g z hz := by
    rw [innerValue,toL2_neg,← neg_one_smul ℂ (toL2 g),analyticValue_smul _ _ hz,neg_one_mul]
    rfl

/-- The two constant subsequences preclude every positive-power summable scalar shift. -/
theorem alternatingDivergence : AlternatingDivergenceObligation := by
  intro p hp c hs
  have ht := tendsto_zero_of_summableValues (fun n => alternatingValues n-c) p hp hs
  have heven : StrictMono (fun n : ℕ => 2*n) := by intro i j hij; change 2*i < 2*j; omega
  have hodd : StrictMono (fun n : ℕ => 2*n+1) := by intro i j hij; change 2*i+1 < 2*j+1; omega
  have he := ht.comp heven.tendsto_atTop
  have ho := ht.comp hodd.tendsto_atTop
  have hev (n : ℕ) : alternatingValues (2*n)-c = -c := by simp [alternatingValues]
  have hod (n : ℕ) : alternatingValues (2*n+1)-c = 1-c := by simp [alternatingValues]
  have he' : Tendsto (fun _ : ℕ => -c) atTop (𝓝 0) := by
    convert he using 1
    funext n; exact (hev n).symm
  have ho' : Tendsto (fun _ : ℕ => 1-c) atTop (𝓝 0) := by
    convert ho using 1
    funext n; exact (hod n).symm
  have hc : c=0 := neg_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds he')
  have hc' : 1-c=0 := tendsto_nhds_unique tendsto_const_nhds ho'
  norm_num [hc] at hc'

/-- Interpolating classification and symbol splitting from an analytic-lift hypothesis. -/
theorem blaschkeSplitting_of_lift (hL : AnalyticLiftObligation) : BlaschkeSplittingConclusion :=
  Reduction.blaschkeSplitting (perturbedKernelBasisClassification_of_lift hL) coreLaws scalarSplit
    shiftSymbolLaws (alternatingInterpolation_of_lift hL) alternatingDivergence

end TTO.Paper.Proved
