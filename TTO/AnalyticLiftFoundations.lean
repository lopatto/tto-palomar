/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.GraphFoundations
public import TTO.AnalyticBoundaryFoundations
public import TTO.BlaschkeFoundations
public import TTO.KernelRemainderFoundations
public import Mathlib.Analysis.Analytic.Constructions

/-! Equal-Gram contractions and analytic lifting infrastructure. -/

@[expose] public section
noncomputable section
open Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved

variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Equal Gram families determine an isometry of their closed spans, extended by zero
on the orthogonal complement of the source span. No independence or countability is required. -/
theorem exists_contraction_of_equal_gram (p : I → E) (q : I → F)
    (hGram : ∀ i j, inner ℂ (p i) (p j) = inner ℂ (q i) (q j)) :
    ∃ T : E →L[ℂ] F, ‖T‖ ≤ 1 ∧ ∀ i, T (p i) = q i := by
  classical
  let P := Finsupp.linearCombination ℂ p
  let Q := Finsupp.linearCombination ℂ q
  have hn : ∀ c : I →₀ ℂ, ‖Q c‖ = ‖P c‖ := by
    intro c
    simp only [Q, P, Finsupp.linearCombination_apply, Finsupp.sum,
      norm_eq_sqrt_re_inner (𝕜 := ℂ), sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hGram]
  let K₀ := LinearMap.range P
  let K := K₀.topologicalClosure
  let e : (I →₀ ℂ) →ₗ[ℂ] K := (Submodule.inclusion K₀.le_topologicalClosure).comp P.rangeRestrict
  have hi : DenseRange (Submodule.inclusion K₀.le_topologicalClosure) := by
    exact (denseRange_inclusion_iff
      (show (K₀ : Set E) ⊆ K from K₀.le_topologicalClosure)).mpr (fun x hx => hx)
  have hd : DenseRange e := hi.comp P.surjective_rangeRestrict.denseRange
    (continuous_subtype_val.subtype_mk _)
  have hne : ∀ c, ‖Q c‖ = ‖e c‖ := by
    intro c
    change ‖Q c‖ = ‖P c‖
    exact hn c
  let L : K →ₗᵢ[ℂ] F := Q.extendOfIsometry hd hne
  let T : E →L[ℂ] F := L.toContinuousLinearMap.comp K.orthogonalProjectionOnto
  refine ⟨T, T.opNorm_le_bound zero_le_one ?_, ?_⟩
  · intro x
    change ‖L (K.orthogonalProjectionOnto x)‖ ≤ 1 * ‖x‖
    rw [L.norm_map, one_mul]
    exact K.norm_orthogonalProjectionOnto_apply_le x
  · intro i
    have hp : p i ∈ K := K₀.le_topologicalClosure ⟨Finsupp.single i 1, by simp [P]⟩
    change L (K.orthogonalProjectionOnto (p i)) = q i
    rw [K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨p i,hp⟩]
    have he : e (Finsupp.single i 1) = ⟨p i,hp⟩ := by
      apply Subtype.ext
      simp [e,P]
    rw [← he]
    change Q.extendOfIsometry hd hne (e (Finsupp.single i 1)) = q i
    rw [LinearMap.extendOfIsometry_eq]
    simp [Q]

section Colligation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ScalarHilbertSum (H : Type*) := WithLp 2 (H × ℂ)

def scalarHilbertInl : H →L[ℂ] ScalarHilbertSum H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H ℂ)

omit [CompleteSpace H] in
@[simp] theorem scalarHilbertInl_apply (x : H) :
    scalarHilbertInl x = WithLp.toLp 2 (x, (0 : ℂ)) := rfl

def colligationState (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) : H →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H ℂ).comp (T.comp scalarHilbertInl)

def colligationInput (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) : H :=
  (T (WithLp.toLp 2 (0, (1 : ℂ)))).fst

def colligationOutput (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) : H →L[ℂ] ℂ :=
  (WithLp.sndL 2 ℂ H ℂ).comp (T.comp scalarHilbertInl)

def colligationConstant (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) : ℂ :=
  (T (WithLp.toLp 2 (0, (1 : ℂ)))).snd

omit [CompleteSpace H] in
theorem colligationState_norm_le (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H)
    (hT : ‖T‖ ≤ 1) : ‖colligationState T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(T (WithLp.toLp 2 (x, (0 : ℂ)))).fst‖ ≤ 1 * ‖x‖
  rw [one_mul]
  calc
    _ ≤ ‖T (WithLp.toLp 2 (x, (0 : ℂ)))‖ := WithLp.norm_fst_le H _
    _ ≤ ‖T‖ * ‖WithLp.toLp 2 (x, (0 : ℂ))‖ := T.le_opNorm _
    _ ≤ ‖x‖ := by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg x)

omit [CompleteSpace H] in
theorem colligation_pair (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H)
    (z : ℂ) (x : H) :
    T (WithLp.toLp 2 (z • x, (1 : ℂ))) =
      WithLp.toLp 2 (z • colligationState T x + colligationInput T,
        z * colligationOutput T x + colligationConstant T) := by
  have hp : WithLp.toLp 2 (z • x, (1 : ℂ)) =
      z • scalarHilbertInl x + WithLp.toLp 2 (0, (1 : ℂ)) := by
    apply WithLp.ofLp_injective
    simp
  rw [hp, map_add, map_smul]
  apply WithLp.ofLp_injective
  ext <;> simp [colligationState, colligationInput, colligationOutput, colligationConstant]

def colligationTransfer (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (z : ℂ) : ℂ :=
  colligationConstant T + z * colligationOutput T
    (Ring.inverse (1 - z • colligationState T) (colligationInput T))

theorem colligation_resolvent_unit
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) : IsUnit (1 - z • colligationState T) := by
  have hn : ‖z • colligationState T‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (colligationState_norm_le T hT) (norm_nonneg z)).trans_lt
      (by simpa using hz)
  exact (Units.oneSub (z • colligationState T) hn).isUnit

theorem colligation_resolvent_state
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    let x := Ring.inverse (1 - z • colligationState T) (colligationInput T)
    z • colligationState T x + colligationInput T = x := by
  dsimp
  have he := congrArg (fun A : H →L[ℂ] H => A (colligationInput T))
    (Ring.mul_inverse_cancel (1 - z • colligationState T) (colligation_resolvent_unit T hT z hz))
  change Ring.inverse (1 - z • colligationState T) (colligationInput T) -
    z • colligationState T (Ring.inverse (1 - z • colligationState T) (colligationInput T)) =
      colligationInput T at he
  exact ((eq_sub_iff_add_eq.mp he.symm).symm.trans (add_comm _ _)).symm

theorem colligationTransfer_analytic
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1) :
    AnalyticOnNhd ℂ (colligationTransfer T) disk := by
  intro z hz
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 - w • colligationState T) z := by fun_prop
  have hu := colligation_resolvent_unit T hT z hz
  have hr : AnalyticAt ℂ Ring.inverse (1 - z • colligationState T) := by
    rw [← hu.unit_spec]
    exact analyticAt_inverse (𝕜 := ℂ) hu.unit
  have hi : AnalyticAt ℂ (fun w : ℂ => Ring.inverse (1 - w • colligationState T)) z :=
    hr.comp (f := fun w : ℂ => 1 - w • colligationState T) ha
  have hx := ((ContinuousLinearMap.apply ℂ H (colligationInput T)).analyticAt _).comp hi
  have ho := ((colligationOutput T).analyticAt _).comp hx
  exact analyticAt_const.add (analyticAt_id.mul ho)

theorem colligationTransfer_norm_le
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) : ‖colligationTransfer T z‖ ≤ 1 := by
  let x := Ring.inverse (1 - z • colligationState T) (colligationInput T)
  have he : T (WithLp.toLp 2 (z • x, (1 : ℂ))) =
      WithLp.toLp 2 (x, colligationTransfer T z) := by
    rw [colligation_pair,colligation_resolvent_state T hT z hz]
    congr 1
    simp [colligationTransfer,x,add_comm]
  have hn : ‖T (WithLp.toLp 2 (z • x, (1 : ℂ)))‖ ≤
      ‖WithLp.toLp 2 (z • x, (1 : ℂ))‖ :=
    (T.le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg (WithLp.toLp 2 (z • x, (1 : ℂ)))))
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  rw [he,WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2] at hs
  change ‖x‖^2 + ‖colligationTransfer T z‖^2 ≤ ‖z • x‖^2 + ‖(1 : ℂ)‖^2 at hs
  rw [norm_smul,mul_pow,norm_one,one_pow] at hs
  have hz2 : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hm := mul_le_mul_of_nonneg_right hz2 (sq_nonneg ‖x‖)
  nlinarith [norm_nonneg (colligationTransfer T z)]

theorem colligationTransfer_interpolate
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) (v : H) (w : ℂ)
    (hv : T (WithLp.toLp 2 (z • v, (1 : ℂ))) = WithLp.toLp 2 (v,w)) :
    colligationTransfer T z = w := by
  rw [colligation_pair] at hv
  have hs := congrArg WithLp.fst hv
  have ho := congrArg WithLp.snd hv
  change z • colligationState T v + colligationInput T = v at hs
  change z * colligationOutput T v + colligationConstant T = w at ho
  have hl : (1 - z • colligationState T) v = colligationInput T := by
    change v - z • colligationState T v = colligationInput T
    exact sub_eq_iff_eq_add.mpr (hs.symm.trans (add_comm _ _))
  have hx : Ring.inverse (1 - z • colligationState T) (colligationInput T) = v := by
    rw [← hl]
    exact congrArg (fun A : H →L[ℂ] H => A v)
      (Ring.inverse_mul_cancel _ (colligation_resolvent_unit T hT z hz))
  simpa [colligationTransfer,hx,add_comm] using ho

/-- A contractive colligation interpolates every specified node through one Schur function. -/
theorem exists_schur_of_colligation_nodes
    (T : ScalarHilbertSum H →L[ℂ] ScalarHilbertSum H) (hT : ‖T‖ ≤ 1)
    (a : I → ℂ) (ha : ∀ i, ‖a i‖ < 1) (v : I → H) (w : I → ℂ)
    (hv : ∀ i, T (WithLp.toLp 2 (a i • v i, (1 : ℂ))) = WithLp.toLp 2 (v i,w i)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F disk ∧ (∀ z ∈ disk, ‖F z‖ ≤ 1) ∧
      ∀ i, F (a i) = w i :=
  ⟨colligationTransfer T,colligationTransfer_analytic T hT,
    fun z hz => colligationTransfer_norm_le T hT z hz,
    fun i => colligationTransfer_interpolate T hT (a i) (ha i) (v i) (w i) (hv i)⟩


end Colligation

section Defect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded positive defect associated with a Hilbert-space contraction. -/
theorem contraction_defect_positive (B : H →L[ℂ] H) (hB : ‖B‖ ≤ 1) :
    (1 - B * B.adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have he : inner ℂ ((1 - B * B.adjoint) x) x =
      ((‖x‖^2 - ‖B.adjoint x‖^2 : ℝ) : ℂ) := by
    simp only [sub_apply,one_apply_eq_self,
      mul_apply_eq_comp,inner_sub_left]
    rw [← ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K,Complex.ofReal_sub]
    push_cast
    rfl
  have hn : ‖B.adjoint x‖ ≤ ‖x‖ :=
    (B.adjoint.le_opNorm x).trans (by
      rw [ContinuousLinearMap.adjoint.norm_map]
      simpa using mul_le_mul_of_nonneg_right hB (norm_nonneg x))
  rw [he]
  constructor
  · norm_cast
  · change 0 ≤ ‖x‖^2 - ‖B.adjoint x‖^2
    nlinarith [norm_nonneg x,norm_nonneg (B.adjoint x)]

def contractionDefectRoot (B : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (1 - B * B.adjoint)

theorem contractionDefectRoot_inner (B : H →L[ℂ] H) (hB : ‖B‖ ≤ 1) (x y : H) :
    inner ℂ (contractionDefectRoot B x) (contractionDefectRoot B y) =
      inner ℂ x y - inner ℂ (B.adjoint x) (B.adjoint y) := by
  let D := contractionDefectRoot B
  have hD : D.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hDa : D.adjoint = D := hD.isSelfAdjoint
  have hDD : D * D = 1 - B * B.adjoint :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (contraction_defect_positive B hB))
  calc
    inner ℂ (D x) (D y) = inner ℂ x (D (D y)) := by
      rw [← ContinuousLinearMap.adjoint_inner_right,hDa]
    _ = inner ℂ x ((1 - B * B.adjoint) y) := by
      rw [← mul_apply_eq_comp,hDD]
    _ = inner ℂ x y - inner ℂ (B.adjoint x) (B.adjoint y) := by
      simp only [sub_apply,one_apply_eq_self,
        mul_apply_eq_comp,inner_sub_right]
      rw [ContinuousLinearMap.adjoint_inner_left]

end Defect

/-- An unnormalized Szegő vector at an actual zero of the inner function. -/
def zeroSzegoModel (u : BoundaryLInf) (hu : IsInner u) (w : Disk)
    (hw : innerValue u w.val = 0) : Model u :=
  ⟨(szegoKernel w).val,szegoKernel_mem_model u hu w hw⟩

theorem zeroSzegoModel_gram (u : BoundaryLInf) (hu : IsInner u) (v w : Disk)
    (hv : innerValue u v.val = 0) (hw : innerValue u w.val = 0) :
    inner ℂ (zeroSzegoModel u hu v hv) (zeroSzegoModel u hu w hw) =
      (1 - v.val * conj w.val)⁻¹ := by
  change inner ℂ (szegoKernel v) (szegoKernel w) = _
  rw [inner_szegoKernel,analyticValue_szegoKernel w v.property,mul_comm (conj w.val)]

theorem analytic_tto_zeroSzego_adjoint (u : BoundaryLInf) (hu : IsInner u)
    (φ : Hardy) (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A)
    (w : Disk) (hw : innerValue u w.val = 0) :
    A.adjoint (zeroSzegoModel u hu w hw) =
      conj (analyticValue φ.val w.val) • zeroSzegoModel u hu w hw := by
  let c : ℂ := Real.sqrt (1 - ‖w.val‖^2)
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    have hnorm : ‖w.val‖ < 1 := w.property
    nlinarith [norm_nonneg w.val]
  let k := zeroSzegoModel u hu w hw
  have hk : NodeKernel w (c • k).val := nodeKernel_hardyNodeVector w
  have he := analytic_tto_node_adjoint u hu φ A hA w (c • k) hk
  rw [map_smul,smul_comm] at he
  exact (smul_right_injective _ hc) he


/-- Actual adjoint eigenvectors on zero kernels produce a Schur interpolant.
The defect vectors live in the literal conjugate model, so the resulting transfer
function interpolates at the original nodes without a reflection convention. -/
theorem exists_schur_of_model_eigenvalues (u : BoundaryLInf) (hu : IsInner u)
    (a : I → Disk) (ha : ∀ i, innerValue u (a i).val = 0)
    (B : Model u →L[ℂ] Model u) (hB : ‖B‖ ≤ 1)
    (w : I → ℂ)
    (heigen : ∀ i, B.adjoint (zeroSzegoModel u hu (a i) (ha i)) =
      conj (w i) • zeroSzegoModel u hu (a i) (ha i)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F disk ∧ (∀ z ∈ disk, ‖F z‖ ≤ 1) ∧
      ∀ i, F (a i).val = w i := by
  let k i := zeroSzegoModel u hu (a i) (ha i)
  let v i := modelStarIsometry u (contractionDefectRoot B (k i))
  have hrel : ∀ i j, (1 - conj (a i).val * (a j).val) * inner ℂ (v i) (v j) =
      1 - conj (w i) * w j := by
    intro i j
    have hi : ‖(a i).val‖ < 1 := (a i).property
    have hj : ‖(a j).val‖ < 1 := (a j).property
    have hn : ‖conj (a i).val * (a j).val‖ < 1 := by
      rw [norm_mul,Complex.norm_conj]
      nlinarith [norm_nonneg (a i).val,norm_nonneg (a j).val]
    have hd : 1 - conj (a i).val * (a j).val ≠ 0 := sub_ne_zero.mpr (by
      intro h
      have he := congrArg norm h
      rw [norm_one] at he
      linarith)
    change (1 - conj (a i).val * (a j).val) *
      inner ℂ (modelStarIsometry u (contractionDefectRoot B (k i)))
        (modelStarIsometry u (contractionDefectRoot B (k j))) = _
    have hem : inner ℂ (B.adjoint (k i)) (B.adjoint (k j)) =
        w i * conj (w j) * inner ℂ (k i) (k j) := by
      rw [heigen i,heigen j,
        inner_smul_left (k i) (conj (w j) • k j) (conj (w i)),
        inner_smul_right (k i) (k j) (conj (w j)),Complex.conj_conj]
      ring
    rw [modelStar_inner,contractionDefectRoot_inner B hB,hem]
    simp only [k,zeroSzegoModel_gram,map_sub,map_mul,map_inv₀,map_one,Complex.conj_conj]
    field_simp
  let p i : ScalarHilbertSum (ConjugateModel u) := WithLp.toLp 2 ((a i).val • v i,(1 : ℂ))
  let q i : ScalarHilbertSum (ConjugateModel u) := WithLp.toLp 2 (v i,w i)
  have hGram : ∀ i j, inner ℂ (p i) (p j) = inner ℂ (q i) (q j) := by
    intro i j
    change inner ℂ ((a i).val • v i) ((a j).val • v j) + inner ℂ (1 : ℂ) 1 =
      inner ℂ (v i) (v j) + inner ℂ (w i) (w j)
    rw [inner_smul_left (v i) ((a j).val • v j) (a i).val,
      inner_smul_right (v i) (v j) (a j).val]
    simp only [RCLike.inner_apply,map_one,mul_one]
    linear_combination -(hrel i j)
  obtain ⟨T,hT,hTv⟩ := exists_contraction_of_equal_gram p q hGram
  exact exists_schur_of_colligation_nodes T hT (fun i => (a i).val)
    (fun i => (a i).property) v w hTv


/-- A bounded analytic creator admits a uniformly bounded analytic function agreeing
at every supplied zero, without any interpolation-sequence hypothesis. -/
theorem analytic_tto_bounded_zero_interpolant (u : BoundaryLInf) (hu : IsInner u)
    (a : I → Disk) (ha : ∀ i, innerValue u (a i).val = 0)
    (φ : Hardy) (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) :
    ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧
      ∀ i, innerValue g (a i).val = analyticValue φ.val (a i).val := by
  let C : ℝ := ‖A‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  let B : Model u →L[ℂ] Model u := (C : ℂ)⁻¹ • A
  have hB : ‖B‖ ≤ 1 := by
    change ‖(C : ℂ)⁻¹ • A‖ ≤ 1
    refine (ContinuousLinearMap.opNorm_smul_le ((C : ℂ)⁻¹) A).trans ?_
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hC.le]
    exact (inv_mul_le_iff₀ hC).mpr (by dsimp [C]; linarith)
  let w i := (C : ℂ)⁻¹ * analyticValue φ.val (a i).val
  have he : ∀ i, B.adjoint (zeroSzegoModel u hu (a i) (ha i)) =
      conj (w i) • zeroSzegoModel u hu (a i) (ha i) := by
    intro i
    change (ContinuousLinearMap.adjoint ((C : ℂ)⁻¹ • A)) _ = _
    rw [map_smulₛₗ]
    simp only [smul_apply,analytic_tto_zeroSzego_adjoint u hu φ A hA,
      smul_smul,w,map_mul]
  obtain ⟨F,hF,hFn,hFi⟩ := exists_schur_of_model_eigenvalues u hu a ha B hB w he
  have hG : AnalyticOnNhd ℂ (fun z => (C : ℂ)*F z) disk := by
    intro z hz
    exact analyticAt_const.mul (hF z hz)
  have hGn : ∀ z ∈ disk, ‖(C : ℂ)*F z‖ ≤ C := by
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hC.le]
    simpa using mul_le_mul_of_nonneg_left (hFn z hz) hC.le
  obtain ⟨g,hg,hgv,_hb,_hn⟩ := exists_boundedAnalyticBoundary _ hG C hGn
  refine ⟨g,hg,fun i => ?_⟩
  rw [hgv _ (a i).property,hFi]
  simp [w,hC0]

/-- The analytic lift needed by the simple-Blaschke principal results.
Kernel totality is proved from actual Blaschke Hardy division; no Riesz/interpolation
hypothesis is introduced. This does not assert the lift for arbitrary inner functions. -/
theorem analyticLift_simpleBlaschke (u : BoundaryLInf) (hu : IsInner u)
    (a : ℕ → Disk) (hi : Function.Injective a) (hz : HasBlaschkeZeros u a)
    (φ : Hardy) (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) :
    ∃ g : BoundaryLInf, toL2 g ∈ hardy ∧ RepresentsTTO u (toL2 g) A := by
  obtain ⟨g,hg,hgv⟩ := analytic_tto_bounded_zero_interpolant u hu a
    (blaschkeNodes_zero u a hz) φ A hA
  let D := boundedSymbolOperator u g
  have hD : RepresentsTTO u (toL2 g) D := boundedSymbolOperator_represents u g
  have he : A.adjoint = D.adjoint := by
    apply ContinuousLinearMap.ext_on (blaschkeNodes_dense_of_division blaschkeHardyDivision u hu a hi hz)
    rintro _ ⟨n,rfl⟩
    rw [analytic_tto_node_adjoint u hu φ A hA (a n) _ (blaschkeNodeModel_kernel u hu a hz n),
      analytic_tto_node_adjoint u hu ⟨toL2 g,hg⟩ D hD (a n) _ (blaschkeNodeModel_kernel u hu a hz n)]
    change conj (analyticValue φ.val (a n).val) • _ = conj (innerValue g (a n).val) • _
    rw [hgv n]
  have hAD : A = D := by
    simpa using congrArg ContinuousLinearMap.adjoint he
  exact ⟨g,hg,hAD.symm ▸ hD⟩


section PrincipalBlaschke
open Reduction

theorem boundedSplit_iff_simpleBlaschke (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (a : ℕ → Disk) (hi : Function.Injective a) (hz : HasBlaschkeZeros u a)
    (A : Model u →L[ℂ] Model u) : HasBoundedAnalyticSplit u A ↔ HasBoundedSymbolSplit u A := by
  constructor
  · rintro ⟨φ,ψ,X,Y,hx,hy,rfl⟩
    obtain ⟨g,hg,hX⟩ := analyticLift_simpleBlaschke u hu a hi hz φ X hx
    have hψ : RepresentsTTO u ψ.val Y.adjoint := by simpa using coreLaws.adjoint u _ Y hy
    obtain ⟨k,hk,hY⟩ := analyticLift_simpleBlaschke u hu a hi hz ψ Y.adjoint hψ
    have hY' : RepresentsTTO u (star (toL2 k)) Y := by
      simpa using coreLaws.adjoint u _ Y.adjoint hY
    exact ⟨g,k,hg,hk,coreLaws.add u _ _ _ _ hX hY'⟩
  · rintro ⟨g,k,hg,hk,he⟩
    obtain ⟨X,hx⟩ := coreLaws.bounded u g
    obtain ⟨Y,hy⟩ := coreLaws.bounded u (star k)
    have hy' : RepresentsTTO u (star (toL2 k)) Y := (coreLaws.star_toL2 k) ▸ hy
    exact ⟨⟨toL2 g,hg⟩,⟨toL2 k,hk⟩,X,Y,hx,hy',
      coreLaws.unique u hu hn _ A (X+Y) he (coreLaws.add u _ _ _ _ hx hy')⟩

/-- Full T4, with its original simple-Blaschke scope and every positive Schatten exponent. -/
theorem perturbedKernelBasisClassificationTheorem : PerturbedBasisConclusion := by
  intro u hu hn a ha hb
  refine ⟨boundedSplit_iff_simpleBlaschke u hu hn a ha hb,?_⟩
  intro φ ψ hφ hψ A he
  have hk := kernelRemainder u hu hn a ha hb φ ψ hφ hψ A he
  constructor
  · intro hbase
    obtain ⟨S,D,hd,K,hkc,rfl⟩ := hk.1 hbase
    have hp : IsCompactOperator (similarity S D+K) ↔ IsCompactOperator (similarity S D) := by
      constructor
      · intro hsum
        have hz := idealLaws.compact_add _ _ hsum (idealLaws.compact_neg _ hkc)
        simpa using hz
      · intro h0
        exact idealLaws.compact_add _ _ h0 hkc
    exact hp.trans ((idealLaws.compact_similarity S D).trans (diagonalLaws.compact _ D hd))
  · intro p hp hbase
    obtain ⟨S,D,hd,K,hks,rfl⟩ := hk.2 p hp hbase
    have hpert : Schatten p (similarity S D+K) ↔ Schatten p (similarity S D) := by
      constructor
      · intro hsum
        have hz := idealLaws.schatten_add p _ _ hsum (idealLaws.schatten_neg p _ hks)
        simpa using hz
      · intro h0
        exact idealLaws.schatten_add p _ _ h0 hks
    exact hpert.trans ((idealLaws.schatten_similarity S D p).trans (diagonalLaws.schatten _ D hd p hp))

/-- Actual Riesz data imply bounded analytic interpolation, using the proved
simple-Blaschke lift at this same inner function and these same nodes. -/
theorem interpolating_of_riesz
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
  obtain ⟨g,hg,hgA⟩ := analyticLift_simpleBlaschke u hu a hi hz f A hA
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

theorem alternatingInterpolation : AlternatingInterpolationObligation := by
  intro u hu hn a hi hz p _hp hb
  obtain ⟨e,V,Γ,hΓ,hnode⟩ := hb
  obtain ⟨R,hR⟩ := perturbedKernelBasis_riesz u hu hn a hi hz ⟨e,V,Γ,hΓ.2.1,hnode⟩
  apply interpolating_of_riesz u hu hn a hi hz R hR alternatingValues
  refine ⟨1,fun n => ?_⟩
  unfold alternatingValues
  split_ifs <;> norm_num

/-- Full R5: scalar-shift criterion and its original failure-of-splitting example. -/
theorem blaschkeSplittingTheorem : BlaschkeSplittingConclusion :=
  Reduction.blaschkeSplitting perturbedKernelBasisClassificationTheorem coreLaws scalarSplit
    shiftSymbolLaws alternatingInterpolation alternatingDivergence

end PrincipalBlaschke

end TTO.Paper.Proved
