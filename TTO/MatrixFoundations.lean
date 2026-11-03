/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.TensorFoundations

/-! Literal tensor coordinates, kernel data and coefficient analysis for the energy graph. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

section ModelTensorBasis
variable {I : Type*}

def modelTensorMode (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) (ij : I × I) : TensorModel u :=
  ⟨separatedProduct (b ij.1).val (b ij.2).val,separatedProduct_mem_tensorModel u (b ij.1) (b ij.2)⟩

theorem modelTensorMode_orthonormal (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) :
    Orthonormal ℂ (modelTensorMode u b) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (separatedProduct (b i.1).val (b i.2).val) (separatedProduct (b j.1).val (b j.2).val) = _
  rw [inner_separatedProduct]
  change inner ℂ (b i.1) (b j.1)*inner ℂ (b i.2) (b j.2) = _
  rw [orthonormal_iff_ite.mp b.orthonormal,orthonormal_iff_ite.mp b.orthonormal]
  by_cases ha : i.1 = j.1 <;> by_cases hb : i.2 = j.2 <;> simp [ha,hb,Prod.ext_iff]

theorem modelTensorModes_total (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) :
    (Submodule.span ℂ (Set.range (modelTensorMode u b))).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro G hG
  apply Subtype.ext
  let L := innerSL ℂ G.val
  have hbc (i j : I) : separatedProduct (b i).val (b j).val ∈ L.ker := by
    have hz : inner ℂ (modelTensorMode u b (i,j)) G = 0 :=
      (Submodule.mem_orthogonal _ _).mp hG _ (Submodule.subset_span ⟨(i,j),rfl⟩)
    exact inner_eq_zero_symm.mp hz
  have hle : tensorModel u ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro H ⟨f,g,hH⟩
      have he : H = separatedProduct f.val g.val :=
        Lp.ext (Filter.EventuallyEq.trans hH (separatedProduct_ae f.val g.val).symm)
      rw [he]
      exact separatedProduct_mem_of_basis (model u) (model u) b b L.ker L.isClosed_ker hbc f g
    · exact L.isClosed_ker
  exact inner_self_eq_zero.mp (hle G.property)

def modelTensorBasis (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) : HilbertBasis (I × I) ℂ (TensorModel u) :=
  HilbertBasis.mkOfOrthogonalEqBot (modelTensorMode_orthonormal u b) (modelTensorModes_total u b)

@[simp] theorem modelTensorBasis_apply (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) (ij : I × I) :
    modelTensorBasis u b ij = modelTensorMode u b ij :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (modelTensorMode_orthonormal u b) (modelTensorModes_total u b)) ij

theorem modelTensorBasis_repr (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) (G : TensorModel u) (ij : I × I) :
    (modelTensorBasis u b).repr G ij = inner ℂ (separatedProduct (b ij.1).val (b ij.2).val) G.val := by
  rw [HilbertBasis.repr_apply_apply,modelTensorBasis_apply]
  rfl

end ModelTensorBasis

/-- The fixed-second-factor elementary tensor map on the actual model space. -/
def modelTensorRight (u : BoundaryLInf) (f : Model u) : Model u →L[ℂ] BidiskL2 :=
  separatedBilinear.flip f.val ∘L (model u).subtypeL

theorem modelTensorRight_add (u : BoundaryLInf) (f g : Model u) :
    modelTensorRight u (f+g) = modelTensorRight u f+modelTensorRight u g := by
  apply ContinuousLinearMap.ext
  intro h
  exact separatedProduct_add_right h.val f.val g.val

theorem modelTensorRight_smul (u : BoundaryLInf) (c : ℂ) (f : Model u) :
    modelTensorRight u (c • f) = c • modelTensorRight u f := by
  apply ContinuousLinearMap.ext
  intro h
  exact separatedProduct_smul_right c h.val f.val

theorem norm_modelTensorRight_le (u : BoundaryLInf) (f : Model u) : ‖modelTensorRight u f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro g
  change ‖separatedProduct g.val f.val‖ ≤ ‖f‖*‖g‖
  rw [norm_separatedProduct]
  exact le_of_eq (mul_comm _ _)

/-- Genuine bounded operator associated to a concrete L² tensor; the two conjugate linearities cancel. -/
def tensorOperator (u : BoundaryLInf) (G : BidiskL2) : Model u →L[ℂ] ConjugateModel u :=
  LinearMap.mkContinuous
    { toFun := fun f => modelStarIsometry u ((modelTensorRight u f).adjoint G)
      map_add' := fun f g => by
        rw [modelTensorRight_add,map_add,add_apply,map_add]
      map_smul' := fun c f => by
        rw [modelTensorRight_smul,map_smulₛₗ,smul_apply,map_smulₛₗ]
        simp only [starRingEnd_self_apply,RingHom.id_apply] }
    ‖G‖ (fun f => by
      change ‖modelStarIsometry u ((modelTensorRight u f).adjoint G)‖ ≤ ‖G‖*‖f‖
      rw [(modelStarIsometry u).norm_map]
      calc
        _ ≤ ‖(modelTensorRight u f).adjoint‖*‖G‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖modelTensorRight u f‖*‖G‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
        _ ≤ _ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (norm_modelTensorRight_le u f) (norm_nonneg G))

/-- Its literal first-linear matrix pairing, with all conjugations visible. -/
theorem tensorOperator_inner (u : BoundaryLInf) (G : BidiskL2) (f g : Model u) :
    inner ℂ (modelStarIsometry u g) (tensorOperator u G f) =
      conj (inner ℂ (separatedProduct g.val f.val) G) := by
  change inner ℂ (modelStarIsometry u g) (modelStarIsometry u ((modelTensorRight u f).adjoint G)) = _
  rw [modelStar_inner]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right (modelTensorRight u f) g G

/-- Honest L² boundary product; only the first factor is required bounded. -/
def boundedModelProduct (u : BoundaryLInf) (f g : Model u) (hf : IsBounded f.val) : BoundaryL2 :=
  multiply (hf.toLp f.val) g.val

theorem boundedModelProduct_ae (u : BoundaryLInf) (f g : Model u) (hf : IsBounded f.val) :
    boundedModelProduct u f g hf =ᵐ[circleMeasure] fun t => f.val t*g.val t := by
  filter_upwards [multiply_ae (hf.toLp f.val) g.val,hf.coeFn_toLp] with t hm ht
  change multiply (hf.toLp f.val) g.val t = _
  rw [hm,ht]

theorem inner_boundedModelProduct_mode (u : BoundaryLInf) (hu : IsInner u) (f g : Model u)
    (hf : IsBounded f.val) (n : ℕ) :
    inner ℂ (multiply (multiplyInf u u) (fourierBasis (T := 1) (n : ℤ))) (boundedModelProduct u f g hf) = 0 := by
  have hm : toL2 (mode ((n+1 : ℕ) : ℤ)) ∈ hardy := by
    rw [toL2_mode]
    exact fourierBasis_mem_hardy (n+1)
  let h : Hardy := ⟨multiply (mode ((n+1 : ℕ) : ℤ)) (conjugation u f.val),
    multiply_mem_hardy _ hm _ (conjugation_mem_model u hu f).1⟩
  have hh : h.val =ᵐ[circleMeasure] fun t =>
      fourier (T := 1) ((n+1 : ℕ) : ℤ) t*(u t*conj (fourier (T := 1) 1 t)*conj (f.val t)) := by
    filter_upwards [multiply_ae (mode ((n+1 : ℕ) : ℤ)) (conjugation u f.val),
      mode_ae ((n+1 : ℕ) : ℤ),conjugation_ae u f.val] with t hp ht hc
    change multiply (mode ((n+1 : ℕ) : ℤ)) (conjugation u f.val) t = _
    rw [hp,ht,hc]
  have he : inner ℂ (multiply (multiplyInf u u) (fourierBasis (T := 1) (n : ℤ))) (boundedModelProduct u f g hf) =
      inner ℂ (multiply u h.val) g.val := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiply_ae (multiplyInf u u) (fourierBasis (T := 1) (n : ℤ)),
      multiplyInf_ae u u,fourierBasis_ae (n : ℤ),boundedModelProduct_ae u f g hf,multiply_ae u h.val,hh]
      with t h1 h2 h3 h4 h5 h6
    simp only [RCLike.inner_apply,h1,h2,h3,h4,h5,h6,Nat.cast_add,Nat.cast_one,
      fourier_add,map_mul,Complex.conj_conj]
    calc
      _ = g.val t*f.val t*conj (u t)^2*conj (fourier (T := 1) (n : ℤ) t) := by ring
      _ = (g.val t*f.val t*conj (u t)^2*conj (fourier (T := 1) (n : ℤ) t))*
          (fourier (T := 1) 1 t*conj (fourier (T := 1) 1 t)) := by rw [fourier_mul_conj,mul_one]
      _ = _ := by ring
  exact he.trans (inner_multiply_model u g h)

/-- A product with one bounded model factor belongs to the literal square model. -/
theorem boundedModelProduct_mem (u : BoundaryLInf) (hu : IsInner u) (f g : Model u) (hf : IsBounded f.val) :
    boundedModelProduct u f g hf ∈ model (multiplyInf u u) := by
  have he : toL2 (hf.toLp f.val) = f.val := Lp.ext ((toL2_ae _).trans hf.coeFn_toLp)
  refine ⟨multiply_mem_hardy _ (he.symm ▸ f.property.1) _ g.property.1,?_⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    exact inner_boundedModelProduct_mode u hu f g hf n
  | zero => exact inner_zero_left _
  | add x y hx hy hx' hy' => rw [inner_add_left,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_left,hx',mul_zero]

theorem analyticValue_boundedModelProduct (u : BoundaryLInf) (f g : Model u) (hf : IsBounded f.val) (w : Disk) :
    analyticValue (boundedModelProduct u f g hf) w.val = analyticValue f.val w.val*analyticValue g.val w.val := by
  have he : toL2 (hf.toLp f.val) = f.val := Lp.ext ((toL2_ae _).trans hf.coeFn_toLp)
  rw [boundedModelProduct,analyticValue_multiply _ (he.symm ▸ f.property.1) ⟨g.val,g.property.1⟩ w]
  change analyticValue (toL2 (hf.toLp f.val)) w.val*analyticValue g.val w.val = _
  rw [he]

/-- On the model tensor, ambient Szegő evaluation is exactly model-kernel evaluation. -/
theorem analyticValue₂_tensor_kernels (u : BoundaryLInf) (hu : IsInner u) (G : TensorModel u) (z w : Disk) :
    analyticValue₂ G.val z.val w.val =
      inner ℂ (separatedProduct (modelReproducingKernel u hu z).val (modelReproducingKernel u hu w).val) G.val := by
  let kz := modelReproducingKernel u hu z
  let kw := modelReproducingKernel u hu w
  let rz : Hardy := ⟨(szegoKernel z).val-kz.val,hardy.sub_mem (szegoKernel z).property kz.property.1⟩
  let rw : Hardy := ⟨(szegoKernel w).val-kw.val,hardy.sub_mem (szegoKernel w).property kw.property.1⟩
  have hz : rz.val ∈ (model u).orthogonal := by
    apply (model u).orthogonalProjectionOnto_eq_zero_iff.mp
    change (model u).orthogonalProjectionOnto ((szegoKernel z).val-kz.val) = 0
    rw [map_sub,modelProjection_szegoKernel u hu z,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  have hw : rw.val ∈ (model u).orthogonal := by
    apply (model u).orthogonalProjectionOnto_eq_zero_iff.mp
    change (model u).orthogonalProjectionOnto ((szegoKernel w).val-kw.val) = 0
    rw [map_sub,modelProjection_szegoKernel u hu w,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  have hez : (szegoKernel z).val = kz.val+rz.val := by dsimp [rz]; abel
  have hew : (szegoKernel w).val = kw.val+rw.val := by dsimp [rw]; abel
  rw [analyticValue₂_eq_inner ⟨G.val,tensorModel_le_bidiskHardy u G.property⟩ z w]
  rw [hez,separatedProduct_add_left,inner_add_left,
    inner_separatedProduct_tensor_zero u rz (szegoKernel w) (Or.inl hz) G,add_zero,
    hew,separatedProduct_add_right,inner_add_left,
    inner_separatedProduct_tensor_zero u ⟨kz.val,kz.property.1⟩ rw (Or.inr hw) G,add_zero]

/-- Model kernels determine all bounded linear maps by their actual dense span. -/
theorem clm_eq_of_modelKernels {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : BoundaryLInf) (hu : IsInner u) (A B : Model u →L[ℂ] F)
    (h : ∀ w : Disk, A (modelReproducingKernel u hu w) = B (modelReproducingKernel u hu w)) : A = B := by
  have hspan : Submodule.span ℂ (Set.range (modelReproducingKernel u hu)) ≤ (A-B).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    change A (modelReproducingKernel u hu w)-B (modelReproducingKernel u hu w) = 0
    rw [h w,sub_self]
  have hc := (Submodule.span ℂ (Set.range (modelReproducingKernel u hu))).topologicalClosure_minimal hspan (A-B).isClosed_ker
  have hd := modelReproducingKernels_dense u hu
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
  rw [hd] at hc
  apply ContinuousLinearMap.ext
  intro f
  have hz := hc (show f ∈ (⊤ : Submodule ℂ (Model u)) from trivial)
  exact sub_eq_zero.mp hz

theorem bounded_modelStar (u : BoundaryLInf) (f : Model u) (hf : IsBounded f.val) :
    IsBounded (modelStarIsometry u f).val :=
  hf.star.ae_eq (Lp.coeFn_star f.val).symm

/-- Conjugate model vectors are determined by conjugated actual model kernels. -/
theorem conjugateModel_eq_of_kernel_inner (u : BoundaryLInf) (hu : IsInner u)
    (A B : ConjugateModel u)
    (h : ∀ w : Disk, inner ℂ (modelStarIsometry u (modelReproducingKernel u hu w)) A =
      inner ℂ (modelStarIsometry u (modelReproducingKernel u hu w)) B) : A = B := by
  let a : Model u := ⟨star A.val,star_mem_model_of_conjugateModel u A⟩
  let b : Model u := ⟨star B.val,star_mem_model_of_conjugateModel u B⟩
  have ha : modelStarIsometry u a = A := Subtype.ext (star_star A.val)
  have hb : modelStarIsometry u b = B := Subtype.ext (star_star B.val)
  have he : (⟨a.val,a.property.1⟩ : Hardy) = (⟨b.val,b.property.1⟩ : Hardy) :=
    hardy_analyticValue_injective _ _ (fun z hz => by
      have hh := h ⟨z,hz⟩
      rw [← ha,← hb,modelStar_inner,modelStar_inner,
        inner_modelReproducingKernel,inner_modelReproducingKernel] at hh
      simpa only [Complex.conj_conj] using congrArg conj hh)
  have hab : a = b := Subtype.ext (congrArg (fun x : Hardy => x.val) he)
  exact ha.symm.trans ((congrArg (modelStarIsometry u) hab).trans hb)

/-- Literal projected raw L²-symbol column on any bounded model input. -/
def rawTHOColumn (u : BoundaryLInf) (σ : BoundaryL2) (f : Model u) (hf : IsBounded f.val) : ConjugateModel u :=
  (conjugateModel u).orthogonalProjectionOnto (coreMultiply σ ⟨f.val,hf⟩)

theorem rawTHOColumn_inner (u : BoundaryLInf) (σ : BoundaryL2) (f : Model u) (hf : IsBounded f.val)
    (g : ConjugateModel u) : inner ℂ g (rawTHOColumn u σ f hf) = coreForm σ f.val g.val := by
  rw [coreForm_eq_inner_left σ _ _ hf]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left g _

/-- Core pairing against a conjugated bounded model vector is the literal conjugated product integral. -/
theorem coreForm_star_product (u : BoundaryLInf) (η : BoundaryL2) (f g : Model u) (hg : IsBounded g.val) :
    coreForm (star η) f.val (modelStarIsometry u g).val =
      conj (inner ℂ (boundedModelProduct u g f hg) η) := by
  rw [coreForm,L2.inner_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star η,Lp.coeFn_star g.val,boundedModelProduct_ae u g f hg] with t hη hg ht
  change (star η) t = conj (η t) at hη
  change (star g.val) t = conj (g.val t) at hg
  change (star η) t*f.val t*conj ((star g.val) t) = _
  rw [hη,hg,RCLike.inner_apply,ht]
  simp only [map_mul,Complex.conj_conj]
  ring

theorem coreForm_star_kernel_pair (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) (z w : Disk) :
    coreForm (star η) (modelReproducingKernel u hu w).val (modelStarIsometry u (modelReproducingKernel u hu z)).val =
      conj (FKernel u η z.val w.val) := by
  rw [coreForm_star_product u η _ _ (bounded_modelReproducingKernel u hu z),FKernel,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [boundedModelProduct_ae u (modelReproducingKernel u hu z) (modelReproducingKernel u hu w)
    (bounded_modelReproducingKernel u hu z),modelReproducingKernel_ae u hu z,modelReproducingKernel_ae u hu w]
    with t hp hz hw
  rw [RCLike.inner_apply,hp,hz,hw]

/-- Kernel tests suffice by first fixing a bounded source kernel, then a bounded opposite test. -/
theorem representsTHO_iff_kernel_pairs (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2)
    (B : Model u →L[ℂ] ConjugateModel u) :
    RepresentsTHO u (star η) B ↔
      ∀ z w : Disk, inner ℂ (modelStarIsometry u (modelReproducingKernel u hu z))
        (B (modelReproducingKernel u hu w)) = conj (FKernel u η z.val w.val) := by
  constructor
  · intro hB z w
    exact (hB _ _ (bounded_modelReproducingKernel u hu w)
      (bounded_modelStar u _ (bounded_modelReproducingKernel u hu z))).trans (coreForm_star_kernel_pair u hu η z w)
  · intro hB
    have hcol (w : Disk) : B (modelReproducingKernel u hu w) =
        rawTHOColumn u (star η) (modelReproducingKernel u hu w) (bounded_modelReproducingKernel u hu w) := by
      apply conjugateModel_eq_of_kernel_inner u hu
      intro z
      rw [hB z w,rawTHOColumn_inner,coreForm_star_kernel_pair]
    intro f g _hf hg
    let v := multiply (hg.toLp g.val) η
    let L := innerSL ℂ g ∘L B
    let R := innerSL ℂ v ∘L (model u).subtypeL
    have he : L = R := clm_eq_of_modelKernels u hu L R (fun w => by
      change inner ℂ g (B (modelReproducingKernel u hu w)) = inner ℂ v (modelReproducingKernel u hu w).val
      rw [hcol w,rawTHOColumn_inner,coreForm_eq_inner_right (star η) _ _ hg,star_star])
    have hh := congrArg (fun A => A f) he
    change inner ℂ g (B f) = inner ℂ v f.val at hh
    rw [coreForm_eq_inner_right (star η) _ _ hg,star_star]
    exact hh

/-- The literal analytic graph is equivalent to representing the actual raw THO form. -/
theorem QGraph_iff_tensorOperator (u : BoundaryLInf) (hu : IsInner u) (η : Ambient u) (G : TensorModel u) :
    QGraph u η G ↔ RepresentsTHO u (star η.val) (tensorOperator u G.val) := by
  rw [representsTHO_iff_kernel_pairs u hu η.val]
  constructor
  · intro h z w
    rw [tensorOperator_inner,← analyticValue₂_tensor_kernels u hu G z w]
    exact congrArg conj (h z.val z.property w.val w.property)
  · intro h z hz w hw
    have he := h ⟨z,hz⟩ ⟨w,hw⟩
    rw [tensorOperator_inner,← analyticValue₂_tensor_kernels u hu G ⟨z,hz⟩ ⟨w,hw⟩] at he
    simpa only [Complex.conj_conj] using congrArg conj he

section ConcreteMatrixData
variable {I : Type*}

/-- Completely specified integral coefficient as a genuine continuous linear functional on K_(u²). -/
def tensorCoefficient (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (ij : I × I) : Ambient u →L[ℂ] ℂ :=
  innerSL ℂ (boundedModelProduct u (b ij.1) (b ij.2) (hb ij.1)) ∘L (model (multiplyInf u u)).subtypeL

theorem tensorCoefficient_apply (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (ij : I × I) (η : Ambient u) :
    tensorCoefficient u b hb ij η = inner ℂ (boundedModelProduct u (b ij.1) (b ij.2) (hb ij.1)) η.val := rfl

theorem tensorCoefficient_integral (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (ij : I × I) (η : Ambient u) :
    tensorCoefficient u b hb ij η =
      ∫ t, η.val t*conj ((b ij.1).val t*(b ij.2).val t) ∂circleMeasure := by
  rw [tensorCoefficient_apply,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedModelProduct_ae u (b ij.1) (b ij.2) (hb ij.1)] with t ht
  rw [RCLike.inner_apply,ht]

/-- Full raw form reconstruction from bounded basis columns, with no unused MatrixData fields. -/
theorem representsTHO_of_basis_rawColumns (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (σ : BoundaryL2) (B : Model u →L[ℂ] ConjugateModel u)
    (hB : ∀ i, B (b i) = rawTHOColumn u σ (b i) (hb i)) : RepresentsTHO u σ B := by
  intro f g _hf hg
  let v := multiply (hg.toLp g.val) (star σ)
  let L := innerSL ℂ g ∘L B
  let R := innerSL ℂ v ∘L (model u).subtypeL
  have he : L = R := clm_eq_of_hilbertBasis b L R (fun i => by
    change inner ℂ g (B (b i)) = inner ℂ v (b i).val
    rw [hB i,rawTHOColumn_inner,coreForm_eq_inner_right σ _ _ hg])
  have h := congrArg (fun A => A f) he
  change inner ℂ g (B f) = inner ℂ v f.val at h
  exact h.trans (coreForm_eq_inner_right σ f.val g.val hg).symm

/-- The concrete tensor coordinates agree with the raw operator exactly when they are the symbol coefficients. -/
theorem tensorOperator_represents_iff_coefficients (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (η : Ambient u) (G : TensorModel u) :
    RepresentsTHO u (star η.val) (tensorOperator u G.val) ↔
      ∀ ij : I × I, (modelTensorBasis u b).repr G ij = tensorCoefficient u b hb ij η := by
  constructor
  · intro hB ij
    have he := hB (b ij.2) (modelStarIsometry u (b ij.1)) (hb ij.2) (bounded_modelStar u _ (hb ij.1))
    rw [tensorOperator_inner,coreForm_star_product u η.val _ _ (hb ij.1)] at he
    rw [modelTensorBasis_repr,tensorCoefficient_apply]
    simpa only [Complex.conj_conj] using congrArg conj he
  · intro hc
    apply representsTHO_of_basis_rawColumns u b hb (star η.val) (tensorOperator u G.val)
    intro j
    apply (conjugateBasis u b).repr.injective
    apply lp.ext
    funext i
    rw [(conjugateBasis u b).repr_apply_apply,(conjugateBasis u b).repr_apply_apply,
      conjugateBasis_apply,tensorOperator_inner,rawTHOColumn_inner,coreForm_star_product u η.val _ _ (hb i)]
    congr 1
    exact (modelTensorBasis_repr u b G (i,j)).symm.trans (hc (i,j))

/-- The true square-model reproducing kernel, distinct from the squared u-kernel. -/
def ambientKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) : Ambient u :=
  modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w

/-- The literal squared u-kernel as a verified member of K_(u²). -/
def squaredModelKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) : Ambient u :=
  ⟨boundedModelProduct u (modelReproducingKernel u hu w) (modelReproducingKernel u hu w)
      (bounded_modelReproducingKernel u hu w),
    boundedModelProduct_mem u hu _ _ (bounded_modelReproducingKernel u hu w)⟩

theorem squaredModelKernel_value (u : BoundaryLInf) (hu : IsInner u) (w z : Disk) :
    analyticValue (squaredModelKernel u hu w).val z.val = kernelValue u w.val z.val^2 := by
  change analyticValue (boundedModelProduct u (modelReproducingKernel u hu w) (modelReproducingKernel u hu w)
    (bounded_modelReproducingKernel u hu w)) z.val = _
  rw [analyticValue_boundedModelProduct,analyticValue_modelReproducingKernel u hu w z.property]
  exact (pow_two _).symm

theorem tensorCoefficient_ambientKernel (u : BoundaryLInf) (hu : IsInner u) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (w : Disk) (ij : I × I) :
    tensorCoefficient u b hb ij (ambientKernel u hu w) =
      conj (analyticValue (b ij.1).val w.val*analyticValue (b ij.2).val w.val) := by
  let p : Ambient u := ⟨boundedModelProduct u (b ij.1) (b ij.2) (hb ij.1),
    boundedModelProduct_mem u hu _ _ (hb ij.1)⟩
  rw [tensorCoefficient_apply,← inner_conj_symm]
  change conj (inner ℂ (ambientKernel u hu w) p) = _
  rw [ambientKernel,inner_modelReproducingKernel]
  exact congrArg conj (analyticValue_boundedModelProduct u _ _ (hb ij.1) w)

theorem ambientKernel_coefficients (u : BoundaryLInf) (hu : IsInner u) (b : HilbertBasis I ℂ (Model u))
    (hb : ∀ i, IsBounded (b i).val) (w : Disk) :
    ∃ x : lp (fun _ : I × I => ℂ) 2, ∀ ij, x ij = tensorCoefficient u b hb ij (ambientKernel u hu w) := by
  let k := modelReproducingKernel u hu w
  let G : TensorModel u := ⟨separatedProduct k.val k.val,separatedProduct_mem_tensorModel u k k⟩
  refine ⟨(modelTensorBasis u b).repr G,?_⟩
  intro ij
  rw [modelTensorBasis_repr,tensorCoefficient_ambientKernel]
  change inner ℂ (separatedProduct (b ij.1).val (b ij.2).val) (separatedProduct k.val k.val) = _
  rw [inner_separatedProduct]
  have hi : inner ℂ (b ij.1).val k.val = conj (analyticValue (b ij.1).val w.val) := by
    change inner ℂ (b ij.1) k = _
    rw [← inner_conj_symm,inner_modelReproducingKernel]
  have hj : inner ℂ (b ij.2).val k.val = conj (analyticValue (b ij.2).val w.val) := by
    change inner ℂ (b ij.2) k = _
    rw [← inner_conj_symm,inner_modelReproducingKernel]
  rw [hi,hj,map_mul]

/-- Fully specified matrix data built from the actual bounded basis, native tensor and literal kernels. -/
def actualMatrixData (u : BoundaryLInf) (hu : IsInner u) : MatrixData u where
  Index := ModelBasisIndex u hu
  countable := inferInstance
  basis := boundedModelBasis u hu
  bounded := bounded_boundedModelBasis u hu
  coefficient := tensorCoefficient u (boundedModelBasis u hu) (bounded_boundedModelBasis u hu)
  coefficient_eq := tensorCoefficient_integral u (boundedModelBasis u hu) (bounded_boundedModelBasis u hu)
  tensor := (modelTensorBasis u (boundedModelBasis u hu)).repr.symm
  graph_coefficients η G :=
    (QGraph_iff_tensorOperator u hu η G).trans
      (tensorOperator_represents_iff_coefficients u (boundedModelBasis u hu) (bounded_boundedModelBasis u hu) η G)
  kernel := ambientKernel u hu
  kernel_value w z := analyticValue_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w z.property
  total := modelReproducingKernels_dense (multiplyInf u u) (isInner_multiplyInf u u hu hu)
  kernel_coefficients := ambientKernel_coefficients u hu (boundedModelBasis u hu) (bounded_boundedModelBasis u hu)
  squareKernel := squaredModelKernel u hu
  squareKernel_value := squaredModelKernel_value u hu
  reproduces η w := (inner_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w η).symm

/-- The entire actual coefficient/tensor/kernel data obligation, with no unproved graph premise. -/
theorem matrixData : MatrixDataObligation := fun u hu _hn => ⟨actualMatrixData u hu⟩

end ConcreteMatrixData

/-- Working T8 entry point after constructing the literal matrix/tensor/kernel data. -/
theorem hilbertSchmidtEnergy_of_matrix (hP : BoundaryParsevalObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : HilbertSchmidtConclusion :=
  hilbertSchmidtEnergy_of_tensor matrixData hP hF hTests

/-- Working T9 entry point after constructing the literal matrix/tensor/kernel data. -/
theorem differentialRealization_of_matrix (hP : BoundaryParsevalObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : DifferentialConclusion :=
  differentialRealization_of_tensor matrixData hP hF hTests

/-- Interior bidisk values determine the actual Hardy class, not arbitrary bidisk L² classes. -/
theorem bidiskHardy_analyticValue₂_injective (G H : ↥bidiskHardy)
    (h : ∀ z w : Disk, analyticValue₂ G.val z.val w.val = analyticValue₂ H.val z.val w.val) : G = H := by
  let R := G.val-H.val
  have hR : R ∈ bidiskHardy := bidiskHardy.sub_mem G.property H.property
  have hv (z w : Disk) : analyticValue₂ R z.val w.val = 0 := by
    rw [analyticValue₂_eq_inner ⟨R,hR⟩ z w]
    change inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val) (G.val-H.val) = 0
    rw [inner_sub_right,← analyticValue₂_eq_inner G z w,← analyticValue₂_eq_inner H z w,h z w,sub_self]
  have hsec (w : Disk) : firstSection R w = 0 := hardy_analyticValue_injective _ _ (fun z hz => by
    change analyticValue (firstSection R w).val z = analyticValue (0 : BoundaryL2) z
    rw [analyticValue_zero]
    exact (firstSection_eval ⟨R,hR⟩ ⟨z,hz⟩ w).trans (hv ⟨z,hz⟩ w))
  have hrzero : R = 0 := bidiskHardy_eq_zero_of_products R hR (fun f g => by
    let A := hardyTensorLeft f
    let a : Hardy := A.adjoint R
    have hazero : a = 0 := hardy_analyticValue_injective _ _ (fun w hw => by
      change analyticValue a.val w = analyticValue (0 : BoundaryL2) w
      rw [analyticValue_zero]
      calc
        _ = inner ℂ (szegoKernel ⟨w,hw⟩) a := (inner_szegoKernel _ a).symm
        _ = inner ℂ (separatedProduct f.val (szegoKernel ⟨w,hw⟩).val) R :=
          ContinuousLinearMap.adjoint_inner_right A _ R
        _ = inner ℂ f (firstSection R ⟨w,hw⟩) := (firstSection_inner R _ f).symm
        _ = 0 := by rw [hsec,inner_zero_right])
    have he := ContinuousLinearMap.adjoint_inner_right A g R
    change inner ℂ g a = inner ℂ (separatedProduct f.val g.val) R at he
    rw [hazero,inner_zero_right] at he
    exact he.symm)
  exact Subtype.ext (sub_eq_zero.mp hrzero)

theorem QGraph_unique (u : BoundaryLInf) (η : Ambient u) (G H : TensorModel u)
    (hG : QGraph u η G) (hH : QGraph u η H) : G = H := by
  have he := bidiskHardy_analyticValue₂_injective
    ⟨G.val,tensorModel_le_bidiskHardy u G.property⟩ ⟨H.val,tensorModel_le_bidiskHardy u H.property⟩
    (fun z w => (hG z.val z.property w.val w.property).trans (hH z.val z.property w.val w.property).symm)
  exact Subtype.ext (congrArg (fun x : ↥bidiskHardy => x.val) he)

/-- The tensor representing evaluation of the coefficient graph at the u² reproducing kernel. -/
def reproducingTensor (u : BoundaryLInf) (hu : IsInner u) (w : Disk) : TensorModel u :=
  ⟨separatedProduct (modelReproducingKernel u hu w).val (modelReproducingKernel u hu w).val,
    separatedProduct_mem_tensorModel u _ _⟩

theorem ambientKernel_graph (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    QGraph u (ambientKernel u hu w) (reproducingTensor u hu w) := by
  intro z hz t ht
  let kz := modelReproducingKernel u hu ⟨z,hz⟩
  let kt := modelReproducingKernel u hu ⟨t,ht⟩
  let kw := modelReproducingKernel u hu w
  let p : Ambient u := ⟨boundedModelProduct u kz kt (bounded_modelReproducingKernel u hu ⟨z,hz⟩),
    boundedModelProduct_mem u hu _ _ (bounded_modelReproducingKernel u hu ⟨z,hz⟩)⟩
  rw [analyticValue₂_tensor_kernels u hu (reproducingTensor u hu w) ⟨z,hz⟩ ⟨t,ht⟩]
  change inner ℂ (separatedProduct kz.val kt.val) (separatedProduct kw.val kw.val) = _
  rw [inner_separatedProduct,FKernel_eq_inner_product u hu (ambientKernel u hu w).val ⟨z,hz⟩ ⟨t,ht⟩]
  change inner ℂ kz kw*inner ℂ kt kw = inner ℂ p (ambientKernel u hu w)
  rw [← inner_conj_symm (𝕜 := ℂ) p (ambientKernel u hu w),ambientKernel,
    inner_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w p]
  change inner ℂ kz kw*inner ℂ kt kw =
    conj (analyticValue (boundedModelProduct u kz kt (bounded_modelReproducingKernel u hu ⟨z,hz⟩)) w.val)
  rw [analyticValue_boundedModelProduct]
  have hi : inner ℂ kz kw = conj (analyticValue kz.val w.val) := by
    simpa only [inner_conj_symm] using congrArg conj (inner_modelReproducingKernel u hu w kz)
  have hj : inner ℂ kt kw = conj (analyticValue kt.val w.val) := by
    simpa only [inner_conj_symm] using congrArg conj (inner_modelReproducingKernel u hu w kt)
  rw [hi,hj,map_mul]

theorem matrixData_kernel_eq (u : BoundaryLInf) (hu : IsInner u) (b : MatrixData u) (w : Disk) :
    b.kernel w = ambientKernel u hu w := by
  have he := hardy_analyticValue_injective
    (⟨(b.kernel w).val,(b.kernel w).property.1⟩ : Hardy)
    (⟨(ambientKernel u hu w).val,(ambientKernel u hu w).property.1⟩ : Hardy)
    (fun z hz => (b.kernel_value w ⟨z,hz⟩).trans
      (analyticValue_modelReproducingKernel (multiplyInf u u) (isInner_multiplyInf u u hu hu) w hz).symm)
  exact Subtype.ext (congrArg (fun x : Hardy => x.val) he)

theorem matrixData_squareKernel_eq (u : BoundaryLInf) (hu : IsInner u) (b : MatrixData u) (w : Disk) :
    b.squareKernel w = squaredModelKernel u hu w := by
  have he := hardy_analyticValue_injective
    (⟨(b.squareKernel w).val,(b.squareKernel w).property.1⟩ : Hardy)
    (⟨(squaredModelKernel u hu w).val,(squaredModelKernel u hu w).property.1⟩ : Hardy)
    (fun z hz => (b.squareKernel_value w ⟨z,hz⟩).trans (squaredModelKernel_value u hu w ⟨z,hz⟩).symm)
  exact Subtype.ext (congrArg (fun x : Hardy => x.val) he)

/-- Native l² pairing transports the fully specified coefficient series to the concrete tensor inner product. -/
theorem coefficientPair_tensor (u : BoundaryLInf) (b : MatrixData u) (η γ : Ambient u)
    (x y : lp (fun _ : b.Index × b.Index => ℂ) 2)
    (hx : ∀ ij, x ij = b.coefficient ij η) (hy : ∀ ij, y ij = b.coefficient ij γ) :
    coefficientPair b η γ = inner ℂ (b.tensor y) (b.tensor x) := by
  calc
    _ = ∑' ij, x ij*conj (y ij) := tsum_congr (fun ij => by rw [hx ij,hy ij])
    _ = inner ℂ y x := (l2CoordinateLaws.inner _ x y).symm
    _ = _ := (b.tensor.inner_map_map y x).symm

/-- Both kernel coefficient tests hold for every permitted matrix data package. -/
theorem kernelCoefficient : KernelCoefficientObligation := by
  intro u hu _hn b η hη w
  let x : lp (fun _ : b.Index × b.Index => ℂ) 2 :=
    ⟨fun ij => b.coefficient ij η,(memlp_two_iff_energy _).mpr hη⟩
  obtain ⟨y,hy⟩ := b.kernel_coefficients w
  let G := b.tensor x
  let K := b.tensor y
  have hx (ij) : x ij = b.coefficient ij η := rfl
  have hG : QGraph u η G := (b.graph_coefficients η G).mpr (fun ij => by
    change b.tensor.symm (b.tensor x) ij = _
    rw [b.tensor.symm_apply_apply])
  have hK : QGraph u (b.kernel w) K := (b.graph_coefficients (b.kernel w) K).mpr (fun ij => by
    change b.tensor.symm (b.tensor y) ij = _
    rw [b.tensor.symm_apply_apply]
    exact hy ij)
  rw [matrixData_kernel_eq u hu b w] at hK
  have heK : K = reproducingTensor u hu w := QGraph_unique u _ K _ hK (ambientKernel_graph u hu w)
  have hval : inner ℂ (reproducingTensor u hu w) G = FKernel u η.val w.val w.val :=
    (analyticValue₂_tensor_kernels u hu G w w).symm.trans (hG w.val w.property w.val w.property)
  have hp := coefficientPair_tensor u b η (b.kernel w) x y hx hy
  change coefficientPair b η (b.kernel w) = inner ℂ K G at hp
  rw [heK] at hp
  have hp' := coefficientPair_tensor u b (b.kernel w) η y x hy hx
  change coefficientPair b (b.kernel w) η = inner ℂ G K at hp'
  rw [heK] at hp'
  have hsquare : inner ℂ η (b.squareKernel w) = conj (FKernel u η.val w.val w.val) := by
    rw [matrixData_squareKernel_eq u hu b w]
    have hf : FKernel u η.val w.val w.val = inner ℂ (squaredModelKernel u hu w) η :=
      FKernel_eq_inner_product u hu η.val w w
    have hh := congrArg conj hf
    rw [inner_conj_symm] at hh
    exact hh.symm
  constructor
  · calc
      _ = inner ℂ G (reproducingTensor u hu w) := hp'
      _ = conj (inner ℂ (reproducingTensor u hu w) G) := (inner_conj_symm (𝕜 := ℂ) _ _).symm
      _ = conj (FKernel u η.val w.val w.val) := congrArg conj hval
      _ = _ := hsquare.symm
  · exact hp.trans hval

/-- Only exact boundary Parseval and natural closed-form/square-root theory remain for T8. -/
theorem hilbertSchmidtEnergy_of_kernels (hP : BoundaryParsevalObligation) (hF : GraphFormObligation) :
    HilbertSchmidtConclusion := hilbertSchmidtEnergy_of_matrix hP hF kernelCoefficient

/-- The same two genuine internal obligations remain for the full T9 domain conclusion. -/
theorem differentialRealization_of_kernels (hP : BoundaryParsevalObligation) (hF : GraphFormObligation) :
    DifferentialConclusion := differentialRealization_of_matrix hP hF kernelCoefficient

end TTO.Paper.Proved
