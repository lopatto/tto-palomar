/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.Proofs
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.MeasureTheory.Integral.Prod

/-! Native bounded model bases and concrete L² tensor foundations. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction InnerProductSpace

instance : CompleteSpace ↥bidiskHardy := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Countably many actual projected positive modes, each a bounded model vector. -/
def projectedMode (u : BoundaryLInf) (hu : IsInner u) (n : ℕ) : Model u :=
  ⟨modelPolynomial u n,modelPolynomial_mem u hu n⟩

theorem projectedModes_dense (u : BoundaryLInf) (hu : IsInner u) :
    Dense (Submodule.span ℂ (Set.range (projectedMode u hu)) : Set (Model u)) := by
  let C := Submodule.span ℂ (Set.range (projectedMode u hu))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro x _
  have hs := ((fourierBasis (T := 1)).hasSum_repr x.val).mapL (model u).orthogonalProjectionOnto
  simp only [map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hs
  apply (Submodule.isClosed_topologicalClosure C).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply C.topologicalClosure.sum_mem
  intro n _
  by_cases hn : 0 ≤ n
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have he : (model u).orthogonalProjectionOnto (fourierBasis (T := 1) (k : ℤ)) = projectedMode u hu k :=
      Subtype.ext (modelProjection_fourierBasis u hu k)
    rw [he]
    exact C.topologicalClosure.smul_mem _ (C.le_topologicalClosure (Submodule.subset_span ⟨k,rfl⟩))
  · have hz := (mem_hardy_iff x.val).mp x.property.1 n (by omega)
    simp only [fourierBasis_repr,hz,zero_smul]
    exact C.topologicalClosure.zero_mem

def modelGramVector (u : BoundaryLInf) (hu : IsInner u) (n : ℕ) : Model u :=
  gramSchmidtNormed ℂ (projectedMode u hu) n

/-- Gram–Schmidt stays in the algebraic bounded core; closedness of that core is not asserted. -/
theorem bounded_modelGramVector (u : BoundaryLInf) (hu : IsInner u) (n : ℕ) :
    IsBounded (modelGramVector u hu n).val := by
  let B : Submodule ℂ (Model u) := boundedL2.comap (model u).subtype
  have hspan : Submodule.span ℂ (Set.range (projectedMode u hu)) ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact bounded_modelPolynomial u k
  have hg := gramSchmidt_mem_span ℂ (projectedMode u hu) (j := n) (i := n) le_rfl
  have hb := hspan (Submodule.span_mono (Set.image_subset_range _ _) hg)
  change gramSchmidtNormed ℂ (projectedMode u hu) n ∈ B
  exact B.smul_mem _ hb

abbrev ModelBasisIndex (u : BoundaryLInf) (hu : IsInner u) := {n : ℕ | modelGramVector u hu n ≠ 0}

theorem modelGram_range (u : BoundaryLInf) (hu : IsInner u) :
    Set.range (fun i : ModelBasisIndex u hu => modelGramVector u hu i.val) =
      Set.range (modelGramVector u hu) \ {0} := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨i.val,rfl⟩,i.property⟩
  · rintro ⟨⟨n,rfl⟩,hn⟩
    exact ⟨⟨n,hn⟩,rfl⟩

theorem modelGram_span (u : BoundaryLInf) (hu : IsInner u) :
    Submodule.span ℂ (Set.range (fun i : ModelBasisIndex u hu => modelGramVector u hu i.val)) =
      Submodule.span ℂ (Set.range (projectedMode u hu)) := by
  rw [modelGram_range,Submodule.span_sdiff_singleton_zero]
  exact (span_gramSchmidtNormed_range (𝕜 := ℂ) (projectedMode u hu)).trans (span_gramSchmidt ℂ (projectedMode u hu))

/-- A literal countable bounded-core Hilbert basis, retaining finite and zero-dimensional cases. -/
def boundedModelBasis (u : BoundaryLInf) (hu : IsInner u) : HilbertBasis (ModelBasisIndex u hu) ℂ (Model u) :=
  HilbertBasis.mk (gramSchmidtNormed_orthonormal' (𝕜 := ℂ) (projectedMode u hu)) (by
    change ⊤ ≤ (Submodule.span ℂ (Set.range (fun i : ModelBasisIndex u hu => modelGramVector u hu i.val))).topologicalClosure
    rw [modelGram_span]
    have hd := projectedModes_dense u hu
    rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
    exact hd.ge)

@[simp] theorem boundedModelBasis_apply (u : BoundaryLInf) (hu : IsInner u) (i : ModelBasisIndex u hu) :
    boundedModelBasis u hu i = modelGramVector u hu i.val :=
  congrFun (HilbertBasis.coe_mk (gramSchmidtNormed_orthonormal' (𝕜 := ℂ) (projectedMode u hu)) _) i

theorem bounded_boundedModelBasis (u : BoundaryLInf) (hu : IsInner u) (i : ModelBasisIndex u hu) :
    IsBounded (boundedModelBasis u hu i).val := by
  rw [boundedModelBasis_apply]
  exact bounded_modelGramVector u hu i.val

/-- Separated products of arbitrary L² circle classes are genuinely square integrable. -/
theorem separatedProduct_memLp (f g : BoundaryL2) :
    MemLp (fun p : Boundary × Boundary => f p.1*g p.2) 2 (circleMeasure.prod circleMeasure) := by
  have hm : AEStronglyMeasurable (fun p : Boundary × Boundary => f p.1*g p.2) (circleMeasure.prod circleMeasure) :=
    (((Lp.stronglyMeasurable f).measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_mul,mul_pow] using
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
      ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

/-- Concrete separated product in the bidisk L² space. -/
def separatedProduct (f g : BoundaryL2) : BidiskL2 :=
  (separatedProduct_memLp f g).toLp (fun p => f p.1*g p.2)

theorem separatedProduct_ae (f g : BoundaryL2) :
    separatedProduct f g =ᵐ[circleMeasure.prod circleMeasure] fun p => f p.1*g p.2 :=
  (separatedProduct_memLp f g).coeFn_toLp

theorem boundary_ae_fst {f g : Boundary → ℂ} (h : f =ᵐ[circleMeasure] g) :
    (fun p : Boundary × Boundary => f p.1) =ᵐ[circleMeasure.prod circleMeasure] fun p => g p.1 := by
  simpa only [Function.comp_def] using
    (measurePreserving_fst (μ := circleMeasure) (ν := circleMeasure)).quasiMeasurePreserving.ae_eq_comp h

theorem boundary_ae_snd {f g : Boundary → ℂ} (h : f =ᵐ[circleMeasure] g) :
    (fun p : Boundary × Boundary => f p.2) =ᵐ[circleMeasure.prod circleMeasure] fun p => g p.2 := by
  simpa only [Function.comp_def] using
    (measurePreserving_snd (μ := circleMeasure) (ν := circleMeasure)).quasiMeasurePreserving.ae_eq_comp h

theorem separatedProduct_add_left (f₁ f₂ g : BoundaryL2) :
    separatedProduct (f₁+f₂) g = separatedProduct f₁ g+separatedProduct f₂ g := by
  apply Lp.ext
  filter_upwards [separatedProduct_ae (f₁+f₂) g,separatedProduct_ae f₁ g,separatedProduct_ae f₂ g,
    boundary_ae_fst (Lp.coeFn_add f₁ f₂),Lp.coeFn_add (separatedProduct f₁ g) (separatedProduct f₂ g)]
    with p hl h1 h2 hf hs
  simp only [Pi.add_apply] at hf hs
  rw [hl,hs,h1,h2,hf,add_mul]

theorem separatedProduct_smul_left (c : ℂ) (f g : BoundaryL2) :
    separatedProduct (c • f) g = c • separatedProduct f g := by
  apply Lp.ext
  filter_upwards [separatedProduct_ae (c • f) g,separatedProduct_ae f g,
    boundary_ae_fst (Lp.coeFn_smul c f),Lp.coeFn_smul c (separatedProduct f g)] with p hl hr hf hs
  simp only [Pi.smul_apply,smul_eq_mul] at hf hs
  rw [hl,hs,hr,hf,mul_assoc]

theorem separatedProduct_add_right (f g₁ g₂ : BoundaryL2) :
    separatedProduct f (g₁+g₂) = separatedProduct f g₁+separatedProduct f g₂ := by
  apply Lp.ext
  filter_upwards [separatedProduct_ae f (g₁+g₂),separatedProduct_ae f g₁,separatedProduct_ae f g₂,
    boundary_ae_snd (Lp.coeFn_add g₁ g₂),Lp.coeFn_add (separatedProduct f g₁) (separatedProduct f g₂)]
    with p hl h1 h2 hg hs
  simp only [Pi.add_apply] at hg hs
  rw [hl,hs,h1,h2,hg,mul_add]

theorem separatedProduct_smul_right (c : ℂ) (f g : BoundaryL2) :
    separatedProduct f (c • g) = c • separatedProduct f g := by
  apply Lp.ext
  filter_upwards [separatedProduct_ae f (c • g),separatedProduct_ae f g,
    boundary_ae_snd (Lp.coeFn_smul c g),Lp.coeFn_smul c (separatedProduct f g)] with p hl hr hg hs
  simp only [Pi.smul_apply,smul_eq_mul] at hg hs
  rw [hl,hs,hr,hg]
  ring

/-- Fubini gives the literal product inner product, with the native second-linear convention. -/
theorem inner_separatedProduct (f₁ g₁ f₂ g₂ : BoundaryL2) :
    inner ℂ (separatedProduct f₁ g₁) (separatedProduct f₂ g₂) =
      inner ℂ f₁ f₂*inner ℂ g₁ g₂ := by
  calc
    _ = ∫ p, (f₂ p.1*conj (f₁ p.1))*(g₂ p.2*conj (g₁ p.2)) ∂circleMeasure.prod circleMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [separatedProduct_ae f₁ g₁,separatedProduct_ae f₂ g₂] with p h1 h2
      rw [RCLike.inner_apply,h1,h2,map_mul]
      ring
    _ = (∫ t, f₂ t*conj (f₁ t) ∂circleMeasure)*(∫ t, g₂ t*conj (g₁ t) ∂circleMeasure) :=
      integral_prod_mul (μ := circleMeasure) (ν := circleMeasure)
        (fun t : Boundary => f₂ t*conj (f₁ t)) (fun t : Boundary => g₂ t*conj (g₁ t))
    _ = _ := by simp only [L2.inner_def,RCLike.inner_apply]

theorem norm_separatedProduct (f g : BoundaryL2) : ‖separatedProduct f g‖ = ‖f‖*‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg (separatedProduct f g)) (mul_nonneg (norm_nonneg f) (norm_nonneg g))).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_separatedProduct,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  norm_cast
  ring

/-- Continuous bilinear concrete tensor product, with exact elementary tensor norms. -/
def separatedBilinear : BoundaryL2 →L[ℂ] BoundaryL2 →L[ℂ] BidiskL2 :=
  (LinearMap.mk₂ ℂ separatedProduct separatedProduct_add_left separatedProduct_smul_left
    separatedProduct_add_right separatedProduct_smul_right).mkContinuous₂ 1
      (fun f g => by rw [LinearMap.mk₂_apply,norm_separatedProduct,one_mul])

@[simp] theorem separatedBilinear_apply (f g : BoundaryL2) :
    separatedBilinear f g = separatedProduct f g := rfl

/-- Extending elementary products from two Hilbert bases uses only closedness and continuous bilinearity. -/
theorem separatedProduct_mem_of_basis {I J : Type*} (K L : Submodule ℂ BoundaryL2)
    (b : HilbertBasis I ℂ K) (c : HilbertBasis J ℂ L) (C : Submodule ℂ BidiskL2)
    (hC : IsClosed (C : Set BidiskL2))
    (hbc : ∀ i j, separatedProduct (b i).val (c j).val ∈ C) (f : K) (g : L) :
    separatedProduct f.val g.val ∈ C := by
  have hfirst (j : J) : separatedProduct f.val (c j).val ∈ C := by
    let A := (separatedBilinear.flip (c j).val) ∘L K.subtypeL
    have hs := A.hasSum (b.hasSum_repr f)
    change HasSum (fun i => A (b.repr f i • b i)) (separatedProduct f.val (c j).val) at hs
    simp only [map_smul] at hs
    apply hC.mem_of_tendsto hs
    apply Filter.Eventually.of_forall
    intro t
    exact C.sum_mem (fun i _ => C.smul_mem _ (hbc i j))
  let A := (separatedBilinear f.val) ∘L L.subtypeL
  have hs := A.hasSum (c.hasSum_repr g)
  change HasSum (fun j => A (c.repr g j • c j)) (separatedProduct f.val g.val) at hs
  simp only [map_smul] at hs
  apply hC.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro t
  exact C.sum_mem (fun j _ => C.smul_mem _ (hfirst j))

/-- The positive bidisk mode is exactly the concrete separated Fourier product. -/
theorem separatedProduct_fourierBasis (m n : ℕ) :
    separatedProduct (fourierBasis (T := 1) (m : ℤ)) (fourierBasis (T := 1) (n : ℤ)) =
      ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode m n) := by
  apply Lp.ext
  filter_upwards [separatedProduct_ae (fourierBasis (T := 1) (m : ℤ)) (fourierBasis (T := 1) (n : ℤ)),
    boundary_ae_fst (fourierBasis_ae (m : ℤ)),boundary_ae_snd (fourierBasis_ae (n : ℤ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (circleMeasure.prod circleMeasure) (bidiskMode m n)] with p hp hm hn hc
  rw [hp,hc,hm,hn]
  rfl

/-- Actual separated products of Hardy vectors belong to the positive bidisk space. -/
theorem separatedProduct_mem_bidiskHardy (f g : Hardy) : separatedProduct f.val g.val ∈ bidiskHardy := by
  apply separatedProduct_mem_of_basis hardy hardy hardyBasis hardyBasis bidiskHardy
    (Submodule.isClosed_topologicalClosure _) (fun m n => ?_) f g
  simp only [hardyBasis_apply]
  change separatedProduct (fourierBasis (T := 1) (m : ℤ)) (fourierBasis (T := 1) (n : ℤ)) ∈ bidiskHardy
  rw [separatedProduct_fourierBasis]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(m,n),rfl⟩)

/-- The positive Fourier product basis lives in the actual closed positive bidisk span. -/
def bidiskHardyMode (i : ℕ × ℕ) : ↥bidiskHardy :=
  ⟨ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode i.1 i.2),
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)⟩

theorem bidiskHardyMode_orthonormal : Orthonormal ℂ bidiskHardyMode := by
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode i.1 i.2))
    (ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode j.1 j.2)) = _
  rw [← separatedProduct_fourierBasis,← separatedProduct_fourierBasis,inner_separatedProduct]
  have h1 : inner ℂ (fourierBasis (T := 1) (i.1 : ℤ)) (fourierBasis (T := 1) (j.1 : ℤ)) =
      if i.1 = j.1 then 1 else 0 := by
    change inner ℂ (hardyMode i.1) (hardyMode j.1) = _
    exact orthonormal_iff_ite.mp hardyMode_orthonormal _ _
  have h2 : inner ℂ (fourierBasis (T := 1) (i.2 : ℤ)) (fourierBasis (T := 1) (j.2 : ℤ)) =
      if i.2 = j.2 then 1 else 0 := by
    change inner ℂ (hardyMode i.2) (hardyMode j.2) = _
    exact orthonormal_iff_ite.mp hardyMode_orthonormal _ _
  rw [h1,h2]
  by_cases ha : i.1 = j.1 <;> by_cases hb : i.2 = j.2 <;> simp [ha,hb,Prod.ext_iff]

theorem bidiskHardyModes_total :
    (Submodule.span ℂ (Set.range bidiskHardyMode)).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro G hG
  apply Subtype.ext
  have hle : bidiskHardy ≤ (innerSL ℂ G.val).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have hh : inner ℂ (bidiskHardyMode i) G = 0 :=
        (Submodule.mem_orthogonal _ _).mp hG _ (Submodule.subset_span ⟨i,rfl⟩)
      exact inner_eq_zero_symm.mp hh
    · exact (innerSL ℂ G.val).isClosed_ker
  have hz := hle G.property
  change inner ℂ G.val G.val = 0 at hz
  exact inner_self_eq_zero.mp hz

def bidiskHardyBasis : HilbertBasis (ℕ × ℕ) ℂ ↥bidiskHardy :=
  HilbertBasis.mkOfOrthogonalEqBot bidiskHardyMode_orthonormal bidiskHardyModes_total

@[simp] theorem bidiskHardyBasis_apply (i : ℕ × ℕ) : bidiskHardyBasis i = bidiskHardyMode i :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot bidiskHardyMode_orthonormal bidiskHardyModes_total) i

/-- The double Taylor series is the native bidisk reproducing pairing. -/
theorem analyticValue₂_eq_inner (G : ↥bidiskHardy) (z w : Disk) :
    analyticValue₂ G.val z.val w.val = inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val) G.val := by
  let k : ↥bidiskHardy := ⟨separatedProduct (szegoKernel z).val (szegoKernel w).val,
    separatedProduct_mem_bidiskHardy (szegoKernel z) (szegoKernel w)⟩
  have hs := bidiskHardyBasis.hasSum_inner_mul_inner k G
  have he (i : ℕ × ℕ) : inner ℂ k (bidiskHardyBasis i)*inner ℂ (bidiskHardyBasis i) G =
      (∫ t, G.val t*conj (bidiskMode i.1 i.2 t) ∂circleMeasure.prod circleMeasure)*z.val^i.1*w.val^i.2 := by
    simp only [bidiskHardyBasis_apply]
    have hleft : inner ℂ k (bidiskHardyMode i) = z.val^i.1*w.val^i.2 := by
      change inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val)
        (ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode i.1 i.2)) = _
      rw [← separatedProduct_fourierBasis,inner_separatedProduct]
      have hz : inner ℂ (szegoKernel z).val (fourierBasis (T := 1) (i.1 : ℤ)) = z.val^i.1 := by
        exact (inner_szegoKernel z (hardyMode i.1)).trans (analyticValue_fourierBasis i.1 z.val)
      have hw : inner ℂ (szegoKernel w).val (fourierBasis (T := 1) (i.2 : ℤ)) = w.val^i.2 := by
        exact (inner_szegoKernel w (hardyMode i.2)).trans (analyticValue_fourierBasis i.2 w.val)
      rw [hz,hw]
    have hright : inner ℂ (bidiskHardyMode i) G =
        ∫ t, G.val t*conj (bidiskMode i.1 i.2 t) ∂circleMeasure.prod circleMeasure := by
      rw [show inner ℂ (bidiskHardyMode i) G = inner ℂ (bidiskHardyMode i).val G.val from rfl,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (circleMeasure.prod circleMeasure) (bidiskMode i.1 i.2)] with t ht
      change (bidiskHardyMode i).val t = (bidiskMode i.1 i.2) t at ht
      rw [RCLike.inner_apply,ht]
    rw [hleft,hright]
    ring
  simp_rw [he] at hs
  exact hs.tsum_eq

theorem separatedProduct_mem_tensorModel (u : BoundaryLInf) (f g : Model u) :
    separatedProduct f.val g.val ∈ tensorModel u :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f,g,separatedProduct_ae f.val g.val⟩)

/-- The concrete model tensor is contained in the concrete bidisk Hardy space. -/
theorem tensorModel_le_bidiskHardy (u : BoundaryLInf) : tensorModel u ≤ bidiskHardy := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro G ⟨f,g,hG⟩
    have he : G = separatedProduct f.val g.val := Lp.ext (Filter.EventuallyEq.trans hG (separatedProduct_ae f.val g.val).symm)
    rw [he]
    exact separatedProduct_mem_bidiskHardy ⟨f.val,f.property.1⟩ ⟨g.val,g.property.1⟩
  · exact Submodule.isClosed_topologicalClosure _

def hardyTensorRight (g : Hardy) : Hardy →L[ℂ] BidiskL2 :=
  separatedBilinear.flip g.val ∘L hardy.subtypeL

def hardyTensorLeft (f : Hardy) : Hardy →L[ℂ] BidiskL2 :=
  separatedBilinear f.val ∘L hardy.subtypeL

/-- Actual Hardy section in the first variable, defined by the bounded adjoint. -/
def firstSection (G : BidiskL2) (w : Disk) : Hardy := (hardyTensorRight (szegoKernel w)).adjoint G

/-- Actual Hardy section in the second variable, defined by the bounded adjoint. -/
def secondSection (G : BidiskL2) (z : Disk) : Hardy := (hardyTensorLeft (szegoKernel z)).adjoint G

theorem firstSection_inner (G : BidiskL2) (w : Disk) (f : Hardy) :
    inner ℂ f (firstSection G w) = inner ℂ (separatedProduct f.val (szegoKernel w).val) G :=
  ContinuousLinearMap.adjoint_inner_right (hardyTensorRight (szegoKernel w)) f G

theorem secondSection_inner (G : BidiskL2) (z : Disk) (g : Hardy) :
    inner ℂ g (secondSection G z) = inner ℂ (separatedProduct (szegoKernel z).val g.val) G :=
  ContinuousLinearMap.adjoint_inner_right (hardyTensorLeft (szegoKernel z)) g G

theorem firstSection_eval (G : ↥bidiskHardy) (z w : Disk) :
    analyticValue (firstSection G.val w).val z.val = analyticValue₂ G.val z.val w.val := by
  rw [← inner_szegoKernel z (firstSection G.val w),firstSection_inner,analyticValue₂_eq_inner]

theorem secondSection_eval (G : ↥bidiskHardy) (z w : Disk) :
    analyticValue (secondSection G.val z).val w.val = analyticValue₂ G.val z.val w.val := by
  rw [← inner_szegoKernel w (secondSection G.val z),secondSection_inner,analyticValue₂_eq_inner]

/-- Tensor vectors pair trivially with a product having either factor orthogonal to the model. -/
theorem inner_separatedProduct_tensor_zero (u : BoundaryLInf) (f g : Hardy)
    (hfg : f.val ∈ (model u).orthogonal ∨ g.val ∈ (model u).orthogonal) (T : TensorModel u) :
    inner ℂ (separatedProduct f.val g.val) T.val = 0 := by
  let L := innerSL ℂ (separatedProduct f.val g.val)
  have hle : tensorModel u ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro H ⟨a,b,hH⟩
      have he : H = separatedProduct a.val b.val := Lp.ext (Filter.EventuallyEq.trans hH (separatedProduct_ae a.val b.val).symm)
      change inner ℂ (separatedProduct f.val g.val) H = 0
      rw [he,inner_separatedProduct]
      rcases hfg with hf | hg
      · rw [(Submodule.mem_orthogonal' _ _).mp hf _ a.property,zero_mul]
      · rw [(Submodule.mem_orthogonal' _ _).mp hg _ b.property,mul_zero]
    · exact L.isClosed_ker
  exact hle T.property

/-- Positive product coefficients determine every vector in the actual bidisk Hardy space. -/
theorem bidiskHardy_eq_zero_of_products (G : BidiskL2) (hG : G ∈ bidiskHardy)
    (hz : ∀ f g : Hardy, inner ℂ (separatedProduct f.val g.val) G = 0) : G = 0 := by
  have hle : bidiskHardy ≤ (innerSL ℂ G).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change inner ℂ G (ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode i.1 i.2)) = 0
      rw [← separatedProduct_fourierBasis]
      exact inner_eq_zero_symm.mp (hz (hardyMode i.1) (hardyMode i.2))
    · exact (innerSL ℂ G).isClosed_ker
  exact inner_self_eq_zero.mp (hle hG)

/-- Model-valued first sections force annihilation in the first orthogonal factor. -/
theorem separatedProduct_annihilate_left (u : BoundaryLInf) (G : BidiskL2)
    (hsec : ∀ w : Disk, (firstSection G w).val ∈ model u)
    (f : Hardy) (hf : f.val ∈ (model u).orthogonal) (g : Hardy) :
    inner ℂ (separatedProduct f.val g.val) G = 0 := by
  let A := hardyTensorLeft f
  let h : Hardy := A.adjoint G
  have hval (w : Disk) : analyticValue h.val w.val = 0 := by
    calc
      _ = inner ℂ (szegoKernel w) h := (inner_szegoKernel w h).symm
      _ = inner ℂ (separatedProduct f.val (szegoKernel w).val) G :=
        ContinuousLinearMap.adjoint_inner_right A (szegoKernel w) G
      _ = inner ℂ f (firstSection G w) := (firstSection_inner G w f).symm
      _ = 0 := (Submodule.mem_orthogonal' _ _).mp hf _ (hsec w)
  have hz : h = 0 := hardy_analyticValue_injective h 0 (fun w hw => by
    change analyticValue h.val w = analyticValue (0 : BoundaryL2) w
    rw [analyticValue_zero]
    exact hval ⟨w,hw⟩)
  have he := ContinuousLinearMap.adjoint_inner_right A g G
  change inner ℂ g h = inner ℂ (separatedProduct f.val g.val) G at he
  rw [hz,inner_zero_right] at he
  exact he.symm

/-- Model-valued second sections force annihilation in the second orthogonal factor. -/
theorem separatedProduct_annihilate_right (u : BoundaryLInf) (G : BidiskL2)
    (hsec : ∀ z : Disk, (secondSection G z).val ∈ model u)
    (f g : Hardy) (hg : g.val ∈ (model u).orthogonal) :
    inner ℂ (separatedProduct f.val g.val) G = 0 := by
  let A := hardyTensorRight g
  let h : Hardy := A.adjoint G
  have hval (z : Disk) : analyticValue h.val z.val = 0 := by
    calc
      _ = inner ℂ (szegoKernel z) h := (inner_szegoKernel z h).symm
      _ = inner ℂ (separatedProduct (szegoKernel z).val g.val) G :=
        ContinuousLinearMap.adjoint_inner_right A (szegoKernel z) G
      _ = inner ℂ g (secondSection G z) := (secondSection_inner G z g).symm
      _ = 0 := (Submodule.mem_orthogonal' _ _).mp hg _ (hsec z)
  have hz : h = 0 := hardy_analyticValue_injective h 0 (fun z hz => by
    change analyticValue h.val z = analyticValue (0 : BoundaryL2) z
    rw [analyticValue_zero]
    exact hval ⟨z,hz⟩)
  have he := ContinuousLinearMap.adjoint_inner_right A f G
  change inner ℂ f h = inner ℂ (separatedProduct f.val g.val) G at he
  rw [hz,inner_zero_right] at he
  exact he.symm

/-- The genuine two-variable Hardy section criterion for the concrete completed model tensor. -/
theorem tensor_section_criterion (u : BoundaryLInf) (G : BidiskL2) (hG : G ∈ bidiskHardy)
    (hfirst : ∀ w ∈ disk, ∃ f : Model u, ∀ z ∈ disk, analyticValue f.val z = analyticValue₂ G z w)
    (hsecond : ∀ z ∈ disk, ∃ f : Model u, ∀ w ∈ disk, analyticValue f.val w = analyticValue₂ G z w) :
    G ∈ tensorModel u := by
  have hs1 (w : Disk) : (firstSection G w).val ∈ model u := by
    obtain ⟨f,hf⟩ := hfirst w.val w.property
    have he : firstSection G w = (⟨f.val,f.property.1⟩ : Hardy) :=
      hardy_analyticValue_injective _ _ (fun z hz =>
        (firstSection_eval ⟨G,hG⟩ ⟨z,hz⟩ w).trans (hf z hz).symm)
    rw [he]
    exact f.property
  have hs2 (z : Disk) : (secondSection G z).val ∈ model u := by
    obtain ⟨f,hf⟩ := hsecond z.val z.property
    have he : secondSection G z = (⟨f.val,f.property.1⟩ : Hardy) :=
      hardy_analyticValue_injective _ _ (fun w hw =>
        (secondSection_eval ⟨G,hG⟩ z ⟨w,hw⟩).trans (hf w hw).symm)
    rw [he]
    exact f.property
  let T := (tensorModel u).orthogonalProjectionOnto G
  let R := G-T.val
  have hR : R ∈ bidiskHardy := bidiskHardy.sub_mem hG (tensorModel_le_bidiskHardy u T.property)
  have hzero : R = 0 := bidiskHardy_eq_zero_of_products R hR (fun f g => by
    let p := (model u).orthogonalProjectionOnto f.val
    let q := (model u).orthogonalProjectionOnto g.val
    let f₀ : Hardy := ⟨f.val-p.val,hardy.sub_mem f.property p.property.1⟩
    let g₀ : Hardy := ⟨g.val-q.val,hardy.sub_mem g.property q.property.1⟩
    have hf₀ : f₀.val ∈ (model u).orthogonal := by
      apply (model u).orthogonalProjectionOnto_eq_zero_iff.mp
      change (model u).orthogonalProjectionOnto (f.val-p.val) = 0
      rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
    have hg₀ : g₀.val ∈ (model u).orthogonal := by
      apply (model u).orthogonalProjectionOnto_eq_zero_iff.mp
      change (model u).orthogonalProjectionOnto (g.val-q.val) = 0
      rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
    have hl (h : Hardy) : inner ℂ (separatedProduct f₀.val h.val) R = 0 := by
      change inner ℂ (separatedProduct f₀.val h.val) (G-T.val) = 0
      rw [inner_sub_right,separatedProduct_annihilate_left u G hs1 f₀ hf₀ h,
        inner_separatedProduct_tensor_zero u f₀ h (Or.inl hf₀) T,sub_self]
    have hr (h : Hardy) : inner ℂ (separatedProduct h.val g₀.val) R = 0 := by
      change inner ℂ (separatedProduct h.val g₀.val) (G-T.val) = 0
      rw [inner_sub_right,separatedProduct_annihilate_right u G hs2 h g₀ hg₀,
        inner_separatedProduct_tensor_zero u h g₀ (Or.inr hg₀) T,sub_self]
    have hm : inner ℂ (separatedProduct p.val q.val) R = 0 := by
      have hp := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
        (⟨separatedProduct p.val q.val,separatedProduct_mem_tensorModel u p q⟩ : TensorModel u) G
      change inner ℂ (separatedProduct p.val q.val) T.val = inner ℂ (separatedProduct p.val q.val) G at hp
      change inner ℂ (separatedProduct p.val q.val) (G-T.val) = 0
      rw [inner_sub_right,← hp,sub_self]
    have hf : f.val = p.val+f₀.val := by dsimp [f₀]; abel
    have hg : g.val = q.val+g₀.val := by dsimp [g₀]; abel
    calc
      _ = inner ℂ (separatedProduct p.val g.val) R+inner ℂ (separatedProduct f₀.val g.val) R := by
        rw [hf,separatedProduct_add_left,inner_add_left]
      _ = 0 := by
        rw [hl g,add_zero,hg,separatedProduct_add_right,inner_add_left,hm,
          hr (⟨p.val,p.property.1⟩ : Hardy),add_zero])
  have he : G = T.val := sub_eq_zero.mp hzero
  rw [he]
  exact T.property

/-- Tensor-section criterion for the concrete model spaces. -/
theorem tensorSection : TensorSectionObligation where
  tensor_hardy u _hu := tensorModel_le_bidiskHardy u
  sections u hu _hn η := FKernel_sections u hu η.val
  criterion u _hu G hG hfirst hsecond := tensor_section_criterion u G hG hfirst hsecond

/-- Hilbert–Schmidt energy criterion from tensor sections, matrix data, boundary Parseval,
graph-form theory and kernel coefficient identities. -/
theorem hilbertSchmidtEnergy_of_tensor (hB : MatrixDataObligation) (hP : BoundaryParsevalObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : HilbertSchmidtConclusion :=
  hilbertSchmidtEnergy hB hP tensorSection hF hTests

/-- T9 reduction with actual tensor sections and explicit natural domain/graph inputs. -/
theorem differentialRealization_of_tensor (hB : MatrixDataObligation) (hP : BoundaryParsevalObligation)
    (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : DifferentialConclusion :=
  differentialRealization hB hP tensorSection hF hTests

end TTO.Paper.Proved
