/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.Reduction
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Discharged mathematical obligations. The reviewed principal contracts remain in Challenge. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved

open Reduction

/-- Holder multiplication agrees with ordinary multiplication almost everywhere. -/
theorem multiply_ae (a : BoundaryLInf) (f : BoundaryL2) :
    multiply a f =ᵐ[circleMeasure] fun t => a t * f t := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder a f

/-- With bounded input, the core form is an ordinary L² inner product. -/
theorem coreForm_eq_inner_left (σ f g : BoundaryL2) (hf : IsBounded f) :
    coreForm σ f g = inner ℂ g (multiply (hf.toLp f) σ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae (hf.toLp f) σ, hf.coeFn_toLp] with t hm ht
  simp only [RCLike.inner_apply, hm, ht]
  ring

/-- With bounded test, the other variable also has a continuous L² pairing. -/
theorem coreForm_eq_inner_right (σ f g : BoundaryL2) (hg : IsBounded g) :
    coreForm σ f g = inner ℂ (multiply (hg.toLp g) (star σ)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae (hg.toLp g) (star σ), hg.coeFn_toLp,
    Lp.coeFn_star σ] with t hm ht hs
  change (star σ) t = star (σ t) at hs
  simp only [RCLike.inner_apply, hm, ht, hs]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Lemma 1, in the stronger set form used by analytic gluing. -/
theorem denseCoreSet : DenseCoreSetObligation := by
  intro u σ Z S hd hb hZ
  have first (g : Model u) (hg : g ∈ S) (f : Model u) :
      inner ℂ g (Z f) = coreForm σ f.val g.val := by
    let v := multiply ((hb g hg).toLp g.val) (star σ)
    have he : (fun f : Model u => inner ℂ g (Z f)) =
        (fun f : Model u => inner ℂ v f.val) :=
      Continuous.ext_on hd (continuous_const.inner Z.continuous)
        (continuous_const.inner continuous_subtype_val)
        (fun f hf => (hZ f hf g hg).trans (coreForm_eq_inner_right σ f.val g.val (hb g hg)))
    exact (congrFun he f).trans (coreForm_eq_inner_right σ f.val g.val (hb g hg)).symm
  intro f g hf _hg
  let w := multiply (hf.toLp f.val) σ
  have he : (fun g : Model u => inner ℂ g (Z f)) =
      (fun g : Model u => inner ℂ g.val w) :=
    Continuous.ext_on hd (continuous_id.inner continuous_const)
      (continuous_subtype_val.inner continuous_const)
      (fun g hg => (first g hg f).trans (coreForm_eq_inner_left σ f.val g.val hf))
  exact (congrFun he g).trans (coreForm_eq_inner_left σ f.val g.val hf).symm

/-- Lemma 1 for a dense bounded subspace; all prerequisites are supplied by the statement. -/
theorem denseCoreExtension : DenseCoreExtensionObligation := by
  intro u σ Z M hd hb hZ
  exact denseCoreSet u σ Z (M : Set (Model u)) hd
    (fun f hf => hb ⟨f,hf⟩) (fun f hf g hg => hZ ⟨f,hf⟩ ⟨g,hg⟩)

theorem toL2_ae (a : BoundaryLInf) : toL2 a =ᵐ[circleMeasure] a := by
  exact MemLp.coeFn_toLp _

/-- A bounded symbol defines an actual compressed multiplication operator. -/
def boundedSymbolOperator (u a : BoundaryLInf) : Model u →L[ℂ] Model u :=
  (model u).orthogonalProjectionOnto ∘L multiply a ∘L (model u).subtypeL

theorem boundedSymbolOperator_represents (u a : BoundaryLInf) :
    RepresentsTTO u (toL2 a) (boundedSymbolOperator u a) := by
  intro f g _ _
  have hi : inner ℂ g (boundedSymbolOperator u a f) = inner ℂ g.val (multiply a f.val) := by
    simp [boundedSymbolOperator]
  rw [hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae a f.val, toL2_ae a] with t hm ht
  simp only [RCLike.inner_apply, hm, ht]

theorem represents_zero (u : BoundaryLInf) :
    RepresentsTTO u 0 (0 : Model u →L[ℂ] Model u) := by
  intro f g hf _
  rw [coreForm_eq_inner_left 0 f.val g.val hf]
  simp

theorem coreForm_add (σ τ f g : BoundaryL2) (hf : IsBounded f) :
    coreForm (σ + τ) f g = coreForm σ f g + coreForm τ f g := by
  rw [coreForm_eq_inner_left (σ+τ) f g hf, map_add, inner_add_right,
    ← coreForm_eq_inner_left σ f g hf, ← coreForm_eq_inner_left τ f g hf]

theorem coreForm_sub (σ τ f g : BoundaryL2) (hf : IsBounded f) :
    coreForm (σ - τ) f g = coreForm σ f g - coreForm τ f g := by
  rw [coreForm_eq_inner_left (σ-τ) f g hf, map_sub, inner_sub_right,
    ← coreForm_eq_inner_left σ f g hf, ← coreForm_eq_inner_left τ f g hf]

theorem represents_add (u : BoundaryLInf) (σ τ : BoundaryL2)
    (A B : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) (hB : RepresentsTTO u τ B) :
    RepresentsTTO u (σ+τ) (A+B) := by
  intro f g hf hg
  rw [add_apply, inner_add_right, hA f g hf hg, hB f g hf hg,
    coreForm_add σ τ f.val g.val hf]

theorem represents_sub (u : BoundaryLInf) (σ τ : BoundaryL2)
    (A B : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) (hB : RepresentsTTO u τ B) :
    RepresentsTTO u (σ-τ) (A-B) := by
  intro f g hf hg
  rw [sub_apply, inner_sub_right, hA f g hf hg, hB f g hf hg,
    coreForm_sub σ τ f.val g.val hf]

/-- Conjugate symbols swap the variables in the core form. -/
theorem coreForm_star (σ f g : BoundaryL2) (hf : IsBounded f) :
    coreForm (star σ) f g = conj (coreForm σ g f) := by
  rw [coreForm_eq_inner_left (star σ) f g hf, coreForm_eq_inner_right σ g f hf,
    inner_conj_symm]

theorem represents_adjoint (u : BoundaryLInf) (σ : BoundaryL2)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) :
    RepresentsTTO u (star σ) A.adjoint := by
  intro f g hf hg
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, hA g f hg hf,
    coreForm_star σ f.val g.val hf]

theorem toL2_star (a : BoundaryLInf) : toL2 (star a) = star (toL2 a) := by
  apply Lp.ext
  filter_upwards [toL2_ae (star a), Lp.coeFn_star a, toL2_ae a,
    Lp.coeFn_star (toL2 a)] with t ht hs ha hsa
  change (star a) t = star (a t) at hs
  change (star (toL2 a)) t = star ((toL2 a) t) at hsa
  rw [ht, hsa, ha, hs]

/-- Uniqueness needs only density of the actual bounded model core. -/
theorem represents_unique_of_dense (u : BoundaryLInf)
    (hd : Dense {f : Model u | IsBounded f.val}) (σ : BoundaryL2)
    (A B : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) (hB : RepresentsTTO u σ B) : A = B := by
  have he : (fun f => A f) = (fun f => B f) :=
    Continuous.ext_on hd A.continuous B.continuous (fun f hf =>
      hd.eq_of_inner_right ℂ (fun g hg => (hA f g hf hg).trans (hB f g hf hg).symm))
  exact ContinuousLinearMap.ext (congrFun he)

/-- The analytic Fourier modes agree with their continuous circle representatives a.e. -/
theorem fourierBasis_ae (n : ℤ) :
    fourierBasis (T := 1) n =ᵐ[circleMeasure] fourier (T := 1) n := by
  simpa only [coe_fourierBasis] using (coeFn_fourierLp (T := 1) 2 n)

theorem mode_ae (n : ℤ) : mode n =ᵐ[circleMeasure] fourier (T := 1) n := by
  exact coeFn_fourierLp ∞ n

theorem toL2_mode (n : ℤ) : toL2 (mode n) = fourierBasis (T := 1) n := by
  apply Lp.ext
  exact ((toL2_ae (mode n)).trans (mode_ae n)).trans (fourierBasis_ae n).symm

theorem bounded_toL2 (a : BoundaryLInf) : IsBounded (toL2 a) :=
  (Lp.memLp a).ae_eq (toL2_ae a).symm

/-- The bounded L² classes form a linear subspace, with the original MemLp meaning. -/
def boundedL2 : Submodule ℂ BoundaryL2 where
  carrier := {f | IsBounded f}
  zero_mem' := (MemLp.zero : MemLp (0 : Boundary → ℂ) ∞ circleMeasure).ae_eq (Lp.coeFn_zero ℂ ∞ circleMeasure).symm
  add_mem' hf hg := (hf.add hg).ae_eq (Lp.coeFn_add _ _).symm
  smul_mem' c _ hf := (hf.const_smul c).ae_eq (Lp.coeFn_smul c _).symm

theorem bounded_fourierBasis (n : ℤ) : IsBounded (fourierBasis (T := 1) n) :=
  toL2_mode n ▸ bounded_toL2 (mode n)

theorem fourierBasis_mem_hardy (n : ℕ) : fourierBasis (T := 1) (n : ℤ) ∈ hardy :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n,rfl⟩)

/- The following Fourier-span/shift arguments adapt the Apache-2.0 Tau Ceti contributors'
Hardy/Basic.lean and Fourier/AddCircle.lean at d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad.
They are compiled here against the pinned Mathlib; Tau is not imported. -/
/-- The actual closed positive Fourier span is precisely the nonnegative spectrum. -/
theorem mem_hardy_iff (f : BoundaryL2) :
    f ∈ hardy ↔ ∀ n : ℤ, n < 0 → fourierCoeff f n = 0 := by
  constructor
  · intro hf n hn
    let c := innerSL ℂ (fourierBasis (T := 1) n)
    have hle : hardy ≤ c.ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro _ ⟨k,rfl⟩
        have hnk : n ≠ (k : ℤ) := by omega
        exact (orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal n (k : ℤ)).trans
          (ite_eq_right hnk)
      · exact c.isClosed_ker
    simpa only [LinearMap.mem_ker,c,ContinuousLinearMap.coe_coe,innerSL_apply_apply,
      ← HilbertBasis.repr_apply_apply,fourierBasis_repr] using hle hf
  · intro hf
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      ((fourierBasis (T := 1)).hasSum_repr f)
    apply Filter.Eventually.of_forall
    intro s
    apply hardy.sum_mem
    intro n _
    by_cases hn : 0 ≤ n
    · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact hardy.smul_mem _ (fourierBasis_mem_hardy k)
    · simp [fourierBasis_repr,hf n (by omega)]

/-- Multiplication by a Fourier mode shifts the coefficient of a bounded symbol. -/
theorem fourierCoeff_multiply_mode (a : BoundaryLInf) (m n : ℤ) :
    fourierCoeff (multiply a (fourierBasis (T := 1) m)) n = fourierCoeff a (n-m) := by
  have hae : multiply a (fourierBasis (T := 1) m) =ᵐ[circleMeasure]
      fun t => fourier (T := 1) m t * a t := by
    filter_upwards [multiply_ae a (fourierBasis (T := 1) m),fourierBasis_ae m] with t ht hm
    rw [ht,hm,mul_comm]
  rw [fourierCoeff_congr_ae hae,fourierCoeff,fourierCoeff]
  congr 1
  funext t
  rw [smul_eq_mul,smul_eq_mul,← mul_assoc,← fourier_add]
  congr 3
  ring

theorem bounded_multiply (a : BoundaryLInf) (f : BoundaryL2) (hf : IsBounded f) :
    IsBounded (multiply a f) :=
  ((Lp.memLp a).mul hf).ae_eq (multiply_ae a f).symm

/-- Multiplication by a unimodular symbol is a genuine native L² linear isometry. -/
def innerMultiplyIsometry (u : BoundaryLInf) (hu : IsInner u) : BoundaryL2 →ₗᵢ[ℂ] BoundaryL2 where
  toLinearMap := (multiply u).toLinearMap
  norm_map' f := by
    have hn : ∀ᵐ t ∂circleMeasure, ‖multiply u f t‖ = ‖f t‖ := by
      filter_upwards [multiply_ae u f,hu.2] with t ht hnorm
      rw [ht,norm_mul,hnorm,one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
      (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.ge)))

theorem inner_multiply_mode (u : BoundaryLInf) (hu : IsInner u) (j k : ℕ) :
    inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ)))
      (multiply u (fourierBasis (T := 1) (k : ℤ))) = if j = k then 1 else 0 := by
  change inner ℂ (innerMultiplyIsometry u hu (fourierBasis (T := 1) (j : ℤ)))
    (innerMultiplyIsometry u hu (fourierBasis (T := 1) (k : ℤ))) = _
  rw [(innerMultiplyIsometry u hu).inner_map_map]
  simpa only [Int.natCast_inj] using
    orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal (j : ℤ) (k : ℤ)

theorem multiply_mode_mem_hardy (u : BoundaryLInf) (hu : IsInner u) (j : ℕ) :
    multiply u (fourierBasis (T := 1) (j : ℤ)) ∈ hardy := by
  apply (mem_hardy_iff _).mpr
  intro n hn
  rw [fourierCoeff_multiply_mode]
  have hz := (mem_hardy_iff (toL2 u)).mp hu.1 (n-(j : ℤ)) (by omega)
  simpa only [fourierCoeff_congr_ae (toL2_ae u)] using hz

/-- A positive mode sees only finitely many of the shifted inner-function modes. -/
theorem inner_multiply_mode_tail (u : BoundaryLInf) (hu : IsInner u) (n j : ℕ) (hnj : n < j) :
    inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ)))
      (fourierBasis (T := 1) (n : ℤ)) = 0 := by
  rw [← inner_conj_symm,← HilbertBasis.repr_apply_apply,fourierBasis_repr,
    fourierCoeff_multiply_mode]
  have hz := (mem_hardy_iff (toL2 u)).mp hu.1 ((n : ℤ)-(j : ℤ)) (by omega)
  rw [fourierCoeff_congr_ae (toL2_ae u)] at hz
  rw [hz,map_zero]

/-- Only finitely many shifted inner modes are needed to project a positive Fourier mode. -/
def modelPolynomial (u : BoundaryLInf) (n : ℕ) : BoundaryL2 :=
  fourierBasis (T := 1) (n : ℤ) - ∑ j ∈ Finset.range (n+1),
    inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ))) (fourierBasis (T := 1) (n : ℤ)) •
      multiply u (fourierBasis (T := 1) (j : ℤ))

theorem inner_modelPolynomial (u : BoundaryLInf) (hu : IsInner u) (n j : ℕ) :
    inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ))) (modelPolynomial u n) = 0 := by
  classical
  unfold modelPolynomial
  rw [inner_sub_right,inner_sum]
  simp only [inner_smul_right,inner_multiply_mode u hu]
  by_cases hj : j < n+1
  · simp [mul_ite,hj]
  · have hnj : n < j := by omega
    simp [mul_ite,hj]
    simpa only [coe_fourierBasis] using inner_multiply_mode_tail u hu n j hnj

theorem modelPolynomial_mem (u : BoundaryLInf) (hu : IsInner u) (n : ℕ) :
    modelPolynomial u n ∈ model u := by
  constructor
  · exact hardy.sub_mem (fourierBasis_mem_hardy n)
      (hardy.sum_mem (fun j _ => hardy.smul_mem _ (multiply_mode_mem_hardy u hu j)))
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      exact inner_modelPolynomial u hu n j
    | zero => simp
    | add x y hx hy hx' hy' => rw [inner_add_left,hx',hy',add_zero]
    | smul c x hx hx' => rw [inner_smul_left,hx',mul_zero]

theorem bounded_modelPolynomial (u : BoundaryLInf) (n : ℕ) : IsBounded (modelPolynomial u n) :=
  boundedL2.sub_mem (bounded_fourierBasis (n : ℤ))
    (boundedL2.sum_mem (fun j _ => boundedL2.smul_mem _
      (bounded_multiply u _ (bounded_fourierBasis (j : ℤ)))))

/-- Identification with the native orthogonal projection, not a replacement projection definition. -/
theorem modelProjection_fourierBasis (u : BoundaryLInf) (hu : IsInner u) (n : ℕ) :
    ((model u).orthogonalProjectionOnto (fourierBasis (T := 1) (n : ℤ))).val = modelPolynomial u n := by
  have hmode (j : ℕ) : multiply u (fourierBasis (T := 1) (j : ℤ)) ∈ (model u).orthogonal := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro x hx
    have hx' : x ∈ (Submodule.span ℂ (Set.range (fun k : ℕ =>
        multiply u (fourierBasis (T := 1) (k : ℤ))))).orthogonal := hx.2
    exact (Submodule.mem_orthogonal _ x).mp hx' _ (Submodule.subset_span ⟨j,rfl⟩)
  apply (model u).eq_starProjection_of_mem_orthogonal (modelPolynomial_mem u hu n)
  have he : fourierBasis (T := 1) (n : ℤ) - modelPolynomial u n =
      ∑ j ∈ Finset.range (n+1),
        inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ))) (fourierBasis (T := 1) (n : ℤ)) •
          multiply u (fourierBasis (T := 1) (j : ℤ)) := by
    unfold modelPolynomial
    abel
  rw [he]
  exact (model u).orthogonal.sum_mem (fun j _ => (model u).orthogonal.smul_mem _ (hmode j))

/-- The actual bounded vectors are dense in K_u for every inner u, including finite-dimensional cases. -/
theorem bounded_modelCore_dense (u : BoundaryLInf) (hu : IsInner u) :
    Dense {f : Model u | IsBounded f.val} := by
  let B : Submodule ℂ (Model u) := boundedL2.comap (model u).subtype
  change Dense (B : Set (Model u))
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro x _
  have hs := ((fourierBasis (T := 1)).hasSum_repr x.val).mapL (model u).orthogonalProjectionOnto
  simp only [map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hs
  apply (Submodule.isClosed_topologicalClosure B).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply B.topologicalClosure.sum_mem
  intro n _
  by_cases hn : 0 ≤ n
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    apply B.le_topologicalClosure
    apply B.smul_mem
    change IsBounded (((model u).orthogonalProjectionOnto (fourierBasis (T := 1) (k : ℤ))).val)
    rw [modelProjection_fourierBasis u hu k]
    exact bounded_modelPolynomial u k
  · have hz := (mem_hardy_iff x.val).mp x.property.1 n (by omega)
    simp only [fourierBasis_repr,hz,zero_smul]
    exact B.topologicalClosure.zero_mem

/-- The entire shared core-law obligation is discharged, including actual model-core uniqueness. -/
theorem coreLaws : CoreLaws where
  zero := represents_zero
  bounded u a := ⟨boundedSymbolOperator u a,boundedSymbolOperator_represents u a⟩
  add := represents_add
  sub := represents_sub
  unique u hu _ σ A B hA hB := represents_unique_of_dense u (bounded_modelCore_dense u hu) σ A B hA hB
  adjoint := represents_adjoint
  star_toL2 := toL2_star

/-- Uniform a.e. bounds give the exact operator norm bound for the actual symbol. -/
theorem boundedCoreNorm : BoundedCoreNormObligation := by
  intro u σ M hM hb
  have hσ : IsBounded σ := memLp_top_of_bound (Lp.aestronglyMeasurable σ) M hb
  let a : BoundaryLInf := hσ.toLp σ
  have he : toL2 a = σ := Lp.ext ((toL2_ae a).trans hσ.coeFn_toLp)
  refine ⟨boundedSymbolOperator u a,he ▸ boundedSymbolOperator_represents u a,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  apply ((model u).norm_orthogonalProjectionOnto_apply_le (multiply a f.val)).trans
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae a f.val,hσ.coeFn_toLp,hb] with t hm ha ht
  rw [hm,ha,norm_mul]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

theorem constL2_fourier (c : ℂ) : constL2 c = c • fourierBasis (T := 1) (0 : ℤ) := by
  apply Lp.ext
  have hc : constL2 c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  filter_upwards [hc,Lp.coeFn_smul c (fourierBasis (T := 1) (0 : ℤ)),fourierBasis_ae 0] with t ht hs hf
  rw [ht,hs]
  change c = c * ((fourierBasis (T := 1) 0 : BoundaryL2) t)
  rw [hf,fourier_zero,mul_one]

theorem coreForm_const (c : ℂ) (f g : BoundaryL2) :
    coreForm (constL2 c) f g = c * inner ℂ g f := by
  rw [L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  have hc : constL2 c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  filter_upwards [hc] with t ht
  simp only [ht,RCLike.inner_apply]
  ring

/-- Constants have the correct analytic membership and scalar-operator meanings. -/
theorem constantCoreLaws : ConstantCoreLaws where
  hardy c := constL2_fourier c ▸ hardy.smul_mem c (fourierBasis_mem_hardy 0)
  represents u c := by
    intro f g _ _
    rw [coreForm_const]
    change inner ℂ g (c • f) = c * inner ℂ g f
    exact inner_smul_right g f c

/-- The value-level conclusion of manuscript Lemma 1, using the actual native compression. -/
theorem denseCoreSet_value (u : BoundaryLInf) (σ : BoundaryL2) (Z : Model u →L[ℂ] Model u)
    (S : Set (Model u)) (hd : Dense S) (hb : ∀ f ∈ S, IsBounded f.val)
    (hZ : ∀ f ∈ S, ∀ g ∈ S, inner ℂ g (Z f) = coreForm σ f.val g.val)
    (f : Model u) (hf : IsBounded f.val) :
    Z f = (model u).orthogonalProjectionOnto (multiply (hf.toLp f.val) σ) := by
  apply hd.eq_of_inner_right ℂ
  intro g hg
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact (denseCoreSet u σ Z S hd hb hZ f g hf (hb g hg)).trans
    (coreForm_eq_inner_left σ f.val g.val hf)

/-- Monotonicity of positive power summability, including the quasi-Banach exponent range. -/
theorem summable_rpow_mono (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (p q : ℝ)
    (hp : 0 < p) (hpq : p ≤ q) (hs : Summable (fun n => a n ^ p)) :
    Summable (fun n => a n ^ q) := by
  apply hs.of_norm_bounded_eventually_nat
  have hsmall : ∀ᶠ n in atTop, a n ^ p < 1 :=
    hs.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hsmall] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (ha n) q)]
  exact Real.rpow_le_rpow_of_exponent_ge' (ha n)
    ((Real.rpow_lt_one_iff' (ha n) hp).mp hn).le hp.le hpq

/-- The all-positive-p nesting needed by the endpoint and boundary consequences. -/
theorem schattenMonotonicity : SchattenMonotonicity := by
  intro H _ _ A p q hp hpq hs
  exact ⟨hp.trans_le hpq,hs.2.1,summable_rpow_mono
    (fun n => (approximationNumber A n : ℝ)) (fun n => (approximationNumber A n).coe_nonneg)
    p q hp hpq hs.2.2⟩

/-- A compact scalar multiple of the identity vanishes in infinite dimension. -/
theorem scalarCompact : ScalarCompactObligation := by
  intro H _ _ _ hd c hc
  by_contra hne
  have hi : IsCompactOperator (id : H → H) :=
    (IsCompactOperator.smul_isUnit_iff (isUnit_iff_ne_zero.mpr hne)).mp hc
  let : LocallyCompactSpace H := LocallyCompactSpace.of_isCompactOperator_id hi
  exact hd (FiniteDimensional.of_locallyCompactSpace ℂ)

/-- Finite rank gives compactness by the actual finite-dimensional range factorization. -/
theorem finiteRank_compact {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (hf : FiniteRank A) : IsCompactOperator A := by
  obtain ⟨n,hn⟩ := hf
  let : FiniteDimensional ℂ A.range := Module.rank_lt_aleph0_iff.mp
    (hn.trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
  have hc := isCompactOperator_of_locallyCompactSpace_dom A.rangeRestrict
  exact hc.clm_comp A.range.subtypeL

theorem approximationNumber_eq_zero_of_rank_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (n : ℕ) (hn : A.rank ≤ (n : Cardinal)) : approximationNumber A n = 0 := by
  apply le_antisymm _ (show (0 : ℝ≥0) ≤ approximationNumber A n from zero_le)
  let F : {R : H →L[ℂ] H // R.rank ≤ (n : Cardinal)} → ℝ≥0 := fun R => ‖A - R.val‖₊
  have hb : BddBelow (Set.range F) := ⟨0,fun _ _ => zero_le⟩
  have hi := ciInf_le (f := F) hb (⟨A,hn⟩ : {R : H →L[ℂ] H // R.rank ≤ (n : Cardinal)})
  change approximationNumber A n ≤ F ⟨A,hn⟩ at hi
  simpa only [F,sub_self,nnnorm_zero] using hi

/-- Finite-rank operators belong to every positive Schatten class, without a p≥1 carrier. -/
theorem finiteRankSchatten : FiniteRankSchattenObligation := by
  intro H _ _ _ A hf p hp
  obtain ⟨n,hn⟩ := hf
  refine ⟨hp,finiteRank_compact A ⟨n,hn⟩,summable_of_ne_finset_zero (s := Finset.range n) ?_⟩
  intro k hk
  have hnk : n ≤ k := by simpa using hk
  have hc : (n : Cardinal) ≤ (k : Cardinal) := by exact_mod_cast hnk
  rw [approximationNumber_eq_zero_of_rank_le A k (hn.trans hc),NNReal.coe_zero,Real.zero_rpow hp.ne']

/-! Approximation-number calculus. The short infimum/rank arguments adapt the Apache-2.0
Tau Ceti contributors' ApproximationNumber/Basic.lean at d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad.
No Tau import or dependency is used. -/
section ApproximationNumbers
variable {E F G K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

private instance approximationRankNonempty (n : ℕ) : Nonempty {R : E →L[ℂ] F // R.rank ≤ n} :=
  ⟨⟨0,by simp⟩⟩

theorem approximationNumber_le_nnnorm_sub (A : E →L[ℂ] F) {n : ℕ} {R : E →L[ℂ] F}
    (hR : R.rank ≤ n) : approximationNumber A n ≤ ‖A-R‖₊ := by
  unfold approximationNumber
  exact ciInf_le (f := fun R : {R : E →L[ℂ] F // R.rank ≤ n} => ‖A-R.val‖₊)
    (OrderBot.bddBelow _) ⟨R,hR⟩

theorem le_approximationNumber_iff {A : E →L[ℂ] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ approximationNumber A n ↔ ∀ R : E →L[ℂ] F, R.rank ≤ n → c ≤ ‖A-R‖₊ := by
  unfold approximationNumber
  exact (le_ciInf_iff (f := fun R : {R : E →L[ℂ] F // R.rank ≤ n} => ‖A-R.val‖₊)
    (OrderBot.bddBelow _)).trans Subtype.forall

theorem approximationNumber_antitone (A : E →L[ℂ] F) : Antitone (approximationNumber A) :=
  fun _ _ hmn => le_approximationNumber_iff.mpr fun _ hR =>
    approximationNumber_le_nnnorm_sub A (hR.trans (by exact_mod_cast hmn))

theorem approximationNumber_le_nnnorm (A : E →L[ℂ] F) (n : ℕ) : approximationNumber A n ≤ ‖A‖₊ := by
  simpa only [sub_zero] using approximationNumber_le_nnnorm_sub A (n := n) (R := 0) (by simp)

@[simp] theorem approximationNumber_zero (n : ℕ) : approximationNumber (0 : E →L[ℂ] F) n = 0 :=
  le_antisymm (by simpa using approximationNumber_le_nnnorm (0 : E →L[ℂ] F) n) bot_le

/-- Mixed-index addition, with the manuscript's zero-based rank≤n indexing. -/
theorem approximationNumber_add (A B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (A+B) (m+n) ≤ approximationNumber A m + approximationNumber B n :=
  NNReal.le_iInf_add_iInf fun R₁ R₂ =>
    (approximationNumber_le_nnnorm_sub (A+B) (R := R₁.val+R₂.val) (by
      rw [Nat.cast_add]
      exact (LinearMap.rank_add_le _ _).trans (add_le_add R₁.property R₂.property))).trans (by
        rw [add_sub_add_comm]
        exact nnnorm_add_le _ _)

/-- Postcomposition by a bounded map. -/
theorem approximationNumber_comp_left (L : F →L[ℂ] G) (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (L ∘L A) n ≤ ‖L‖₊ * approximationNumber A n := by
  unfold approximationNumber
  rw [NNReal.mul_iInf]
  refine le_ciInf fun R => ?_
  have hR := (LinearMap.lift_rank_comp_le_right R.val.toLinearMap L.toLinearMap).trans
    (Cardinal.lift_le.mpr R.property)
  rw [Cardinal.lift_natCast,Cardinal.lift_le_nat_iff] at hR
  refine (approximationNumber_le_nnnorm_sub (L ∘L A) (R := L ∘L R.val) hR).trans ?_
  rw [← ContinuousLinearMap.comp_sub]
  exact ContinuousLinearMap.opNNNorm_comp_le _ _

/-- Precomposition by a bounded map. -/
theorem approximationNumber_comp_right (A : F →L[ℂ] G) (R : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (A ∘L R) n ≤ approximationNumber A n * ‖R‖₊ := by
  unfold approximationNumber
  rw [NNReal.iInf_mul]
  refine le_ciInf fun T =>
    (approximationNumber_le_nnnorm_sub (A ∘L R) (R := T.val ∘L R)
      ((LinearMap.rank_comp_le_left _ _).trans T.property)).trans ?_
  rw [← ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.opNNNorm_comp_le _ _

/-- The two-sided ideal inequality, for rectangular bounded maps as well. -/
theorem approximationNumber_comp (L : G →L[ℂ] K) (A : F →L[ℂ] G) (R : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (L ∘L A ∘L R) n ≤ ‖L‖₊ * approximationNumber A n * ‖R‖₊ := by
  exact (approximationNumber_comp_left L (A ∘L R) n).trans (by
    rw [mul_assoc]
    gcongr
    exact approximationNumber_comp_right A R n)

/-- Mixed-index composition inequality. -/
theorem approximationNumber_comp_add (A : F →L[ℂ] G) (B : E →L[ℂ] F) (m n : ℕ) :
    approximationNumber (A ∘L B) (m+n) ≤ approximationNumber A m * approximationNumber B n := by
  unfold approximationNumber
  rw [NNReal.iInf_mul]
  refine le_ciInf fun R₁ => ?_
  rw [NNReal.mul_iInf]
  refine le_ciInf fun R₂ => ?_
  have h₂ := (LinearMap.lift_rank_comp_le_right R₂.val.toLinearMap (A-R₁.val).toLinearMap).trans
    (Cardinal.lift_le.mpr R₂.property)
  rw [Cardinal.lift_natCast,Cardinal.lift_le_nat_iff] at h₂
  have hrank : (R₁.val ∘L B + (A-R₁.val) ∘L R₂.val).rank ≤ (m+n : ℕ) := by
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le _ _).trans
      (add_le_add ((LinearMap.rank_comp_le_left _ _).trans R₁.property) h₂)
  refine (approximationNumber_le_nnnorm_sub (A ∘L B) hrank).trans ?_
  have he : A ∘L B - (R₁.val ∘L B + (A-R₁.val) ∘L R₂.val) = (A-R₁.val) ∘L (B-R₂.val) := by
    simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp]
    abel
  rw [he]
  exact ContinuousLinearMap.opNNNorm_comp_le _ _

@[simp] theorem approximationNumber_smul (c : ℂ) (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (c • A) n = ‖c‖₊ * approximationNumber A n := by
  have hle (c : ℂ) (A : E →L[ℂ] F) : approximationNumber (c • A) n ≤ ‖c‖₊ * approximationNumber A n := by
    unfold approximationNumber
    rw [NNReal.mul_iInf]
    refine le_ciInf fun R =>
      (approximationNumber_le_nnnorm_sub (c • A) (R := c • R.val)
        ((Submodule.rank_mono (LinearMap.range_smul_le_range _ c)).trans R.property)).trans ?_
    rw [← smul_sub]
    exact nnnorm_smul_le _ _
  refine (hle c A).antisymm ?_
  by_cases hc : c = 0
  · subst c; simp
  · calc
      ‖c‖₊ * approximationNumber A n = ‖c‖₊ * approximationNumber (c⁻¹ • c • A) n := by rw [inv_smul_smul₀ hc]
      _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * approximationNumber (c • A) n) := by gcongr; exact hle _ _
      _ = approximationNumber (c • A) n := by
        rw [← mul_assoc,nnnorm_inv,mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hc),one_mul]

@[simp] theorem approximationNumber_neg (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (-A) n = approximationNumber A n := by
  simpa only [neg_one_smul,norm_neg,norm_one,NNReal.coe_one,nnnorm_neg,nnnorm_one,one_mul]
    using approximationNumber_smul (-1) A n

end ApproximationNumbers

section SchattenIdeals
variable {E F G K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- A sufficient power bound valid for all positive exponents, without a p≥1 triangle inequality. -/
theorem add_rpow_bound (a b p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 < p) :
    (a+b)^p ≤ (2:ℝ)^p * (a^p+b^p) := by
  calc
    (a+b)^p ≤ (2*max a b)^p := Real.rpow_le_rpow (by positivity) (by
      have h₁ := le_max_left a b
      have h₂ := le_max_right a b
      linarith) hp.le
    _ = (2:ℝ)^p * max (a^p) (b^p) := by rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_max ha hb hp.le]
    _ ≤ (2:ℝ)^p * (a^p+b^p) := mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (Real.rpow_nonneg hb p))
        (le_add_of_nonneg_left (Real.rpow_nonneg ha p))) (Real.rpow_nonneg (by norm_num) p)

/-- Pointwise domination is enough for power summability at every positive p. -/
theorem summable_rpow_of_le {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ n, a n ≤ C*b n) (p : ℝ) (hp : 0 < p)
    (hs : Summable (fun n => b n ^ p)) : Summable (fun n => a n ^ p) := by
  apply (hs.mul_left (C^p)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (ha n) p)]
  exact (Real.rpow_le_rpow (ha n) (h n) hp.le).trans_eq (Real.mul_rpow hC (hb n))

/-- Addition closure of the actual approximation-number Schatten predicate, including 0<p<1. -/
theorem schatten_add {p : ℝ} {A B : E →L[ℂ] F} (hA : Schatten p A) (hB : Schatten p B) :
    Schatten p (A+B) := by
  refine ⟨hA.1,hA.2.1.add hB.2.1,?_⟩
  have hmajor : Summable (fun n => (2:ℝ)^p *
      ((approximationNumber A n : ℝ)^p + (approximationNumber B n : ℝ)^p)) :=
    (hA.2.2.add hB.2.2).mul_left _
  have heven : Summable (fun n => (approximationNumber (A+B) (2*n) : ℝ)^p) := by
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
    have hab : (approximationNumber (A+B) (2*n) : ℝ) ≤
        (approximationNumber A n : ℝ) + (approximationNumber B n : ℝ) := by
      exact_mod_cast (show approximationNumber (A+B) (2*n) ≤ _ by
        simpa only [two_mul] using approximationNumber_add A B n n)
    exact (Real.rpow_le_rpow (by positivity) hab hA.1.le).trans
      (add_rpow_bound _ _ p (by positivity) (by positivity) hA.1)
  have hodd : Summable (fun n => (approximationNumber (A+B) (2*n+1) : ℝ)^p) := by
    apply heven.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
    apply Real.rpow_le_rpow (by positivity) _ hA.1.le
    exact_mod_cast approximationNumber_antitone (A+B) (by omega : 2*n ≤ 2*n+1)
  exact heven.even_add_odd hodd

theorem schatten_comp_left {p : ℝ} {A : E →L[ℂ] F} (hA : Schatten p A) (L : F →L[ℂ] G) :
    Schatten p (L ∘L A) := by
  refine ⟨hA.1,hA.2.1.clm_comp L,?_⟩
  exact summable_rpow_of_le (fun n => (approximationNumber (L ∘L A) n).coe_nonneg)
    (fun n => (approximationNumber A n).coe_nonneg) ‖L‖ (norm_nonneg _)
    (fun n => by exact_mod_cast approximationNumber_comp_left L A n) p hA.1 hA.2.2

theorem schatten_comp_right {p : ℝ} {A : F →L[ℂ] G} (hA : Schatten p A) (R : E →L[ℂ] F) :
    Schatten p (A ∘L R) := by
  refine ⟨hA.1,hA.2.1.comp_clm R,?_⟩
  apply summable_rpow_of_le (fun n => (approximationNumber (A ∘L R) n).coe_nonneg)
    (fun n => (approximationNumber A n).coe_nonneg) ‖R‖ (norm_nonneg _) _ p hA.1 hA.2.2
  intro n
  simpa only [mul_comm] using (show (approximationNumber (A ∘L R) n : ℝ) ≤
    (approximationNumber A n : ℝ)*‖R‖ by exact_mod_cast approximationNumber_comp_right A R n)

theorem schatten_comp {p : ℝ} {A : F →L[ℂ] G} (hA : Schatten p A)
    (L : G →L[ℂ] K) (R : E →L[ℂ] F) : Schatten p (L ∘L A ∘L R) :=
  schatten_comp_left (schatten_comp_right hA R) L

theorem schatten_smul {p : ℝ} {A : E →L[ℂ] F} (hA : Schatten p A) (c : ℂ) : Schatten p (c • A) := by
  refine ⟨hA.1,hA.2.1.smul c,?_⟩
  apply summable_rpow_of_le (fun n => (approximationNumber (c • A) n).coe_nonneg)
    (fun n => (approximationNumber A n).coe_nonneg) ‖c‖ (norm_nonneg _) _ p hA.1 hA.2.2
  intro n
  exact_mod_cast (le_of_eq (approximationNumber_smul c A n))

theorem schatten_neg {p : ℝ} {A : E →L[ℂ] F} (hA : Schatten p A) : Schatten p (-A) := by
  exact ⟨hA.1,hA.2.1.neg,by simpa only [approximationNumber_neg] using hA.2.2⟩

theorem schatten_zero (p : ℝ) (hp : 0 < p) : Schatten p (0 : E →L[ℂ] F) := by
  refine ⟨hp,isCompactOperator_zero,?_⟩
  simp only [approximationNumber_zero,NNReal.coe_zero,Real.zero_rpow hp.ne']
  exact summable_zero

end SchattenIdeals

section IdealNorms
variable {E F G K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Pointwise approximation-number domination yields the stated Schatten gauge bound. -/
theorem schattenNorm_le_of_approx_le {p : ℝ} {A : E →L[ℂ] F} {B : G →L[ℂ] K}
    (hB : Schatten p B) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, (approximationNumber A n : ℝ) ≤ C*(approximationNumber B n : ℝ)) :
    schattenNorm p A ≤ C * schattenNorm p B := by
  have hpoint (n : ℕ) : (approximationNumber A n : ℝ)^p ≤ C^p * (approximationNumber B n : ℝ)^p :=
    (Real.rpow_le_rpow (NNReal.coe_nonneg _) (h n) hB.1.le).trans_eq
      (Real.mul_rpow hC (NNReal.coe_nonneg _))
  have hsA := summable_rpow_of_le (fun n => (approximationNumber A n).coe_nonneg)
    (fun n => (approximationNumber B n).coe_nonneg) C hC h p hB.1 hB.2.2
  have hsum : (∑' n, (approximationNumber A n : ℝ)^p) ≤ C^p * ∑' n, (approximationNumber B n : ℝ)^p := by
    calc
      _ ≤ ∑' n, C^p * (approximationNumber B n : ℝ)^p :=
        Summable.tsum_le_tsum hpoint hsA (hB.2.2.mul_left _)
      _ = _ := tsum_mul_left
  unfold schattenNorm
  calc
    _ ≤ (C^p * ∑' n, (approximationNumber B n : ℝ)^p)^(1/p) :=
      Real.rpow_le_rpow (tsum_nonneg (fun n => Real.rpow_nonneg (NNReal.coe_nonneg _) p)) hsum (one_div_nonneg.mpr hB.1.le)
    _ = C * (∑' n, (approximationNumber B n : ℝ)^p)^(1/p) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hC p) (tsum_nonneg (fun n => Real.rpow_nonneg (NNReal.coe_nonneg _) p))]
      congr 1
      simpa only [one_div] using Real.rpow_rpow_inv hC hB.1.ne'

/-- Two-sided bounded-composition estimate, valid for every positive Schatten exponent. -/
theorem schattenNorm_comp_le {p : ℝ} {A : F →L[ℂ] G} (hA : Schatten p A)
    (L : G →L[ℂ] K) (R : E →L[ℂ] F) :
    schattenNorm p (L ∘L A ∘L R) ≤ (‖L‖*‖R‖) * schattenNorm p A := by
  apply schattenNorm_le_of_approx_le hA (‖L‖*‖R‖) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro n
  have h := approximationNumber_comp L A R n
  have hr : (approximationNumber (L ∘L A ∘L R) n : ℝ) ≤
      ‖L‖*(approximationNumber A n : ℝ)*‖R‖ := by exact_mod_cast h
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hr

end IdealNorms

/-- Reverse the actual bounded similarity; this is operator algebra, not a spectral assumption. -/
theorem similarity_reverse {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) :
    S.symm.toContinuousLinearMap ∘L similarity S D ∘L S.toContinuousLinearMap = D := by
  ext x
  simp [similarity]

theorem compact_similarity {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) :
    IsCompactOperator (similarity S D) ↔ IsCompactOperator D := by
  constructor
  · intro hc
    have hr : IsCompactOperator (S.symm.toContinuousLinearMap ∘L similarity S D ∘L S.toContinuousLinearMap) :=
      (hc.comp_clm S.toContinuousLinearMap).clm_comp S.symm.toContinuousLinearMap
    rw [similarity_reverse] at hr
    exact hr
  · intro hc
    exact (hc.comp_clm S.symm.toContinuousLinearMap).clm_comp S.toContinuousLinearMap

theorem schatten_similarity {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) (p : ℝ) :
    Schatten p (similarity S D) ↔ Schatten p D := by
  constructor
  · intro hs
    have hr := schatten_comp hs S.symm.toContinuousLinearMap S.toContinuousLinearMap
    rw [similarity_reverse] at hr
    exact hr
  · intro hs
    exact schatten_comp hs S.toContinuousLinearMap S.symm.toContinuousLinearMap

theorem similarity_norm {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : SequenceL2 ≃L[ℂ] H) (D : SequenceOperator) (p : ℝ) (hD : Schatten p D) :
    (‖S.toContinuousLinearMap‖*‖S.symm.toContinuousLinearMap‖)⁻¹ * schattenNorm p D ≤
      schattenNorm p (similarity S D) ∧
    schattenNorm p (similarity S D) ≤
      (‖S.toContinuousLinearMap‖*‖S.symm.toContinuousLinearMap‖) * schattenNorm p D := by
  have hup := schattenNorm_comp_le hD S.toContinuousLinearMap S.symm.toContinuousLinearMap
  refine ⟨?_,hup⟩
  have hback := schattenNorm_comp_le ((schatten_similarity S D p).mpr hD)
    S.symm.toContinuousLinearMap S.toContinuousLinearMap
  rw [similarity_reverse] at hback
  rw [mul_comm ‖S.symm.toContinuousLinearMap‖ ‖S.toContinuousLinearMap‖] at hback
  by_cases hzero : ‖S.toContinuousLinearMap‖*‖S.symm.toContinuousLinearMap‖ = 0
  · simpa only [hzero,inv_zero,zero_mul] using schattenNorm_nonneg p (similarity S D)
  · calc
      _ ≤ (‖S.toContinuousLinearMap‖*‖S.symm.toContinuousLinearMap‖)⁻¹ *
          ((‖S.toContinuousLinearMap‖*‖S.symm.toContinuousLinearMap‖)*schattenNorm p (similarity S D)) :=
        mul_le_mul_of_nonneg_left hback (inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hzero,one_mul]

/-- All fields of the shared all-p ideal-law obligation are now actual proofs. -/
theorem idealLaws : IdealLaws where
  schatten_add _p _A _B hA hB := schatten_add hA hB
  schatten_neg _p _A hA := schatten_neg hA
  compact_add _A _B hA hB := hA.add hB
  compact_neg _A hA := hA.neg
  compact_similarity := compact_similarity
  schatten_similarity := schatten_similarity
  similarity_norm := similarity_norm

/-- The actual Schatten predicate as an ordinary complex submodule, for each p>0. -/
def schattenIdeal (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] (p : ℝ) (hp : 0 < p) :
    Submodule ℂ (H →L[ℂ] H) where
  carrier := {A | Schatten p A}
  zero_mem' := schatten_zero p hp
  add_mem' hA hB := schatten_add hA hB
  smul_mem' c _ hA := schatten_smul hA c

theorem schattenIdeal_twoSided (u : BoundaryLInf) (p : ℝ) (hp : 0 < p) :
    TwoSided u (schattenIdeal (Model u) p hp) :=
  fun _ hA L R => schatten_comp hA L R

/-- Finite sums are closed without imposing p≥1. -/
theorem schatten_sum {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (s : Finset ι) (A : ι → H →L[ℂ] H) (p : ℝ) (hp : 0 < p)
    (hA : ∀ i ∈ s, Schatten p (A i)) : Schatten p (∑ i ∈ s, A i) :=
  (schattenIdeal H p hp).sum_mem hA

/-- Finite rank uses the unchanged numerical rank-bound predicate. -/
def finiteRankIdeal (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    Submodule ℂ (H →L[ℂ] H) where
  carrier := {A | FiniteRank A}
  zero_mem' := ⟨0,by simp⟩
  add_mem' {A B} hA hB := by
    obtain ⟨m,hm⟩ := hA
    obtain ⟨n,hn⟩ := hB
    refine ⟨m+n,?_⟩
    rw [Nat.cast_add]
    exact (LinearMap.rank_add_le _ _).trans (add_le_add hm hn)
  smul_mem' c A hA := by
    obtain ⟨n,hn⟩ := hA
    exact ⟨n,(Submodule.rank_mono (LinearMap.range_smul_le_range A.toLinearMap c)).trans hn⟩

theorem finiteRankIdeal_twoSided (u : BoundaryLInf) : TwoSided u (finiteRankIdeal (Model u)) := by
  intro A hA L R
  obtain ⟨n,hn⟩ := hA
  refine ⟨n,?_⟩
  exact (LinearMap.rank_comp_le_right (A ∘L R).toLinearMap L.toLinearMap).trans
    ((LinearMap.rank_comp_le_left R.toLinearMap A.toLinearMap).trans hn)

/-- Every ideal carrier used by the gap specializations is now an actual submodule. -/
theorem idealCarriers : IdealCarriers where
  schatten u p hp := ⟨schattenIdeal (Model u) p hp,schattenIdeal_twoSided u p hp,fun _ => Iff.rfl⟩
  compact u := ⟨compactOperator (RingHom.id ℂ) (Model u) (Model u),
    fun _ hA L R => (hA.comp_clm R).clm_comp L,fun _ => Iff.rfl⟩
  finiteRank u := ⟨finiteRankIdeal (Model u),finiteRankIdeal_twoSided u,fun _ => Iff.rfl⟩

/-- Gap classification using the ideal closure laws. -/
theorem gapSpecializations (h : FiniteCompressionObligation) : GapSpecializationsConclusion :=
  Reduction.gapSpecializations h idealCarriers

/-- Inversion of the actual unitary conjugation. -/
theorem unitaryConjugate_reverse {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) :
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L unitaryConjugate U A ∘L
      U.toContinuousLinearEquiv.toContinuousLinearMap = A := by
  ext x
  simp [unitaryConjugate]

/-- Unitary ideal invariance and the S₂⊆S_p consequence use the proved generic ideal laws. -/
theorem unitaryIdealLaws : UnitaryIdealLaws where
  compact U A := by
    constructor
    · intro hc
      have hr : IsCompactOperator (U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          unitaryConjugate U A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap) :=
        (hc.comp_clm U.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      rw [unitaryConjugate_reverse] at hr
      exact hr
    · intro hc
      exact (hc.comp_clm U.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
        U.toContinuousLinearEquiv.toContinuousLinearMap
  schatten U A p := by
    constructor
    · intro hs
      have hr := schatten_comp hs U.symm.toContinuousLinearEquiv.toContinuousLinearMap
        U.toContinuousLinearEquiv.toContinuousLinearMap
      rw [unitaryConjugate_reverse] at hr
      exact hr
    · intro hs
      exact schatten_comp hs U.toContinuousLinearEquiv.toContinuousLinearMap
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  inclusion A p hp hs := schattenMonotonicity A 2 p (by norm_num) hp hs

/-! Native Hardy evaluation. The geometric-series and Riesz-kernel proof route adapts the
Apache-2.0 Tau Ceti Hardy DiskFunction/ReproducingKernel files at the recorded revision;
all definitions here use analyticValue and the native full Fourier basis. -/
section HardyEvaluation

/-- Each coefficient is bounded using the full native Fourier isometry. -/
theorem norm_fourierCoeff_le (f : BoundaryL2) (n : ℤ) : ‖fourierCoeff f n‖ ≤ ‖f‖ := by
  rw [← fourierBasis_repr]
  exact (lp.norm_apply_le_norm (by norm_num) (fourierBasis.repr f) n).trans_eq (fourierBasis.repr.norm_map f)

/-- The coefficient series converges absolutely at every point of the open disk. -/
theorem summable_norm_analyticValue (f : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖fourierCoeff f (n : ℤ) * z^n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖f‖)
  rw [norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_right (norm_fourierCoeff_le f n) (by positivity)

theorem hasSum_analyticValue (f : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => fourierCoeff f (n : ℤ) * z^n) (analyticValue f z) :=
  (summable_norm_analyticValue f hz).of_norm.hasSum

/-- A coarse evaluation bound suffices to construct a bounded functional before its sharp kernel. -/
theorem norm_analyticValue_le (f : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖analyticValue f z‖ ≤ ‖f‖ / (1-‖z‖) := by
  have hmajor := (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖f‖
  calc
    ‖analyticValue f z‖ ≤ ∑' n : ℕ, ‖fourierCoeff f (n : ℤ) * z^n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_analyticValue f hz)
    _ ≤ ∑' n : ℕ, ‖f‖ * ‖z‖^n := by
      apply Summable.tsum_le_tsum _ (summable_norm_analyticValue f hz) hmajor
      intro n
      rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_right (norm_fourierCoeff_le f n) (by positivity)
    _ = ‖f‖ / (1-‖z‖) := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (norm_nonneg z) hz,div_eq_mul_inv]

/-- Evaluation is additive inside the disk, with no assertion about total tsum values outside it. -/
theorem analyticValue_add (f g : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (f+g) z = analyticValue f z + analyticValue g z := by
  refine (hasSum_analyticValue (f+g) hz).unique ?_
  have h := (hasSum_analyticValue f hz).add (hasSum_analyticValue g hz)
  simpa only [← fourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply,add_mul] using h

theorem analyticValue_smul (c : ℂ) (f : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (c • f) z = c * analyticValue f z := by
  refine (hasSum_analyticValue (c • f) hz).unique ?_
  have h := (hasSum_analyticValue f hz).mul_left c
  simpa only [← fourierBasis_repr,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_assoc] using h

/-- The bounded evaluation functional uses the unchanged native Hardy subtype. -/
def hardyEvaluation (z : Disk) : Hardy →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => analyticValue f.val z.val
      map_add' := fun f g => analyticValue_add f.val g.val z.property
      map_smul' := fun c f => analyticValue_smul c f.val z.property }
    (1-‖z.val‖)⁻¹ fun f => by
      simpa only [LinearMap.coe_mk,AddHom.coe_mk,div_eq_mul_inv,mul_comm,Submodule.norm_coe] using
        norm_analyticValue_le f.val z.property

@[simp] theorem hardyEvaluation_apply (z : Disk) (f : Hardy) :
    hardyEvaluation z f = analyticValue f.val z.val := rfl

/-- The native Riesz vector of actual disk evaluation, with no new assumed reproducing property. -/
def szegoKernel (z : Disk) : Hardy :=
  (InnerProductSpace.toDual ℂ Hardy).symm (hardyEvaluation z)

@[simp] theorem inner_szegoKernel (z : Disk) (f : Hardy) :
    inner ℂ (szegoKernel z) f = analyticValue f.val z.val := by
  simp [szegoKernel]

@[simp] theorem analyticValue_fourierBasis (n : ℕ) (z : ℂ) :
    analyticValue (fourierBasis (T := 1) (n : ℤ)) z = z^n := by
  unfold analyticValue
  rw [tsum_eq_single n]
  · rw [← fourierBasis_repr,HilbertBasis.repr_self,lp.single_apply,Pi.single_eq_same,one_mul]
  · intro k hkn
    rw [← fourierBasis_repr,HilbertBasis.repr_self,lp.single_apply,Pi.single_eq_of_ne (by exact_mod_cast hkn),zero_mul]

/-- Nonnegative Fourier coefficients of the Riesz kernel have the correct conjugate powers. -/
@[simp] theorem fourierCoeff_szegoKernel (z : Disk) (n : ℕ) :
    fourierCoeff (szegoKernel z).val (n : ℤ) = conj z.val ^ n := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  change inner ℂ (⟨fourierBasis (T := 1) (n : ℤ),fourierBasis_mem_hardy n⟩ : Hardy) (szegoKernel z) = _
  rw [← inner_conj_symm,inner_szegoKernel,analyticValue_fourierBasis,map_pow]

@[simp] theorem analyticValue_szegoKernel (w : Disk) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (szegoKernel w).val z = (1-conj w.val*z)⁻¹ := by
  have hw : ‖w.val‖ < 1 := w.property
  have hprod : ‖conj w.val*z‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [hw,norm_nonneg w.val,norm_nonneg z]
  unfold analyticValue
  simp_rw [fourierCoeff_szegoKernel,← mul_pow]
  exact tsum_geometric_of_norm_lt_one hprod

/-- The exact squared norm is derived from reproduction, after constructing bounded evaluation. -/
theorem norm_szegoKernel_sq (w : Disk) : ‖szegoKernel w‖^2 = (1-‖w.val‖^2)⁻¹ := by
  have hw : ‖w.val‖ < 1 := w.property
  have hpos : 0 < 1-‖w.val‖^2 := by nlinarith [hw,norm_nonneg w.val]
  calc
    ‖szegoKernel w‖^2 = ‖inner ℂ (szegoKernel w) (szegoKernel w)‖ := by
      rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq]
    _ = ‖(1-conj w.val*w.val)⁻¹‖ := by rw [inner_szegoKernel,analyticValue_szegoKernel w w.property]
    _ = (1-‖w.val‖^2)⁻¹ := by
      rw [norm_inv,Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_one,
        ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]

theorem norm_szegoKernel (w : Disk) : ‖szegoKernel w‖ = (Real.sqrt (1-‖w.val‖^2))⁻¹ := by
  rw [← Real.sqrt_inv,← norm_szegoKernel_sq,Real.sqrt_sq (norm_nonneg _)]

/-- Sharp norm of the genuine evaluation CLM on the open disk. -/
theorem norm_hardyEvaluation (w : Disk) : ‖hardyEvaluation w‖ = (Real.sqrt (1-‖w.val‖^2))⁻¹ := by
  rw [← norm_szegoKernel]
  exact ((InnerProductSpace.toDual ℂ Hardy).symm.norm_map (hardyEvaluation w)).symm

/-- The exact evaluation estimate on Hardy vectors. -/
theorem norm_analyticValue_hardy_le (f : Hardy) (w : Disk) :
    ‖analyticValue f.val w.val‖ ≤ ‖f‖ / Real.sqrt (1-‖w.val‖^2) := by
  simpa only [hardyEvaluation_apply,norm_hardyEvaluation,div_eq_mul_inv,mul_comm] using
    (hardyEvaluation w).le_opNorm f

/-- The literal Fourier coefficient series of analyticValue. -/
def analyticSeries (f : BoundaryL2) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => fourierCoeff f (n : ℤ))

theorem one_le_radius_analyticSeries (f : BoundaryL2) : 1 ≤ (analyticSeries f).radius := by
  have h := (analyticSeries f).le_radius_of_bound ‖f‖ (r := 1) fun n => by
    rw [NNReal.coe_one,one_pow,mul_one,analyticSeries,FormalMultilinearSeries.ofScalars_norm]
    exact norm_fourierCoeff_le f n
  simpa using h

/-- The series is an actual analytic power series throughout the open disk. -/
theorem hasFPowerSeriesOnBall_analyticValue (f : BoundaryL2) :
    HasFPowerSeriesOnBall (analyticValue f) (analyticSeries f) 0 1 := by
  have h := ((analyticSeries f).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (one_le_radius_analyticSeries f))).mono zero_lt_one
    (one_le_radius_analyticSeries f)
  have hsum : (analyticSeries f).sum = analyticValue f := by
    funext z
    rw [FormalMultilinearSeries.sum,analyticValue]
    simp only [analyticSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]
  rwa [hsum] at h

theorem analyticOnNhd_analyticValue (f : BoundaryL2) : AnalyticOnNhd ℂ (analyticValue f) disk := by
  intro z hz
  have h := (hasFPowerSeriesOnBall_analyticValue f).analyticAt_of_mem (y := z)
    (by simpa [← ENNReal.coe_one,Metric.eball_coe,disk] using hz)
  simpa using h

theorem differentiableOn_analyticValue (f : BoundaryL2) : DifferentiableOn ℂ (analyticValue f) disk :=
  (analyticOnNhd_analyticValue f).differentiableOn

/-- Equality of analytic values determines a Hardy vector; arbitrary negative spectrum is excluded. -/
theorem hardy_analyticValue_injective (f g : Hardy)
    (h : ∀ z ∈ disk, analyticValue f.val z = analyticValue g.val z) : f = g := by
  have hevent : ∀ᶠ z in 𝓝 (0 : ℂ), analyticValue f.val z = analyticValue g.val z := by
    have hb : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 zero_lt_one
    filter_upwards [hb] with z hz
    apply h z
    simpa only [Metric.mem_ball,dist_zero_right,disk,Set.mem_ofPred_eq] using hz
  have hs : analyticSeries f.val = analyticSeries g.val :=
    (hasFPowerSeriesOnBall_analyticValue f.val).hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesOnBall_analyticValue g.val).hasFPowerSeriesAt hevent
  apply Subtype.ext
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  rw [fourierBasis_repr,fourierBasis_repr]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    have hc := congrArg (fun P : FormalMultilinearSeries ℂ ℂ ℂ => P n (fun _ => 1)) hs
    simpa only [analyticSeries,FormalMultilinearSeries.ofScalars_apply_eq,one_pow,smul_eq_mul,mul_one] using hc
  · rw [(mem_hardy_iff f.val).mp f.property n (lt_of_not_ge hn),
      (mem_hardy_iff g.val).mp g.property n (lt_of_not_ge hn)]

/-- The Fourier characters at nonnegative indices are powers of the first character. -/
theorem fourier_nat_pow (n : ℕ) (t : Boundary) : fourier (T := 1) (n : ℤ) t = (fourier 1 t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,fourier_add,ih,pow_succ]

/-- The actual native L² series for the Szegő vector, with summable geometric coefficients. -/
theorem hasSum_szegoKernel (w : Disk) :
    HasSum (fun n : ℕ => conj w.val^n • fourierBasis (T := 1) (n : ℤ)) (szegoKernel w).val := by
  have hneg (n : ℕ) : fourierCoeff (szegoKernel w).val (-(n+1 : ℤ)) = 0 :=
    (mem_hardy_iff _).mp (szegoKernel w).property _ (by omega)
  have h := (hasSum_fourier_series_L2 (szegoKernel w).val).nat_add_neg_add_one
  simpa only [hneg,zero_smul,add_zero,fourierCoeff_szegoKernel,coe_fourierBasis] using h

/-- The Riesz kernel has the literal rational boundary representative almost everywhere. -/
theorem szegoKernel_ae (w : Disk) :
    (szegoKernel w).val =ᵐ[circleMeasure] fun t => (1-conj w.val*fourier (T := 1) 1 t)⁻¹ := by
  let C : ℕ → BoundaryL2 := fun n => conj w.val^n • fourierBasis (T := 1) (n : ℤ)
  have hn (n : ℕ) : ‖C n‖ = ‖w.val‖^n := by
    simp only [C,norm_smul,norm_pow,Complex.norm_conj,(fourierBasis (T := 1)).orthonormal.norm_eq_one,mul_one]
  have hnorm : Summable (fun n => ‖C n‖) := by
    simpa only [hn] using summable_geometric_of_lt_one (norm_nonneg w.val) w.property
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have hsum : (∑' n, C n) = (szegoKernel w).val := (hasSum_szegoKernel w).tsum_eq
  rw [hsum] at hae
  have hcoe (n : ℕ) : C n =ᵐ[circleMeasure]
      fun t => conj w.val^n * fourier (T := 1) (n : ℤ) t := by
    filter_upwards [Lp.coeFn_smul (conj w.val^n) (fourierBasis (T := 1) (n : ℤ)),fourierBasis_ae n] with t hs hb
    simp only [C]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hb]
  filter_upwards [hae,ae_all_iff.mpr hcoe] with t ht hc
  have hw : ‖w.val‖ < 1 := w.property
  have hprod : ‖conj w.val*fourier (T := 1) 1 t‖ < 1 := by
    simpa only [norm_mul,Complex.norm_conj,fourier_apply,Circle.norm_coe,mul_one] using hw
  have hg := hasSum_geometric_of_norm_lt_one hprod
  have heq : (fun n : ℕ => C n t) = fun n => (conj w.val*fourier (T := 1) 1 t)^n := by
    funext n
    rw [hc n,fourier_nat_pow,mul_pow]
  rw [heq] at ht
  exact ht.unique hg

/-- A normalized Szegő vector with exactly the manuscript's boundary NodeKernel meaning. -/
def hardyNodeVector (w : Disk) : Hardy := (Real.sqrt (1-‖w.val‖^2) : ℂ) • szegoKernel w

theorem nodeKernel_hardyNodeVector (w : Disk) : NodeKernel w (hardyNodeVector w).val := by
  filter_upwards [szegoKernel_ae w,Lp.coeFn_smul (Real.sqrt (1-‖w.val‖^2) : ℂ) (szegoKernel w).val] with t hk hs
  change ((Real.sqrt (1-‖w.val‖^2) : ℂ) • (szegoKernel w).val) t = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hk,div_eq_mul_inv]

@[simp] theorem fourierCoeff_toL2 (a : BoundaryLInf) (n : ℤ) :
    fourierCoeff (toL2 a) n = fourierCoeff a n :=
  congrFun (fourierCoeff_congr_ae (toL2_ae a)) n

/-- Positive Fourier modes remain Hardy after multiplication by any bounded Hardy symbol. -/
theorem multiply_mode_hardy (a : BoundaryLInf) (ha : toL2 a ∈ hardy) (n : ℕ) :
    multiply a (fourierBasis (T := 1) (n : ℤ)) ∈ hardy := by
  apply (mem_hardy_iff _).mpr
  intro k hk
  rw [fourierCoeff_multiply_mode]
  have hz := (mem_hardy_iff (toL2 a)).mp ha (k-(n : ℤ)) (by omega)
  simpa only [fourierCoeff_toL2] using hz

/-- Coefficient shifts give analytic multiplication by a positive mode without a convolution theorem. -/
theorem analyticValue_multiply_mode (a : BoundaryLInf) (ha : toL2 a ∈ hardy)
    (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (multiply a (fourierBasis (T := 1) (n : ℤ))) z = innerValue a z * z^n := by
  let F : ℕ → ℂ := fun k => fourierCoeff (multiply a (fourierBasis (T := 1) (n : ℤ))) (k : ℤ)*z^k
  have htail : HasSum (fun k : ℕ => F (k+n)) (innerValue a z*z^n) := by
    change HasSum (fun k : ℕ => F (k+n)) (analyticValue (toL2 a) z*z^n)
    convert (hasSum_analyticValue (toL2 a) hz).mul_right (z^n) using 1
    funext k
    simp only [F,fourierCoeff_multiply_mode,Nat.cast_add,add_sub_cancel_right,pow_add,fourierCoeff_toL2]
    ring
  have hzero : ∑ k ∈ Finset.range n, F k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hcoeff := (mem_hardy_iff (toL2 a)).mp ha ((k : ℤ)-(n : ℤ)) (by omega)
    simp only [fourierCoeff_toL2] at hcoeff
    simp only [F,fourierCoeff_multiply_mode,hcoeff,zero_mul]
  have hsum := htail.sum_range_add
  rw [hzero,zero_add] at hsum
  exact (hasSum_analyticValue (multiply a (fourierBasis (T := 1) (n : ℤ))) hz).unique hsum

/-- At an actual zero of the inner disk function, the Szegő vector lies in the literal model space. -/
theorem szegoKernel_mem_model (u : BoundaryLInf) (hu : IsInner u) (w : Disk)
    (hw : innerValue u w.val = 0) : (szegoKernel w).val ∈ model u := by
  refine ⟨(szegoKernel w).property,?_⟩
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n,rfl⟩ := hy
    change inner ℂ (szegoKernel w)
      (⟨multiply u (fourierBasis (T := 1) (n : ℤ)),multiply_mode_hardy u hu.1 n⟩ : Hardy) = 0
    rw [inner_szegoKernel,analyticValue_multiply_mode u hu.1 n w.property,hw,zero_mul]
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]

/-- The normalized node vector is a model vector at every actual zero, without a basis assumption. -/
theorem hardyNodeVector_mem_model (u : BoundaryLInf) (hu : IsInner u) (w : Disk)
    (hw : innerValue u w.val = 0) : (hardyNodeVector w).val ∈ model u :=
  (model u).smul_mem _ (szegoKernel_mem_model u hu w hw)

/-- A positive Fourier character as a native Hardy subtype vector. -/
def hardyMode (n : ℕ) : Hardy := ⟨fourierBasis (T := 1) (n : ℤ),fourierBasis_mem_hardy n⟩

/-- The actual positive modes have dense linear span in the native Hardy space. -/
theorem hardyModes_dense : Dense (Submodule.span ℂ (Set.range hardyMode) : Set Hardy) := by
  let B : Submodule ℂ Hardy := Submodule.span ℂ (Set.range hardyMode)
  change Dense (B : Set Hardy)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro f _
  have hs := ((fourierBasis (T := 1)).hasSum_repr f.val).mapL hardy.orthogonalProjectionOnto
  simp only [map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hs
  apply (Submodule.isClosed_topologicalClosure B).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply B.topologicalClosure.sum_mem
  intro n _
  by_cases hn : 0 ≤ n
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hn
    apply B.topologicalClosure.smul_mem
    apply B.le_topologicalClosure
    change (hardy.orthogonalProjectionOnto (hardyMode k).val) ∈ B
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact Submodule.subset_span ⟨k,rfl⟩
  · have hz := (mem_hardy_iff f.val).mp f.property n (by omega)
    simp only [fourierBasis_repr,hz,zero_smul]
    exact B.topologicalClosure.zero_mem

/-- Bounded Hardy symbols multiply the entire Hardy space into itself by closure. -/
theorem multiply_mem_hardy (a : BoundaryLInf) (ha : toL2 a ∈ hardy)
    (f : BoundaryL2) (hf : f ∈ hardy) : multiply a f ∈ hardy := by
  have hle : hardy ≤ hardy.comap (multiply a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      exact multiply_mode_hardy a ha n
    · exact (Submodule.isClosed_topologicalClosure _).preimage (multiply a).continuous
  exact hle hf

/-- Bounded analytic multiplication on the unchanged native Hardy space. -/
def hardyMultiply (a : BoundaryLInf) (ha : toL2 a ∈ hardy) : Hardy →L[ℂ] Hardy :=
  ((multiply a) ∘L hardy.subtypeL).codRestrict hardy (fun f => multiply_mem_hardy a ha f.val f.property)

@[simp] theorem hardyMultiply_apply (a : BoundaryLInf) (ha : toL2 a ∈ hardy) (f : Hardy) :
    (hardyMultiply a ha f).val = multiply a f.val := rfl

/-- Analytic evaluation respects actual boundary multiplication, proved on modes then by density. -/
theorem analyticValue_multiply (a : BoundaryLInf) (ha : toL2 a ∈ hardy) (f : Hardy) (w : Disk) :
    analyticValue (multiply a f.val) w.val = innerValue a w.val * analyticValue f.val w.val := by
  let F : Hardy →L[ℂ] ℂ := hardyEvaluation w ∘L hardyMultiply a ha
  let G : Hardy →L[ℂ] ℂ := innerValue a w.val • hardyEvaluation w
  have he : F = G := by
    apply ContinuousLinearMap.ext_on hardyModes_dense
    rintro _ ⟨n,rfl⟩
    change analyticValue (multiply a (fourierBasis (T := 1) (n : ℤ))) w.val =
      innerValue a w.val * analyticValue (fourierBasis (T := 1) (n : ℤ)) w.val
    rw [analyticValue_multiply_mode a ha n w.property,analyticValue_fourierBasis]
  change F f = G f
  exact congrArg (fun L : Hardy →L[ℂ] ℂ => L f) he

/-- The actual Hölder multiplication has the expected L∞×L² operator bound. -/
theorem norm_multiply_le (a : BoundaryLInf) (f : BoundaryL2) : ‖multiply a f‖ ≤ ‖a‖*‖f‖ := by
  change ‖(ContinuousLinearMap.lsmul ℂ ℂ).holder 2 a f‖ ≤ ‖a‖*‖f‖
  calc
    _ ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ)‖*‖a‖*‖f‖ :=
      (ContinuousLinearMap.lsmul ℂ ℂ).norm_holder_apply_apply_le a f
    _ ≤ 1*‖a‖*‖f‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = ‖a‖*‖f‖ := by rw [one_mul]

theorem norm_hardyMultiply_le (a : BoundaryLInf) (ha : toL2 a ∈ hardy) :
    ‖hardyMultiply a ha‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact norm_multiply_le a f.val

/-- Bounded analytic boundary symbols have uniformly bounded actual analytic values. -/
theorem norm_innerValue_le (a : BoundaryLInf) (ha : toL2 a ∈ hardy) (w : Disk) :
    ‖innerValue a w.val‖ ≤ ‖a‖ := by
  let k := szegoKernel w
  have hw : ‖w.val‖ < 1 := w.property
  have hpos : 0 < ‖k‖^2 := by
    rw [show k = szegoKernel w from rfl,norm_szegoKernel_sq]
    exact inv_pos.mpr (by nlinarith [norm_nonneg w.val])
  have he : inner ℂ k (hardyMultiply a ha k) = innerValue a w.val * inner ℂ k k := by
    rw [inner_szegoKernel,inner_szegoKernel]
    exact analyticValue_multiply a ha k w
  have hself : ‖inner ℂ k k‖ = ‖k‖^2 := by
    rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq]
  have hb : ‖innerValue a w.val‖*‖k‖^2 ≤ ‖a‖*‖k‖^2 := by
    calc
      _ = ‖innerValue a w.val * inner ℂ k k‖ := by rw [norm_mul,hself]
      _ = ‖inner ℂ k (hardyMultiply a ha k)‖ := congrArg norm he.symm
      _ ≤ ‖k‖*‖hardyMultiply a ha k‖ := norm_inner_le_norm _ _
      _ ≤ ‖k‖*(‖a‖*‖k‖) := mul_le_mul_of_nonneg_left (norm_multiply_le a k.val) (norm_nonneg k)
      _ = ‖a‖*‖k‖^2 := by ring
  exact (mul_le_mul_iff_left₀ hpos).mp hb

/-- The normalized native node vector has norm exactly one. -/
theorem norm_hardyNodeVector (w : Disk) : ‖hardyNodeVector w‖ = 1 := by
  have hw : ‖w.val‖ < 1 := w.property
  have hs : 0 < Real.sqrt (1-‖w.val‖^2) := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg w.val])
  rw [hardyNodeVector,norm_smul,norm_szegoKernel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  exact mul_inv_cancel₀ hs.ne'

/-- Every model vector is orthogonal to the entire actual uH² image, by closure of the mode span. -/
theorem inner_multiply_model (u : BoundaryLInf) (f : Model u) (g : Hardy) :
    inner ℂ (multiply u g.val) f.val = 0 := by
  let L := innerSL ℂ f.val ∘L multiply u
  have hle : hardy ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      change inner ℂ f.val (multiply u (fourierBasis (T := 1) (n : ℤ))) = 0
      exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp f.property.2 _
        (Submodule.subset_span ⟨n,rfl⟩))
    · exact L.isClosed_ker
  exact inner_eq_zero_symm.mp (hle g.property)

/-- The explicit model-kernel vector uses the genuine boundary multiplication operator. -/
def modelKernelVector (u : BoundaryLInf) (w : Disk) : BoundaryL2 :=
  (szegoKernel w).val - conj (innerValue u w.val) • multiply u (szegoKernel w).val

theorem modelKernelVector_mem (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    modelKernelVector u w ∈ model u := by
  refine ⟨hardy.sub_mem (szegoKernel w).property
    (hardy.smul_mem _ (multiply_mem_hardy u hu.1 _ (szegoKernel w).property)),?_⟩
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n,rfl⟩ := hy
    change inner ℂ ((szegoKernel w).val-conj (innerValue u w.val) • multiply u (szegoKernel w).val)
      (multiply u (fourierBasis (T := 1) (n : ℤ))) = 0
    rw [inner_sub_left,inner_smul_left]
    have hm : inner ℂ (multiply u (szegoKernel w).val) (multiply u (fourierBasis (T := 1) (n : ℤ))) =
        inner ℂ (szegoKernel w).val (fourierBasis (T := 1) (n : ℤ)) :=
      (innerMultiplyIsometry u hu).inner_map_map _ _
    rw [hm]
    change inner ℂ (szegoKernel w)
      (⟨multiply u (fourierBasis (T := 1) (n : ℤ)),multiply_mode_hardy u hu.1 n⟩ : Hardy) -
      conj (conj (innerValue u w.val)) * inner ℂ (szegoKernel w) (hardyMode n) = 0
    rw [inner_szegoKernel,analyticValue_multiply_mode u hu.1 n w.property,inner_szegoKernel]
    simp only [hardyMode,analyticValue_fourierBasis,Complex.conj_conj,sub_self]
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]

/-- The model's Riesz kernel as an actual member of its native submodule. -/
def modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) : Model u :=
  ⟨modelKernelVector u w,modelKernelVector_mem u hu w⟩

/-- Model reproduction, with the kernel in the conjugate-linear slot. -/
theorem inner_modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) (f : Model u) :
    inner ℂ (modelReproducingKernel u hu w) f = analyticValue f.val w.val := by
  change inner ℂ ((szegoKernel w).val-conj (innerValue u w.val) • multiply u (szegoKernel w).val) f.val = _
  rw [inner_sub_left,inner_smul_left,inner_multiply_model,mul_zero,sub_zero]
  exact inner_szegoKernel w (⟨f.val,f.property.1⟩ : Hardy)

/-- Analytic evaluation is subtractive inside the disk. -/
theorem analyticValue_sub (f g : BoundaryL2) {z : ℂ} (hz : ‖z‖ < 1) :
    analyticValue (f-g) z = analyticValue f z-analyticValue g z := by
  refine (hasSum_analyticValue (f-g) hz).unique ?_
  have h := (hasSum_analyticValue f hz).sub (hasSum_analyticValue g hz)
  simpa only [← fourierBasis_repr,map_sub,lp.coeFn_sub,Pi.sub_apply,sub_mul] using h

/-- The actual model kernel realizes the manuscript's literal interior kernelValue formula. -/
theorem analyticValue_modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk)
    {z : ℂ} (hz : ‖z‖ < 1) : analyticValue (modelReproducingKernel u hu w).val z = kernelValue u w.val z := by
  change analyticValue ((szegoKernel w).val-conj (innerValue u w.val) • multiply u (szegoKernel w).val) z = _
  rw [analyticValue_sub _ _ hz,analyticValue_smul _ _ hz,analyticValue_multiply u hu.1 _ ⟨z,hz⟩,
    analyticValue_szegoKernel w hz]
  unfold kernelValue
  rw [div_eq_mul_inv]
  ring

/-- The actual model kernel realizes the manuscript's literal a.e. boundary kernel. -/
theorem modelReproducingKernel_ae (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    (modelReproducingKernel u hu w).val =ᵐ[circleMeasure] kernelBoundary u w.val := by
  filter_upwards [Lp.coeFn_sub (szegoKernel w).val (conj (innerValue u w.val) • multiply u (szegoKernel w).val),
    Lp.coeFn_smul (conj (innerValue u w.val)) (multiply u (szegoKernel w).val),
    multiply_ae u (szegoKernel w).val,szegoKernel_ae w] with t hs hc hm hk
  change ((szegoKernel w).val-conj (innerValue u w.val) • multiply u (szegoKernel w).val) t = _
  rw [hs]
  simp only [Pi.sub_apply,hc,Pi.smul_apply,smul_eq_mul,hm,hk,kernelBoundary,div_eq_mul_inv]
  ring

/-- The exact squared norm of the actual model kernel, including constant-inner degeneracy. -/
theorem norm_modelReproducingKernel_sq (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    ‖modelReproducingKernel u hu w‖^2 = (1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2) := by
  have h := inner_modelReproducingKernel u hu w (modelReproducingKernel u hu w)
  rw [inner_self_eq_norm_sq_to_K,analyticValue_modelReproducingKernel u hu w w.property] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  simpa [kernelValue,Complex.conj_mul'] using h

theorem norm_modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    ‖modelReproducingKernel u hu w‖ = Real.sqrt ((1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2)) := by
  rw [← norm_modelReproducingKernel_sq u hu w,Real.sqrt_sq (norm_nonneg _)]

/-- The literal boundary denominator never vanishes for a point of the open disk. -/
theorem kernelDenominator_ne_zero (w : Disk) (t : Boundary) :
    1-conj w.val*fourier (T := 1) 1 t ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  have hw : ‖w.val‖ < 1 := w.property
  simp only [norm_one,norm_mul,Complex.norm_conj,fourier_apply,Circle.norm_coe,mul_one] at he
  linarith

/-- A nonconstant inner function has a nonzero model kernel at every disk point. -/
theorem modelReproducingKernel_ne_zero (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (w : Disk) : modelReproducingKernel u hu w ≠ 0 := by
  intro hzero
  have hv : (modelReproducingKernel u hu w).val = 0 := congrArg Subtype.val hzero
  have hz : (modelReproducingKernel u hu w).val =ᵐ[circleMeasure] fun _ => (0 : ℂ) := by
    rw [hv]
    exact Lp.coeFn_zero ℂ 2 circleMeasure
  have hnum : ∀ᵐ t ∂circleMeasure, 1-conj (innerValue u w.val)*u t = 0 := by
    filter_upwards [modelReproducingKernel_ae u hu w,hz] with t hk ht
    have he : kernelBoundary u w.val t = 0 := hk.symm.trans ht
    exact (div_eq_zero_iff.mp he).resolve_right (kernelDenominator_ne_zero w t)
  have hc : conj (innerValue u w.val) ≠ 0 := by
    obtain ⟨t,ht⟩ := hnum.exists
    intro hc
    simp only [hc,zero_mul,sub_zero] at ht
    exact one_ne_zero ht
  apply hn
  refine ⟨(conj (innerValue u w.val))⁻¹,?_⟩
  apply Lp.ext
  have hconst : constLInf ((conj (innerValue u w.val))⁻¹) =ᵐ[circleMeasure]
      fun _ => (conj (innerValue u w.val))⁻¹ := (memLp_const _).coeFn_toLp
  filter_upwards [hnum,hconst] with t ht hct
  rw [hct]
  apply mul_left_cancel₀ hc
  rw [mul_inv_cancel₀ hc]
  exact (sub_eq_zero.mp ht).symm

/-- Native unit normalization satisfies the manuscript's complete a.e. normalized-kernel predicate. -/
theorem normalizedModelKernel_normalize (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    normalizedModelKernel u w (NormedSpace.normalize (modelReproducingKernel u hu w)) := by
  let d : ℝ := Real.sqrt ((1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2))
  have he : NormedSpace.normalize (modelReproducingKernel u hu w) =
      ((d⁻¹ : ℝ) : ℂ) • modelReproducingKernel u hu w := by
    rw [NormedSpace.normalize,norm_modelReproducingKernel]
    exact (Complex.coe_smul ..).symm
  rw [he]
  filter_upwards [modelReproducingKernel_ae u hu w,
    Lp.coeFn_smul ((d⁻¹ : ℝ) : ℂ) (modelReproducingKernel u hu w).val] with t hk hs
  change (((d⁻¹ : ℝ) : ℂ) • (modelReproducingKernel u hu w).val) t = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hk]
  change ((d⁻¹ : ℝ) : ℂ)*kernelBoundary u w.val t = kernelBoundary u w.val t / (d : ℂ)
  rw [Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

/-- Nonconstant inner functions have genuine unit-norm normalized model kernels. -/
theorem norm_normalize_modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u)
    (hn : Nonconstant u) (w : Disk) : ‖NormedSpace.normalize (modelReproducingKernel u hu w)‖ = 1 :=
  NormedSpace.norm_normalize_eq_one_iff.mpr (modelReproducingKernel_ne_zero u hu hn w)

/-- The actual analytic value of a nonconstant inner function stays strictly in the disk. -/
theorem norm_innerValue_lt_one (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (w : Disk) :
    ‖innerValue u w.val‖ < 1 := by
  have hk : 0 < ‖modelReproducingKernel u hu w‖ :=
    norm_pos_iff.mpr (modelReproducingKernel_ne_zero u hu hn w)
  have hpos : 0 < ‖modelReproducingKernel u hu w‖^2 := pow_pos hk 2
  rw [norm_modelReproducingKernel_sq] at hpos
  have hw : ‖w.val‖ < 1 := w.property
  have hd : 0 < 1-‖w.val‖^2 := by nlinarith [norm_nonneg w.val]
  rcases div_pos_iff.mp hpos with ⟨hnum,_⟩ | ⟨_,hden⟩
  · nlinarith [norm_nonneg (innerValue u w.val)]
  · linarith

/-- The boundary geometric denominator is uniformly bounded away from zero. -/
theorem kernelDenominator_norm_lower (w : Disk) (t : Boundary) :
    1-‖w.val‖ ≤ ‖1-conj w.val*fourier (T := 1) 1 t‖ := by
  simpa only [norm_one,norm_mul,Complex.norm_conj,fourier_apply,Circle.norm_coe,mul_one] using
    norm_sub_norm_le (1 : ℂ) (conj w.val*fourier (T := 1) 1 t)

/-- Interior Szegő vectors are bounded boundary functions, so they are legitimate core tests. -/
theorem bounded_szegoKernel (w : Disk) : IsBounded (szegoKernel w).val := by
  apply memLp_top_of_bound (Lp.aestronglyMeasurable (szegoKernel w).val) (1-‖w.val‖)⁻¹
  filter_upwards [szegoKernel_ae w] with t ht
  rw [ht,norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr w.property) (kernelDenominator_norm_lower w t)

theorem bounded_hardyNodeVector (w : Disk) : IsBounded (hardyNodeVector w).val :=
  boundedL2.smul_mem _ (bounded_szegoKernel w)

/-- Every actual interior model kernel belongs to the original bounded model core. -/
theorem bounded_modelReproducingKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    IsBounded (modelReproducingKernel u hu w).val :=
  boundedL2.sub_mem (bounded_szegoKernel w)
    (boundedL2.smul_mem _ (bounded_multiply u _ (bounded_szegoKernel w)))

@[simp] theorem analyticValue_zero (z : ℂ) : analyticValue (0 : BoundaryL2) z = 0 := by
  unfold analyticValue
  simp only [← fourierBasis_repr,map_zero,lp.coeFn_zero,Pi.zero_apply,zero_mul,tsum_zero]

/-- Model kernels are total for the actual native model space, by proved Hardy injectivity. -/
theorem modelReproducingKernels_dense (u : BoundaryLInf) (hu : IsInner u) :
    Dense (Submodule.span ℂ (Set.range (modelReproducingKernel u hu)) : Set (Model u)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have he : (⟨f.val,f.property.1⟩ : Hardy) = 0 := by
    apply hardy_analyticValue_injective
    intro z hz
    change analyticValue f.val z = analyticValue (0 : BoundaryL2) z
    rw [analyticValue_zero]
    exact (inner_modelReproducingKernel u hu ⟨z,hz⟩ f).symm.trans
      ((Submodule.mem_orthogonal _ _).mp hf _
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨z,hz⟩,rfl⟩)))
  exact Subtype.ext (congrArg (fun x : Hardy => x.val) he)

end HardyEvaluation

section DualDiagonalModel

/-- Literal NodeKernel data uniquely identifies the already constructed normalized Hardy vector. -/
theorem nodeKernel_eq_hardyNodeVector (w : Disk) (k : BoundaryL2) (hk : NodeKernel w k) :
    k = (hardyNodeVector w).val := by
  apply Lp.ext
  filter_upwards [hk,nodeKernel_hardyNodeVector w] with t ht hv
  exact ht.trans hv.symm

theorem bounded_nodeKernel (w : Disk) (k : BoundaryL2) (hk : NodeKernel w k) : IsBounded k := by
  rw [nodeKernel_eq_hardyNodeVector w k hk]
  exact bounded_hardyNodeVector w

/-- The literal normalized node kernel reproduces Hardy evaluation with its exact positive factor. -/
theorem inner_nodeKernel (w : Disk) (k : BoundaryL2) (hk : NodeKernel w k) (f : Hardy) :
    inner ℂ k f.val = (Real.sqrt (1-‖w.val‖^2) : ℂ)*analyticValue f.val w.val := by
  rw [nodeKernel_eq_hardyNodeVector w k hk]
  change inner ℂ ((Real.sqrt (1-‖w.val‖^2) : ℂ) • (szegoKernel w).val) f.val = _
  rw [inner_smul_left,Complex.conj_ofReal]
  exact congrArg (fun v => (Real.sqrt (1-‖w.val‖^2) : ℂ)*v) (inner_szegoKernel w f)

/-- The actual analytic core form gives node eigenfunctionals even for merely H² symbols. -/
theorem analytic_tto_node_pairing (u : BoundaryLInf) (φ : Hardy) (A : Model u →L[ℂ] Model u)
    (hA : RepresentsTTO u φ.val A) (w : Disk) (k : Model u) (hk : NodeKernel w k.val)
    (f : Model u) (hf : IsBounded f.val) :
    inner ℂ k (A f) = analyticValue φ.val w.val * inner ℂ k f := by
  let af : BoundaryLInf := hf.toLp f.val
  have he : toL2 af = f.val := Lp.ext ((toL2_ae af).trans hf.coeFn_toLp)
  have haf : toL2 af ∈ hardy := he.symm ▸ f.property.1
  have hp : multiply af φ.val ∈ hardy := multiply_mem_hardy af haf φ.val φ.property
  have hev : innerValue af w.val = analyticValue f.val w.val := congrArg (fun g => analyticValue g w.val) he
  calc
    inner ℂ k (A f) = coreForm φ.val f.val k.val := hA f k hf (bounded_nodeKernel w k.val hk)
    _ = inner ℂ k.val (multiply af φ.val) := coreForm_eq_inner_left φ.val f.val k.val hf
    _ = (Real.sqrt (1-‖w.val‖^2) : ℂ)*analyticValue (multiply af φ.val) w.val :=
      inner_nodeKernel w k.val hk ⟨multiply af φ.val,hp⟩
    _ = (Real.sqrt (1-‖w.val‖^2) : ℂ)*(analyticValue f.val w.val*analyticValue φ.val w.val) := by
      rw [analyticValue_multiply af haf φ w,hev]
    _ = analyticValue φ.val w.val * inner ℂ k f := by
      change (Real.sqrt (1-‖w.val‖^2) : ℂ)*(analyticValue f.val w.val*analyticValue φ.val w.val) =
        analyticValue φ.val w.val * inner ℂ k.val f.val
      rw [inner_nodeKernel w k.val hk (⟨f.val,f.property.1⟩ : Hardy)]
      ring

/-- The analytic TTO adjoint acts on its actual normalized node kernel by the conjugate value. -/
theorem analytic_tto_node_adjoint (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A)
    (w : Disk) (k : Model u) (hk : NodeKernel w k.val) :
    A.adjoint k = conj (analyticValue φ.val w.val) • k := by
  apply (bounded_modelCore_dense u hu).eq_of_inner_left ℂ
  intro f hf
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ k.val (A f).val = inner ℂ (conj (analyticValue φ.val w.val) • k.val) f.val
  rw [inner_smul_left,Complex.conj_conj]
  exact analytic_tto_node_pairing u φ A hA w k hk f hf

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The dual synthesis is literally the inverse adjoint of the original Riesz synthesis. -/
def dualSynthesis (R : SequenceL2 ≃L[ℂ] H) : SequenceL2 ≃L[ℂ] H :=
  ContinuousLinearEquiv.equivOfInverse' R.symm.toContinuousLinearMap.adjoint R.toContinuousLinearMap.adjoint
    (by
      have h := congrArg (fun T : H →L[ℂ] H => T.adjoint) R.coe_comp_coe_symm
      simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h)
    (by
      have h := congrArg (fun T : SequenceOperator => T.adjoint) R.coe_symm_comp_coe
      simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h)

@[simp] theorem dualSynthesis_coe (R : SequenceL2 ≃L[ℂ] H) :
    (dualSynthesis R).toContinuousLinearMap = R.symm.toContinuousLinearMap.adjoint := rfl

@[simp] theorem dualSynthesis_symm_coe (R : SequenceL2 ≃L[ℂ] H) :
    (dualSynthesis R).symm.toContinuousLinearMap = R.toContinuousLinearMap.adjoint := rfl

theorem norm_dualSynthesis (R : SequenceL2 ≃L[ℂ] H) :
    ‖(dualSynthesis R).toContinuousLinearMap‖ = ‖R.symm.toContinuousLinearMap‖ :=
  ContinuousLinearMap.adjoint.norm_map _

theorem norm_dualSynthesis_symm (R : SequenceL2 ≃L[ℂ] H) :
    ‖(dualSynthesis R).symm.toContinuousLinearMap‖ = ‖R.toContinuousLinearMap‖ :=
  ContinuousLinearMap.adjoint.norm_map _

/-- Inverse dual coordinates are pairings with the original normalized kernels. -/
theorem dualSynthesis_coord (R : SequenceL2 ≃L[ℂ] H) (f : H) (n : ℕ) :
    ((dualSynthesis R).symm f) n = inner ℂ (R (lp.single 2 n (1 : ℂ))) f := by
  change (R.toContinuousLinearMap.adjoint f) n = _
  simpa [lp.inner_single_left,RCLike.inner_apply] using
    ContinuousLinearMap.adjoint_inner_right R.toContinuousLinearMap (lp.single 2 n (1 : ℂ)) f

/-- The basis-vector diagonal predicate determines all pointwise coordinates. -/
theorem diagonal_apply (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D) (x : SequenceL2) (n : ℕ) :
    D x n = w n*x n := by
  let F : SequenceL2 →L[ℂ] ℂ := innerSL ℂ (lp.single 2 n (1 : ℂ)) ∘L D
  let G : SequenceL2 →L[ℂ] ℂ := w n • innerSL ℂ (lp.single 2 n (1 : ℂ))
  have he : F = G := by
    apply lp.ext_continuousLinearMap (𝕜 := ℂ) (E := fun _ : ℕ => ℂ) (p := 2) (f := F) (g := G) (by norm_num)
    intro i
    apply ContinuousLinearMap.ext_ring
    change inner ℂ (lp.single 2 n (1 : ℂ)) (D (lp.single 2 i (1 : ℂ))) =
      w n * inner ℂ (lp.single 2 n (1 : ℂ) : SequenceL2) (lp.single 2 i (1 : ℂ))
    rw [hd i,inner_smul_right]
    by_cases hni : n = i
    · subst i
      rfl
    · simp [lp.inner_single_left,RCLike.inner_apply,lp.single_apply,Pi.single_eq_of_ne hni]
  have h := congrArg (fun L : SequenceL2 →L[ℂ] ℂ => L x) he
  simpa [F,G,lp.inner_single_left,RCLike.inner_apply] using h

/-- Pairings with the synthesis columns determine a vector, via inverse dual coordinates. -/
theorem eq_of_inner_synthesis (R : SequenceL2 ≃L[ℂ] H) (x y : H)
    (h : ∀ n, inner ℂ (R (lp.single 2 n (1 : ℂ))) x = inner ℂ (R (lp.single 2 n (1 : ℂ))) y) : x = y := by
  apply (dualSynthesis R).symm.injective
  apply lp.ext
  funext n
  rw [dualSynthesis_coord,dualSynthesis_coord]
  exact h n

/-- Transport by the dual synthesis diagonalizes exactly the adjoint eigenvectors of the primal columns. -/
theorem diagonal_dualTransport_iff (R : SequenceL2 ≃L[ℂ] H) (w : ℕ → ℂ) (A : H →L[ℂ] H) :
    Diagonal w ((dualSynthesis R).symm.toContinuousLinearMap ∘L A ∘L (dualSynthesis R).toContinuousLinearMap) ↔
      ∀ n, A.adjoint (R (lp.single 2 n (1 : ℂ))) = conj (w n) • R (lp.single 2 n (1 : ℂ)) := by
  let S := dualSynthesis R
  constructor
  · intro hd n
    apply ext_inner_right ℂ
    intro f
    calc
      inner ℂ (A.adjoint (R (lp.single 2 n (1 : ℂ)))) f = inner ℂ (R (lp.single 2 n (1 : ℂ))) (A f) :=
        ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = (S.symm (A f)) n := (dualSynthesis_coord R (A f) n).symm
      _ = ((S.symm.toContinuousLinearMap ∘L A ∘L S.toContinuousLinearMap) (S.symm f)) n := by simp
      _ = w n*(S.symm f) n := diagonal_apply w _ hd (S.symm f) n
      _ = inner ℂ (conj (w n) • R (lp.single 2 n (1 : ℂ))) f := by
        rw [inner_smul_left,Complex.conj_conj,← dualSynthesis_coord]
  · intro heig
    have hcoord (x : SequenceL2) (n : ℕ) : (S.symm (A (S x))) n = w n*x n := by
      rw [dualSynthesis_coord,← ContinuousLinearMap.adjoint_inner_left,heig n,
        inner_smul_left,Complex.conj_conj,← dualSynthesis_coord]
      rw [S.symm_apply_apply]
    intro j
    apply lp.ext
    funext i
    change (S.symm (A (S (lp.single 2 j (1 : ℂ))))) i = (w j • (lp.single 2 j (1 : ℂ) : SequenceL2)) i
    rw [hcoord]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    by_cases hij : i = j
    · subst i
      rfl
    · simp [lp.single_apply,Pi.single_eq_of_ne hij]

theorem pairing_of_adjoint_eigen (A : H →L[ℂ] H) (k : H) (v : ℂ)
    (h : A.adjoint k = conj v • k) (f : H) : inner ℂ k (A f) = v*inner ℂ k f := by
  rw [← ContinuousLinearMap.adjoint_inner_left,h,inner_smul_left,Complex.conj_conj]

/-- Analytic TTO representation is exactly its actual normalized-kernel adjoint eigenvalue law.
The reverse direction reconstructs each bounded-core value by the native model projection. -/
theorem representsTTO_iff_node_adjoint (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (R : SequenceL2 ≃L[ℂ] Model u) (hR : RieszSynthesis u a R) (φ : Hardy) (A : Model u →L[ℂ] Model u) :
    RepresentsTTO u φ.val A ↔ ∀ n,
      A.adjoint (R (lp.single 2 n (1 : ℂ))) =
        conj (analyticValue φ.val (a n).val) • R (lp.single 2 n (1 : ℂ)) := by
  constructor
  · intro hA n
    exact analytic_tto_node_adjoint u hu φ A hA (a n) _ (hR n)
  · intro heig f g hf _hg
    let af : BoundaryLInf := hf.toLp f.val
    have he : toL2 af = f.val := Lp.ext ((toL2_ae af).trans hf.coeFn_toLp)
    have haf : toL2 af ∈ hardy := he.symm ▸ f.property.1
    have hp : multiply af φ.val ∈ hardy := multiply_mem_hardy af haf φ.val φ.property
    have hev (w : Disk) : innerValue af w.val = analyticValue f.val w.val :=
      congrArg (fun v => analyticValue v w.val) he
    let P : Model u := (model u).orthogonalProjectionOnto (multiply af φ.val)
    have hAf : A f = P := by
      apply eq_of_inner_synthesis R
      intro n
      calc
        inner ℂ (R (lp.single 2 n (1 : ℂ))) (A f) =
            analyticValue φ.val (a n).val * inner ℂ (R (lp.single 2 n (1 : ℂ))) f :=
          pairing_of_adjoint_eigen A _ _ (heig n) f
        _ = (Real.sqrt (1-‖(a n).val‖^2) : ℂ)*analyticValue (multiply af φ.val) (a n).val := by
          change analyticValue φ.val (a n).val * inner ℂ (R (lp.single 2 n (1 : ℂ))).val f.val = _
          rw [inner_nodeKernel (a n) _ (hR n) (⟨f.val,f.property.1⟩ : Hardy),
            analyticValue_multiply af haf φ (a n),hev]
          ring
        _ = inner ℂ (R (lp.single 2 n (1 : ℂ))).val (multiply af φ.val) :=
          (inner_nodeKernel (a n) _ (hR n) ⟨multiply af φ.val,hp⟩).symm
        _ = inner ℂ (R (lp.single 2 n (1 : ℂ))) P :=
          (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).symm
    rw [hAf]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact (coreForm_eq_inner_left φ.val f.val g.val hf).symm

/-- The paper's dual-kernel operator model is proved from the actual Riesz synthesis data. -/
theorem dualDiagonal : DualDiagonalObligation := by
  intro u hu _hn a _ha _hb R hR
  let S := dualSynthesis R
  refine ⟨S,dualSynthesis_coe R,norm_dualSynthesis R,norm_dualSynthesis_symm R,?_⟩
  intro φ
  constructor
  · intro A hA
    let D : SequenceOperator := S.symm.toContinuousLinearMap ∘L A ∘L S.toContinuousLinearMap
    have hd : Diagonal (fun n => analyticValue φ.val (a n).val) D :=
      (diagonal_dualTransport_iff R _ A).mpr ((representsTTO_iff_node_adjoint u hu a R hR φ A).mp hA)
    refine ⟨D,hd,?_⟩
    ext x
    simp [similarity,D]
  · intro D hD
    apply (representsTTO_iff_node_adjoint u hu a R hR φ (similarity S D)).mpr
    apply (diagonal_dualTransport_iff R _ (similarity S D)).mp
    have he : S.symm.toContinuousLinearMap ∘L similarity S D ∘L S.toContinuousLinearMap = D := by
      ext x
      simp [similarity]
    change Diagonal _ (S.symm.toContinuousLinearMap ∘L similarity S D ∘L S.toContinuousLinearMap)
    rw [he]
    exact hD

end DualDiagonalModel

section HilbertAdjoints
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite-rank adjoints factor through the same finite-dimensional range. -/
theorem rank_adjoint_le_of_rank_le (R : H →L[ℂ] H) {n : ℕ} (hn : R.rank ≤ (n : Cardinal)) :
    R.adjoint.rank ≤ (n : Cardinal) := by
  let : FiniteDimensional ℂ R.range := Module.rank_lt_aleph0_iff.mp
    (hn.trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
  have he : R.adjoint = R.rangeRestrict.adjoint ∘L R.range.orthogonalProjectionOnto := by
    simpa only [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL] using
      congrArg (fun T : H →L[ℂ] H => T.adjoint)
        (show R = R.range.subtypeL ∘L R.rangeRestrict from rfl)
  rw [he]
  exact (LinearMap.rank_comp_le_left _ _).trans ((LinearMap.rank_le_domain _).trans hn)

/-- Each rank-bounded approximant supplies its adjoint at exactly the same norm distance. -/
theorem approximationNumber_adjoint_le (A : H →L[ℂ] H) (n : ℕ) :
    approximationNumber A.adjoint n ≤ approximationNumber A n := by
  apply le_approximationNumber_iff.mpr
  intro R hR
  refine (approximationNumber_le_nnnorm_sub A.adjoint (rank_adjoint_le_of_rank_le R hR)).trans_eq ?_
  rw [← map_sub, LinearIsometryEquiv.nnnorm_map]

@[simp] theorem approximationNumber_adjoint (A : H →L[ℂ] H) (n : ℕ) :
    approximationNumber A.adjoint n = approximationNumber A n :=
  (approximationNumber_adjoint_le A n).antisymm (by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using approximationNumber_adjoint_le A.adjoint n)

omit [CompleteSpace H] in
/-- Finite-dimensional projection approximates a compact operator in norm.
The compact-cover/projection argument adapts Tau Ceti ApproximationNumber/Compact.lean:137–167
at the Apache-2.0 revision recorded above, without importing that library. -/
theorem compact_finiteRank_approx (A : H →L[ℂ] H) (hc : IsCompactOperator A)
    (ε : ℝ) (hε : 0 < ε) : ∃ R : H →L[ℂ] H, FiniteRank R ∧ ‖A-R‖ ≤ ε := by
  obtain ⟨K,hK,hAK⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨t,_,ht,hKt⟩ := hK.finite_cover_balls hε
  let V := Submodule.span ℂ t
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ ht
  let R := V.starProjection ∘L A
  have hR : R.rank ≤ (Module.finrank ℂ V : Cardinal) := by
    refine (Submodule.rank_mono ?_).trans_eq (Module.finrank_eq_rank ℂ V).symm
    exact (LinearMap.range_comp_le_range _ _).trans (by simp)
  refine ⟨R,⟨Module.finrank ℂ V,hR⟩,?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hKt (hAK ⟨x,by simp [hx],rfl⟩))
  have hyV : y ∈ V := Submodule.subset_span hy
  calc
    ‖(A-R) x‖ = Metric.infDist (A x) V := by
      simp [R,← dist_eq_norm,Submodule.dist_starProjection_eq_infDist]
    _ ≤ dist (A x) y := Metric.infDist_le_dist_of_mem hyV
    _ ≤ ε := (Metric.mem_ball.mp hxy).le

/-- Compactness is preserved by the actual Hilbert adjoint. -/
theorem compact_adjoint_of_compact (A : H →L[ℂ] H) (hc : IsCompactOperator A) :
    IsCompactOperator A.adjoint := by
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨R,⟨n,hn⟩,hclose⟩ := compact_finiteRank_approx A hc (ε/2) (by positivity)
  refine ⟨R.adjoint,finiteRank_compact R.adjoint ⟨n,rank_adjoint_le_of_rank_le R hn⟩,?_⟩
  have hdist : dist A.adjoint R.adjoint = ‖A-R‖ := by
    rw [dist_eq_norm,← map_sub,LinearIsometryEquiv.norm_map]
  exact hdist.trans_le hclose |>.trans_lt (half_lt_self hε)

@[simp] theorem compact_adjoint_iff (A : H →L[ℂ] H) :
    IsCompactOperator A.adjoint ↔ IsCompactOperator A :=
  ⟨fun h => by simpa only [ContinuousLinearMap.adjoint_adjoint] using compact_adjoint_of_compact A.adjoint h,
    compact_adjoint_of_compact A⟩

/-- Adjoint invariance of the actual compact, positive-p, summable approximation predicate. -/
@[simp] theorem schatten_adjoint_iff (A : H →L[ℂ] H) (p : ℝ) :
    Schatten p A.adjoint ↔ Schatten p A := by
  simp only [Schatten,compact_adjoint_iff,approximationNumber_adjoint]

end HilbertAdjoints

/-! Sequence diagonals and finite truncations. Narrow map/rank arguments adapt the Apache-2.0
Tau Ceti Normed/Lp/Diagonal/Basic, ApproximationNumber/MinMax and
ApproximationNumber/FiniteDiagonal:128–147 at the recorded revision.
No antitone hypothesis is imposed on the general coefficient sequence. -/
section DiagonalOperators

/-- A genuinely bounded coefficient family defines the native coordinate multiplier on ℓ². -/
def diagonalOperator (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) : SequenceOperator :=
  lp.mapCLM 2 (fun n => ContinuousLinearMap.lsmul ℂ ℂ (w n)) hM
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℂ) (E := ℂ) (w n)).trans (hw n))

@[simp] theorem diagonalOperator_apply (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (x : SequenceL2) (n : ℕ) : diagonalOperator w M hM hw x n = w n*x n := rfl

theorem diagonalOperator_isDiagonal (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    Diagonal w (diagonalOperator w M hM hw) := by
  intro n
  apply lp.ext
  funext i
  simp only [diagonalOperator_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hin : i = n
  · subst i
    rfl
  · simp [lp.single_apply,Pi.single_eq_of_ne hin]

theorem diagonal_bounded_iff (w : ℕ → ℂ) :
    (∃ D : SequenceOperator, Diagonal w D) ↔ ∃ M : ℝ, ∀ n, ‖w n‖ ≤ M := by
  constructor
  · rintro ⟨D,hd⟩
    refine ⟨‖D‖,fun n => ?_⟩
    have h := D.le_opNorm (lp.single 2 n (1 : ℂ))
    rw [hd n,norm_smul] at h
    simpa [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h
  · rintro ⟨M,hw⟩
    have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hw 0)
    exact ⟨diagonalOperator w M hM hw,diagonalOperator_isDiagonal w M hM hw⟩

theorem diagonal_unique (w : ℕ → ℂ) (D E : SequenceOperator) (hD : Diagonal w D) (hE : Diagonal w E) : D = E := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  rw [diagonal_apply w D hD x n,diagonal_apply w E hE x n]

@[simp] theorem sequence_eval_apply (n : ℕ) (x : SequenceL2) :
    lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n x = x n := rfl

/-- Retain a finite set of the actual diagonal coordinates. -/
def diagonalTruncation (w : ℕ → ℂ) (s : Finset ℕ) : SequenceOperator :=
  ∑ i ∈ s, (w i • lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 i) ∘L
    lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i

theorem diagonalTruncation_eq_sum_single (w : ℕ → ℂ) (s : Finset ℕ) (x : SequenceL2) :
    diagonalTruncation w s x = ∑ i ∈ s, (w i*x i) • (lp.single 2 i (1 : ℂ) : SequenceL2) := by
  rw [diagonalTruncation,sum_apply]
  simp [lp.singleContinuousLinearMap_apply,← lp.single_smul,sequence_eval_apply]

@[simp] theorem diagonalTruncation_apply (w : ℕ → ℂ) (s : Finset ℕ) (x : SequenceL2) (n : ℕ) :
    diagonalTruncation w s x n = if n ∈ s then w n*x n else 0 := by
  rw [diagonalTruncation_eq_sum_single]
  change lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n (∑ i ∈ s, (w i*x i) • (lp.single 2 i (1 : ℂ) : SequenceL2)) = _
  rw [map_sum]
  simp [sequence_eval_apply,lp.single_apply,Pi.single_apply]

/-- A truncation has no more rank than retained coordinates. -/
theorem rank_diagonalTruncation_le (w : ℕ → ℂ) (s : Finset ℕ) :
    (diagonalTruncation w s).rank ≤ (s.card : Cardinal) := by
  classical
  let v : ℕ → SequenceL2 := fun i => lp.single 2 i (1 : ℂ)
  have hrange : (diagonalTruncation w s).toLinearMap.range ≤ Submodule.span ℂ (v '' (s : Set ℕ)) := by
    rintro _ ⟨x,rfl⟩
    rw [ContinuousLinearMap.coe_coe,diagonalTruncation_eq_sum_single]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  calc
    _ ≤ Module.rank ℂ (Submodule.span ℂ (v '' (s : Set ℕ))) := Submodule.rank_mono hrange
    _ ≤ (s.card : Cardinal) := by
      rw [← Finset.coe_image]
      exact (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le)

/-- Bounds on discarded coordinates control the actual operator-norm error. -/
theorem norm_diagonal_sub_truncation_le (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (s : Finset ℕ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∉ s, ‖w i‖ ≤ C) :
    ‖D-diagonalTruncation w s‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  calc
    ‖(D-diagonalTruncation w s) x‖ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      simp only [sub_apply,lp.coeFn_sub,Pi.sub_apply,
        diagonal_apply w D hd,diagonalTruncation_apply]
      by_cases hi : i ∈ s
      · simp only [hi,ite_true,sub_self,norm_zero]
        exact norm_nonneg _
      · simpa [hi,norm_mul,abs_of_nonneg hC] using
          mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg (x i))
    _ = C*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,lp.norm_toNorm]

/-- Rank-kernel coercivity is an elementary lower bound for the actual approximation infimum. -/
theorem le_approximationNumber_of_lt_rank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) {n : ℕ} {V : Submodule ℂ E} (hV : (n : Cardinal) < Module.rank ℂ V)
    {c : ℝ} (hc : ∀ x ∈ V, c*‖x‖ ≤ ‖T x‖) : c ≤ (approximationNumber T n : ℝ) := by
  rcases le_or_gt c 0 with h | h
  · exact h.trans (NNReal.coe_nonneg _)
  lift c to ℝ≥0 using h.le
  apply NNReal.coe_le_coe.mpr
  apply le_approximationNumber_iff.mpr
  intro R hR
  obtain ⟨x,hxV,hRx,hx0⟩ : ∃ x ∈ V, R x = 0 ∧ x ≠ 0 := by
    by_contra! h
    let F : V →ₗ[ℂ] R.range := R.toLinearMap.rangeRestrict.comp V.subtype
    have hi : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply h (x.val-y.val) (V.sub_mem x.property y.property)
      have hh := congrArg Subtype.val hxy
      change R x.val = R y.val at hh
      simpa only [map_sub,sub_eq_zero] using hh
    have hle := LinearMap.rank_le_of_injective F hi
    exact hV.not_ge (hle.trans hR)
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  apply NNReal.coe_le_coe.mp
  change (c : ℝ) ≤ ‖T-R‖
  apply (mul_le_mul_iff_left₀ hx).mp
  calc
    (c : ℝ)*‖x‖ ≤ ‖T x‖ := hc x hxV
    _ = ‖(T-R) x‖ := by simp [hRx]
    _ ≤ ‖T-R‖*‖x‖ := (T-R).le_opNorm x

/-- Coordinate unit vectors are linearly independent in the actual ℓ² subtype. -/
theorem sequence_units_linearIndependent : LinearIndependent ℂ (fun i : ℕ => (lp.single 2 i (1 : ℂ) : SequenceL2)) := by
  apply LinearIndependent.of_comp (lpSubmodule ℂ (fun _ : ℕ => ℂ) 2).subtype
  have hcoe : (lpSubmodule ℂ (fun _ : ℕ => ℂ) 2).subtype ∘
      (fun i : ℕ => (lp.single 2 i (1 : ℂ) : SequenceL2)) = fun i => Pi.single i (1 : ℂ) := by
    funext i
    exact lp.coeFn_single 2 i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ℕ ℂ

/-- Vectors in a finite coordinate span vanish off its generating indices. -/
theorem sequence_span_support {ι : Type*} (e : ι → ℕ) {x : SequenceL2}
    (hx : x ∈ Submodule.span ℂ (Set.range (fun j => (lp.single 2 (e j) (1 : ℂ) : SequenceL2))))
    {i : ℕ} (hi : i ∉ Set.range e) : x i = 0 := by
  have hle : Submodule.span ℂ (Set.range (fun j => (lp.single 2 (e j) (1 : ℂ) : SequenceL2))) ≤
      (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change (lp.single 2 (e j) (1 : ℂ) : SequenceL2) i = 0
    simp [lp.single_apply,Pi.single_eq_of_ne (fun h => hi ⟨j,h.symm⟩)]
  exact hle hx

/-- Removing at most n coordinates yields an approximation upper bound from the remaining values. -/
theorem approximationNumber_diagonal_le (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (n : ℕ) (s : Finset ℕ) (hs : s.card ≤ n) (C : ℝ≥0) (hc : ∀ i ∉ s, ‖w i‖ ≤ C) :
    approximationNumber D n ≤ C := by
  have hr : (diagonalTruncation w s).rank ≤ (n : Cardinal) :=
    (rank_diagonalTruncation_le w s).trans (by exact_mod_cast hs)
  apply (approximationNumber_le_nnnorm_sub D hr).trans
  exact_mod_cast norm_diagonal_sub_truncation_le w D hd s C C.property hc

/-- More than n sufficiently large diagonal entries force an approximation lower bound. -/
theorem le_approximationNumber_diagonal_of_card (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    {n : ℕ} (s : Finset ℕ) (hs : n < s.card) (c : ℝ) (hc : ∀ i ∈ s, c ≤ ‖w i‖) :
    c ≤ (approximationNumber D n : ℝ) := by
  classical
  rcases le_or_gt c 0 with h | h
  · exact h.trans (NNReal.coe_nonneg _)
  let e : s → ℕ := fun j => j.val
  let v : s → SequenceL2 := fun j => lp.single 2 (e j) (1 : ℂ)
  have hv : LinearIndependent ℂ v := sequence_units_linearIndependent.comp e Subtype.val_injective
  let V := Submodule.span ℂ (Set.range v)
  have hV : (n : Cardinal) < Module.rank ℂ V := by
    let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
    rw [← Module.finrank_eq_rank,finrank_span_eq_card hv,Fintype.card_coe]
    exact_mod_cast hs
  apply le_approximationNumber_of_lt_rank D hV
  intro x hx
  calc
    c*‖x‖ = ‖c • lp.toNorm x‖ := by simp [norm_smul,abs_of_pos h,lp.norm_toNorm]
    _ ≤ ‖D x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      by_cases hi : i ∈ s
      · simpa [diagonal_apply w D hd,norm_mul,abs_of_pos h] using
          mul_le_mul_of_nonneg_right (hc i hi) (norm_nonneg (x i))
      · have hz : x i = 0 := sequence_span_support e hx (by
          rintro ⟨j,hj⟩
          exact hi (hj ▸ j.property))
        simp [diagonal_apply w D hd,hz]

/-- Finite sorted-support diagonals have exactly their sorted coefficient approximation numbers.
Only the finite list is sorted; arbitrary zero coordinates outside it are retained. -/
theorem approximationNumber_finite_diagonal (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    {N : ℕ} (e : Fin N ↪ ℕ) (he : Antitone (fun i => ‖w (e i)‖))
    (hzero : ∀ i, i ∉ Set.range e → w i = 0) (k : Fin N) :
    approximationNumber D k = ‖w (e k)‖₊ := by
  apply le_antisymm
  · apply approximationNumber_diagonal_le w D hd k ((Finset.Iio k).map e) (by simp) ‖w (e k)‖₊
    intro i hi
    by_cases hr : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hr
      exact he (by simpa using hi)
    · simp [hzero i hr]
  · exact_mod_cast le_approximationNumber_diagonal_of_card w D hd ((Finset.Iic k).map e) (by simp)
      ‖w (e k)‖ (fun i hi => by
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
        exact he (Finset.mem_Iic.mp hj))


/-- Each finite truncation is diagonal with exactly the indicated zero extension. -/
theorem diagonalTruncation_isDiagonal (w : ℕ → ℂ) (s : Finset ℕ) :
    Diagonal (fun i => if i ∈ s then w i else 0) (diagonalTruncation w s) := by
  intro n
  apply lp.ext
  funext i
  simp only [diagonalTruncation_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hi : i = n
  · subst i
    simp [lp.single_apply]
  · simp [lp.single_apply,Pi.single_eq_of_ne hi]

/-- The exact p-power sum of a finite truncation, without hypotheses on the full sequence. -/
theorem diagonalTruncation_power_sum (w : ℕ → ℂ) (N : ℕ) (p : ℝ) (hp : 0 < p) :
    (∑' n, (approximationNumber (diagonalTruncation w (Finset.range N)) n : ℝ)^p) =
      ∑ i ∈ Finset.range N, ‖w i‖^p := by
  classical
  let D := diagonalTruncation w (Finset.range N)
  let v : ℕ → ℂ := fun i => if i ∈ Finset.range N then w i else 0
  let σ := Tuple.sort (α := OrderDual ℝ) (fun i : Fin N => ‖w i.val‖)
  let e : Fin N ↪ ℕ := ⟨fun i => (σ i).val,Fin.val_injective.comp σ.injective⟩
  have he : ∀ i : Fin N, v (e i) = w (σ i).val := by
    intro i
    simp [v,e,(σ i).isLt]
  have hmono : Antitone (fun i => ‖v (e i)‖) := by
    intro i j hij
    simp only [he]
    exact Tuple.monotone_sort (α := OrderDual ℝ) (fun i : Fin N => ‖w i.val‖) hij
  have hz : ∀ i, i ∉ Set.range e → v i = 0 := by
    intro i hi
    have hn : ¬i < N := by
      intro hin
      apply hi
      refine ⟨σ.symm ⟨i,hin⟩,?_⟩
      simp [e]
    simp [v,hn]
  have ha (i : Fin N) : approximationNumber D i = ‖w (σ i).val‖₊ := by
    simpa only [he] using approximationNumber_finite_diagonal v D
      (diagonalTruncation_isDiagonal w (Finset.range N)) e hmono hz i
  calc
    _ = ∑ n ∈ Finset.range N, (approximationNumber D n : ℝ)^p := by
      apply tsum_eq_sum
      intro n hn
      rw [approximationNumber_eq_zero_of_rank_le D n
        ((rank_diagonalTruncation_le w (Finset.range N)).trans (by
          simp only [Finset.card_range]
          exact_mod_cast Nat.le_of_not_gt (by simpa using hn))),NNReal.coe_zero,Real.zero_rpow hp.ne']
    _ = ∑ i : Fin N, (approximationNumber D i : ℝ)^p := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin N, ‖w (σ i).val‖^p := by simp_rw [ha,coe_nnnorm]
    _ = ∑ i : Fin N, ‖w i.val‖^p := Equiv.sum_comp σ (fun i : Fin N => ‖w i.val‖^p)
    _ = ∑ i ∈ Finset.range N, ‖w i‖^p := Fin.sum_univ_eq_sum_range (fun i => ‖w i‖^p) N


/-- Approximation numbers vary by at most the operator-norm perturbation. -/
theorem abs_approximationNumber_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (A B : E →L[ℂ] F) (n : ℕ) :
    |(approximationNumber A n : ℝ)-(approximationNumber B n : ℝ)| ≤ ‖A-B‖ := by
  have h (A B : E →L[ℂ] F) :
      approximationNumber A n ≤ approximationNumber B n + ‖A-B‖₊ := by
    have hh := (approximationNumber_add B (A-B) n 0).trans
      (add_le_add le_rfl (approximationNumber_le_nnnorm (A-B) 0))
    simpa only [add_sub_cancel,add_zero] using hh
  have hab : (approximationNumber A n : ℝ) ≤ (approximationNumber B n : ℝ)+‖A-B‖ := by
    exact_mod_cast h A B
  have hba : (approximationNumber B n : ℝ) ≤ (approximationNumber A n : ℝ)+‖A-B‖ := by
    simpa only [norm_sub_rev] using (show (approximationNumber B n : ℝ) ≤
      (approximationNumber A n : ℝ)+‖B-A‖ by exact_mod_cast h B A)
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem continuous_approximationNumber {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (n : ℕ) :
    Continuous (fun D : E →L[ℂ] F => (approximationNumber D n : ℝ)) := by
  apply (show LipschitzWith 1 (fun D : E →L[ℂ] F => (approximationNumber D n : ℝ)) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs] using abs_approximationNumber_sub_le A B n

theorem norm_diagonalTruncation_le (w : ℕ → ℂ) (s : Finset ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ C) : ‖diagonalTruncation w s‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  calc
    ‖diagonalTruncation w s x‖ ≤ ‖C • lp.toNorm x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      by_cases hi : i ∈ s
      · simpa [diagonalTruncation_apply,hi,norm_mul,abs_of_nonneg hC] using
          mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg (x i))
      · simp only [diagonalTruncation_apply,hi,ite_false,norm_zero]
        exact norm_nonneg _
    _ = C*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,lp.norm_toNorm]

/-- Coordinate compression cannot increase any approximation number. -/
theorem approximationNumber_diagonalTruncation_le (w : ℕ → ℂ) (D : SequenceOperator)
    (hd : Diagonal w D) (s : Finset ℕ) (n : ℕ) :
    approximationNumber (diagonalTruncation w s) n ≤ approximationNumber D n := by
  let P := diagonalTruncation (fun _ => (1 : ℂ)) s
  have hP : ‖P‖₊ ≤ 1 := by
    exact_mod_cast norm_diagonalTruncation_le (fun _ => (1 : ℂ)) s 1 (by norm_num) (by simp)
  have heq : diagonalTruncation w s = P ∘L D := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp only [ContinuousLinearMap.comp_apply,diagonalTruncation_apply,diagonal_apply w D hd,P]
    split_ifs <;> simp
  rw [heq]
  exact (approximationNumber_comp_left P D n).trans (by simpa using mul_le_mul_of_nonneg_right hP (by positivity))

/-- A null diagonal is the operator-norm limit of its literal finite coordinate truncations. -/
theorem diagonalTruncation_tendsto (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun N => diagonalTruncation w (Finset.range N)) atTop (𝓝 D) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hw (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  apply (norm_diagonal_sub_truncation_le w D hd (Finset.range n) (ε/2) (by positivity) ?_).trans_lt
    (half_lt_self hε)
  intro i hi
  exact (show ‖w i‖ < ε/2 by simpa using hN i (hn.trans (Nat.le_of_not_gt (by simpa using hi)))).le

theorem compact_diagonal_of_tendsto (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (hw : Tendsto w atTop (𝓝 0)) : IsCompactOperator D := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto (diagonalTruncation_tendsto w D hd hw)
  exact Eventually.of_forall fun N => finiteRank_compact _ ⟨N,by simpa using rank_diagonalTruncation_le w (Finset.range N)⟩


/-- Compactness forces a diagonal coefficient sequence to vanish, using only finite rank tests. -/
theorem tendsto_diagonal_of_compact (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (hD : IsCompactOperator D) : Tendsto w atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf : Set.Finite {i | ε ≤ ‖w i‖} := by
    by_contra hi
    obtain ⟨R,⟨m,hm⟩,hclose⟩ := compact_finiteRank_approx D hD (ε/2) (by positivity)
    obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (m+1)
    have hlo := le_approximationNumber_diagonal_of_card w D hd (n := m) s (by omega) ε (fun i hi => hs hi)
    have hup : (approximationNumber D m : ℝ) ≤ ‖D-R‖ := by
      exact_mod_cast approximationNumber_le_nnnorm_sub D hm
    linarith
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [hf.eventually_cofinite_notMem] with i hi
  simpa only [dist_zero_right] using lt_of_not_ge hi

theorem diagonal_compact_iff (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D) :
    IsCompactOperator D ↔ Tendsto w atTop (𝓝 0) :=
  ⟨tendsto_diagonal_of_compact w D hd,compact_diagonal_of_tendsto w D hd⟩


theorem tendsto_zero_of_summableValues (w : ℕ → ℂ) (p : ℝ) (hp : 0 < p)
    (hw : summableValues p w) : Tendsto w atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := Metric.tendsto_nhds.mp hw.tendsto_atTop_zero (ε^p) (Real.rpow_pos_of_pos hε p)
  filter_upwards [ht] with n hn
  have hh : ‖w n‖^p < ε^p := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (w n)) p)] using hn
  simpa only [dist_zero_right] using (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hp).mp hh


/-- Finite coefficient sums are bounded by the full approximation-number power sum. -/
theorem diagonal_values_partial_le (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hp : 0 < p) (hD : Summable (fun n => (approximationNumber D n : ℝ)^p)) (N : ℕ) :
    ∑ i ∈ Finset.range N, ‖w i‖^p ≤ ∑' n, (approximationNumber D n : ℝ)^p := by
  rw [← diagonalTruncation_power_sum w N p hp]
  apply Summable.tsum_le_tsum _
    (finiteRankSchatten _ ⟨N,by simpa using rank_diagonalTruncation_le w (Finset.range N)⟩ p hp).2.2 hD
  intro n
  exact Real.rpow_le_rpow (NNReal.coe_nonneg _)
    (by exact_mod_cast approximationNumber_diagonalTruncation_le w D hd (Finset.range N) n) hp.le

/-- Finite spectral sums of the norm limit are bounded by summable coefficient powers. -/
theorem diagonal_spectral_partial_le (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hp : 0 < p) (hw : summableValues p w) (M : ℕ) :
    ∑ i ∈ Finset.range M, (approximationNumber D i : ℝ)^p ≤ ∑' n, ‖w n‖^p := by
  have hlim := diagonalTruncation_tendsto w D hd (tendsto_zero_of_summableValues w p hp hw)
  have ht : Tendsto (fun N => ∑ i ∈ Finset.range M,
      (approximationNumber (diagonalTruncation w (Finset.range N)) i : ℝ)^p)
      atTop (𝓝 (∑ i ∈ Finset.range M, (approximationNumber D i : ℝ)^p)) := by
    apply tendsto_finsetSum
    intro i hi
    exact ((Real.continuous_rpow_const hp.le).comp (continuous_approximationNumber i)).continuousAt.tendsto.comp hlim
  apply le_of_tendsto' ht
  intro N
  calc
    _ ≤ ∑' i, (approximationNumber (diagonalTruncation w (Finset.range N)) i : ℝ)^p :=
      Summable.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
        (finiteRankSchatten _ ⟨N,by simpa using rank_diagonalTruncation_le w (Finset.range N)⟩ p hp).2.2
    _ = ∑ i ∈ Finset.range N, ‖w i‖^p := diagonalTruncation_power_sum w N p hp
    _ ≤ ∑' i, ‖w i‖^p := Summable.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hw

/-- Arbitrary diagonals have summable approximation powers exactly when their coefficients do. -/
theorem diagonal_summable_iff (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hp : 0 < p) :
    Summable (fun n => (approximationNumber D n : ℝ)^p) ↔ summableValues p w := by
  constructor
  · intro hD
    exact summable_of_sum_range_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (diagonal_values_partial_le w D hd p hp hD)
  · intro hw
    exact summable_of_sum_range_le (fun _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (diagonal_spectral_partial_le w D hd p hp hw)

/-- The exact power-sum identity includes every positive p and arbitrary coefficient order. -/
theorem diagonal_power_sum_eq (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hp : 0 < p) (hw : summableValues p w) :
    (∑' n, (approximationNumber D n : ℝ)^p) = ∑' n, ‖w n‖^p := by
  apply le_antisymm
  · exact Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (NNReal.coe_nonneg _) _)
      (diagonal_spectral_partial_le w D hd p hp hw)
  · exact Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (diagonal_values_partial_le w D hd p hp ((diagonal_summable_iff w D hd p hp).mpr hw))

theorem diagonal_schatten_iff (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hp : 0 < p) : Schatten p D ↔ summableValues p w := by
  constructor
  · intro hD
    exact (diagonal_summable_iff w D hd p hp).mp hD.2.2
  · intro hw
    exact ⟨hp,compact_diagonal_of_tendsto w D hd (tendsto_zero_of_summableValues w p hp hw),
      (diagonal_summable_iff w D hd p hp).mpr hw⟩

theorem diagonal_schattenNorm (w : ℕ → ℂ) (D : SequenceOperator) (hd : Diagonal w D)
    (p : ℝ) (hD : Schatten p D) : schattenNorm p D = valueNorm p w := by
  unfold schattenNorm valueNorm
  rw [diagonal_power_sum_eq w D hd p hD.1 ((diagonal_schatten_iff w D hd p hD.1).mp hD)]

/-- The complete native arbitrary-diagonal interface, with no external mathematical assumptions. -/
theorem diagonalLaws : DiagonalLaws :=
  ⟨diagonal_bounded_iff,diagonal_compact_iff,diagonal_schatten_iff,diagonal_schattenNorm⟩

end DiagonalOperators

section FiniteBlocks
variable {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]

@[simp] theorem finiteSingle_apply (j : Fin m) (x : H j) (i : Fin m) :
    finiteSingle H j x i = Pi.single j x i := rfl

@[simp] theorem finiteDiagonal_apply (T : (j : Fin m) → H j →L[ℂ] H j) (x : PiLp 2 H) (i : Fin m) :
    finiteDiagonal T x i = T i (x i) := rfl

theorem finiteSingle_sum (x : PiLp 2 H) : (∑ j, finiteSingle H j (x j)) = x := by
  apply (PiLp.continuousLinearEquiv 2 ℂ H).injective
  rw [map_sum]
  change (∑ j, Pi.single j (x j)) = x.ofLp
  exact LinearMap.sum_single_apply H x.ofLp

variable {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Coordinate resolutions sum to the identity, including the empty coordinate family. -/
theorem coordinateResolution_sum (W : PiLp 2 H ≃L[ℂ] K) :
    (∑ j, coordinateResolution W j) = ContinuousLinearMap.id ℂ K := by
  ext x
  simp only [sum_apply, coordinateResolution, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, PiLp.proj_apply]
  rw [← map_sum, finiteSingle_sum, W.apply_symm_apply]

theorem coordinateResolution_idempotent (W : PiLp 2 H ≃L[ℂ] K) (j : Fin m) :
    coordinateResolution W j ∘L coordinateResolution W j = coordinateResolution W j := by
  ext x
  simp [coordinateResolution]

theorem coordinateResolution_disjoint (W : PiLp 2 H ≃L[ℂ] K) (i j : Fin m) (hij : i ≠ j) :
    coordinateResolution W i ∘L coordinateResolution W j = 0 := by
  ext x
  simp [coordinateResolution, Pi.single_eq_of_ne hij]

theorem coordinateResolution_range (W : PiLp 2 H ≃L[ℂ] K) (j : Fin m) :
    (coordinateResolution W j).toLinearMap.range =
      (W.toContinuousLinearMap ∘L finiteSingle H j).toLinearMap.range := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(W.symm x) j,rfl⟩
  · rintro ⟨x,rfl⟩
    refine ⟨W (finiteSingle H j x),?_⟩
    simp [coordinateResolution]

/-- A finite block diagonal is the finite sum of its coordinate inclusions/compressions. -/
theorem finiteDiagonal_eq_sum (T : (j : Fin m) → H j →L[ℂ] H j) :
    finiteDiagonal T = ∑ j, finiteSingle H j ∘L T j ∘L PiLp.proj 2 H j := by
  apply ContinuousLinearMap.ext
  intro x
  rw [sum_apply]
  simpa only [finiteDiagonal_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    using (finiteSingle_sum (finiteDiagonal T x)).symm

@[simp] theorem finiteDiagonal_compression (T : (j : Fin m) → H j →L[ℂ] H j) (j : Fin m) :
    PiLp.proj 2 H j ∘L finiteDiagonal T ∘L finiteSingle H j = T j := by
  ext x
  simp

/-- Finite block membership uses bounded coordinate maps and finite sums, for all p>0. -/
theorem schatten_finiteDiagonal_iff (T : (j : Fin m) → H j →L[ℂ] H j) (p : ℝ) (hp : 0 < p) :
    Schatten p (finiteDiagonal T) ↔ ∀ j, Schatten p (T j) := by
  constructor
  · intro h j
    simpa only [finiteDiagonal_compression] using schatten_comp h (PiLp.proj 2 H j) (finiteSingle H j)
  · intro h
    rw [finiteDiagonal_eq_sum]
    apply schatten_sum Finset.univ _ p hp
    intro j _
    exact schatten_comp (h j) (finiteSingle H j) (PiLp.proj 2 H j)

end FiniteBlocks

/-- The generic adjoint interface is closed without spectral or literature assumptions. -/
theorem adjointLaws : AdjointLaws where
  compact := compact_adjoint_iff
  schatten := schatten_adjoint_iff
  approximation := approximationNumber_adjoint

/-- The generic coordinate-algebra interface is closed with its actual native maps. -/
theorem coordinateResolutionLaws : CoordinateResolutionLaws where
  sum := coordinateResolution_sum
  idempotent := coordinateResolution_idempotent
  disjoint := coordinateResolution_disjoint
  range := coordinateResolution_range

/-- Qualitative finite Hilbert block membership, including the empty family and p<1. -/
theorem finiteBlockSchatten : FiniteBlockSchattenObligation := by
  intro m H _ _ _ K _ _ _ W A T h p hp
  have heq : A = W.toContinuousLinearMap ∘L finiteDiagonal T ∘L W.symm.toContinuousLinearMap := by
    ext x
    have hx := h (W.symm x)
    change A x = W (WithLp.toLp 2 (fun j => T j ((W.symm x) j)))
    simpa only [W.apply_symm_apply] using hx
  have hback : finiteDiagonal T = W.symm.toContinuousLinearMap ∘L A ∘L W.toContinuousLinearMap := by
    rw [heq]
    ext x
    simp
  constructor
  · intro hs
    apply (schatten_finiteDiagonal_iff T p hp).mp
    rw [hback]
    exact schatten_comp hs W.symm.toContinuousLinearMap W.toContinuousLinearMap
  · intro hs
    rw [heq]
    exact schatten_comp ((schatten_finiteDiagonal_iff T p hp).mpr hs)
      W.toContinuousLinearMap W.symm.toContinuousLinearMap

/-- Unitary conjugation respects the ordinary algebra and the Hilbert adjoint. -/
theorem unitaryAlgebraLaws : UnitaryAlgebraLaws where
  add U A B := by
    ext x
    simp [unitaryConjugate]
  sub U A B := by
    ext x
    simp [unitaryConjugate]
  scalar U c := by
    ext x
    simp [unitaryConjugate]
  adjoint U A := by
    change U.conjStarAlgEquiv A.adjoint = (U.conjStarAlgEquiv A).adjoint
    simpa only [ContinuousLinearMap.star_eq_adjoint] using map_star U.conjStarAlgEquiv A

section IsometricTransport
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem approximationNumber_comp_contraction (L : F →L[ℂ] G) (hL : ‖L‖ ≤ 1)
    (A : E →L[ℂ] F) (n : ℕ) : approximationNumber (L ∘L A) n ≤ approximationNumber A n := by
  have h : ‖L‖₊ ≤ 1 := by exact_mod_cast hL
  exact (approximationNumber_comp_left L A n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h (by positivity))

/-- Contractive inverse-on-range maps preserve the actual approximation infima exactly. -/
theorem approximationNumber_comp_retract (L : F →L[ℂ] G) (R : G →L[ℂ] F)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hRL : ∀ x, R (L x) = x) (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (L ∘L A) n = approximationNumber A n := by
  apply le_antisymm (approximationNumber_comp_contraction L hL A n)
  have he : R ∘L (L ∘L A) = A := by ext x; exact hRL (A x)
  have h := approximationNumber_comp_contraction R hR (L ∘L A) n
  rw [he] at h
  exact h

theorem compact_comp_retract_iff (L : F →L[ℂ] G) (R : G →L[ℂ] F)
    (hRL : ∀ x, R (L x) = x) (A : E →L[ℂ] F) : IsCompactOperator (L ∘L A) ↔ IsCompactOperator A := by
  constructor
  · intro h
    have he : R ∘L (L ∘L A) = A := by ext x; exact hRL (A x)
    rw [← he]
    exact h.clm_comp R
  · exact fun h => h.clm_comp L

theorem norm_isometry_clm_le_one (U : F →ₗᵢ[ℂ] G) : ‖U.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖U x‖ ≤ 1*‖x‖
  rw [U.norm_map,one_mul]

theorem approximationNumber_unitary_comp (U : F ≃ₗᵢ[ℂ] G) (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A) n = approximationNumber A n :=
  approximationNumber_comp_retract U.toContinuousLinearEquiv.toContinuousLinearMap
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap (norm_isometry_clm_le_one U.toLinearIsometry)
    (norm_isometry_clm_le_one U.symm.toLinearIsometry) U.symm_apply_apply A n

theorem schatten_unitary_comp_iff (U : F ≃ₗᵢ[ℂ] G) (A : E →L[ℂ] F) (p : ℝ) :
    Schatten p (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A) ↔ Schatten p A := by
  unfold Schatten
  simp only [approximationNumber_unitary_comp,
    compact_comp_retract_iff U.toContinuousLinearEquiv.toContinuousLinearMap
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap U.symm_apply_apply]

end IsometricTransport

section ModelConjugation

/-- The first circle character has its literal a.e. boundary value. -/
theorem coordinate_ae : coordinate =ᵐ[circleMeasure] fourier (T := 1) 1 := mode_ae 1

theorem coordinate_unimodular : ∀ᵐ t ∂circleMeasure, ‖coordinate t‖ = 1 := by
  filter_upwards [coordinate_ae] with t ht
  simp [ht,fourier_apply]

/-- The boundary conjugation is the actual u·bar(z)·bar(f). -/
theorem conjugation_ae (u : BoundaryLInf) (f : BoundaryL2) :
    conjugation u f =ᵐ[circleMeasure] fun t => u t*conj (fourier (T := 1) 1 t)*conj (f t) := by
  filter_upwards [multiply_ae u (multiply (star coordinate) (star f)),
    multiply_ae (star coordinate) (star f),Lp.coeFn_star coordinate,Lp.coeFn_star f,coordinate_ae]
    with t ho hi hc hf hz
  change (star coordinate) t = star (coordinate t) at hc
  change (star f) t = star (f t) at hf
  change multiply u (multiply (star coordinate) (star f)) t = _
  rw [ho,hi,hc,hf,hz]
  simp only [Complex.star_def,mul_assoc]

/-- Unimodularity makes the genuine boundary conjugation involutive. -/
theorem conjugation_involutive (u : BoundaryLInf) (hu : IsInner u) (f : BoundaryL2) :
    conjugation u (conjugation u f) = f := by
  apply Lp.ext
  filter_upwards [conjugation_ae u (conjugation u f),conjugation_ae u f,hu.2] with t ho hi hut
  have huu : conj (u t)*u t = 1 := by simp [Complex.conj_mul',hut]
  have hzz : conj (fourier (T := 1) 1 t)*fourier (T := 1) 1 t = 1 := by
    simp [Complex.conj_mul',fourier_apply]
  rw [ho,hi]
  simp only [map_mul,Complex.conj_conj]
  calc
    _ = (conj (u t)*u t)*(conj (fourier (T := 1) 1 t)*fourier (T := 1) 1 t)*f t := by ring
    _ = f t := by rw [huu,hzz,one_mul,one_mul]

theorem norm_conjugation (u : BoundaryLInf) (hu : IsInner u) (f : BoundaryL2) :
    ‖conjugation u f‖ = ‖f‖ := by
  have hn : ∀ᵐ t ∂circleMeasure, ‖conjugation u f t‖ = ‖f t‖ := by
    filter_upwards [conjugation_ae u f,hu.2] with t ht hut
    simp only [ht,norm_mul,Complex.norm_conj,hut,one_mul,fourier_apply,Circle.norm_coe]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.ge)))

theorem bounded_conjugation (u : BoundaryLInf) (f : BoundaryL2) (hf : IsBounded f) :
    IsBounded (conjugation u f) := by
  apply bounded_multiply
  apply bounded_multiply
  exact hf.star.ae_eq (Lp.coeFn_star f).symm

/-- Conjugation's Fourier coefficient is the precise model-space orthogonality pairing. -/
theorem fourierCoeff_conjugation (u : BoundaryLInf) (f : BoundaryL2) (n : ℤ) :
    fourierCoeff (conjugation u f) n = inner ℂ f (multiply u (fourierBasis (T := 1) (-n-1))) := by
  rw [fourierCoeff,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [conjugation_ae u f,multiply_ae u (fourierBasis (T := 1) (-n-1)),fourierBasis_ae (-n-1)]
    with t hc hm hb
  simp only [hc,hm,hb,RCLike.inner_apply,smul_eq_mul]
  rw [show (-n-1 : ℤ) = -n+(-1) by ring,fourier_add]
  simp only [fourier_neg]
  ring

/-- The actual boundary conjugation preserves the complete native model space. -/
theorem conjugation_mem_model (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    conjugation u f.val ∈ model u := by
  refine ⟨(mem_hardy_iff _).mpr ?_,?_⟩
  · intro n hn
    obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n-1 by omega)
    rw [fourierCoeff_conjugation,hk]
    exact (Submodule.mem_orthogonal' _ _).mp f.property.2 _ (Submodule.subset_span ⟨k,rfl⟩)
  · apply (Submodule.mem_orthogonal' _ _).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k,rfl⟩ := hy
      have he := fourierCoeff_conjugation u (conjugation u f.val) (-(k : ℤ)-1)
      rw [conjugation_involutive u hu] at he
      have hidx : -(-(k : ℤ)-1)-1 = (k : ℤ) := by ring
      rw [hidx] at he
      exact he.symm.trans ((mem_hardy_iff _).mp f.property.1 _ (by omega))
    | zero => simp
    | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
    | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]


/-- Explicit native L² star laws; Lp supplies a star operation but not these bundled instances. -/
theorem boundary_star_add (f g : BoundaryL2) : star (f+g) = star f+star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f+g),Lp.coeFn_add f g,Lp.coeFn_add (star f) (star g),
    Lp.coeFn_star f,Lp.coeFn_star g] with t hfg ha hs hf hg
  change (star (f+g)) t = star ((f+g) t) at hfg
  change (star f) t = star (f t) at hf
  change (star g) t = star (g t) at hg
  rw [hfg,ha,hs]
  simp only [Pi.add_apply,hf,hg,star_add]

theorem boundary_star_smul (c : ℂ) (f : BoundaryL2) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f),Lp.coeFn_smul c f,Lp.coeFn_smul (star c) (star f),Lp.coeFn_star f]
    with t hcs hc hs hf
  change (star (c • f)) t = star ((c • f) t) at hcs
  change (star f) t = star (f t) at hf
  rw [hcs,hc,hs]
  simp only [Pi.smul_apply,hf,star_smul]

theorem boundary_norm_star (f : BoundaryL2) : ‖star f‖ = ‖f‖ := by
  have hn : ∀ᵐ t ∂circleMeasure, ‖star f t‖ = ‖f t‖ := by
    filter_upwards [Lp.coeFn_star f] with t ht
    change (star f) t = star (f t) at ht
    rw [ht,norm_star]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (hn.mono (fun _ h => h.ge)))

/-- Literal boundary complex conjugation as a semilinear isometric equivalence. -/
def boundaryStar : BoundaryL2 ≃ₗᵢ⋆[ℂ] BoundaryL2 where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := boundary_star_add
  map_smul' := boundary_star_smul
  norm_map' := boundary_norm_star

/-- The closed span definition of the conjugate model has its literal conjugate meaning. -/
theorem star_mem_model_of_conjugateModel (u : BoundaryLInf) (f : ConjugateModel u) :
    star f.val ∈ model u := by
  let V : Submodule ℂ BoundaryL2 := {
    carrier := {g | star g ∈ model u}
    zero_mem' := by
      change boundaryStar (0 : BoundaryL2) ∈ model u
      rw [map_zero]
      exact (model u).zero_mem
    add_mem' := by
      intro g h hg hh
      change star (g+h) ∈ model u
      rw [boundary_star_add]
      exact (model u).add_mem hg hh
    smul_mem' := by
      intro c g hg
      change star (c • g) ∈ model u
      rw [boundary_star_smul]
      exact (model u).smul_mem (star c) hg }
  have hs : Submodule.span ℂ (star '' (model u : Set BoundaryL2)) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,rfl⟩
    change star (star g) ∈ model u
    rw [star_star]
    exact hg
  have hclosed : IsClosed (V : Set BoundaryL2) :=
    ((Submodule.isClosed_topologicalClosure _).inter (Submodule.isClosed_orthogonal _)).preimage boundaryStar.continuous
  exact (Submodule.topologicalClosure_minimal _ hs hclosed) f.property

theorem star_mem_conjugateModel (u : BoundaryLInf) (f : Model u) : star f.val ∈ conjugateModel u :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f.val,f.property,rfl⟩)

/-- Multiplication u·bar(z) on the conjugate model agrees with model conjugation after star. -/
theorem multiply_conjugation_star (u : BoundaryLInf) (f : BoundaryL2) :
    multiply u (multiply (star coordinate) f) = conjugation u (star f) := by
  simp only [conjugation,star_star]

/-- The actual linear isometry U=M_(u·bar(z)) from the conjugate model to K_u. -/
def conjugateModelIsometry (u : BoundaryLInf) (hu : IsInner u) : ConjugateModel u →ₗᵢ[ℂ] Model u where
  toLinearMap := LinearMap.codRestrict (model u)
    (((multiply u).toLinearMap.comp (multiply (star coordinate)).toLinearMap).comp (conjugateModel u).subtype)
    (fun f => by
      rw [LinearMap.comp_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.coe_coe,
        multiply_conjugation_star]
      exact conjugation_mem_model u hu ⟨star f.val,star_mem_model_of_conjugateModel u f⟩)
  norm_map' f := by
    change ‖multiply u (multiply (star coordinate) f.val)‖ = ‖f.val‖
    rw [multiply_conjugation_star,norm_conjugation u hu,boundary_norm_star]

@[simp] theorem conjugateModelIsometry_apply (u : BoundaryLInf) (hu : IsInner u) (f : ConjugateModel u) :
    (conjugateModelIsometry u hu f).val = multiply u (multiply (star coordinate) f.val) := rfl

/-- The paper's unitary, constructed by a real surjectivity proof rather than postulated. -/
def conjugateModelUnitary (u : BoundaryLInf) (hu : IsInner u) : ConjugateModel u ≃ₗᵢ[ℂ] Model u :=
  LinearIsometryEquiv.ofSurjective (conjugateModelIsometry u hu) (by
    intro f
    let Cf : Model u := ⟨conjugation u f.val,conjugation_mem_model u hu f⟩
    refine ⟨⟨star Cf.val,star_mem_conjugateModel u Cf⟩,?_⟩
    apply Subtype.ext
    change multiply u (multiply (star coordinate) (star (conjugation u f.val))) = f.val
    rw [multiply_conjugation_star,star_star,conjugation_involutive u hu])

@[simp] theorem conjugateModelUnitary_apply (u : BoundaryLInf) (hu : IsInner u) (f : ConjugateModel u) :
    (conjugateModelUnitary u hu f).val = multiply u (multiply (star coordinate) f.val) := rfl

theorem conjugateModelUnitary_symm_apply (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    ((conjugateModelUnitary u hu).symm f).val = star (conjugation u f.val) := by
  let Cf : Model u := ⟨conjugation u f.val,conjugation_mem_model u hu f⟩
  have h : conjugateModelUnitary u hu ⟨star Cf.val,star_mem_conjugateModel u Cf⟩ = f := by
    apply Subtype.ext
    change multiply u (multiply (star coordinate) (star (conjugation u f.val))) = f.val
    rw [multiply_conjugation_star,star_star,conjugation_involutive u hu]
  exact congrArg Subtype.val ((conjugateModelUnitary u hu).symm_apply_eq.mpr h.symm)


/-- Hölder L∞ multiplication has the literal product representative. -/
theorem multiplyInf_ae (a b : BoundaryLInf) :
    multiplyInf a b =ᵐ[circleMeasure] fun t => a t*b t :=
  (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder a b

theorem multiply_assoc (a b : BoundaryLInf) (f : BoundaryL2) :
    multiply a (multiply b f) = multiply (multiplyInf a b) f := by
  apply Lp.ext
  filter_upwards [multiply_ae a (multiply b f),multiply_ae b f,multiply_ae (multiplyInf a b) f,
    multiplyInf_ae a b] with t ha hb hab hi
  rw [ha,hb,hab,hi,mul_assoc]

theorem multiply_comm (a b : BoundaryLInf) (f : BoundaryL2) :
    multiply a (multiply b f) = multiply b (multiply a f) := by
  apply Lp.ext
  filter_upwards [multiply_ae a (multiply b f),multiply_ae b f,multiply_ae b (multiply a f),multiply_ae a f]
    with t hab hb hba ha
  rw [hab,hb,hba,ha,mul_left_comm]

theorem multiply_star (a : BoundaryLInf) (f : BoundaryL2) :
    star (multiply a f) = multiply (star a) (star f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (multiply a f),multiply_ae a f,multiply_ae (star a) (star f),
    Lp.coeFn_star a,Lp.coeFn_star f] with t hs hm hsm ha hf
  change (star (multiply a f)) t = star (multiply a f t) at hs
  change (star a) t = star (a t) at ha
  change (star f) t = star (f t) at hf
  rw [hs,hm,hsm,ha,hf,star_mul,mul_comm]

theorem multiply_star_cancel (a : BoundaryLInf) (ha : ∀ᵐ t ∂circleMeasure, ‖a t‖ = 1) (f : BoundaryL2) :
    multiply (star a) (multiply a f) = f := by
  apply Lp.ext
  filter_upwards [multiply_ae (star a) (multiply a f),multiply_ae a f,Lp.coeFn_star a,ha] with t ho hi hs hn
  change (star a) t = star (a t) at hs
  rw [ho,hi,hs,← mul_assoc]
  have hh : star (a t)*a t = 1 := by simp [Complex.conj_mul',hn]
  rw [hh,one_mul]

theorem multiply_cancel_star (a : BoundaryLInf) (ha : ∀ᵐ t ∂circleMeasure, ‖a t‖ = 1) (f : BoundaryL2) :
    multiply a (multiply (star a) f) = f := by
  rw [multiply_comm]
  exact multiply_star_cancel a ha f

/-- Both directions of the literal U multiplier preserve the bounded core. -/
theorem bounded_conjugateModelUnitary (u : BoundaryLInf) (hu : IsInner u) (f : ConjugateModel u)
    (hf : IsBounded f.val) : IsBounded (conjugateModelUnitary u hu f).val := by
  rw [conjugateModelUnitary_apply]
  exact bounded_multiply _ _ (bounded_multiply _ _ hf)

theorem bounded_conjugateModelUnitary_symm (u : BoundaryLInf) (hu : IsInner u) (f : Model u)
    (hf : IsBounded f.val) : IsBounded ((conjugateModelUnitary u hu).symm f).val := by
  rw [conjugateModelUnitary_symm_apply]
  exact (bounded_conjugation u f.val hf).star.ae_eq (Lp.coeFn_star _).symm

/-- The exact TTO/THO integral pairing identity for arbitrary L² symbols. -/
theorem coreForm_unitary (u : BoundaryLInf) (hu : IsInner u) (σ f : BoundaryL2) (g : ConjugateModel u) :
    coreForm (star (conjugation u σ)) f g.val = coreForm σ f (conjugateModelUnitary u hu g).val := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (conjugation u σ),conjugation_ae u σ,
    multiply_ae u (multiply (star coordinate) g.val),multiply_ae (star coordinate) g.val,
    Lp.coeFn_star coordinate,coordinate_ae] with t hs hc ho hi hz he
  change (star (conjugation u σ)) t = star (conjugation u σ t) at hs
  change (star coordinate) t = star (coordinate t) at hz
  change (star (conjugation u σ)) t*f t*conj (g.val t) =
    σ t*f t*conj (multiply u (multiply (star coordinate) g.val) t)
  rw [hs,hc,ho,hi,hz,he]
  simp only [Complex.star_def,map_mul,Complex.conj_conj]
  ring

/-- U transfers actual bounded TTO core forms to actual THO core forms, and conversely. -/
theorem representsTTO_iff_THO (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2)
    (A : Model u →L[ℂ] Model u) :
    RepresentsTTO u σ A ↔ RepresentsTHO u (star (conjugation u σ))
      ((conjugateModelUnitary u hu).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A) := by
  let U := conjugateModelUnitary u hu
  constructor
  · intro hA f g hf hg
    have hi : inner ℂ g ((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A) f) =
        inner ℂ (U g) (A f) := by
      change inner ℂ g (U.symm (A f)) = inner ℂ (U g) (A f)
      have hh := U.inner_map_map g (U.symm (A f))
      rw [U.apply_symm_apply] at hh
      exact hh.symm
    rw [hi,hA f (U g) hf (bounded_conjugateModelUnitary u hu g hg)]
    exact (coreForm_unitary u hu σ f.val g).symm
  · intro hB f g hf hg
    have h := hB f (U.symm g) hf (bounded_conjugateModelUnitary_symm u hu g hg)
    have hi : inner ℂ (U.symm g) ((U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A) f) =
        inner ℂ g (A f) := by
      exact U.symm.inner_map_map g (A f)
    rw [hi,coreForm_unitary u hu σ f.val (U.symm g)] at h
    simpa only [U,LinearIsometryEquiv.apply_symm_apply] using h

end ModelConjugation

section CanonicalModel

/-- The orthogonal complement of the literal Hardy space has zero nonnegative spectrum. -/
theorem mem_hardy_orthogonal_iff (f : BoundaryL2) :
    f ∈ hardy.orthogonal ↔ ∀ n : ℕ, fourierCoeff f (n : ℤ) = 0 := by
  constructor
  · intro hf n
    have h := (Submodule.mem_orthogonal _ _).mp hf _ (fourierBasis_mem_hardy n)
    simpa only [← HilbertBasis.repr_apply_apply,fourierBasis_repr] using h
  · intro hf
    let L := innerSL ℂ f
    have hle : hardy ≤ L.ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro _ ⟨n,rfl⟩
        change inner ℂ f (fourierBasis (T := 1) (n : ℤ)) = 0
        apply inner_eq_zero_symm.mp
        simpa only [← HilbertBasis.repr_apply_apply,fourierBasis_repr] using hf n
      · exact L.isClosed_ker
    exact (Submodule.mem_orthogonal' _ _).mpr (fun g hg => hle hg)

/-- Multiplication by bar(u) converts model orthogonality into Fourier coefficients. -/
theorem fourierCoeff_multiply_star (u : BoundaryLInf) (f : BoundaryL2) (n : ℤ) :
    fourierCoeff (multiply (star u) f) n = inner ℂ (multiply u (fourierBasis (T := 1) n)) f := by
  rw [fourierCoeff,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae (star u) f,Lp.coeFn_star u,multiply_ae u (fourierBasis (T := 1) n),fourierBasis_ae n]
    with t hs hu hm he
  change (star u) t = star (u t) at hu
  rw [hs,hu,hm,he]
  simp only [smul_eq_mul,RCLike.inner_apply,map_mul,fourier_neg,Complex.star_def]
  ring

/-- The native model definition is exactly H² intersect bar(u)⁻¹(H²⊥). -/
theorem mem_model_iff_spectrum (u : BoundaryLInf) (f : BoundaryL2) :
    f ∈ model u ↔ f ∈ hardy ∧ multiply (star u) f ∈ hardy.orthogonal := by
  constructor
  · intro hf
    refine ⟨hf.1,(mem_hardy_orthogonal_iff _).mpr ?_⟩
    intro n
    rw [fourierCoeff_multiply_star]
    exact (Submodule.mem_orthogonal _ _).mp hf.2 _ (Submodule.subset_span ⟨n,rfl⟩)
  · rintro ⟨hf,hbar⟩
    refine ⟨hf,(Submodule.mem_orthogonal _ _).mpr ?_⟩
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n,rfl⟩ := hy
      rw [← fourierCoeff_multiply_star]
      exact (mem_hardy_orthogonal_iff _).mp hbar n
    | zero => simp
    | add x y hx hy hx' hy' => rw [inner_add_left,hx',hy',add_zero]
    | smul c x hx hx' => rw [inner_smul_left,hx',mul_zero]

/-- The backward shift has the expected coefficient shift on actual L² classes. -/
theorem fourierCoeff_backwardShift (f : BoundaryL2) (n : ℤ) :
    fourierCoeff (multiply (star coordinate) f) n = fourierCoeff f (n+1) := by
  rw [fourierCoeff,fourierCoeff]
  apply integral_congr_ae
  filter_upwards [multiply_ae (star coordinate) f,Lp.coeFn_star coordinate,coordinate_ae] with t hm hs hz
  change (star coordinate) t = star (coordinate t) at hs
  rw [hm,hs,hz]
  simp only [smul_eq_mul,Complex.star_def]
  rw [show (-(n+1) : ℤ) = -n+(-1) by ring,fourier_add]
  simp only [fourier_neg]
  ring

theorem analyticValue_at_zero (f : BoundaryL2) : analyticValue f 0 = fourierCoeff f 0 := by
  rw [analyticValue,tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The paper's ψ/z really belongs to the unchanged native model when ψ(0)=0. -/
theorem backwardShift_mem_model (u : BoundaryLInf) (ψ : Model u) (hψ : analyticValue ψ.val 0 = 0) :
    multiply (star coordinate) ψ.val ∈ model u := by
  apply (mem_model_iff_spectrum _ _).mpr
  constructor
  · apply (mem_hardy_iff _).mpr
    intro n hn
    rw [fourierCoeff_backwardShift]
    rcases lt_or_eq_of_le (show n+1 ≤ 0 by omega) with h | h
    · exact (mem_hardy_iff _).mp ψ.property.1 _ h
    · rw [h,← analyticValue_at_zero]
      exact hψ
  · apply (mem_hardy_orthogonal_iff _).mpr
    intro n
    rw [multiply_comm,fourierCoeff_backwardShift]
    have h := (mem_hardy_orthogonal_iff _).mp ((mem_model_iff_spectrum _ _).mp ψ.property).2 (n+1)
    simpa only [Nat.cast_add,Nat.cast_one] using h

/-- Both model summands in K_(u²)=K_u⊕uK_u lie in the literal square model. -/
theorem model_mem_squareModel (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    f.val ∈ model (multiplyInf u u) := by
  refine ⟨f.property.1,(Submodule.mem_orthogonal' _ _).mpr ?_⟩
  intro g hg
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n,rfl⟩ := hy
    change inner ℂ f.val (multiply (multiplyInf u u) (fourierBasis (T := 1) (n : ℤ))) = 0
    rw [← multiply_assoc]
    exact inner_eq_zero_symm.mp (inner_multiply_model u f
      ⟨multiply u (fourierBasis (T := 1) (n : ℤ)),multiply_mode_mem_hardy u hu n⟩)
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]

theorem multiply_model_mem_squareModel (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    multiply u f.val ∈ model (multiplyInf u u) := by
  refine ⟨multiply_mem_hardy u hu.1 f.val f.property.1,(Submodule.mem_orthogonal' _ _).mpr ?_⟩
  intro g hg
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n,rfl⟩ := hy
    change inner ℂ (multiply u f.val) (multiply (multiplyInf u u) (fourierBasis (T := 1) (n : ℤ))) = 0
    rw [← multiply_assoc]
    change inner ℂ (innerMultiplyIsometry u hu f.val)
      (innerMultiplyIsometry u hu (multiply u (fourierBasis (T := 1) (n : ℤ)))) = 0
    rw [(innerMultiplyIsometry u hu).inner_map_map]
    exact (Submodule.mem_orthogonal' _ _).mp f.property.2 _ (Submodule.subset_span ⟨n,rfl⟩)
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]


/-- The actual U transfer preserves Schatten membership for every p, with no symbol regularity loss. -/
theorem hasSchattenTTO_iff_THO_conjugation (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2) (p : ℝ) :
    HasSchattenTTO p u σ ↔ HasSchattenTHO p u (star (conjugation u σ)) := by
  let U := conjugateModelUnitary u hu
  constructor
  · rintro ⟨A,hA,hs⟩
    exact ⟨U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A,
      (representsTTO_iff_THO u hu σ A).mp hA,(schatten_unitary_comp_iff U.symm A p).mpr hs⟩
  · rintro ⟨B,hB,hs⟩
    let A := U.toContinuousLinearEquiv.toContinuousLinearMap ∘L B
    have he : U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A = B := by ext f; simp [A]
    refine ⟨A,?_,(schatten_unitary_comp_iff U B p).mpr hs⟩
    apply (representsTTO_iff_THO u hu σ A).mpr
    change RepresentsTHO u (star (conjugation u σ)) (U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A)
    rw [he]
    exact hB

/-- The canonical η is an actual K_(u²) vector with exactly the two reviewed energy projections. -/
theorem canonicalSymbolData (u : BoundaryLInf) (hu : IsInner u) (φ ψ : Model u)
    (hψ : analyticValue ψ.val 0 = 0) :
    ∃ η : Ambient u,
      η.val = conjugation u φ.val + multiply u (multiply (star coordinate) ψ.val) ∧
      energyH u η.val = multiply coordinate (conjugation u φ.val) ∧ energyG u η.val = ψ.val ∧
      conjugation u (splitSymbol φ.val ψ.val) = η.val := by
  let Cf : Model u := ⟨conjugation u φ.val,conjugation_mem_model u hu φ⟩
  let ν : Model u := ⟨multiply (star coordinate) ψ.val,backwardShift_mem_model u ψ hψ⟩
  let η : Ambient u := ⟨Cf.val+multiply u ν.val,
    (model (multiplyInf u u)).add_mem (model_mem_squareModel u hu Cf) (multiply_model_mem_squareModel u hu ν)⟩
  have hz1 : (model u).orthogonalProjectionOnto (multiply u ν.val) = 0 := by
    apply (model u).orthogonalProjectionOnto_eq_zero_iff.mpr
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro f hf
    exact inner_multiply_model u ⟨f,hf⟩ ⟨ν.val,ν.property.1⟩
  have hp1 : (model u).orthogonalProjectionOnto η.val = Cf := by
    change (model u).orthogonalProjectionOnto (Cf.val+multiply u ν.val) = Cf
    rw [map_add,hz1,add_zero]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self Cf
  have hz2 : (model u).orthogonalProjectionOnto (multiply (star u) Cf.val) = 0 := by
    apply (model u).orthogonalProjectionOnto_eq_zero_iff.mpr
    exact Submodule.orthogonal_le (show model u ≤ hardy from inf_le_left)
      ((mem_model_iff_spectrum _ _).mp Cf.property).2
  have hp2 : (model u).orthogonalProjectionOnto (multiply (star u) η.val) = ν := by
    change (model u).orthogonalProjectionOnto (multiply (star u) (Cf.val+multiply u ν.val)) = ν
    rw [map_add,multiply_star_cancel u hu.2,map_add,hz2,zero_add]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ν
  refine ⟨η,rfl,?_,?_,?_⟩
  · unfold energyH eta₁
    rw [hp1]
  · unfold energyG eta₂
    rw [hp2]
    exact multiply_cancel_star coordinate coordinate_unimodular ψ.val
  · simp only [splitSymbol,conjugation,boundary_star_add,star_star,map_add]
    rfl

/-- Lemma 3's full canonical THO obligation, including actual η/energy meanings and exact singular data. -/
theorem canonicalTHO : CanonicalTHOObligation := by
  intro u hu _hn φ ψ hψ
  obtain ⟨η,he,hH,hG,hη⟩ := canonicalSymbolData u hu φ ψ hψ
  refine ⟨η,he,hH,hG,?_,?_⟩
  · rw [← hη]
    exact hasSchattenTTO_iff_THO_conjugation u hu (splitSymbol φ.val ψ.val) 2
  · intro A hA hs
    let U := conjugateModelUnitary u hu
    let B := U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L A
    refine ⟨B,?_,(schatten_unitary_comp_iff U.symm A 2).mpr hs,?_⟩
    · rw [← hη]
      exact (representsTTO_iff_THO u hu (splitSymbol φ.val ψ.val) A).mp hA
    · intro n
      exact (approximationNumber_unitary_comp U.symm A n).symm

end CanonicalModel

section ExactHankelModel

/-- Actual multiplier adjoint pairing, valid for every bounded symbol. -/
theorem inner_multiply_left (a : BoundaryLInf) (f g : BoundaryL2) :
    inner ℂ (multiply a f) g = inner ℂ f (multiply (star a) g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae a f,multiply_ae (star a) g,Lp.coeFn_star a] with t hm hs ha
  change (star a) t = star (a t) at ha
  simp only [RCLike.inner_apply,hm,hs,ha,Complex.star_def,map_mul]
  ring

/-- The paper's J is the literal bar(u) multiplier into the negative Hardy subspace. -/
def hankelModelIsometry (u : BoundaryLInf) (hu : IsInner u) : Model u →ₗᵢ[ℂ] ↥hardy.orthogonal where
  toLinearMap := LinearMap.codRestrict hardy.orthogonal
    ((multiply (star u)).toLinearMap.comp (model u).subtype)
    (fun f => ((mem_model_iff_spectrum u f.val).mp f.property).2)
  norm_map' f := by
    change ‖multiply (star u) f.val‖ = ‖f.val‖
    calc
      _ = ‖multiply u (multiply (star u) f.val)‖ :=
        ((innerMultiplyIsometry u hu).norm_map (multiply (star u) f.val)).symm
      _ = ‖f.val‖ := by rw [multiply_cancel_star u hu.2]

@[simp] theorem hankelModelIsometry_apply (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    (hankelModelIsometry u hu f).val = multiply (star u) f.val := rfl

theorem modelProjection_multiply_hardy_zero (u : BoundaryLInf) (f : Hardy) :
    (model u).orthogonalProjectionOnto (multiply u f.val) = 0 := by
  apply (model u).orthogonalProjectionOnto_eq_zero_iff.mpr
  exact (Submodule.mem_orthogonal' _ _).mpr (fun g hg => inner_multiply_model u ⟨g,hg⟩ f)

/-- The exact native projection identity, proved without a boundedness claim for model projection. -/
theorem negativeProjection_multiply_star (u : BoundaryLInf) (hu : IsInner u) (h : Hardy) :
    hardy.orthogonal.orthogonalProjectionOnto (multiply (star u) h.val) =
      hankelModelIsometry u hu ((model u).orthogonalProjectionOnto h.val) := by
  let g := multiply (star u) h.val
  let p : Hardy := hardy.orthogonalProjectionOnto g
  let v : BoundaryL2 := h.val-multiply u p.val
  have hvh : v ∈ hardy := hardy.sub_mem h.property (multiply_mem_hardy u hu.1 p.val p.property)
  have hbar : multiply (star u) v = g-p.val := by
    change multiply (star u) (h.val-multiply u p.val) = g-p.val
    rw [map_sub,multiply_star_cancel u hu.2]
  have hvm : v ∈ model u := (mem_model_iff_spectrum _ _).mpr ⟨hvh,by
    rw [hbar]
    exact hardy.sub_starProjection_mem_orthogonal g⟩
  have hp : (model u).starProjection h.val = v := by
    apply (model u).eq_starProjection_of_mem_orthogonal hvm
    have he : h.val-v = multiply u p.val := by dsimp [v]; abel
    rw [he]
    exact (model u).orthogonalProjectionOnto_eq_zero_iff.mp (modelProjection_multiply_hardy_zero u p)
  apply Subtype.ext
  change hardy.orthogonal.starProjection g = multiply (star u) ((model u).starProjection h.val)
  rw [hardy.starProjection_orthogonal_val,hp]
  exact hbar.symm

/-- Bounded core multiplication by an L² symbol is an honest linear map on the bounded submodule. -/
def coreMultiply (σ : BoundaryL2) : boundedL2 →ₗ[ℂ] BoundaryL2 where
  toFun f := multiply (f.property.toLp f.val) σ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [multiply_ae ((f+g).property.toLp (f+g).val) σ,(f+g).property.coeFn_toLp,
      multiply_ae (f.property.toLp f.val) σ,f.property.coeFn_toLp,
      multiply_ae (g.property.toLp g.val) σ,g.property.coeFn_toLp,
      Lp.coeFn_add f.val g.val,Lp.coeFn_add (multiply (f.property.toLp f.val) σ) (multiply (g.property.toLp g.val) σ)]
      with t hfg hfgv hf hfv hg hgv ha hs
    rw [hfg,hfgv]
    change (f.val+g.val) t*σ t = (multiply (f.property.toLp f.val) σ+multiply (g.property.toLp g.val) σ) t
    rw [ha,hs]
    simp only [Pi.add_apply]
    rw [hf,hfv,hg,hgv]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [multiply_ae ((c • f).property.toLp (c • f).val) σ,(c • f).property.coeFn_toLp,
      multiply_ae (f.property.toLp f.val) σ,f.property.coeFn_toLp,
      Lp.coeFn_smul c f.val,Lp.coeFn_smul c (multiply (f.property.toLp f.val) σ)]
      with t hcf hcfv hf hfv hc hs
    rw [hcf,hcfv]
    change (c • f.val) t*σ t = (c • multiply (f.property.toLp f.val) σ) t
    rw [hc,hs]
    simp only [Pi.smul_apply]
    rw [hf,hfv]
    simp only [smul_eq_mul,mul_assoc]

/-- A bounded symbol's core product agrees with ordinary Hölder multiplication. -/
theorem coreMultiply_toL2 (σ : BoundaryL2) (a : BoundaryLInf) :
    coreMultiply σ ⟨toL2 a,bounded_toL2 a⟩ = multiply a σ := by
  apply Lp.ext
  filter_upwards [multiply_ae ((bounded_toL2 a).toLp (toL2 a)) σ,(bounded_toL2 a).coeFn_toLp,
    toL2_ae a,multiply_ae a σ] with t hp ht ha hm
  change multiply ((bounded_toL2 a).toLp (toL2 a)) σ t = multiply a σ t
  rw [hp,ht,ha,hm]


theorem coreMultiply_fourierBasis (σ : BoundaryL2) (n : ℤ) :
    coreMultiply σ ⟨fourierBasis (T := 1) n,bounded_fourierBasis n⟩ = multiply (mode n) σ := by
  have he : (⟨fourierBasis (T := 1) n,bounded_fourierBasis n⟩ : boundedL2) =
      ⟨toL2 (mode n),bounded_toL2 (mode n)⟩ := Subtype.ext (toL2_mode n).symm
  rw [he,coreMultiply_toL2]

theorem coreMultiply_multiply (σ : BoundaryL2) (a : BoundaryLInf) (f : BoundaryL2) (hf : IsBounded f) :
    coreMultiply σ ⟨multiply a f,bounded_multiply a f hf⟩ = multiply a (coreMultiply σ ⟨f,hf⟩) := by
  apply Lp.ext
  filter_upwards [multiply_ae ((bounded_multiply a f hf).toLp (multiply a f)) σ,
    (bounded_multiply a f hf).coeFn_toLp,multiply_ae a f,
    multiply_ae a (coreMultiply σ ⟨f,hf⟩),multiply_ae (hf.toLp f) σ,hf.coeFn_toLp]
    with t hprod hv hm hout hcore hfval
  change multiply ((bounded_multiply a f hf).toLp (multiply a f)) σ t =
    multiply a (multiply (hf.toLp f) σ) t
  change multiply a (multiply (hf.toLp f) σ) t = a t* multiply (hf.toLp f) σ t at hout
  rw [hprod,hv,hm,hout,hcore,hfval,mul_assoc]

/-- Bounded TTO core values are the genuine model projections of their product. -/
theorem representsTTO_value (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) (f : Model u) (hf : IsBounded f.val) :
    A f = (model u).orthogonalProjectionOnto (coreMultiply σ ⟨f.val,hf⟩) :=
  denseCoreSet_value u σ A {g | IsBounded g.val} (bounded_modelCore_dense u hu)
    (fun _ h => h) (fun f hf g hg => hA f g hf hg) f hf

/-- Finite model-projection corrections contribute no analytic compressed product. -/
theorem analyticTTO_modelPolynomial_value (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) (n : ℕ) :
    A ((model u).orthogonalProjectionOnto (fourierBasis (T := 1) (n : ℤ))) =
      (model u).orthogonalProjectionOnto (multiply (mode (n : ℤ)) φ.val) := by
  classical
  let e : boundedL2 := ⟨fourierBasis (T := 1) (n : ℤ),bounded_fourierBasis _⟩
  let v (j : ℕ) : boundedL2 := ⟨multiply u (fourierBasis (T := 1) (j : ℤ)),
    bounded_multiply u _ (bounded_fourierBasis _)⟩
  let c (j : ℕ) := inner ℂ (multiply u (fourierBasis (T := 1) (j : ℤ))) (fourierBasis (T := 1) (n : ℤ))
  let f : Model u := ⟨modelPolynomial u n,modelPolynomial_mem u hu n⟩
  let b : boundedL2 := ⟨modelPolynomial u n,bounded_modelPolynomial u n⟩
  have he : b = e-∑ j ∈ Finset.range (n+1),c j • v j := by
    apply Subtype.ext
    simp only [Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul]
    rfl
  have hf : (model u).orthogonalProjectionOnto (fourierBasis (T := 1) (n : ℤ)) = f :=
    Subtype.ext (modelProjection_fourierBasis u hu n)
  have hz (j : ℕ) : (model u).orthogonalProjectionOnto (coreMultiply φ.val (v j)) = 0 := by
    change (model u).orthogonalProjectionOnto
      (coreMultiply φ.val ⟨multiply u (fourierBasis (T := 1) (j : ℤ)),bounded_multiply u _ (bounded_fourierBasis _)⟩) = 0
    rw [coreMultiply_multiply φ.val u (fourierBasis (T := 1) (j : ℤ)) (bounded_fourierBasis _),coreMultiply_fourierBasis]
    exact modelProjection_multiply_hardy_zero u
      ⟨multiply (mode (j : ℤ)) φ.val,multiply_mem_hardy _ (by
        rw [toL2_mode]; exact fourierBasis_mem_hardy j) φ.val φ.property⟩
  rw [hf,representsTTO_value u hu φ.val A hA f (bounded_modelPolynomial u n)]
  change (model u).orthogonalProjectionOnto (coreMultiply φ.val b) = _
  rw [he,map_sub,map_sum,map_sub,map_sum]
  simp only [map_smul,hz,smul_zero,Finset.sum_const_zero,sub_zero]
  exact congrArg (model u).orthogonalProjectionOnto (coreMultiply_fourierBasis φ.val (n : ℤ))

/-- The transformed Hankel symbol is exactly bar(u)·φ, with no finite-rank error. -/
theorem hankelSymbol_eq (u : BoundaryLInf) (φ : BoundaryL2) :
    hankelSymbol u φ = multiply (star u) φ := by
  unfold hankelSymbol conjugation
  rw [multiply_star,multiply_star,multiply_star,star_star,star_star]
  rw [multiply_comm (star coordinate) (star u),multiply_star_cancel coordinate coordinate_unimodular]


/-- The native inclusion K_u→H², with its actual inherited norm. -/
def modelHardyIsometry (u : BoundaryLInf) : Model u →ₗᵢ[ℂ] Hardy where
  toLinearMap := LinearMap.codRestrict hardy (model u).subtype (fun f => f.property.1)
  norm_map' _ := rfl

/-- Restrict the genuine model projection to the Hardy space. -/
def hardyModelProjection (u : BoundaryLInf) : Hardy →L[ℂ] Model u :=
  (model u).orthogonalProjectionOnto ∘L hardy.subtypeL

/-- Exact zero extension JAP_u, with codomain the native negative Hardy space. -/
def hankelExtension (u : BoundaryLInf) (hu : IsInner u) (A : Model u →L[ℂ] Model u) : HankelOperator :=
  (hankelModelIsometry u hu).toContinuousLinearMap ∘L A ∘L hardyModelProjection u

/-- Analytic product with a mode is a genuine Hardy vector. -/
theorem mode_multiply_hardy (φ : Hardy) (n : ℕ) : multiply (mode (n : ℤ)) φ.val ∈ hardy :=
  multiply_mem_hardy _ (by rw [toL2_mode]; exact fourierBasis_mem_hardy n) φ.val φ.property

/-- The mode calculation uses only bounded modelPolynomial tests, never arbitrary bounded projections. -/
theorem hankelExtension_mode_value (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) (n : ℕ) :
    hankelExtension u hu A (hardyMode n) =
      hardy.orthogonal.orthogonalProjectionOnto (multiply (star u) (multiply (mode (n : ℤ)) φ.val)) := by
  change hankelModelIsometry u hu (A ((model u).orthogonalProjectionOnto (fourierBasis (T := 1) (n : ℤ)))) = _
  rw [analyticTTO_modelPolynomial_value u hu φ A hA n]
  exact (negativeProjection_multiply_star u hu ⟨multiply (mode (n : ℤ)) φ.val,mode_multiply_hardy φ n⟩).symm

theorem coreForm_hankelSymbol_mode (u : BoundaryLInf) (φ : BoundaryL2) (n : ℕ) (g : BoundaryL2) :
    coreForm (hankelSymbol u φ) (fourierBasis (T := 1) (n : ℤ)) g =
      inner ℂ g (multiply (star u) (multiply (mode (n : ℤ)) φ)) := by
  rw [hankelSymbol_eq,coreForm_eq_inner_left _ _ _ (bounded_fourierBasis _)]
  change inner ℂ g (coreMultiply (multiply (star u) φ)
    ⟨fourierBasis (T := 1) (n : ℤ),bounded_fourierBasis _⟩) = _
  rw [coreMultiply_fourierBasis,multiply_comm]

/-- Density in the first slot extends the honest finite-mode calculation to the full Hankel core. -/
theorem hankelExtension_represents (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) :
    RepresentsHankel (hankelSymbol u φ.val) (hankelExtension u hu A) := by
  intro f g _hf hg
  let σ := hankelSymbol u φ.val
  let F := innerSL ℂ g ∘L hankelExtension u hu A
  let G := innerSL ℂ (multiply (hg.toLp g.val) (star σ)) ∘L hardy.subtypeL
  have he : F = G := by
    apply ContinuousLinearMap.ext_on hardyModes_dense
    rintro _ ⟨n,rfl⟩
    change inner ℂ g (hankelExtension u hu A (hardyMode n)) =
      inner ℂ (multiply (hg.toLp g.val) (star σ)) (fourierBasis (T := 1) (n : ℤ))
    rw [hankelExtension_mode_value u hu φ A hA n,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact (coreForm_hankelSymbol_mode u φ.val n g.val).symm.trans
      (coreForm_eq_inner_right σ _ g.val hg)
  have hv := congrArg (fun L : Hardy →L[ℂ] ℂ => L f) he
  change inner ℂ g (hankelExtension u hu A f) = inner ℂ (multiply (hg.toLp g.val) (star σ)) f.val at hv
  exact hv.trans (coreForm_eq_inner_right σ f.val g.val hg).symm


/-- Every strictly negative Fourier character lies in the actual Hardy orthogonal complement. -/
theorem fourierBasis_mem_negative {n : ℤ} (hn : n < 0) : fourierBasis (T := 1) n ∈ hardy.orthogonal := by
  apply (mem_hardy_orthogonal_iff _).mpr
  intro k
  have hne : (k : ℤ) ≠ n := by omega
  have hi := orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal (k : ℤ) n
  rw [ite_eq_right hne] at hi
  simpa only [← HilbertBasis.repr_apply_apply,fourierBasis_repr] using hi

/-- Hankel core forms determine their bounded operator, using actual positive/negative modes. -/
theorem representsHankel_unique (σ : BoundaryL2) (H K : HankelOperator)
    (hH : RepresentsHankel σ H) (hK : RepresentsHankel σ K) : H = K := by
  apply ContinuousLinearMap.ext_on hardyModes_dense
  rintro _ ⟨n,rfl⟩
  apply Subtype.ext
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext j
  rw [fourierBasis_repr,fourierBasis_repr]
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    rw [(mem_hardy_orthogonal_iff _).mp (H (hardyMode n)).property j,
      (mem_hardy_orthogonal_iff _).mp (K (hardyMode n)).property j]
  · let g : ↥hardy.orthogonal := ⟨fourierBasis (T := 1) j,fourierBasis_mem_negative (lt_of_not_ge hj)⟩
    have hi := (hH (hardyMode n) g (bounded_fourierBasis _) (bounded_fourierBasis _)).trans
      (hK (hardyMode n) g (bounded_fourierBasis _) (bounded_fourierBasis _)).symm
    change inner ℂ (fourierBasis (T := 1) j) (H (hardyMode n)).val =
      inner ℂ (fourierBasis (T := 1) j) (K (hardyMode n)).val at hi
    simpa only [← HilbertBasis.repr_apply_apply,fourierBasis_repr] using hi

/-- The inverse construction uses the genuine adjoint J*, with no extra range assumption. -/
def hankelCompression (u : BoundaryLInf) (hu : IsInner u) (H : HankelOperator) : Model u →L[ℂ] Model u :=
  (hankelModelIsometry u hu).toContinuousLinearMap.adjoint ∘L H ∘L (modelHardyIsometry u).toContinuousLinearMap

theorem coreForm_hankel_model (u : BoundaryLInf) (hu : IsInner u) (φ f g : BoundaryL2) :
    coreForm (hankelSymbol u φ) f (multiply (star u) g) = coreForm φ f g := by
  rw [hankelSymbol_eq]
  apply integral_congr_ae
  filter_upwards [multiply_ae (star u) φ,multiply_ae (star u) g,Lp.coeFn_star u,hu.2]
    with t hφ hg hs hn
  change (star u) t = star (u t) at hs
  rw [hφ,hg,hs]
  simp only [Complex.star_def,map_mul,Complex.conj_conj]
  have hh : conj (u t)*u t = 1 := by simp [Complex.conj_mul',hn]
  calc
    _ = (conj (u t)*u t)*(φ t*f t*conj (g t)) := by ring
    _ = _ := by rw [hh,one_mul]

/-- Every represented classical Hankel operator gives the corresponding analytic TTO on its bounded core. -/
theorem hankelCompression_represents (u : BoundaryLInf) (hu : IsInner u) (φ : BoundaryL2)
    (H : HankelOperator) (hH : RepresentsHankel (hankelSymbol u φ) H) :
    RepresentsTTO u φ (hankelCompression u hu H) := by
  intro f g hf hg
  change inner ℂ g ((hankelModelIsometry u hu).toContinuousLinearMap.adjoint
    (H (modelHardyIsometry u f))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (hankelModelIsometry u hu g) (H (modelHardyIsometry u f)) = _
  rw [hH (modelHardyIsometry u f) (hankelModelIsometry u hu g) hf
    (bounded_multiply (star u) g.val hg)]
  exact coreForm_hankel_model u hu φ f.val g.val

/-- J* JAP_u equals A because both the inclusion/projection and J*/J pairs are actual inverses. -/
theorem hankelCompression_extension (u : BoundaryLInf) (hu : IsInner u) (A : Model u →L[ℂ] Model u) :
    hankelCompression u hu (hankelExtension u hu A) = A := by
  apply ContinuousLinearMap.ext
  intro f
  have hp : hardyModelProjection u (modelHardyIsometry u f) = f :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self f
  change (hankelModelIsometry u hu).toContinuousLinearMap.adjoint
    ((hankelModelIsometry u hu).toContinuousLinearMap (A (hardyModelProjection u (modelHardyIsometry u f)))) = A f
  rw [hp]
  exact congrArg (fun L : Model u →L[ℂ] Model u => L (A f)) (hankelModelIsometry u hu).adjoint_comp_self


theorem approximationNumber_comp_right_contraction {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (A : F →L[ℂ] G) (R : E →L[ℂ] F)
    (hR : ‖R‖ ≤ 1) (n : ℕ) : approximationNumber (A ∘L R) n ≤ approximationNumber A n := by
  have h : ‖R‖₊ ≤ 1 := by exact_mod_cast hR
  exact (approximationNumber_comp_right A R n).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (by positivity))

theorem norm_hardyModelProjection_le (u : BoundaryLInf) : ‖hardyModelProjection u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(model u).orthogonalProjectionOnto f.val‖ ≤ 1*‖f.val‖
  rw [one_mul]
  exact (model u).norm_orthogonalProjectionOnto_apply_le f.val

/-- The exact zero extension preserves compactness and every approximation number, including index zero. -/
theorem hankelExtension_data (u : BoundaryLInf) (hu : IsInner u) (A : Model u →L[ℂ] Model u) :
    (IsCompactOperator A ↔ IsCompactOperator (hankelExtension u hu A)) ∧
      ∀ n, approximationNumber A n = approximationNumber (hankelExtension u hu A) n := by
  let J := (hankelModelIsometry u hu).toContinuousLinearMap
  let I := (modelHardyIsometry u).toContinuousLinearMap
  have hJ : ‖J‖ ≤ 1 := norm_isometry_clm_le_one _
  have hI : ‖I‖ ≤ 1 := norm_isometry_clm_le_one _
  have hR : ‖J.adjoint‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hJ
  constructor
  · constructor
    · intro hc
      exact (hc.comp_clm (hardyModelProjection u)).clm_comp J
    · intro hc
      have hh : IsCompactOperator (hankelCompression u hu (hankelExtension u hu A)) :=
        (hc.comp_clm I).clm_comp J.adjoint
      rw [hankelCompression_extension] at hh
      exact hh
  · intro n
    apply le_antisymm
    · have h := (approximationNumber_comp_contraction J.adjoint hR
          (hankelExtension u hu A ∘L I) n).trans
        (approximationNumber_comp_right_contraction (hankelExtension u hu A) I hI n)
      change approximationNumber (hankelCompression u hu (hankelExtension u hu A)) n ≤
        approximationNumber (hankelExtension u hu A) n at h
      rw [hankelCompression_extension] at h
      exact h
    · exact (approximationNumber_comp_contraction J hJ (A ∘L hardyModelProjection u) n).trans
        (approximationNumber_comp_right_contraction A (hardyModelProjection u) (norm_hardyModelProjection_le u) n)

/-- The two core constructions are actual inverses for every represented analytic Hankel operator. -/
theorem hankelExtension_compression (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (H : HankelOperator) (hH : RepresentsHankel (hankelSymbol u φ.val) H) :
    hankelExtension u hu (hankelCompression u hu H) = H :=
  representsHankel_unique _ _ _
    (hankelExtension_represents u hu φ _ (hankelCompression_represents u hu φ.val H hH)) hH

/-- Lemma 2's complete exact classical-Hankel obligation, with its genuine analytic core proof. -/
theorem exactHankel : ExactHankelObligation := by
  intro u hu _hn φ
  refine ⟨(conjugation_mem_model u hu φ).1,?_,?_⟩
  · intro A hA
    exact ⟨hankelExtension u hu A,hankelExtension_represents u hu ⟨φ.val,φ.property.1⟩ A hA,
      (hankelExtension_data u hu A).1,(hankelExtension_data u hu A).2⟩
  · intro H hH
    let A := hankelCompression u hu H
    have hA := hankelCompression_represents u hu φ.val H hH
    have he : hankelExtension u hu A = H := hankelExtension_compression u hu ⟨φ.val,φ.property.1⟩ H hH
    have hd := hankelExtension_data u hu A
    rw [he] at hd
    exact ⟨A,hA,hd.1,hd.2⟩

end ExactHankelModel



section ScalarAmbiguity

theorem fourierCoeff_sub_L2 (f g : BoundaryL2) (n : ℤ) :
    fourierCoeff (f-g) n = fourierCoeff f n-fourierCoeff g n := by
  simp only [← fourierBasis_repr,map_sub,lp.coeFn_sub,Pi.sub_apply]

theorem fourierCoeff_constL2 (c : ℂ) (n : ℤ) :
    fourierCoeff (constL2 c) n = if n = 0 then c else 0 := by
  rw [← fourierBasis_repr,constL2_fourier,map_smul,HilbertBasis.repr_self]
  simp [lp.single_apply,Pi.single_apply]

theorem bounded_constL2 (c : ℂ) : IsBounded (constL2 c) := by
  rw [constL2_fourier]
  exact boundedL2.smul_mem c (bounded_fourierBasis 0)

theorem inner_constL2_right (f : BoundaryL2) (c : ℂ) :
    inner ℂ f (constL2 c) = c*conj (fourierCoeff f 0) := by
  rw [constL2_fourier,inner_smul_right]
  congr 1
  rw [← inner_conj_symm]
  congr 1
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

/-- Literal Hardy backward shift, including subtraction of the value at the origin. -/
def hardyBackwardShift (f : BoundaryL2) : BoundaryL2 :=
  multiply (star coordinate) (f-constL2 (analyticValue f 0))

theorem hardyBackwardShift_hardy (f : Hardy) : hardyBackwardShift f.val ∈ hardy := by
  apply (mem_hardy_iff _).mpr
  intro n hn
  rw [hardyBackwardShift,fourierCoeff_backwardShift,fourierCoeff_sub_L2,fourierCoeff_constL2]
  rcases lt_or_eq_of_le (show n+1 ≤ 0 by omega) with h | h
  · rw [ite_eq_right h.ne,(mem_hardy_iff _).mp f.property _ h,sub_self]
  · rw [h,ite_eq_left rfl,← analyticValue_at_zero,sub_self]

theorem fourierCoeff_multiply_star_const_pos (u : BoundaryLInf) (hu : IsInner u) (c : ℂ)
    (n : ℤ) (hn : 0 < n) : fourierCoeff (multiply (star u) (constL2 c)) n = 0 := by
  rw [fourierCoeff_multiply_star,inner_constL2_right,fourierCoeff_multiply_mode]
  have hz := (mem_hardy_iff _).mp hu.1 (-n) (by omega)
  rw [fourierCoeff_congr_ae (toL2_ae u)] at hz
  simp only [zero_sub,hz,map_zero,mul_zero]

/-- The full model is backward-shift invariant; f−f(0) itself need not be a model vector. -/
theorem hardyBackwardShift_mem_model (u : BoundaryLInf) (hu : IsInner u) (f : Model u) :
    hardyBackwardShift f.val ∈ model u := by
  apply (mem_model_iff_spectrum _ _).mpr
  refine ⟨hardyBackwardShift_hardy ⟨f.val,f.property.1⟩,(mem_hardy_orthogonal_iff _).mpr ?_⟩
  intro n
  rw [hardyBackwardShift,multiply_comm,fourierCoeff_backwardShift,map_sub,fourierCoeff_sub_L2]
  have hf := (mem_hardy_orthogonal_iff _).mp ((mem_model_iff_spectrum _ _).mp f.property).2 (n+1)
  rw [show ((n+1 : ℕ) : ℤ) = (n : ℤ)+1 by simp] at hf
  rw [hf,fourierCoeff_multiply_star_const_pos u hu _ _ (by omega),sub_self]

theorem bounded_hardyBackwardShift (f : BoundaryL2) (hf : IsBounded f) :
    IsBounded (hardyBackwardShift f) :=
  bounded_multiply _ _ (boundedL2.sub_mem hf (bounded_constL2 _))

/-- Actual boundary value of the model-preserving backward shift. -/
theorem hardyBackwardShift_ae (f : BoundaryL2) :
    hardyBackwardShift f =ᵐ[circleMeasure] fun t =>
      conj (fourier (T := 1) 1 t)*(f t-analyticValue f 0) := by
  filter_upwards [multiply_ae (star coordinate) (f-constL2 (analyticValue f 0)),
    Lp.coeFn_star coordinate,coordinate_ae,Lp.coeFn_sub f (constL2 (analyticValue f 0)),
    (memLp_const (analyticValue f 0)).coeFn_toLp] with t hm hs hz hsub hc
  change (star coordinate) t = star (coordinate t) at hs
  change constL2 (analyticValue f 0) t = analyticValue f 0 at hc
  change multiply (star coordinate) (f-constL2 (analyticValue f 0)) t = _
  rw [hm,hs,hz,hsub]
  simp only [Pi.sub_apply,hc,Complex.star_def]


theorem inner_constL2_left (f : BoundaryL2) (c : ℂ) :
    inner ℂ (constL2 c) f = conj c*fourierCoeff f 0 := by
  rw [constL2_fourier,inner_smul_left]
  congr 1
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

theorem coreForm_sub_first (σ f h g : BoundaryL2) (hg : IsBounded g) :
    coreForm σ (f-h) g = coreForm σ f g-coreForm σ h g := by
  rw [coreForm_eq_inner_right _ _ _ hg,inner_sub_right,
    ← coreForm_eq_inner_right _ _ _ hg,← coreForm_eq_inner_right _ _ _ hg]

theorem coreForm_sub_second (σ f g h : BoundaryL2) (hf : IsBounded f) :
    coreForm σ f (g-h) = coreForm σ f g-coreForm σ f h := by
  rw [coreForm_eq_inner_left _ _ _ hf,inner_sub_left,
    ← coreForm_eq_inner_left _ _ _ hf,← coreForm_eq_inner_left _ _ _ hf]

theorem coreForm_const_first (σ g : BoundaryL2) (c : ℂ) :
    coreForm σ (constL2 c) g = c*inner ℂ g σ := by
  rw [L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  have hc : constL2 c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  filter_upwards [hc] with t ht
  simp only [ht,RCLike.inner_apply]
  ring

/-- Analytic multiplication has the exact mean-value identity on a bounded Hardy input. -/
theorem coreForm_const_second_analytic (φ f : Hardy) (hf : IsBounded f.val) (c : ℂ) :
    coreForm φ.val f.val (constL2 c) = conj c*analyticValue f.val 0*analyticValue φ.val 0 := by
  let a : BoundaryLInf := hf.toLp f.val
  have he : toL2 a = f.val := Lp.ext ((toL2_ae a).trans hf.coeFn_toLp)
  have ha : toL2 a ∈ hardy := he.symm ▸ f.property
  rw [coreForm_eq_inner_left _ _ _ hf,inner_constL2_left,← analyticValue_at_zero]
  change conj c*analyticValue (multiply a φ.val) 0 = _
  rw [analyticValue_multiply a ha φ ⟨0,by norm_num [disk]⟩]
  unfold innerValue
  rw [he]
  ring

theorem coreForm_multiply_unimodular (σ : BoundaryL2) (a : BoundaryLInf)
    (ha : ∀ᵐ t ∂circleMeasure, ‖a t‖ = 1) (f g : BoundaryL2) :
    coreForm σ (multiply a f) (multiply a g) = coreForm σ f g := by
  apply integral_congr_ae
  filter_upwards [multiply_ae a f,multiply_ae a g,ha] with t hf hg hn
  rw [hf,hg]
  simp only [map_mul]
  have hh : conj (a t)*a t = 1 := by simp [Complex.conj_mul',hn]
  calc
    _ = (conj (a t)*a t)*(σ t*f t*conj (g t)) := by ring
    _ = _ := by rw [hh,one_mul]

/-- The form defect uses only bounded Hardy inputs, not bounded analytic component operators. -/
theorem coreForm_backwardShift_defect (φ f g : Hardy) (hf : IsBounded f.val) (hg : IsBounded g.val) :
    coreForm φ.val f.val g.val-coreForm φ.val (hardyBackwardShift f.val) (hardyBackwardShift g.val) =
      analyticValue f.val 0*inner ℂ g.val φ.val := by
  have hunit : ∀ᵐ t ∂circleMeasure, ‖(star coordinate) t‖ = 1 := by
    filter_upwards [Lp.coeFn_star coordinate,coordinate_unimodular] with t ht hn
    change (star coordinate) t = star (coordinate t) at ht
    rw [ht,norm_star,hn]
  rw [hardyBackwardShift,hardyBackwardShift,coreForm_multiply_unimodular _ _ hunit]
  rw [coreForm_sub_second _ _ _ _ (boundedL2.sub_mem hf (bounded_constL2 _)),
    coreForm_sub_first _ _ _ _ hg,coreForm_sub_first _ _ _ _ (bounded_constL2 _),
    coreForm_const_first,coreForm_const_second_analytic φ f hf,coreForm_const_first,
    inner_constL2_left,← analyticValue_at_zero]
  ring


theorem coreForm_backwardShift_defect_coanalytic (ψ f g : Hardy) (hf : IsBounded f.val) (hg : IsBounded g.val) :
    coreForm (star ψ.val) f.val g.val-coreForm (star ψ.val) (hardyBackwardShift f.val) (hardyBackwardShift g.val) =
      conj (analyticValue g.val 0)*inner ℂ ψ.val f.val := by
  rw [coreForm_star _ _ _ hf,coreForm_star _ _ _ (bounded_hardyBackwardShift f.val hf),
    ← map_sub,coreForm_backwardShift_defect ψ g f hg hf,map_mul,inner_conj_symm]

/-- A Hardy vector killed by the genuine model projection has an actual uH² factor. -/
theorem innerFactor_of_modelProjection_zero (u : BoundaryLInf) (hu : IsInner u) (h : Hardy)
    (hzero : (model u).orthogonalProjectionOnto h.val = 0) :
    ∃ q : Hardy, h.val = multiply u q.val := by
  let q : Hardy := hardy.orthogonalProjectionOnto (multiply (star u) h.val)
  have he := negativeProjection_multiply_star u hu h
  rw [hzero,map_zero] at he
  have hv := congrArg Subtype.val he
  change hardy.orthogonal.starProjection (multiply (star u) h.val) = 0 at hv
  rw [hardy.starProjection_orthogonal_val] at hv
  have hh := congrArg (multiply u) (sub_eq_zero.mp hv)
  rw [multiply_cancel_star u hu.2] at hh
  exact ⟨q,hh⟩

/-- Genuine uH² symbols vanish on every bounded model test, without a bounded symbol assumption. -/
theorem represents_inner_multiple_zero (u : BoundaryLInf) (q : Hardy) :
    RepresentsTTO u (multiply u q.val) (0 : Model u →L[ℂ] Model u) := by
  intro f g hf _hg
  let a : BoundaryLInf := hf.toLp f.val
  have he : toL2 a = f.val := Lp.ext ((toL2_ae a).trans hf.coeFn_toLp)
  have ha : toL2 a ∈ hardy := he.symm ▸ f.property.1
  rw [coreForm_eq_inner_left _ _ _ hf]
  simp only [zero_apply,inner_zero_right]
  change (0 : ℂ) = inner ℂ g.val (multiply a (multiply u q.val))
  rw [multiply_comm]
  exact (inner_eq_zero_symm.mp (inner_multiply_model u g
    ⟨multiply a q.val,multiply_mem_hardy a ha q.val q.property⟩)).symm

/-- The native Riesz model vector is the actual projection of the Szegő vector. -/
theorem modelProjection_szegoKernel (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    (model u).orthogonalProjectionOnto (szegoKernel w).val = modelReproducingKernel u hu w := by
  apply Subtype.ext
  apply (model u).eq_starProjection_of_mem_orthogonal (modelKernelVector_mem u hu w)
  have he : (szegoKernel w).val-modelKernelVector u w =
      conj (innerValue u w.val) • multiply u (szegoKernel w).val := by unfold modelKernelVector; abel
  rw [he]
  apply (model u).orthogonal.smul_mem
  exact (Submodule.mem_orthogonal' _ _).mpr (fun f hf => inner_multiply_model u ⟨f,hf⟩ (szegoKernel w))

/-- The actual origin in the open unit disk. -/
def origin : Disk := ⟨0,by norm_num [disk]⟩

theorem constL2_one_eq_szego_origin : constL2 1 = (szegoKernel origin).val := by
  apply Lp.ext
  have hc : constL2 1 =ᵐ[circleMeasure] fun _ => 1 := (memLp_const (1 : ℂ)).coeFn_toLp
  filter_upwards [hc,szegoKernel_ae origin] with t hc hs
  rw [hc,hs]
  simp [origin]

theorem modelProjection_constL2 (u : BoundaryLInf) (hu : IsInner u) (c : ℂ) :
    (model u).orthogonalProjectionOnto (constL2 c) = c • modelReproducingKernel u hu origin := by
  have he : constL2 c = c • constL2 1 := by rw [constL2_fourier c,constL2_fourier 1,one_smul]
  rw [he,map_smul,constL2_one_eq_szego_origin,modelProjection_szegoKernel]


theorem boundary_star_sub (f g : BoundaryL2) : star (f-g) = star f-star g := boundaryStar.map_sub f g

/-- Equality of analytic and coanalytic core forms forces an actual common scalar operator. -/
theorem analytic_coanalytic_scalar (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (φ ψ : Hardy)
    (hsame : ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
      coreForm φ.val f.val g.val = coreForm (star ψ.val) f.val g.val) :
    ∃ c : ℂ, RepresentsTTO u φ.val (c • ContinuousLinearMap.id ℂ _) ∧
      RepresentsTTO u (star ψ.val) (c • ContinuousLinearMap.id ℂ _) := by
  let k := modelReproducingKernel u hu origin
  have hk : IsBounded k.val := bounded_modelReproducingKernel u hu origin
  have hv : analyticValue k.val 0 ≠ 0 := by
    intro h
    have hi : inner ℂ k k = 0 := (inner_modelReproducingKernel u hu origin k).trans h
    exact modelReproducingKernel_ne_zero u hu hn origin (inner_self_eq_zero.mp hi)
  let c : ℂ := inner ℂ ψ.val k.val/analyticValue k.val 0
  have hp : (model u).orthogonalProjectionOnto φ.val = c • k := by
    apply (bounded_modelCore_dense u hu).eq_of_inner_right ℂ
    intro g hg
    let Bk : Model u := ⟨hardyBackwardShift k.val,hardyBackwardShift_mem_model u hu k⟩
    let Bg : Model u := ⟨hardyBackwardShift g.val,hardyBackwardShift_mem_model u hu g⟩
    have h0 := hsame k g hk hg
    have hB := hsame Bk Bg (bounded_hardyBackwardShift k.val hk) (bounded_hardyBackwardShift g.val hg)
    have hd := coreForm_backwardShift_defect φ ⟨k.val,k.property.1⟩ ⟨g.val,g.property.1⟩ hk hg
    rw [h0,hB,coreForm_backwardShift_defect_coanalytic ψ ⟨k.val,k.property.1⟩ ⟨g.val,g.property.1⟩ hk hg] at hd
    have hr : inner ℂ g.val k.val = conj (analyticValue g.val 0) := by
      rw [← inner_conj_symm]
      exact congrArg conj (inner_modelReproducingKernel u hu origin g)
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change inner ℂ g.val φ.val = inner ℂ g.val (c • k.val)
    rw [inner_smul_right,hr]
    apply mul_left_cancel₀ hv
    calc
      analyticValue k.val 0*inner ℂ g.val φ.val = conj (analyticValue g.val 0)*inner ℂ ψ.val k.val := hd.symm
      _ = analyticValue k.val 0*(c*conj (analyticValue g.val 0)) := by dsimp [c]; field_simp [hv]
  have hz : (model u).orthogonalProjectionOnto (φ.val-constL2 c) = 0 := by
    rw [map_sub,hp,modelProjection_constL2 u hu c,sub_self]
  obtain ⟨q,hq⟩ := innerFactor_of_modelProjection_zero u hu
    ⟨φ.val-constL2 c,hardy.sub_mem φ.property (constantCoreLaws.hardy c)⟩ hz
  have hzero : RepresentsTTO u (φ.val-constL2 c) (0 : Model u →L[ℂ] Model u) := by
    change φ.val-constL2 c = multiply u q.val at hq
    rw [hq]
    exact represents_inner_multiple_zero u q
  have hφ : RepresentsTTO u φ.val (c • ContinuousLinearMap.id ℂ _) := by
    intro f g hf hg
    have hz := hzero f g hf hg
    simp only [zero_apply,inner_zero_right] at hz
    rw [coreForm_sub _ _ _ _ hf] at hz
    have heq := sub_eq_zero.mp hz.symm
    exact (constantCoreLaws.represents u c f g hf hg).trans heq.symm
  refine ⟨c,hφ,?_⟩
  intro f g hf hg
  exact (hφ f g hf hg).trans (hsame f g hf hg)

/-- Lemma 4, proved at form level without assuming either analytic component bounded. -/
theorem scalarAmbiguity : ScalarAmbiguityObligation := by
  intro u hu hn φ₁ φ₂ ψ₁ ψ₂ hsame
  let φ : Hardy := ⟨φ₁.val-φ₂.val,hardy.sub_mem φ₁.property φ₂.property⟩
  let ψ : Hardy := ⟨ψ₂.val-ψ₁.val,hardy.sub_mem ψ₂.property ψ₁.property⟩
  have he : ∀ f g : Model u, IsBounded f.val → IsBounded g.val →
      coreForm φ.val f.val g.val = coreForm (star ψ.val) f.val g.val := by
    intro f g hf hg
    have hh := hsame f g hf hg
    simp only [splitSymbol] at hh
    rw [coreForm_add φ₁.val (star ψ₁.val) f.val g.val hf,
      coreForm_add φ₂.val (star ψ₂.val) f.val g.val hf] at hh
    change coreForm (φ₁.val-φ₂.val) f.val g.val = coreForm (star (ψ₂.val-ψ₁.val)) f.val g.val
    rw [boundary_star_sub,coreForm_sub _ _ _ _ hf,coreForm_sub _ _ _ _ hf]
    linear_combination hh
  obtain ⟨c,hφ,hψ⟩ := analytic_coanalytic_scalar u hu hn φ ψ he
  refine ⟨c,hφ,?_⟩
  simpa only [ψ,boundary_star_sub] using hψ


/-- Analytic symbols have precisely their genuine model-projected representative on the entire core. -/
theorem sameTTO_analytic_projection (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy) :
    SameTTO u φ.val (((model u).orthogonalProjectionOnto φ.val).val) := by
  let Pφ := (model u).orthogonalProjectionOnto φ.val
  have hz : (model u).orthogonalProjectionOnto (φ.val-Pφ.val) = 0 := by
    rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  obtain ⟨q,hq⟩ := innerFactor_of_modelProjection_zero u hu
    ⟨φ.val-Pφ.val,hardy.sub_mem φ.property Pφ.property.1⟩ hz
  change φ.val-Pφ.val = multiply u q.val at hq
  have hzero := represents_inner_multiple_zero u q
  rw [← hq] at hzero
  intro f g hf hg
  have he := hzero f g hf hg
  simp only [zero_apply,inner_zero_right] at he
  rw [coreForm_sub _ _ _ _ hf] at he
  exact sub_eq_zero.mp he.symm

theorem boundary_star_constL2 (c : ℂ) : star (constL2 c) = constL2 (conj c) := by
  apply Lp.ext
  have hc : constL2 c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  have hcc : constL2 (conj c) =ᵐ[circleMeasure] fun _ => conj c := (memLp_const (conj c)).coeFn_toLp
  filter_upwards [Lp.coeFn_star (constL2 c),hc,hcc] with t hs hc hcc
  change (star (constL2 c)) t = star (constL2 c t) at hs
  rw [hs,hc,hcc]
  rfl

/-- Generic Schatten splitting now follows from the proved scalar ambiguity and actual ideal algebra. -/
theorem scalarSplit : ScalarSplitObligation := by
  intro u hu hn φ ψ p A hA hsA
  constructor
  · rintro ⟨α,β,X,Y,hX,hY,hsX,_hsY,hAeq⟩
    have he : SameTTO u (splitSymbol φ.val ψ.val) (splitSymbol α.val β.val) := by
      intro f g hf hg
      have hh := (represents_add u α.val (star β.val) X Y hX hY) f g hf hg
      rw [← hAeq] at hh
      exact (hA f g hf hg).symm.trans hh
    obtain ⟨c,hc,_⟩ := scalarAmbiguity u hu hn φ α ψ β he
    refine ⟨c,X+c • ContinuousLinearMap.id ℂ _,?_,?_⟩
    · convert represents_add u α.val (φ.val-α.val) X (c • ContinuousLinearMap.id ℂ _) hX hc using 1; abel
    · rw [show X+c • ContinuousLinearMap.id ℂ (Model u)-c • ContinuousLinearMap.id ℂ (Model u) = X by abel]
      exact hsX
  · rintro ⟨c,X,hX,hsX⟩
    let α : Hardy := ⟨φ.val-constL2 c,hardy.sub_mem φ.property (constantCoreLaws.hardy c)⟩
    let β : Hardy := ⟨ψ.val+constL2 (conj c),hardy.add_mem ψ.property (constantCoreLaws.hardy _)⟩
    let X' := X-c • ContinuousLinearMap.id ℂ (Model u)
    let Y' := A-X'
    have hX' : RepresentsTTO u α.val X' :=
      represents_sub u φ.val (constL2 c) X _ hX (constantCoreLaws.represents u c)
    have hY0 : RepresentsTTO u (star ψ.val) (A-X) := by
      convert represents_sub u (splitSymbol φ.val ψ.val) φ.val A X hA hX using 1
      unfold splitSymbol
      abel
    have hY' : RepresentsTTO u (star β.val) Y' := by
      have hh := represents_add u (star ψ.val) (constL2 c) (A-X) (c • ContinuousLinearMap.id ℂ _)
        hY0 (constantCoreLaws.represents u c)
      change RepresentsTTO u (star (ψ.val+constL2 (conj c))) (A-(X-c • ContinuousLinearMap.id ℂ _))
      rw [boundary_star_add,boundary_star_constL2,Complex.conj_conj]
      convert hh using 1; abel
    have hsY := schatten_add hsA (schatten_neg hsX)
    have hy : Y' = A+ -(X-c • ContinuousLinearMap.id ℂ (Model u)) := by dsimp [Y',X']; abel
    rw [← hy] at hsY
    exact ⟨α,β,X',Y',hX',hY',hsX,hsY,by dsimp [Y']; abel⟩

end ScalarAmbiguity

section CanonicalSymbols

/-- Native L² complex conjugation reverses and conjugates the full Fourier spectrum. -/
theorem fourierCoeff_star_L2 (f : BoundaryL2) (n : ℤ) :
    fourierCoeff (star f : BoundaryL2) n = conj (fourierCoeff f (-n)) := by
  rw [fourierCoeff,fourierCoeff,← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with t ht
  change (star f) t = star (f t) at ht
  rw [ht]
  simp only [smul_eq_mul,Complex.star_def,map_mul,fourier_neg,neg_neg]

/-- Conjugating a negative Hardy vector gives a genuine positive Hardy vector. -/
theorem star_negative_mem_hardy (f : ↥hardy.orthogonal) : star f.val ∈ hardy := by
  apply (mem_hardy_iff _).mpr
  intro n hn
  rw [fourierCoeff_star_L2]
  obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
  rw [hk,(mem_hardy_orthogonal_iff _).mp f.property k,map_zero]

/-- Every literal L² symbol decomposes into analytic and coanalytic Hardy vectors. -/
theorem hardy_symbol_decomposition (σ : BoundaryL2) :
    ∃ φ ψ : Hardy, σ = φ.val+star ψ.val := by
  let φ : Hardy := hardy.orthogonalProjectionOnto σ
  let v : ↥hardy.orthogonal := ⟨σ-φ.val,hardy.sub_starProjection_mem_orthogonal σ⟩
  let ψ : Hardy := ⟨star v.val,star_negative_mem_hardy v⟩
  refine ⟨φ,ψ,?_⟩
  change σ = φ.val+star (star (σ-φ.val))
  rw [star_star]
  abel

theorem sameTTO_star (u : BoundaryLInf) (σ τ : BoundaryL2) (h : SameTTO u σ τ) :
    SameTTO u (star σ) (star τ) := by
  intro f g hf hg
  rw [coreForm_star _ _ _ hf,coreForm_star _ _ _ hf,h g f hg hf]

/-- Model projection preserves an actual represented analytic core form. -/
theorem representsTTO_analytic_projection (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy)
    (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u φ.val A) :
    RepresentsTTO u (((model u).orthogonalProjectionOnto φ.val).val) A := by
  intro f g hf hg
  exact (hA f g hf hg).trans (sameTTO_analytic_projection u hu φ f g hf hg)

/-- Every L² core symbol has an actual pair of model-space symbols, before any bounded extension. -/
theorem model_symbol_pair (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2) :
    ∃ φ ψ : Model u, SameTTO u σ (splitSymbol φ.val ψ.val) := by
  obtain ⟨a,b,hσ⟩ := hardy_symbol_decomposition σ
  refine ⟨(model u).orthogonalProjectionOnto a.val,(model u).orthogonalProjectionOnto b.val,?_⟩
  have ha := sameTTO_analytic_projection u hu a
  have hb := sameTTO_star u b.val (((model u).orthogonalProjectionOnto b.val).val) (sameTTO_analytic_projection u hu b)
  intro f g hf hg
  rw [hσ,splitSymbol,coreForm_add _ _ _ _ hf,coreForm_add _ _ _ _ hf,ha f g hf hg,hb f g hf hg]

/-- A scalar analytic TTO has exactly the scalar multiple of the actual origin model kernel. -/
theorem modelProjection_of_scalar (u : BoundaryLInf) (hu : IsInner u) (φ : Hardy) (c : ℂ)
    (hA : RepresentsTTO u φ.val (c • ContinuousLinearMap.id ℂ (Model u))) :
    (model u).orthogonalProjectionOnto φ.val = c • modelReproducingKernel u hu origin := by
  have hm : multiply (mode (0 : ℤ)) φ.val = φ.val := by
    apply Lp.ext
    filter_upwards [multiply_ae (mode 0) φ.val,mode_ae 0] with t hm hz
    rw [hm,hz]
    simp only [fourier_zero,one_mul]
  have he : (model u).orthogonalProjectionOnto (fourierBasis (T := 1) (0 : ℤ)) =
      modelReproducingKernel u hu origin := by
    have hc := modelProjection_constL2 u hu 1
    rw [constL2_fourier,one_smul,one_smul] at hc
    exact hc
  have hv := analyticTTO_modelPolynomial_value u hu φ (c • ContinuousLinearMap.id ℂ _) hA 0
  change c • ((model u).orthogonalProjectionOnto (fourierBasis (T := 1) (0 : ℤ))) =
    (model u).orthogonalProjectionOnto (multiply (mode (0 : ℤ)) φ.val) at hv
  rw [hm,he] at hv
  exact hv.symm

/-- The actual origin kernel, and all its scalar multiples, represent the scalar identity operator. -/
theorem represents_originKernel (u : BoundaryLInf) (hu : IsInner u) (c : ℂ) :
    RepresentsTTO u (c • (modelReproducingKernel u hu origin).val)
      (c • ContinuousLinearMap.id ℂ (Model u)) := by
  have h := representsTTO_analytic_projection u hu
    ⟨constL2 c,constantCoreLaws.hardy c⟩ _ (constantCoreLaws.represents u c)
  rw [modelProjection_constL2 u hu c] at h
  exact h


theorem coreForm_smul (c : ℂ) (σ f g : BoundaryL2) (hf : IsBounded f) :
    coreForm (c • σ) f g = c*coreForm σ f g := by
  rw [coreForm_eq_inner_left _ _ _ hf,map_smul,inner_smul_right,← coreForm_eq_inner_left _ _ _ hf]

theorem originKernel_value_ne_zero (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) :
    analyticValue (modelReproducingKernel u hu origin).val 0 ≠ 0 := by
  intro h
  have hi : inner ℂ (modelReproducingKernel u hu origin) (modelReproducingKernel u hu origin) = 0 :=
    (inner_modelReproducingKernel u hu origin _).trans h
  exact modelReproducingKernel_ne_zero u hu hn origin (inner_self_eq_zero.mp hi)

/-- The scalar correction of the two model symbols preserves every bounded core pairing. -/
theorem sameTTO_model_pair_shift (u : BoundaryLInf) (hu : IsInner u) (φ ψ : Model u) (a : ℂ) :
    let k := modelReproducingKernel u hu origin
    SameTTO u (splitSymbol φ.val ψ.val) (splitSymbol (φ+conj a • k).val (ψ-a • k).val) := by
  let k := modelReproducingKernel u hu origin
  change SameTTO u (splitSymbol φ.val ψ.val) (splitSymbol (φ+conj a • k).val (ψ-a • k).val)
  have hk : RepresentsTTO u k.val (ContinuousLinearMap.id ℂ _) := by
    simpa only [one_smul] using represents_originKernel u hu 1
  have hsk : RepresentsTTO u (star k.val) (ContinuousLinearMap.id ℂ _) := by
    have hh := represents_adjoint u k.val (ContinuousLinearMap.id ℂ _) hk
    rw [ContinuousLinearMap.adjoint_id] at hh
    exact hh
  have hsym : splitSymbol (φ+conj a • k).val (ψ-a • k).val =
      splitSymbol φ.val ψ.val+conj a • (k.val-star k.val) := by
    change φ.val+conj a • k.val+star (ψ.val-a • k.val) =
      φ.val+star ψ.val+conj a • (k.val-star k.val)
    rw [boundary_star_sub,boundary_star_smul,smul_sub]
    simp only [Complex.star_def]
    abel
  intro f g hf hg
  have hz := represents_sub u k.val (star k.val) (ContinuousLinearMap.id ℂ _) (ContinuousLinearMap.id ℂ _) hk hsk f g hf hg
  change inner ℂ g (f-f) = coreForm (k.val-star k.val) f.val g.val at hz
  rw [sub_self,inner_zero_right] at hz
  rw [hsym,coreForm_add _ _ _ _ hf,coreForm_smul _ _ _ _ hf,← hz,mul_zero,add_zero]

/-- Every L² symbol has a genuinely normalized canonical model pair on the entire bounded core. -/
theorem canonicalSymbols_exists (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (σ : BoundaryL2) :
    ∃ φ ψ : Model u, analyticValue ψ.val 0 = 0 ∧ SameTTO u σ (splitSymbol φ.val ψ.val) := by
  obtain ⟨φ,ψ,he⟩ := model_symbol_pair u hu σ
  let k := modelReproducingKernel u hu origin
  let a := analyticValue ψ.val 0/analyticValue k.val 0
  have hv : analyticValue k.val 0 ≠ 0 := originKernel_value_ne_zero u hu hn
  refine ⟨φ+conj a • k,ψ-a • k,?_,?_⟩
  · change analyticValue (ψ.val-a • k.val) 0 = 0
    rw [analyticValue_sub _ _ (by norm_num),analyticValue_smul _ _ (by norm_num)]
    dsimp [a]
    field_simp [hv]
    ring
  · intro f g hf hg
    exact (he f g hf hg).trans (sameTTO_model_pair_shift u hu φ ψ a f g hf hg)


theorem adjoint_scalar_identity (u : BoundaryLInf) (c : ℂ) :
    (c • ContinuousLinearMap.id ℂ (Model u)).adjoint = conj c • ContinuousLinearMap.id ℂ (Model u) := by
  rw [map_smulₛₗ,ContinuousLinearMap.adjoint_id]

/-- Normalized canonical model pairs are uniquely determined by their bounded core form. -/
theorem canonicalSymbols_unique (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (φ₁ ψ₁ φ₂ ψ₂ : Model u) (hψ₁ : analyticValue ψ₁.val 0 = 0) (hψ₂ : analyticValue ψ₂.val 0 = 0)
    (hsame : SameTTO u (splitSymbol φ₁.val ψ₁.val) (splitSymbol φ₂.val ψ₂.val)) :
    φ₁ = φ₂ ∧ ψ₁ = ψ₂ := by
  let k := modelReproducingKernel u hu origin
  obtain ⟨c,hφ,hψ⟩ := scalarAmbiguity u hu hn
    ⟨φ₁.val,φ₁.property.1⟩ ⟨φ₂.val,φ₂.property.1⟩ ⟨ψ₁.val,ψ₁.property.1⟩ ⟨ψ₂.val,ψ₂.property.1⟩ hsame
  have hψa : RepresentsTTO u (ψ₂.val-ψ₁.val) (conj c • ContinuousLinearMap.id ℂ _) := by
    have hh := represents_adjoint u (star ψ₂.val-star ψ₁.val) (c • ContinuousLinearMap.id ℂ _) hψ
    rw [boundary_star_sub,star_star,star_star,adjoint_scalar_identity] at hh
    exact hh
  have hpψ : ψ₂-ψ₁ = conj c • k := by
    have hh := modelProjection_of_scalar u hu
      ⟨ψ₂.val-ψ₁.val,hardy.sub_mem ψ₂.property.1 ψ₁.property.1⟩ (conj c) hψa
    change (model u).orthogonalProjectionOnto (ψ₂-ψ₁).val = conj c • k at hh
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hh
    exact hh
  have hpφ : φ₁-φ₂ = c • k := by
    have hh := modelProjection_of_scalar u hu
      ⟨φ₁.val-φ₂.val,hardy.sub_mem φ₁.property.1 φ₂.property.1⟩ c hφ
    change (model u).orthogonalProjectionOnto (φ₁-φ₂).val = c • k at hh
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hh
    exact hh
  have he := congrArg (fun f : Model u => analyticValue f.val 0) hpψ
  change analyticValue (ψ₂.val-ψ₁.val) 0 = analyticValue (conj c • k.val) 0 at he
  rw [analyticValue_sub _ _ (by norm_num),hψ₁,hψ₂,sub_self,analyticValue_smul _ _ (by norm_num)] at he
  have hcstar : conj c = 0 := (mul_eq_zero.mp he.symm).resolve_right (originKernel_value_ne_zero u hu hn)
  have hc : c = 0 := by simpa only [Complex.conj_conj,map_zero] using congrArg conj hcstar
  rw [hc,zero_smul] at hpφ
  rw [hcstar,zero_smul] at hpψ
  exact ⟨sub_eq_zero.mp hpφ,(sub_eq_zero.mp hpψ).symm⟩

/-- Complete existence and uniqueness of the normalized canonical symbols at core level. -/
theorem canonicalSymbols (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (σ : BoundaryL2) :
    ∃! pair : Model u × Model u,
      analyticValue pair.2.val 0 = 0 ∧ SameTTO u σ (splitSymbol pair.1.val pair.2.val) := by
  obtain ⟨φ,ψ,hψ,he⟩ := canonicalSymbols_exists u hu hn σ
  refine ⟨(φ,ψ),⟨hψ,he⟩,?_⟩
  rintro ⟨φ',ψ'⟩ ⟨hψ',he'⟩
  have hh : SameTTO u (splitSymbol φ'.val ψ'.val) (splitSymbol φ.val ψ.val) := by
    intro f g hf hg
    exact (he' f g hf hg).symm.trans (he f g hf hg)
  obtain ⟨hφ,hψeq⟩ := canonicalSymbols_unique u hu hn φ' ψ' φ ψ hψ' hψ hh
  exact Prod.ext hφ hψeq


/-- Every represented operator has exactly one normalized canonical pair in the literal model. -/
theorem canonicalSymbols_represents (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (σ : BoundaryL2) (A : Model u →L[ℂ] Model u) (hA : RepresentsTTO u σ A) :
    ∃! pair : Model u × Model u, analyticValue pair.2.val 0 = 0 ∧
      RepresentsTTO u (splitSymbol pair.1.val pair.2.val) A := by
  obtain ⟨φ,ψ,hψ,he⟩ := canonicalSymbols_exists u hu hn σ
  have hrep : RepresentsTTO u (splitSymbol φ.val ψ.val) A := by
    intro f g hf hg
    exact (hA f g hf hg).trans (he f g hf hg)
  refine ⟨(φ,ψ),⟨hψ,hrep⟩,?_⟩
  rintro ⟨φ',ψ'⟩ ⟨hψ',hrep'⟩
  have hh : SameTTO u (splitSymbol φ'.val ψ'.val) (splitSymbol φ.val ψ.val) := by
    intro f g hf hg
    exact (hrep' f g hf hg).symm.trans (hrep f g hf hg)
  obtain ⟨hφ,hψeq⟩ := canonicalSymbols_unique u hu hn φ' ψ' φ ψ hψ' hψ hh
  exact Prod.ext hφ hψeq

end CanonicalSymbols

section GluingModel

theorem toL2_multiplyInf (a b : BoundaryLInf) : toL2 (multiplyInf a b) = multiply a (toL2 b) := by
  apply Lp.ext
  filter_upwards [toL2_ae (multiplyInf a b),multiplyInf_ae a b,multiply_ae a (toL2 b),toL2_ae b]
    with t ht hi hm hb
  rw [ht,hi,hm,hb]

theorem toL2_constLInf (c : ℂ) : toL2 (constLInf c) = constL2 c := by
  apply Lp.ext
  have hi : constLInf c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  have h2 : constL2 c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  filter_upwards [toL2_ae (constLInf c),hi,h2] with t ht hi h2
  rw [ht,hi,h2]

theorem isInner_constLInf_one : IsInner (constLInf 1) := by
  refine ⟨?_,?_⟩
  · rw [toL2_constLInf]
    exact constantCoreLaws.hardy 1
  · have hi : constLInf 1 =ᵐ[circleMeasure] fun _ => 1 := (memLp_const (1 : ℂ)).coeFn_toLp
    filter_upwards [hi] with t ht
    rw [ht,norm_one]

theorem isInner_multiplyInf (u v : BoundaryLInf) (hu : IsInner u) (hv : IsInner v) :
    IsInner (multiplyInf u v) := by
  constructor
  · rw [toL2_multiplyInf]
    exact multiply_mem_hardy u hu.1 (toL2 v) hv.1
  · filter_upwards [multiplyInf_ae u v,hu.2,hv.2] with t hp hut hvt
    rw [hp,norm_mul,hut,hvt,one_mul]

theorem multiplyInf_comm (a b : BoundaryLInf) : multiplyInf a b = multiplyInf b a := by
  apply Lp.ext
  filter_upwards [multiplyInf_ae a b,multiplyInf_ae b a] with t hab hba
  rw [hab,hba,mul_comm]

/-- Actual multiplication by an inner factor embeds K_u into K_(vu), including v=1. -/
theorem multiply_model_mem_product (u v : BoundaryLInf) (hv : IsInner v) (f : Model u) :
    multiply v f.val ∈ model (multiplyInf v u) := by
  refine ⟨multiply_mem_hardy v hv.1 f.val f.property.1,(Submodule.mem_orthogonal' _ _).mpr ?_⟩
  intro g hg
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n,rfl⟩ := hy
    change inner ℂ (multiply v f.val) (multiply (multiplyInf v u) (fourierBasis (T := 1) (n : ℤ))) = 0
    rw [← multiply_assoc]
    change inner ℂ (innerMultiplyIsometry v hv f.val)
      (innerMultiplyIsometry v hv (multiply u (fourierBasis (T := 1) (n : ℤ)))) = 0
    rw [(innerMultiplyIsometry v hv).inner_map_map]
    exact (Submodule.mem_orthogonal' _ _).mp f.property.2 _ (Submodule.subset_span ⟨n,rfl⟩)
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]

def modelProductIsometry (u v : BoundaryLInf) (hv : IsInner v) : Model u →ₗᵢ[ℂ] Model (multiplyInf v u) where
  toLinearMap := LinearMap.codRestrict (model (multiplyInf v u))
    ((multiply v).toLinearMap.comp (model u).subtype) (multiply_model_mem_product u v hv)
  norm_map' f := (innerMultiplyIsometry v hv).norm_map f.val

/-- The essential two-factor projection identity uses genuine Hardy factorization. -/
theorem modelProjection_multiply_inner (u v : BoundaryLInf) (hu : IsInner u) (hv : IsInner v) (h : Hardy) :
    (model (multiplyInf v u)).orthogonalProjectionOnto (multiply v h.val) =
      modelProductIsometry u v hv ((model u).orthogonalProjectionOnto h.val) := by
  let Ph := (model u).orthogonalProjectionOnto h.val
  have hz : (model u).orthogonalProjectionOnto (h.val-Ph.val) = 0 := by
    rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  obtain ⟨q,hq⟩ := innerFactor_of_modelProjection_zero u hu
    ⟨h.val-Ph.val,hardy.sub_mem h.property Ph.property.1⟩ hz
  change h.val-Ph.val = multiply u q.val at hq
  apply Subtype.ext
  apply (model (multiplyInf v u)).eq_starProjection_of_mem_orthogonal (multiply_model_mem_product u v hv Ph)
  change multiply v h.val-multiply v Ph.val ∈ (model (multiplyInf v u)).orthogonal
  rw [← map_sub,hq,multiply_assoc]
  exact (model (multiplyInf v u)).orthogonalProjectionOnto_eq_zero_iff.mp
    (modelProjection_multiply_hardy_zero (multiplyInf v u) q)

/-- Bounded analytic multipliers commute with model projection after projecting the output. -/
theorem modelProjection_analytic_multiply (u : BoundaryLInf) (hu : IsInner u)
    (a : BoundaryLInf) (ha : toL2 a ∈ hardy) (h : Hardy) :
    (model u).orthogonalProjectionOnto (multiply a (((model u).orthogonalProjectionOnto h.val).val)) =
      (model u).orthogonalProjectionOnto (multiply a h.val) := by
  let Ph := (model u).orthogonalProjectionOnto h.val
  have hz : (model u).orthogonalProjectionOnto (h.val-Ph.val) = 0 := by
    rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  obtain ⟨q,hq⟩ := innerFactor_of_modelProjection_zero u hu
    ⟨h.val-Ph.val,hardy.sub_mem h.property Ph.property.1⟩ hz
  change h.val-Ph.val = multiply u q.val at hq
  have he : (model u).orthogonalProjectionOnto (multiply a (h.val-Ph.val)) = 0 := by
    rw [hq,multiply_comm]
    exact modelProjection_multiply_hardy_zero u ⟨multiply a q.val,multiply_mem_hardy a ha q.val q.property⟩
  rw [map_sub,map_sub] at he
  exact (sub_eq_zero.mp he).symm

/-- A core value at a bounded input is exactly its actual compressed L² product. -/
theorem coreValue_iff_projection (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2)
    (f y : Model u) (hf : IsBounded f.val) :
    CoreValue u σ f y ↔ y = (model u).orthogonalProjectionOnto (coreMultiply σ ⟨f.val,hf⟩) := by
  constructor
  · intro hy
    apply (bounded_modelCore_dense u hu).eq_of_inner_right ℂ
    intro g hg
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact (hy g hg).trans (coreForm_eq_inner_left σ f.val g.val hf)
  · intro hy
    subst y
    intro g _hg
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact (coreForm_eq_inner_left σ f.val g.val hf).symm


/-- The Holder fold has precisely the ordinary pointwise finite product representative. -/
theorem listProduct_ae (l : List BoundaryLInf) :
    l.foldr multiplyInf (constLInf 1) =ᵐ[circleMeasure] fun t => (l.map (fun a => a t)).prod := by
  induction l with
  | nil => exact (memLp_const (1 : ℂ)).coeFn_toLp
  | cons a l ih =>
    filter_upwards [multiplyInf_ae a (l.foldr multiplyInf (constLInf 1)),ih] with t hp hl
    change multiplyInf a (l.foldr multiplyInf (constLInf 1)) t = a t*(l.map (fun b => b t)).prod
    rw [hp,hl]

theorem finiteProduct_ae {m : ℕ} (u : Fin m → BoundaryLInf) :
    finiteProduct u =ᵐ[circleMeasure] fun t => ∏ j, u j t := by
  have h := listProduct_ae (List.ofFn u)
  simpa only [finiteProduct,List.map_ofFn,List.prod_ofFn,Function.comp_apply] using h

theorem isInner_listProduct (l : List BoundaryLInf) (hl : ∀ a ∈ l, IsInner a) :
    IsInner (l.foldr multiplyInf (constLInf 1)) := by
  induction l with
  | nil => exact isInner_constLInf_one
  | cons a l ih =>
    apply isInner_multiplyInf
    · exact hl a (by simp)
    · exact ih (fun b hb => hl b (by simp [hb]))

theorem isInner_finiteProduct {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) :
    IsInner (finiteProduct u) := by
  apply isInner_listProduct
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  exact hu j

theorem isInner_cofactor {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) (i : Fin m) :
    IsInner (cofactor u i) := by
  apply isInner_finiteProduct
  intro j
  split_ifs
  · exact isInner_constLInf_one
  · exact hu j

/-- Literal cofactor boundary values, retaining the empty complementary product. -/
theorem cofactor_ae {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) :
    cofactor u j =ᵐ[circleMeasure] fun t => ∏ k, if k = j then 1 else u k t := by
  have h := finiteProduct_ae (fun k => if k = j then constLInf 1 else u k)
  have h1 : constLInf 1 =ᵐ[circleMeasure] fun _ => 1 := (memLp_const (1 : ℂ)).coeFn_toLp
  filter_upwards [h,h1] with t hp h1
  change finiteProduct (fun k => if k = j then constLInf 1 else u k) t = _
  rw [hp]
  apply Finset.prod_congr rfl
  intro k _hk
  split_ifs with hkj
  · exact h1
  · rfl

/-- The explicit finite product equals the actual factor times its actual cofactor. -/
theorem finiteProduct_factor {m : ℕ} (u : Fin m → BoundaryLInf) (j : Fin m) :
    multiplyInf (cofactor u j) (u j) = finiteProduct u := by
  classical
  apply Lp.ext
  filter_upwards [multiplyInf_ae (cofactor u j) (u j),cofactor_ae u j,finiteProduct_ae u]
    with t hm hc hp
  rw [hm,hc,hp]
  have hcut : (∏ k, if k = j then 1 else u k t) = ∏ k ∈ Finset.univ.erase j, u k t := by
    rw [← Finset.prod_erase_mul Finset.univ (fun k => if k = j then 1 else u k t) (Finset.mem_univ j)]
    simp only [ite_true,mul_one]
    apply Finset.prod_congr rfl
    intro k hk
    rw [ite_eq_right (Finset.mem_erase.mp hk).1]
  rw [hcut]
  exact Finset.prod_erase_mul Finset.univ (fun k => u k t) (Finset.mem_univ j)

/-- Distinct cofactors have the required genuine bounded analytic inner divisor. -/
theorem cofactor_divisible {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (i j : Fin m) (hij : i ≠ j) :
    ∃ b : BoundaryLInf, IsInner b ∧ cofactor u j = multiplyInf (u i) b := by
  let v : Fin m → BoundaryLInf := fun k => if k = j then constLInf 1 else u k
  have hv : ∀ k, IsInner (v k) := by
    intro k
    dsimp [v]
    split_ifs
    · exact isInner_constLInf_one
    · exact hu k
  refine ⟨cofactor v i,isInner_cofactor v hv i,?_⟩
  have he := finiteProduct_factor v i
  have hvi : v i = u i := by simp [v,hij]
  change multiplyInf (cofactor v i) (v i) = cofactor u j at he
  rw [hvi,multiplyInf_comm] at he
  exact he.symm


/-- The interior Bézout identity acts as a literal equality on every native Hardy vector. -/
theorem bezout_action {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (h : Hardy) :
    (∑ j, multiply (cofactor u j) (multiply (a j) h.val)) = h.val := by
  let y : Hardy := ∑ j, hardyMultiply (cofactor u j) (isInner_cofactor u hu j).1 (hardyMultiply (a j) (ha.1 j) h)
  have he : y = h := by
    apply hardy_analyticValue_injective
    intro z hz
    let w : Disk := ⟨z,hz⟩
    calc
      analyticValue y.val z = ∑ j, innerValue (cofactor u j) z*(innerValue (a j) z*analyticValue h.val z) := by
        change hardyEvaluation w y = _
        dsimp only [y]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hardyEvaluation_apply,hardyMultiply_apply,
          analyticValue_multiply (cofactor u j) (isInner_cofactor u hu j).1 (hardyMultiply (a j) (ha.1 j) h) w,
          hardyMultiply_apply,analyticValue_multiply (a j) (ha.1 j) h w]
      _ = (∑ j, innerValue (a j) z*innerValue (cofactor u j) z)*analyticValue h.val z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = analyticValue h.val z := by rw [ha.2 z hz,one_mul]
  simpa only [y,Submodule.coe_sum,hardyMultiply_apply] using congrArg Subtype.val he

theorem cofactor_model_mem {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (j : Fin m) (f : Model (u j)) : multiply (cofactor u j) f.val ∈ model (finiteProduct u) := by
  rw [← finiteProduct_factor u j]
  exact multiply_model_mem_product (u j) (cofactor u j) (isInner_cofactor u hu j) f

/-- The actual bounded cofactor embedding of the jth model into the product model. -/
def cofactorInclusion {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) (j : Fin m) :
    Model (u j) →L[ℂ] Model (finiteProduct u) :=
  (multiply (cofactor u j) ∘L (model (u j)).subtypeL).codRestrict (model (finiteProduct u)) (cofactor_model_mem u hu j)

@[simp] theorem cofactorInclusion_apply {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (j : Fin m) (f : Model (u j)) : (cofactorInclusion u hu j f).val = multiply (cofactor u j) f.val := rfl

theorem modelProjection_cofactor {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (j : Fin m) (h : Hardy) :
    (model (finiteProduct u)).orthogonalProjectionOnto (multiply (cofactor u j) h.val) =
      cofactorInclusion u hu j ((model (u j)).orthogonalProjectionOnto h.val) := by
  have he := congrArg Subtype.val (modelProjection_multiply_inner (u j) (cofactor u j)
    (hu j) (isInner_cofactor u hu j) h)
  change (model (multiplyInf (cofactor u j) (u j))).starProjection (multiply (cofactor u j) h.val) =
    multiply (cofactor u j) (((model (u j)).orthogonalProjectionOnto h.val).val) at he
  rw [finiteProduct_factor] at he
  exact Subtype.ext he

/-- Native bounded forward and inverse candidates of the paper's finite gluing map. -/
def gluingForward {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) :
    FiniteModelSum u →L[ℂ] Model (finiteProduct u) :=
  ∑ j, cofactorInclusion u hu j ∘L PiLp.proj 2 (fun i => Model (u i)) j

def gluingBackward {m : ℕ} (u a : Fin m → BoundaryLInf) :
    Model (finiteProduct u) →L[ℂ] FiniteModelSum u :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun i => Model (u i))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => (model (u j)).orthogonalProjectionOnto ∘L
      multiply (a j) ∘L (model (finiteProduct u)).subtypeL)

@[simp] theorem gluingForward_apply {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (g : FiniteModelSum u) : (gluingForward u hu g).val = ∑ j, multiply (cofactor u j) (g j).val := by
  rw [gluingForward,sum_apply,Submodule.coe_sum]
  simp only [ContinuousLinearMap.comp_apply,cofactorInclusion_apply,PiLp.proj_apply]

@[simp] theorem gluingBackward_apply {m : ℕ} (u a : Fin m → BoundaryLInf)
    (x : Model (finiteProduct u)) (j : Fin m) :
    gluingBackward u a x j = (model (u j)).orthogonalProjectionOnto (multiply (a j) x.val) := rfl


theorem modelProjection_cofactor_cross {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (i j : Fin m) (hij : i ≠ j) (h : Hardy) :
    (model (u i)).orthogonalProjectionOnto (multiply (cofactor u j) h.val) = 0 := by
  obtain ⟨b,hb,he⟩ := cofactor_divisible u hu i j hij
  rw [he,← multiply_assoc]
  exact modelProjection_multiply_hardy_zero (u i) ⟨multiply b h.val,multiply_mem_hardy b hb.1 h.val h.property⟩

/-- The diagonal Bézout term is the actual identity on its own model space. -/
theorem modelProjection_bezout_diagonal {m : ℕ} (u a : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (ha : Bezout u a) (i : Fin m) (f : Model (u i)) :
    (model (u i)).orthogonalProjectionOnto (multiply (a i) (multiply (cofactor u i) f.val)) = f := by
  have hh := congrArg (model (u i)).orthogonalProjectionOnto
    (bezout_action u a hu ha ⟨f.val,f.property.1⟩)
  rw [map_sum,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hh
  have hsum : (∑ j, (model (u i)).orthogonalProjectionOnto (multiply (cofactor u j) (multiply (a j) f.val))) =
      (model (u i)).orthogonalProjectionOnto (multiply (cofactor u i) (multiply (a i) f.val)) := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      exact modelProjection_cofactor_cross u hu i j hji.symm
        ⟨multiply (a j) f.val,multiply_mem_hardy (a j) (ha.1 j) f.val f.property.1⟩
    · simp
  rw [hsum] at hh
  rw [multiply_comm]
  exact hh

/-- The explicit inverse candidates satisfy F(Gx)=x on the entire product model. -/
theorem gluingForward_backward {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) : Function.RightInverse (gluingBackward u a) (gluingForward u hu) := by
  intro x
  apply Subtype.ext
  rw [gluingForward_apply]
  simp_rw [gluingBackward_apply]
  calc
    _ = ∑ j, (((model (finiteProduct u)).orthogonalProjectionOnto
        (multiply (cofactor u j) (multiply (a j) x.val))).val) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (congrArg Subtype.val (modelProjection_cofactor u hu j
        ⟨multiply (a j) x.val,multiply_mem_hardy (a j) (ha.1 j) x.val x.property.1⟩)).symm
    _ = ((model (finiteProduct u)).orthogonalProjectionOnto
        (∑ j, multiply (cofactor u j) (multiply (a j) x.val))).val := by rw [map_sum,Submodule.coe_sum]
    _ = ((model (finiteProduct u)).orthogonalProjectionOnto x.val).val := by
      rw [bezout_action u a hu ha ⟨x.val,x.property.1⟩]
    _ = x.val := congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x)

/-- The explicit inverse candidates satisfy G(Fg)=g in the native finite Hilbert sum. -/
theorem gluingBackward_forward {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) : Function.LeftInverse (gluingBackward u a) (gluingForward u hu) := by
  intro g
  apply PiLp.ext
  intro i
  rw [gluingBackward_apply,gluingForward_apply,map_sum,map_sum]
  rw [Finset.sum_eq_single i]
  · exact modelProjection_bezout_diagonal u a hu ha i (g i)
  · intro j _hj hji
    rw [multiply_comm]
    exact modelProjection_cofactor_cross u hu i j hji.symm
      ⟨multiply (a i) (g j).val,multiply_mem_hardy (a i) (ha.1 i) (g j).val (g j).property.1⟩
  · simp

/-- The paper's W, with its actual native bounded inverse and explicit Bézout functions. -/
def gluingEquiv {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) (ha : Bezout u a) :
    FiniteModelSum u ≃L[ℂ] Model (finiteProduct u) :=
  ContinuousLinearEquiv.equivOfInverse (gluingForward u hu) (gluingBackward u a)
    (gluingBackward_forward u a hu ha) (gluingForward_backward u a hu ha)

@[simp] theorem gluingEquiv_apply {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (g : FiniteModelSum u) : gluingEquiv u a hu ha g = gluingForward u hu g := rfl

@[simp] theorem gluingEquiv_symm_apply {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (x : Model (finiteProduct u)) : (gluingEquiv u a hu ha).symm x = gluingBackward u a x := rfl


theorem gluingForward_bounded {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (g : FiniteModelSum u) (hg : ∀ j, IsBounded (g j).val) : IsBounded (gluingForward u hu g).val := by
  rw [gluingForward_apply]
  exact boundedL2.sum_mem (fun j _hj => bounded_multiply _ _ (hg j))

theorem coreMultiply_mem_hardy (γ f : Hardy) (hf : IsBounded f.val) :
    coreMultiply γ.val ⟨f.val,hf⟩ ∈ hardy := by
  let a : BoundaryLInf := hf.toLp f.val
  have he : toL2 a = f.val := Lp.ext ((toL2_ae a).trans hf.coeFn_toLp)
  exact multiply_mem_hardy a (he.symm ▸ f.property) γ.val γ.property

/-- Finite bounded core multiplication commutes with the actual cofactor sum. -/
theorem gluingForward_coreMultiply {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (γ : BoundaryL2) (g : FiniteModelSum u) (hg : ∀ j, IsBounded (g j).val) :
    coreMultiply γ ⟨(gluingForward u hu g).val,gluingForward_bounded u hu g hg⟩ =
      ∑ j, multiply (cofactor u j) (coreMultiply γ ⟨(g j).val,hg j⟩) := by
  let b (j : Fin m) : boundedL2 := ⟨multiply (cofactor u j) (g j).val,bounded_multiply _ _ (hg j)⟩
  have he : (⟨(gluingForward u hu g).val,gluingForward_bounded u hu g hg⟩ : boundedL2) = ∑ j, b j := by
    apply Subtype.ext
    rw [Submodule.coe_sum,gluingForward_apply]
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact coreMultiply_multiply γ (cofactor u j) (g j).val (hg j)

/-- The raw analytic core identity, with actual local and global L² projected products. -/
theorem gluingEquiv_core {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (γ : Hardy) (g : FiniteModelSum u) (hg : ∀ j, IsBounded (g j).val) :
    IsBounded (gluingEquiv u a hu ha g).val ∧ ∃ y : FiniteModelSum u,
      (∀ j, CoreValue (u j) γ.val (g j) (y j)) ∧
      CoreValue (finiteProduct u) γ.val (gluingEquiv u a hu ha g) (gluingEquiv u a hu ha y) := by
  let y : FiniteModelSum u := WithLp.toLp 2 (fun j =>
    (model (u j)).orthogonalProjectionOnto (coreMultiply γ.val ⟨(g j).val,hg j⟩))
  have hb : IsBounded (gluingEquiv u a hu ha g).val := gluingForward_bounded u hu g hg
  refine ⟨hb,y,fun j => (coreValue_iff_projection (u j) (hu j) γ.val (g j) (y j) (hg j)).mpr rfl,?_⟩
  apply (coreValue_iff_projection (finiteProduct u) (isInner_finiteProduct u hu) γ.val _ _ hb).mpr
  apply Subtype.ext
  rw [gluingEquiv_apply,gluingForward_apply]
  calc
    _ = ∑ j, (((model (finiteProduct u)).orthogonalProjectionOnto
        (multiply (cofactor u j) (coreMultiply γ.val ⟨(g j).val,hg j⟩))).val) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact (congrArg Subtype.val (modelProjection_cofactor u hu j
        ⟨coreMultiply γ.val ⟨(g j).val,hg j⟩,coreMultiply_mem_hardy γ ⟨(g j).val,(g j).property.1⟩ (hg j)⟩)).symm
    _ = ((model (finiteProduct u)).orthogonalProjectionOnto
        (∑ j, multiply (cofactor u j) (coreMultiply γ.val ⟨(g j).val,hg j⟩))).val := by rw [map_sum,Submodule.coe_sum]
    _ = _ := congrArg (fun f => (((model (finiteProduct u)).orthogonalProjectionOnto f).val))
      (gluingForward_coreMultiply u hu γ.val g hg).symm

/-- Actual bounded local cores are dense in the native finite Hilbert sum. -/
theorem bounded_finiteModelSum_dense {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) :
    Dense {g : FiniteModelSum u | ∀ j, IsBounded (g j).val} := by
  let E := PiLp.continuousLinearEquiv 2 ℂ (fun j => Model (u j))
  let S : Set ((j : Fin m) → Model (u j)) := {f | ∀ j, IsBounded (f j).val}
  have hd : Dense S := by
    have hh := dense_pi Set.univ (fun j _hj => bounded_modelCore_dense (u j) (hu j))
    have hs : Set.univ.pi (fun j => {f : Model (u j) | IsBounded f.val}) = S := by ext f; simp [S]
    rw [hs] at hh
    exact hh
  have hi := E.symm.surjective.denseRange.dense_image E.symm.continuous hd
  have he : E.symm '' S = {g : FiniteModelSum u | ∀ j, IsBounded (g j).val} := by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact hf
    · intro hg
      exact ⟨E g,hg,E.symm_apply_apply g⟩
  rwa [he] at hi

theorem gluingEquiv_dense {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) (ha : Bezout u a) :
    Dense ((gluingEquiv u a hu ha) '' {g : FiniteModelSum u | ∀ j, IsBounded (g j).val}) :=
  (gluingEquiv u a hu ha).surjective.denseRange.dense_image (gluingEquiv u a hu ha).continuous
    (bounded_finiteModelSum_dense u hu)


theorem coreValue_unique (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2) (f y z : Model u)
    (hy : CoreValue u σ f y) (hz : CoreValue u σ f z) : y = z :=
  (bounded_modelCore_dense u hu).eq_of_inner_right ℂ (fun g hg => (hy g hg).trans (hz g hg).symm)

theorem coreValue_zero (u : BoundaryLInf) (hu : IsInner u) (σ : BoundaryL2) :
    CoreValue u σ (0 : Model u) (0 : Model u) := by
  apply (coreValue_iff_projection u hu σ 0 0 boundedL2.zero_mem).mpr
  change (0 : Model u) = (model u).orthogonalProjectionOnto (coreMultiply σ (0 : boundedL2))
  rw [map_zero,map_zero]

theorem bounded_finiteSingle {m : ℕ} (u : Fin m → BoundaryLInf) (i : Fin m) (f : Model (u i))
    (hf : IsBounded f.val) : ∀ j, IsBounded (finiteSingle (fun k => Model (u k)) i f j).val := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [finiteSingle_apply,Pi.single_eq_same] using hf
  · rw [finiteSingle_apply,Pi.single_eq_of_ne hji]
    exact boundedL2.zero_mem

/-- The true global core value on a single coordinate gives both the local core and its intertwining. -/
theorem gluingEquiv_single_core {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (γ : Hardy) (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hA : RepresentsTTO (finiteProduct u) γ.val A) (i : Fin m) (f : Model (u i)) (hf : IsBounded f.val) :
    CoreValue (u i) γ.val f (localBlock (gluingEquiv u a hu ha) A i f) ∧
      A (gluingEquiv u a hu ha (finiteSingle (fun j => Model (u j)) i f)) =
        gluingEquiv u a hu ha (finiteSingle (fun j => Model (u j)) i (localBlock (gluingEquiv u a hu ha) A i f)) := by
  let W := gluingEquiv u a hu ha
  obtain ⟨hb,y,hy,hglob⟩ := gluingEquiv_core u a hu ha γ
    (finiteSingle (fun j => Model (u j)) i f) (bounded_finiteSingle u i f hf)
  have hy0 (j : Fin m) (hji : j ≠ i) : y j = 0 := by
    apply coreValue_unique (u j) (hu j) γ.val 0 (y j) 0 _ (coreValue_zero (u j) (hu j) γ.val)
    simpa only [finiteSingle_apply,Pi.single_eq_of_ne hji] using hy j
  have hyeq : y = finiteSingle (fun j => Model (u j)) i (y i) := by
    apply PiLp.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp only [finiteSingle_apply,Pi.single_eq_same]
    · rw [finiteSingle_apply,Pi.single_eq_of_ne hji]
      exact hy0 j hji
  have hval : A (W (finiteSingle (fun j => Model (u j)) i f)) = W y :=
    coreValue_unique (finiteProduct u) (isInner_finiteProduct u hu) γ.val _ _ _
      (fun g hg => hA _ g hb hg) hglob
  rw [hyeq] at hval
  have hlocal : localBlock W A i f = y i := by
    change W.symm (A (W (finiteSingle (fun j => Model (u j)) i f))) i = y i
    rw [hval,W.symm_apply_apply]
    simp only [finiteSingle_apply,Pi.single_eq_same]
  constructor
  · change CoreValue (u i) γ.val f (localBlock W A i f)
    rw [hlocal]
    simpa only [finiteSingle_apply,Pi.single_eq_same] using hy i
  · change A (W (finiteSingle (fun j => Model (u j)) i f)) = W (finiteSingle (fun j => Model (u j)) i (localBlock W A i f))
    rw [hlocal]
    exact hval

/-- Every local diagonal block has the actual symbol on all its bounded core tests. -/
theorem gluingEquiv_local_coeff {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (γ : Hardy) (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hA : RepresentsTTO (finiteProduct u) γ.val A) (j : Fin m) (f g : Model (u j))
    (hf : IsBounded f.val) (hg : IsBounded g.val) :
    inner ℂ g (localBlock (gluingEquiv u a hu ha) A j f) = coreForm γ.val f.val g.val :=
  (gluingEquiv_single_core u a hu ha γ A hA j f hf).1 g hg


/-- The bounded global operator is diagonally intertwined on the whole finite Hilbert sum. -/
theorem gluingEquiv_diagonal {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (γ : Hardy) (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hA : RepresentsTTO (finiteProduct u) γ.val A) (g : FiniteModelSum u) :
    A (gluingEquiv u a hu ha g) = gluingEquiv u a hu ha
      (WithLp.toLp 2 (fun j => localBlock (gluingEquiv u a hu ha) A j (g j))) := by
  let W := gluingEquiv u a hu ha
  have hsingle (j : Fin m) (f : Model (u j)) :
      A (W (finiteSingle (fun i => Model (u i)) j f)) =
        W (finiteSingle (fun i => Model (u i)) j (localBlock W A j f)) := by
    let L := A ∘L W.toContinuousLinearMap ∘L finiteSingle (fun i => Model (u i)) j
    let R := W.toContinuousLinearMap ∘L finiteSingle (fun i => Model (u i)) j ∘L localBlock W A j
    have he : (fun f => L f) = (fun f => R f) :=
      Continuous.ext_on (bounded_modelCore_dense (u j) (hu j)) L.continuous R.continuous
        (fun f hf => (gluingEquiv_single_core u a hu ha γ A hA j f hf).2)
    exact congrFun he f
  let d : FiniteModelSum u := WithLp.toLp 2 (fun j => localBlock W A j (g j))
  change A (W g) = W d
  calc
    _ = A (W (∑ j, finiteSingle (fun i => Model (u i)) j (g j))) := by rw [finiteSingle_sum]
    _ = ∑ j, A (W (finiteSingle (fun i => Model (u i)) j (g j))) := by rw [map_sum,map_sum]
    _ = ∑ j, W (finiteSingle (fun i => Model (u i)) j (localBlock W A j (g j))) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hsingle j (g j)
    _ = W d := by rw [← map_sum]; exact congrArg W (finiteSingle_sum d)

/-- Reconstructed local bounded operators have precisely the global analytic core form. -/
theorem gluingEquiv_global_coeff {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (γ : Hardy) (T : (j : Fin m) → Model (u j) →L[ℂ] Model (u j))
    (hT : ∀ j, RepresentsTTO (u j) γ.val (T j)) (g h : FiniteModelSum u)
    (hg : ∀ j, IsBounded (g j).val) (hh : ∀ j, IsBounded (h j).val) :
    inner ℂ (gluingEquiv u a hu ha h) (gluingEquiv u a hu ha (finiteDiagonal T g)) =
      coreForm γ.val (gluingEquiv u a hu ha g).val (gluingEquiv u a hu ha h).val := by
  let W := gluingEquiv u a hu ha
  obtain ⟨_hb,y,hy,hglob⟩ := gluingEquiv_core u a hu ha γ g hg
  have he : y = finiteDiagonal T g := by
    apply PiLp.ext
    intro j
    change y j = T j (g j)
    exact coreValue_unique (u j) (hu j) γ.val (g j) _ _ (hy j)
      (fun f hf => hT j (g j) f (hg j) hf)
  rw [← he]
  exact hglob (W h) (gluingForward_bounded u hu h hh)


/-- A cofactor Bézout symbol has exactly the indicated zero/identity local compression. -/
theorem boundedSymbolOperator_cofactor {m : ℕ} (u a : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (ha : Bezout u a) (i j : Fin m) :
    boundedSymbolOperator (u i) (multiplyInf (a j) (cofactor u j)) =
      if i = j then ContinuousLinearMap.id ℂ (Model (u i)) else 0 := by
  split_ifs with hij
  · subst j
    apply ContinuousLinearMap.ext
    intro f
    change (model (u i)).orthogonalProjectionOnto (multiply (multiplyInf (a i) (cofactor u i)) f.val) = f
    rw [← multiply_assoc]
    exact modelProjection_bezout_diagonal u a hu ha i f
  · apply ContinuousLinearMap.ext
    intro f
    change (model (u i)).orthogonalProjectionOnto (multiply (multiplyInf (a j) (cofactor u j)) f.val) = 0
    rw [← multiply_assoc,multiply_comm]
    exact modelProjection_cofactor_cross u hu i j hij
      ⟨multiply (a j) f.val,multiply_mem_hardy (a j) (ha.1 j) f.val f.property.1⟩

/-- The coordinate idempotent has its actual analytic Bézout symbol, independently of the chosen witness. -/
theorem gluingEquiv_coordinate_symbol {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (a' : Fin m → BoundaryLInf) (ha' : Bezout u a') (j : Fin m) :
    RepresentsTTO (finiteProduct u) (toL2 (multiplyInf (a' j) (cofactor u j)))
      (coordinateResolution (gluingEquiv u a hu ha) j) := by
  let W := gluingEquiv u a hu ha
  let β := multiplyInf (a' j) (cofactor u j)
  have hβ : toL2 β ∈ hardy := by
    rw [toL2_multiplyInf]
    exact multiply_mem_hardy (a' j) (ha'.1 j) _ (isInner_cofactor u hu j).1
  let γ : Hardy := ⟨toL2 β,hβ⟩
  let A := boundedSymbolOperator (finiteProduct u) β
  have hA : RepresentsTTO (finiteProduct u) γ.val A := boundedSymbolOperator_represents _ β
  have hblock (i : Fin m) : localBlock W A i = if i = j then ContinuousLinearMap.id ℂ (Model (u i)) else 0 := by
    apply represents_unique_of_dense (u i) (bounded_modelCore_dense (u i) (hu i)) γ.val
    · intro f g hf hg
      exact gluingEquiv_local_coeff u a hu ha γ A hA i f g hf hg
    · have hb := boundedSymbolOperator_represents (u i) β
      have he := boundedSymbolOperator_cofactor u a' hu ha' i j
      change boundedSymbolOperator (u i) β = _ at he
      rw [he] at hb
      exact hb
  have heq : A = coordinateResolution W j := by
    apply ContinuousLinearMap.ext
    intro x
    have hd := gluingEquiv_diagonal u a hu ha γ A hA (W.symm x)
    rw [W.apply_symm_apply] at hd
    change A x = W (finiteSingle (fun i => Model (u i)) j (W.symm x j))
    rw [hd]
    apply congrArg W
    apply PiLp.ext
    intro i
    change localBlock W A i (W.symm x i) = finiteSingle (fun k => Model (u k)) j (W.symm x j) i
    rw [hblock]
    by_cases hij : i = j
    · subst i
      simp
    · simp only [ite_eq_right hij,zero_apply,finiteSingle_apply,Pi.single_eq_of_ne hij]
  rw [heq] at hA
  exact hA

/-- Every field of the actual finite gluing model is now proved from a literal Bézout witness. -/
theorem gluingGraphData {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j)) (ha : Bezout u a) :
    GluingGraphData u a (gluingEquiv u a hu ha) where
  forward := gluingForward_apply u hu
  inverse x j := congrArg Subtype.val (gluingBackward_apply u a x j)
  core := gluingEquiv_core u a hu ha
  dense := gluingEquiv_dense u a hu ha
  local_coeff := gluingEquiv_local_coeff u a hu ha
  diagonal := gluingEquiv_diagonal u a hu ha
  global_coeff := gluingEquiv_global_coeff u a hu ha
  coordinate_symbol := gluingEquiv_coordinate_symbol u a hu ha

/-- Lemma 9's actual inverse/projection/core model, with no external mathematical assumption. -/
theorem gluingGraph : GluingGraphObligation := by
  intro m _hm u hu _hCorona a ha
  let hi : ∀ j, IsInner (u j) := fun j => (hu j).1
  exact ⟨gluingForward u hi,gluingBackward u a,gluingBackward_forward u a hi ha,
    gluingForward_backward u a hi ha,gluingGraphData u a hi ha⟩

end GluingModel

section DivisorCompression

/-- The literal cofactor inclusion is an isometry, so its operator norm is at most one,
including zero-dimensional local models. -/
theorem norm_cofactorInclusion_le_one {m : ℕ} (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (j : Fin m) : ‖cofactorInclusion u hu j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖innerMultiplyIsometry (cofactor u j) (isInner_cofactor u hu j) f.val‖ ≤ 1*‖f‖
  rw [(innerMultiplyIsometry (cofactor u j) (isInner_cofactor u hu j)).norm_map,one_mul]
  exact le_rfl

/-- The actual compression through the isometric inner-cofactor embedding. -/
def cofactorCompression {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (j : Fin m) (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)) :
    Model (u j) →L[ℂ] Model (u j) :=
  (cofactorInclusion u hu j).adjoint ∘L A ∘L cofactorInclusion u hu j

/-- Compression preserves every actual L² symbol, without bounded analytic-component assumptions. -/
theorem cofactorCompression_represents {m : ℕ} (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (j : Fin m) (σ : BoundaryL2)
    (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hA : RepresentsTTO (finiteProduct u) σ A) :
    RepresentsTTO (u j) σ (cofactorCompression u hu j A) := by
  intro f g hf hg
  let J := cofactorInclusion u hu j
  change inner ℂ g (J.adjoint (A (J f))) = coreForm σ f.val g.val
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hJf : IsBounded (J f).val := bounded_multiply (cofactor u j) f.val hf
  have hJg : IsBounded (J g).val := bounded_multiply (cofactor u j) g.val hg
  exact (hA (J f) (J g) hJf hJg).trans
    (coreForm_multiply_unimodular σ (cofactor u j) (isInner_cofactor u hu j).2 f.val g.val)

/-- Every positive-p Schatten gauge contracts under this actual divisor compression. -/
theorem cofactorCompression_schatten {m : ℕ} (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (j : Fin m) (p : ℝ)
    (A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u)) (hA : Schatten p A) :
    Schatten p (cofactorCompression u hu j A) ∧
      schattenNorm p (cofactorCompression u hu j A) ≤ schattenNorm p A := by
  let J := cofactorInclusion u hu j
  have hJ : ‖J‖ ≤ 1 := norm_cofactorInclusion_le_one u hu j
  have hJ' : ‖J.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map J).trans_le hJ
  have hn : ‖J.adjoint‖*‖J‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hJ' hJ (norm_nonneg J) zero_le_one
  refine ⟨schatten_comp hA J.adjoint J,?_⟩
  calc
    _ ≤ (‖J.adjoint‖*‖J‖)*schattenNorm p A := schattenNorm_comp_le hA J.adjoint J
    _ ≤ 1*schattenNorm p A := mul_le_mul_of_nonneg_right hn (schattenNorm_nonneg p A)
    _ = _ := one_mul _

/-- The local compression input of Theorem6 is proved, in fact for arbitrary finite inner families. -/
theorem atomCompression : AtomCompressionObligation := by
  intro m _hm u _ζ _hζ hu φ ψ p _hp A hA hs j
  let hi : ∀ j, IsInner (u j) := fun j => (hu j).1
  exact ⟨cofactorCompression u hi j A,
    cofactorCompression_represents u hi j (splitSymbol φ.val ψ.val) A hA,
    cofactorCompression_schatten u hi j p A hs⟩

end DivisorCompression

section FiniteSchattenBounds
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A deliberately rough addition constant, valid also below p=1. -/
def schattenAddConstant (p : ℝ) : ℝ := (4*(2:ℝ)^p)^(1/p)

theorem schattenAddConstant_pos (p : ℝ) : 0 < schattenAddConstant p :=
  Real.rpow_pos_of_pos (by positivity) _

/-- The power-sum estimate behind a finite all-p gauge bound. -/
theorem approximation_power_sum_add {p : ℝ} {A B : E →L[ℂ] F}
    (hA : Schatten p A) (hB : Schatten p B) :
    (∑' n, (approximationNumber (A+B) n : ℝ)^p) ≤
      2*(2:ℝ)^p*((∑' n, (approximationNumber A n : ℝ)^p)+(∑' n, (approximationNumber B n : ℝ)^p)) := by
  let f (n : ℕ) : ℝ := (approximationNumber (A+B) n : ℝ)^p
  let M (n : ℕ) : ℝ := (2:ℝ)^p*((approximationNumber A n : ℝ)^p+(approximationNumber B n : ℝ)^p)
  have hM : Summable M := (hA.2.2.add hB.2.2).mul_left _
  have hpoint (n : ℕ) : f (2*n) ≤ M n := by
    have hab : (approximationNumber (A+B) (2*n) : ℝ) ≤
        (approximationNumber A n : ℝ)+(approximationNumber B n : ℝ) := by
      exact_mod_cast (show approximationNumber (A+B) (2*n) ≤ _ by
        simpa only [two_mul] using approximationNumber_add A B n n)
    exact (Real.rpow_le_rpow (by positivity) hab hA.1.le).trans
      (add_rpow_bound _ _ p (by positivity) (by positivity) hA.1)
  have he : Summable (fun n => f (2*n)) := hM.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) p) hpoint
  have hodd (n : ℕ) : f (2*n+1) ≤ f (2*n) := by
    apply Real.rpow_le_rpow (by positivity) _ hA.1.le
    exact_mod_cast approximationNumber_antitone (A+B) (by omega : 2*n ≤ 2*n+1)
  have ho : Summable (fun n => f (2*n+1)) :=
    he.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) p) hodd
  have hE : (∑' n, f (2*n)) ≤ (2:ℝ)^p*((∑' n, (approximationNumber A n : ℝ)^p)+(∑' n, (approximationNumber B n : ℝ)^p)) := by
    calc
      _ ≤ ∑' n, M n := Summable.tsum_le_tsum hpoint he hM
      _ = _ := by rw [tsum_mul_left,hA.2.2.tsum_add hB.2.2]
  have hO : (∑' n, f (2*n+1)) ≤ ∑' n, f (2*n) := Summable.tsum_le_tsum hodd ho he
  have heq : (∑' n, f n) = (∑' n, f (2*n))+(∑' n, f (2*n+1)) := (he.hasSum.even_add_odd ho.hasSum).tsum_eq
  change (∑' n, f n) ≤ _
  rw [heq]
  linarith

theorem schattenNorm_rpow {p : ℝ} {A : E →L[ℂ] F} (hp : 0 < p) :
    schattenNorm p A ^ p = ∑' n, (approximationNumber A n : ℝ)^p := by
  unfold schattenNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) p)) hp.ne'

/-- A rough max-gauge inequality, with no p≥1 norm assertion. -/
theorem schattenNorm_add_le {p : ℝ} {A B : E →L[ℂ] F}
    (hA : Schatten p A) (hB : Schatten p B) :
    schattenNorm p (A+B) ≤ schattenAddConstant p * max (schattenNorm p A) (schattenNorm p B) := by
  let M := max (schattenNorm p A) (schattenNorm p B)
  have hM : 0 ≤ M := (schattenNorm_nonneg p A).trans (le_max_left _ _)
  have hQA : (∑' n, (approximationNumber A n : ℝ)^p) ≤ M^p := by
    rw [← schattenNorm_rpow hA.1]
    exact Real.rpow_le_rpow (schattenNorm_nonneg p A) (le_max_left _ _) hA.1.le
  have hQB : (∑' n, (approximationNumber B n : ℝ)^p) ≤ M^p := by
    rw [← schattenNorm_rpow hA.1]
    exact Real.rpow_le_rpow (schattenNorm_nonneg p B) (le_max_right _ _) hA.1.le
  have hQ : (∑' n, (approximationNumber (A+B) n : ℝ)^p) ≤ (4*(2:ℝ)^p)*M^p := by
    have h := approximation_power_sum_add hA hB
    have h2 : 0 < (2:ℝ)^p := Real.rpow_pos_of_pos (by norm_num) p
    nlinarith
  change (∑' n, (approximationNumber (A+B) n : ℝ)^p)^(1/p) ≤ schattenAddConstant p*M
  calc
    _ ≤ ((4*(2:ℝ)^p)*M^p)^(1/p) := Real.rpow_le_rpow
      (tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) p)) hQ (one_div_nonneg.mpr hA.1.le)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hM p)]
      congr 1
      simpa only [one_div] using Real.rpow_rpow_inv hM hA.1.ne'


@[simp] theorem schattenNorm_zero (p : ℝ) (hp : 0 < p) : schattenNorm p (0 : E →L[ℂ] F) = 0 := by
  simp only [schattenNorm,approximationNumber_zero,NNReal.coe_zero,Real.zero_rpow hp.ne',tsum_zero]
  exact Real.zero_rpow (one_div_ne_zero hp.ne')

/-- Uniform finite-sum gauge control; the rough constant is adequate for quantitative gluing. -/
theorem schattenNorm_sum_le {ι : Type*} (s : Finset ι) (T : ι → E →L[ℂ] F)
    (p : ℝ) (hp : 0 < p) (B : ℝ) (hB : 0 ≤ B) :
    (∀ j ∈ s, Schatten p (T j)) → (∀ j ∈ s, schattenNorm p (T j) ≤ B) →
    schattenNorm p (∑ j ∈ s, T j) ≤ (schattenAddConstant p+1)^s.card*B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simpa only [Finset.sum_empty,Finset.card_empty,pow_zero,one_mul,schattenNorm_zero p hp] using hB
  | @insert a s ha ih =>
    intro hs hb
    have hss : ∀ j ∈ s, Schatten p (T j) := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, schattenNorm p (T j) ≤ B := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hsum : Schatten p (∑ j ∈ s, T j) :=
      Finset.sum_induction T (fun A => Schatten p A) (fun _ _ hA hB => schatten_add hA hB) (schatten_zero p hp) hss
    have hC : 0 ≤ schattenAddConstant p := (schattenAddConstant_pos p).le
    have hpow : 1 ≤ (schattenAddConstant p+1)^s.card := one_le_pow₀ (by linarith)
    have hPB : 0 ≤ (schattenAddConstant p+1)^s.card*B := mul_nonneg (by positivity) hB
    have hm : max (schattenNorm p (T a)) (schattenNorm p (∑ j ∈ s, T j)) ≤
        (schattenAddConstant p+1)^s.card*B := by
      apply max_le
      · exact (hb a (Finset.mem_insert_self a s)).trans (by nlinarith)
      · exact ih hss hbs
    rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha,pow_succ]
    calc
      _ ≤ schattenAddConstant p*max (schattenNorm p (T a)) (schattenNorm p (∑ j ∈ s, T j)) :=
        schattenNorm_add_le (hs a (Finset.mem_insert_self a s)) hsum
      _ ≤ schattenAddConstant p*((schattenAddConstant p+1)^s.card*B) :=
        mul_le_mul_of_nonneg_left hm hC
      _ ≤ (schattenAddConstant p+1)*((schattenAddConstant p+1)^s.card*B) :=
        mul_le_mul_of_nonneg_right (by linarith) hPB
      _ = _ := by ring

end FiniteSchattenBounds

section QuantitativeFiniteBlocks
variable {m : ℕ} (H : Fin m → Type) [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)]

/-- A finite native-coordinate constant, independent of every block operator. -/
def finiteBlockConstant (p : ℝ) : ℝ :=
  (schattenAddConstant p+1)^m * ∑ j, ‖finiteSingle H j‖*‖PiLp.proj (𝕜 := ℂ) 2 H j‖

theorem finiteBlockConstant_nonneg (p : ℝ) : 0 ≤ finiteBlockConstant H p := by
  unfold finiteBlockConstant
  have h := (schattenAddConstant_pos p).le
  positivity

/-- Quantitative all-p finite block control with a uniform bound on its local gauges. -/
theorem schattenNorm_finiteDiagonal_le (T : (j : Fin m) → H j →L[ℂ] H j)
    (p : ℝ) (hp : 0 < p) (hT : ∀ j, Schatten p (T j)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j, schattenNorm p (T j) ≤ B) :
    schattenNorm p (finiteDiagonal T) ≤ finiteBlockConstant H p*B := by
  let M : ℝ := ∑ j, ‖finiteSingle H j‖*‖PiLp.proj (𝕜 := ℂ) 2 H j‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _hj => mul_nonneg (norm_nonneg (finiteSingle H j)) (norm_nonneg (PiLp.proj (𝕜 := ℂ) 2 H j)))
  let L (j : Fin m) := finiteSingle H j ∘L T j ∘L PiLp.proj (𝕜 := ℂ) 2 H j
  have hL (j : Fin m) : Schatten p (L j) := schatten_comp (hT j) _ _
  have hLb (j : Fin m) : schattenNorm p (L j) ≤ M*B := by
    calc
      _ ≤ (‖finiteSingle H j‖*‖PiLp.proj (𝕜 := ℂ) 2 H j‖)*schattenNorm p (T j) := schattenNorm_comp_le (hT j) _ _
      _ ≤ (‖finiteSingle H j‖*‖PiLp.proj (𝕜 := ℂ) 2 H j‖)*B :=
        mul_le_mul_of_nonneg_left (hb j) (mul_nonneg (norm_nonneg (finiteSingle H j)) (norm_nonneg (PiLp.proj (𝕜 := ℂ) 2 H j)))
      _ ≤ M*B := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _hk => mul_nonneg (norm_nonneg (finiteSingle H k)) (norm_nonneg (PiLp.proj (𝕜 := ℂ) 2 H k))) (Finset.mem_univ j)) hB
  rw [finiteDiagonal_eq_sum]
  have hs := schattenNorm_sum_le Finset.univ L p hp (M*B) (mul_nonneg hM hB)
    (fun j _hj => hL j) (fun j _hj => hLb j)
  simpa only [Finset.card_univ,Fintype.card_fin,finiteBlockConstant,M,L,mul_assoc] using hs

end QuantitativeFiniteBlocks

section FiniteProductStructure

theorem innerValue_multiplyInf (a b : BoundaryLInf) (ha : toL2 a ∈ hardy) (hb : toL2 b ∈ hardy) (w : Disk) :
    innerValue (multiplyInf a b) w.val = innerValue a w.val*innerValue b w.val := by
  unfold innerValue
  rw [toL2_multiplyInf]
  exact analyticValue_multiply a ha ⟨toL2 b,hb⟩ w

/-- The actual inner disk value lies in the closed unit disk, including constant inner functions. -/
theorem norm_innerValue_le_one (u : BoundaryLInf) (hu : IsInner u) (w : Disk) :
    ‖innerValue u w.val‖ ≤ 1 := by
  have hw : ‖w.val‖ < 1 := w.property
  have hd : 0 < 1-‖w.val‖^2 := by nlinarith [hw,norm_nonneg w.val]
  have hpos : 0 ≤ (1-‖innerValue u w.val‖^2)/(1-‖w.val‖^2) := by
    rw [← norm_modelReproducingKernel_sq u hu w]
    positivity
  rcases div_nonneg_iff.mp hpos with ⟨hn,_⟩ | ⟨_,hden⟩
  · nlinarith [norm_nonneg (innerValue u w.val)]
  · linarith

/-- A nonempty finite product of nonconstant inner factors is itself nonconstant. -/
theorem nonconstant_finiteProduct {m : ℕ} (hm : 0 < m) (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j) ∧ Nonconstant (u j)) : Nonconstant (finiteProduct u) := by
  let hi : ∀ j, IsInner (u j) := fun j => (hu j).1
  let j : Fin m := ⟨0,hm⟩
  let w := origin
  have hstrict : ‖innerValue (finiteProduct u) w.val‖ < 1 := by
    rw [← finiteProduct_factor u j,innerValue_multiplyInf _ _ (isInner_cofactor u hi j).1 (hi j).1 w,norm_mul]
    calc
      _ ≤ 1*‖innerValue (u j) w.val‖ := mul_le_mul_of_nonneg_right
        (norm_innerValue_le_one _ (isInner_cofactor u hi j) w) (norm_nonneg _)
      _ < 1 := by simpa only [one_mul] using norm_innerValue_lt_one _ (hi j) (hu j).2 w
  rintro ⟨c,hc⟩
  have hn := (isInner_finiteProduct u hi).2
  rw [hc] at hn
  have hcae : constLInf c =ᵐ[circleMeasure] fun _ => c := (memLp_const c).coeFn_toLp
  obtain ⟨t,ht,hct⟩ := (hn.and hcae).exists
  have hnc : ‖c‖ = 1 := by rw [hct] at ht; exact ht
  have he : innerValue (finiteProduct u) w.val = c := by
    rw [hc]
    change analyticValue (toL2 (constLInf c)) 0 = c
    rw [toL2_constLInf,analyticValue_at_zero,fourierCoeff_constL2]
    simp
  rw [he,hnc] at hstrict
  exact (lt_irrefl 1) hstrict

end FiniteProductStructure

section CoordinateCorrections
variable {m : ℕ} {H : Fin m → Type} [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- An idempotent correction is the actual similarity of the corresponding scalar block diagonal. -/
theorem correction_coordinateResolution (W : PiLp 2 H ≃L[ℂ] K) (c : Fin m → ℂ) :
    (∑ j, c j • coordinateResolution W j) = W.toContinuousLinearMap ∘L
      finiteDiagonal (fun j => c j • ContinuousLinearMap.id ℂ (H j)) ∘L W.symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [sum_apply,smul_apply,coordinateResolution,ContinuousLinearMap.comp_apply]
  change (∑ j, c j • W (finiteSingle H j (W.symm x j))) =
    W (finiteDiagonal (fun j => c j • ContinuousLinearMap.id ℂ (H j)) (W.symm x))
  calc
    _ = W (∑ j, c j • finiteSingle H j (W.symm x j)) := by rw [map_sum]; simp only [map_smul]
    _ = W (∑ j, finiteSingle H j (c j • W.symm x j)) := by
      apply congrArg W
      apply Finset.sum_congr rfl
      intro j _hj
      exact (map_smul (finiteSingle H j) (c j) (W.symm x j)).symm
    _ = _ := congrArg W (finiteSingle_sum (finiteDiagonal (fun j => c j • ContinuousLinearMap.id ℂ (H j)) (W.symm x)))

/-- Subtraction of a global coordinate correction is exactly local scalar subtraction. -/
theorem coordinateRemainder_intertwine (W : PiLp 2 H ≃L[ℂ] K) (X : K →L[ℂ] K)
    (T : (j : Fin m) → H j →L[ℂ] H j)
    (h : ∀ g, X (W g) = W (WithLp.toLp 2 (fun j => T j (g j)))) (c : Fin m → ℂ) (g : PiLp 2 H) :
    (X-(∑ j, c j • coordinateResolution W j)) (W g) =
      W (WithLp.toLp 2 (fun j => (T j-c j • ContinuousLinearMap.id ℂ (H j)) (g j))) := by
  rw [sub_apply,h,correction_coordinateResolution]
  simp only [ContinuousLinearMap.comp_apply]
  change W (WithLp.toLp 2 (fun j => T j (g j))) -
    W (finiteDiagonal (fun j => c j • ContinuousLinearMap.id ℂ (H j)) (W.symm (W g))) = _
  rw [W.symm_apply_apply,← map_sub]
  apply congrArg W
  apply PiLp.ext
  intro j
  rfl

/-- A uniform local gauge bound passes through a fixed finite similarity. -/
theorem schattenNorm_finiteIntertwine_le (W : PiLp 2 H ≃L[ℂ] K) (A : K →L[ℂ] K)
    (T : (j : Fin m) → H j →L[ℂ] H j)
    (h : ∀ g, A (W g) = W (WithLp.toLp 2 (fun j => T j (g j))))
    (p : ℝ) (hp : 0 < p) (hT : ∀ j, Schatten p (T j)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j, schattenNorm p (T j) ≤ B) :
    schattenNorm p A ≤ (‖W.toContinuousLinearMap‖*‖W.symm.toContinuousLinearMap‖*finiteBlockConstant H p)*B := by
  have he : A = W.toContinuousLinearMap ∘L finiteDiagonal T ∘L W.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := h (W.symm x)
    change A x = W (WithLp.toLp 2 (fun j => T j (W.symm x j)))
    simpa only [W.apply_symm_apply] using hx
  have hs := (schatten_finiteDiagonal_iff T p hp).mpr hT
  rw [he]
  calc
    _ ≤ (‖W.toContinuousLinearMap‖*‖W.symm.toContinuousLinearMap‖)*schattenNorm p (finiteDiagonal T) :=
      schattenNorm_comp_le hs _ _
    _ ≤ (‖W.toContinuousLinearMap‖*‖W.symm.toContinuousLinearMap‖)*(finiteBlockConstant H p*B) :=
      mul_le_mul_of_nonneg_left (schattenNorm_finiteDiagonal_le H T p hp hT B hB hb)
        (mul_nonneg (norm_nonneg W.toContinuousLinearMap) (norm_nonneg W.symm.toContinuousLinearMap))
    _ = _ := by ring

end CoordinateCorrections

section VectorGluingModel

/-- Idempotents from any literal Bézout witness agree with one fixed gluing coordinate family. -/
theorem gluing_idempotents_eq {m : ℕ} (u a₀ : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha₀ : Bezout u a₀) (a : Fin m → BoundaryLInf) (ha : Bezout u a)
    (E : Fin m → Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hE : RepresentsIdempotents u a E) : E = coordinateResolution (gluingEquiv u a₀ hu ha₀) := by
  funext j
  exact represents_unique_of_dense _ (bounded_modelCore_dense _ (isInner_finiteProduct u hu)) _ _ _
    (hE j) (gluingEquiv_coordinate_symbol u a₀ hu ha₀ a ha j)

/-- Actual vector remainders are equivalent to their local scalar remainders, for every p>0. -/
theorem gluing_remainder_iff {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (p : ℝ) (hp : 0 < p) (φ : Hardy) (c : Fin m → ℂ) :
    AnalyticRemainder p (finiteProduct u) φ.val (correction (coordinateResolution (gluingEquiv u a hu ha)) c) ↔
      ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ (Model (u j))) := by
  let W := gluingEquiv u a hu ha
  have d := gluingGraphData u a hu ha
  constructor
  · rintro ⟨X,hX,hs⟩
    obtain ⟨T,hT,hdiag⟩ := d.local_graph φ X hX
    have hd (g : FiniteModelSum u) :
        (X-correction (coordinateResolution W) c) (W g) =
          W (WithLp.toLp 2 (fun j => (T j-c j • ContinuousLinearMap.id ℂ (Model (u j))) (g j))) :=
      coordinateRemainder_intertwine W X T hdiag c g
    have ht := (finiteBlockSchatten m (fun j => Model (u j)) (Model (finiteProduct u)) W
      (X-correction (coordinateResolution W) c) (fun j => T j-c j • ContinuousLinearMap.id ℂ (Model (u j))) hd p hp).mp hs
    exact fun j => ⟨T j,hT j,ht j⟩
  · intro h
    choose T hT hs using h
    obtain ⟨X,hX,hdiag⟩ := d.global_graph denseCoreSet φ T hT
    refine ⟨X,hX,?_⟩
    apply (finiteBlockSchatten m (fun j => Model (u j)) (Model (finiteProduct u)) W
      (X-correction (coordinateResolution W) c) (fun j => T j-c j • ContinuousLinearMap.id ℂ (Model (u j)))
      (coordinateRemainder_intertwine W X T hdiag c) p hp).mpr
    exact hs

/-- The fixed gluing model gives a quantitative bound independent of symbol, scalars and later witnesses. -/
theorem gluing_remainder_bound {m : ℕ} (u a : Fin m → BoundaryLInf) (hu : ∀ j, IsInner (u j))
    (ha : Bezout u a) (p : ℝ) (hp : 0 < p) (φ : Hardy) (c : Fin m → ℂ)
    (X : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u))
    (hX : RepresentsTTO (finiteProduct u) φ.val X) (B : ℝ) (hB : 0 ≤ B)
    (hlocal : ∀ j, ∃ Xj : Model (u j) →L[ℂ] Model (u j), RepresentsTTO (u j) φ.val Xj ∧
      Schatten p (Xj-c j • ContinuousLinearMap.id ℂ (Model (u j))) ∧
      schattenNorm p (Xj-c j • ContinuousLinearMap.id ℂ (Model (u j))) ≤ B) :
    schattenNorm p (X-correction (coordinateResolution (gluingEquiv u a hu ha)) c) ≤
      (‖(gluingEquiv u a hu ha).toContinuousLinearMap‖*‖(gluingEquiv u a hu ha).symm.toContinuousLinearMap‖*
        finiteBlockConstant (fun j => Model (u j)) p)*B := by
  let W := gluingEquiv u a hu ha
  obtain ⟨T,hT,hdiag⟩ := (gluingGraphData u a hu ha).local_graph φ X hX
  have hr (j : Fin m) : Schatten p (T j-c j • ContinuousLinearMap.id ℂ (Model (u j))) ∧
      schattenNorm p (T j-c j • ContinuousLinearMap.id ℂ (Model (u j))) ≤ B := by
    obtain ⟨Xj,hXj,hs,hb⟩ := hlocal j
    have he : T j = Xj := represents_unique_of_dense _ (bounded_modelCore_dense _ (hu j)) _ _ _ (hT j) hXj
    rw [he]
    exact ⟨hs,hb⟩
  exact schattenNorm_finiteIntertwine_le W (X-correction (coordinateResolution W) c)
    (fun j => T j-c j • ContinuousLinearMap.id ℂ (Model (u j)))
    (coordinateRemainder_intertwine W X T hdiag c) p hp (fun j => (hr j).1) B hB (fun j => (hr j).2)

/-- Quantitative finite vector gluing, with the constant chosen before all later Bézout witnesses.
Witness existence itself is the separate corona obligation; no such existence is assumed here. -/
theorem vectorGluing : VectorGluingObligation := by
  classical
  intro m hm u hu _hCorona p hp
  let hi : ∀ j, IsInner (u j) := fun j => (hu j).1
  by_cases hba : ∃ a₀, Bezout u a₀
  · obtain ⟨a₀,ha₀⟩ := hba
    let W := gluingEquiv u a₀ hi ha₀
    let M := ‖W.toContinuousLinearMap‖*‖W.symm.toContinuousLinearMap‖*finiteBlockConstant (fun j => Model (u j)) p
    have hM : 0 ≤ M := mul_nonneg (mul_nonneg (norm_nonneg W.toContinuousLinearMap) (norm_nonneg W.symm.toContinuousLinearMap)) (finiteBlockConstant_nonneg _ p)
    refine ⟨M+1,by linarith,?_⟩
    intro a ha E hE
    have he : E = coordinateResolution W := gluing_idempotents_eq u a₀ hi ha₀ a ha E hE
    rw [he]
    constructor
    · intro φ c
      refine ⟨gluing_remainder_iff u a₀ hi ha₀ p hp φ c,?_⟩
      intro B hB X hX hlocal
      exact (gluing_remainder_bound u a₀ hi ha₀ p hp φ c X hX B hB hlocal).trans (by dsimp [M]; nlinarith)
    · intro φ ψ A hA hs
      rw [scalarSplit (finiteProduct u) (isInner_finiteProduct u hi) (nonconstant_finiteProduct hm u hu) φ ψ p A hA hs]
      apply exists_congr
      intro c
      have hc := constant_correction (coordinateResolution W)
        ⟨coordinateResolution_sum W,coordinateResolution_idempotent W,coordinateResolution_disjoint W⟩ c
      rw [← hc]
      exact gluing_remainder_iff u a₀ hi ha₀ p hp φ (fun _ => c)
  · refine ⟨1,zero_lt_one,?_⟩
    intro a ha
    exact (hba ⟨a,ha⟩).elim

end VectorGluingModel

/-! Extended Parseval and elementary column-energy calculus narrowly adapt the Apache-2.0
Tau Ceti contributors' Parseval.lean and HilbertSchmidt/Basic.lean at the recorded revision
 d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad. No Tau dependency or replacement Schatten predicate. -/
section HilbertSchmidtColumns
variable {I J I' E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem hasSum_basis_inner_norm_sq (b : HilbertBasis I ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,b.repr_apply_apply,b.repr.norm_map] using h

theorem tsum_basis_inner_enorm_sq (b : HilbertBasis I ℂ E) (x : E) :
    (∑' i, ‖inner ℂ (b i) x‖ₑ^2) = ‖x‖ₑ^2 := by
  calc
    _ = ∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖^2) := tsum_congr (fun i => by
      rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (inner ℂ (b i) x))])
    _ = ENNReal.ofReal (‖x‖^2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖inner ℂ (b i) x‖)
        (hasSum_basis_inner_norm_sq b x).summable,(hasSum_basis_inner_norm_sq b x).tsum_eq]
    _ = ‖x‖ₑ^2 := by rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg x)]

/-- Literal basis-column energy; it may be infinite and makes no compactness assumption. -/
def columnEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) : ℝ≥0∞ := ∑' i, ‖T (b i)‖ₑ^2

theorem columnEnergy_matrix (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ F) :
    columnEnergy T b = ∑' i, ∑' j, ‖inner ℂ (c j) (T (b i))‖ₑ^2 := by
  simp only [columnEnergy,tsum_basis_inner_enorm_sq]

variable [CompleteSpace E] [CompleteSpace F]

theorem columnEnergy_adjoint (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ F) :
    columnEnergy T.adjoint c = columnEnergy T b := by
  rw [columnEnergy_matrix _ c b,columnEnergy_matrix _ b c,ENNReal.tsum_comm]
  simp_rw [ContinuousLinearMap.adjoint_inner_right,← ofReal_norm,norm_inner_symm]

theorem columnEnergy_indep (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (b' : HilbertBasis I' ℂ E) :
    columnEnergy T b = columnEnergy T b' := by
  obtain ⟨_w,c,_⟩ := exists_hilbertBasis ℂ F
  rw [← columnEnergy_adjoint T b c,columnEnergy_adjoint T b' c]

/-- Finite or infinite literal column energy dominates the actual operator norm. -/
theorem opENorm_sq_le_columnEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) :
    ‖T‖ₑ^2 ≤ columnEnergy T b := by
  obtain ⟨_w,c,_⟩ := exists_hilbertBasis ℂ F
  have key (x : E) : ‖T x‖ₑ^2 ≤ columnEnergy T b*‖x‖ₑ^2 := by
    rw [← columnEnergy_adjoint T b c,columnEnergy,← ENNReal.tsum_mul_right,
      ← tsum_basis_inner_enorm_sq c]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [← ContinuousLinearMap.adjoint_inner_left,← mul_pow]
    exact pow_le_pow_left₀ zero_le (enorm_inner_le_enorm _ _) 2
  let M := columnEnergy T b^(2⁻¹ : ℝ)
  have hM : M^2 = columnEnergy T b := ENNReal.rpow_inv_natCast_pow two_ne_zero _
  rw [← hM]
  apply pow_le_pow_left₀ zero_le (T.opENorm_le_bound (fun x => ?_)) 2
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero,mul_pow,hM]
  exact key x

end HilbertSchmidtColumns

/-- Native l² Parseval and inner product identities, with the paper's first-linear pairing. -/
theorem l2CoordinateLaws : L2CoordinateLaws where
  norm I x := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) x
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖x i‖) h.summable,h.tsum_eq]
  inner I x y := by
    rw [lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    simp only [RCLike.inner_apply]


section FiniteCoordinateAnalysis
variable {N : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Finite coefficient analysis in the actual native sequence space, extended by zero. -/
def finiteAnalysis (q : Fin N → F) : F →L[ℂ] SequenceL2 :=
  ∑ i, lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 i.val ∘L innerSL ℂ (q i)

theorem finiteAnalysis_apply (q : Fin N → F) (x : F) :
    finiteAnalysis q x = ∑ i, lp.single 2 i.val (inner ℂ (q i) x) := by
  simp only [finiteAnalysis,sum_apply,ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply,innerSL_apply_apply]

@[simp] theorem finiteAnalysis_at (q : Fin N → F) (x : F) (i : Fin N) :
    finiteAnalysis q x i.val = inner ℂ (q i) x := by
  rw [finiteAnalysis_apply]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  simp [Pi.single_apply,Fin.val_inj]

theorem finiteAnalysis_outside (q : Fin N → F) (x : F) (n : ℕ) (hn : N ≤ n) :
    finiteAnalysis q x n = 0 := by
  rw [finiteAnalysis_apply]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  exact Pi.single_eq_of_ne (M := fun _ : ℕ => ℂ) (by omega : n ≠ i.val) (inner ℂ (q i) x)

/-- Its norm is exactly the finite coefficient square sum. -/
theorem norm_finiteAnalysis_sq (q : Fin N → F) (x : F) :
    ‖finiteAnalysis q x‖^2 = ∑ i, ‖inner ℂ (q i) x‖^2 := by
  calc
    _ = ∑' n, ‖finiteAnalysis q x n‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (finiteAnalysis q x)
    _ = ∑ n ∈ Finset.range N, ‖finiteAnalysis q x n‖^2 := tsum_eq_sum (fun n hn => by
      rw [finiteAnalysis_outside q x n (by simpa only [Finset.mem_range,not_lt] using hn)]
      simp)
    _ = ∑ i : Fin N, ‖finiteAnalysis q x i.val‖^2 := (Fin.sum_univ_eq_sum_range _ N).symm
    _ = _ := Finset.sum_congr rfl (fun i _hi => by rw [finiteAnalysis_at])

/-- Bessel control is precisely the contractivity required by the finite factorization. -/
theorem norm_finiteAnalysis_le_one (q : Fin N → F)
    (h : ∀ x : F, (∑ i, ‖inner ℂ (q i) x‖^2) ≤ ‖x‖^2) : ‖finiteAnalysis q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hs : ‖finiteAnalysis q x‖^2 ≤ ‖x‖^2 := by rw [norm_finiteAnalysis_sq]; exact h x
  change ‖finiteAnalysis q x‖ ≤ 1*‖x‖
  rw [one_mul]
  nlinarith [norm_nonneg (finiteAnalysis q x),norm_nonneg x]

variable [CompleteSpace F]

@[simp] theorem finiteAnalysis_adjoint_single (q : Fin N → F) (i : Fin N) :
    (finiteAnalysis q).adjoint (lp.single 2 i.val (1 : ℂ)) = q i := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,lp.inner_single_left,finiteAnalysis_at]
  simp only [RCLike.inner_apply,map_one,mul_one]

theorem finiteAnalysis_adjoint_single_outside (q : Fin N → F) (n : ℕ) (hn : N ≤ n) :
    (finiteAnalysis q).adjoint (lp.single 2 n (1 : ℂ)) = 0 := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,lp.inner_single_left,finiteAnalysis_outside q x n hn]
  simp

end FiniteCoordinateAnalysis

section FiniteGramBasis
variable {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Normalization of a finite orthogonal family has Bessel control, with zero columns retained as zero. -/
theorem normalizedFamily_bessel (v : Fin N → F)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j) = 0)) (x : F) :
    (∑ i, ‖inner ℂ (NormedSpace.normalize (v i)) x‖^2) ≤ ‖x‖^2 := by
  classical
  let S := {i : Fin N // v i ≠ 0}
  have hON : Orthonormal ℂ (fun i : S => NormedSpace.normalize (v i.val)) := by
    refine ⟨fun i => NormedSpace.norm_normalize i.property,?_⟩
    intro i j hij
    have hne : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [NormedSpace.normalize,inner_smul_left_eq_smul,inner_smul_right_eq_smul,hv hne,smul_zero]
  have he := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => v i ≠ 0)
    (fun i => ‖inner ℂ (NormedSpace.normalize (v i)) x‖^2)
  have hz : (∑ i : {i : Fin N // ¬v i ≠ 0}, ‖inner ℂ (NormedSpace.normalize (v i.val)) x‖^2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    have hvi : v i.val = 0 := not_not.mp i.property
    simp [hvi]
  rw [hz,add_zero] at he
  rw [← he]
  exact hON.sum_inner_products_le x

variable [CompleteSpace F] [FiniteDimensional ℂ E]

local instance finiteGramComplete : CompleteSpace E := FiniteDimensional.complete ℂ E

theorem gramSymmetric (A : E →L[ℂ] F) : (A.adjoint ∘L A).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (A.adjoint (A x)) y = inner ℂ x (A.adjoint (A y))
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]

/-- A native finite Gram eigenbasis; the codomain may be infinite-dimensional. -/
def gramBasis (A : E →L[ℂ] F) : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
  (gramSymmetric A).eigenvectorBasis rfl

theorem gramBasis_images_orthogonal (A : E →L[ℂ] F) :
    Pairwise (fun i j => inner ℂ (A (gramBasis A i)) (A (gramBasis A j)) = 0) := by
  intro i j hij
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ ((A.adjoint ∘L A).toLinearMap (gramBasis A i)) (gramBasis A j) = 0
  change inner ℂ ((A.adjoint ∘L A).toLinearMap ((gramSymmetric A).eigenvectorBasis rfl i))
    ((gramSymmetric A).eigenvectorBasis rfl j) = 0
  rw [(gramSymmetric A).apply_eigenvectorBasis rfl i,inner_smul_left,
    ((gramSymmetric A).eigenvectorBasis rfl).orthonormal.inner_eq_zero hij,mul_zero]

/-- Both Gram coordinate analysis maps are contractions. -/
theorem gramBasis_analysis_contractions (A : E →L[ℂ] F) :
    ‖finiteAnalysis (fun i => gramBasis A i)‖ ≤ 1 ∧
    ‖finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))‖ ≤ 1 := by
  constructor
  · apply norm_finiteAnalysis_le_one
    intro x
    exact ((gramBasis A).sum_sq_norm_inner_right x).le
  · apply norm_finiteAnalysis_le_one
    exact normalizedFamily_bessel _ (gramBasis_images_orthogonal A)

end FiniteGramBasis

section FiniteAnalysisColumns
variable {N : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_normalize_self (v : F) : inner ℂ (NormedSpace.normalize v) v = (‖v‖ : ℂ) := by
  by_cases hv : v = 0
  · subst v; simp
  · rw [NormedSpace.normalize,inner_smul_left_eq_smul,inner_self_eq_norm_sq_to_K,RCLike.real_smul_eq_coe_mul]
    push_cast
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
    field_simp
    rfl

theorem complex_norm_smul_normalize (v : F) : (‖v‖ : ℂ) • NormedSpace.normalize v = v := by
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) ‖v‖ (NormedSpace.normalize v)).symm.trans
    (NormedSpace.norm_smul_normalize v)

/-- Analysis of a finite orthonormal column is its actual sequence unit. -/
theorem finiteAnalysis_orthonormal_column (v : Fin N → F) (hv : Orthonormal ℂ v) (j : Fin N) :
    finiteAnalysis v (v j) = lp.single 2 j.val (1 : ℂ) := by
  rw [finiteAnalysis_apply]
  rw [Finset.sum_eq_single j]
  · rw [orthonormal_iff_ite.mp hv j j,ite_eq_left rfl]
  · intro i _hi hij
    rw [orthonormal_iff_ite.mp hv i j,ite_eq_right hij,lp.single_zero]
  · simp

/-- Normalized orthogonal-column analysis recovers precisely the column length, including a zero column. -/
theorem finiteAnalysis_normalized_column (v : Fin N → F)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j) = 0)) (j : Fin N) :
    finiteAnalysis (fun i => NormedSpace.normalize (v i)) (v j) =
      (‖v j‖ : ℂ) • (lp.single 2 j.val (1 : ℂ) : SequenceL2) := by
  have hc (i : Fin N) : inner ℂ (NormedSpace.normalize (v i)) (v j) = if i = j then (‖v j‖ : ℂ) else 0 := by
    by_cases hij : i = j
    · subst i
      rw [ite_eq_left rfl,inner_normalize_self]
    · rw [ite_eq_right hij,NormedSpace.normalize,inner_smul_left_eq_smul,hv hij,smul_zero]
  rw [finiteAnalysis_apply,Finset.sum_eq_single j]
  · rw [hc j,ite_eq_left rfl,← lp.single_smul,smul_eq_mul,mul_one]
  · intro i _hi hij
    rw [hc i,ite_eq_right hij,lp.single_zero]
  · simp

end FiniteAnalysisColumns

section ContractiveSandwich
variable {E F G K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

theorem approximationNumber_comp_contractions (L : F →L[ℂ] G) (A : E →L[ℂ] F) (R : K →L[ℂ] E)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (n : ℕ) :
    approximationNumber (L ∘L A ∘L R) n ≤ approximationNumber A n := by
  have hL' : ‖L‖₊ ≤ 1 := by exact_mod_cast hL
  have hR' : ‖R‖₊ ≤ 1 := by exact_mod_cast hR
  apply (approximationNumber_comp L A R n).trans
  calc
    _ ≤ 1*approximationNumber A n*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hL' (by positivity)) hR' (by positivity) (by positivity)
    _ = _ := by simp

end ContractiveSandwich

section FiniteGramFactorization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ E]
local instance finiteGramFactorComplete : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The finite Gram column lengths, extended by zero to the actual sequence index. -/
def finiteGramWeights (A : E →L[ℂ] F) (n : ℕ) : ℂ :=
  if hn : n < Module.finrank ℂ E then (‖A (gramBasis A ⟨n,hn⟩)‖ : ℂ) else 0

def finiteGramDiagonal (A : E →L[ℂ] F) : SequenceOperator :=
  diagonalTruncation (finiteGramWeights A) (Finset.range (Module.finrank ℂ E))

@[simp] theorem finiteGramWeights_at (A : E →L[ℂ] F) (i : Fin (Module.finrank ℂ E)) :
    finiteGramWeights A i.val = (‖A (gramBasis A i)‖ : ℂ) := by simp [finiteGramWeights,i.isLt]

@[simp] theorem finiteGramDiagonal_single (A : E →L[ℂ] F) (i : Fin (Module.finrank ℂ E)) :
    finiteGramDiagonal A (lp.single 2 i.val (1 : ℂ)) =
      (‖A (gramBasis A i)‖ : ℂ) • (lp.single 2 i.val (1 : ℂ) : SequenceL2) := by
  have h := diagonalTruncation_isDiagonal (finiteGramWeights A) (Finset.range (Module.finrank ℂ E)) i.val
  simpa only [finiteGramDiagonal,Finset.mem_range,i.isLt,ite_true,finiteGramWeights_at] using h

theorem finiteGramDiagonal_single_outside (A : E →L[ℂ] F) (n : ℕ) (hn : Module.finrank ℂ E ≤ n) :
    finiteGramDiagonal A (lp.single 2 n (1 : ℂ)) = 0 := by
  have h := diagonalTruncation_isDiagonal (finiteGramWeights A) (Finset.range (Module.finrank ℂ E)) n
  simpa only [finiteGramDiagonal,Finset.mem_range,not_lt.mpr hn,ite_false,zero_smul] using h

/-- The actual operator factors through a finite diagonal by contractions. -/
theorem finiteGram_factorization (A : E →L[ℂ] F) :
    A = (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint ∘L
      finiteGramDiagonal A ∘L finiteAnalysis (fun i => gramBasis A i) := by
  apply ContinuousLinearMap.coe_injective
  apply (gramBasis A).toBasis.ext
  intro i
  change A (gramBasis A i) =
    (finiteAnalysis (fun j => NormedSpace.normalize (A (gramBasis A j)))).adjoint
      (finiteGramDiagonal A (finiteAnalysis (fun j => gramBasis A j) (gramBasis A i)))
  rw [finiteAnalysis_orthonormal_column _ (gramBasis A).orthonormal,finiteGramDiagonal_single,
    map_smul,finiteAnalysis_adjoint_single,complex_norm_smul_normalize]

/-- The same finite diagonal is recovered from the operator by the adjoint contractions. -/
theorem finiteGram_diagonal_factorization (A : E →L[ℂ] F) :
    finiteGramDiagonal A = finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i))) ∘L
      A ∘L (finiteAnalysis (fun i => gramBasis A i)).adjoint := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro n
  apply ContinuousLinearMap.ext_ring
  change finiteGramDiagonal A (lp.single 2 n (1 : ℂ)) =
    finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))
      (A ((finiteAnalysis (fun i => gramBasis A i)).adjoint (lp.single 2 n (1 : ℂ))))
  by_cases hn : n < Module.finrank ℂ E
  · let i : Fin (Module.finrank ℂ E) := ⟨n,hn⟩
    change finiteGramDiagonal A (lp.single 2 i.val (1 : ℂ)) =
      finiteAnalysis (fun j => NormedSpace.normalize (A (gramBasis A j)))
        (A ((finiteAnalysis (fun j => gramBasis A j)).adjoint (lp.single 2 i.val (1 : ℂ))))
    rw [finiteGramDiagonal_single,finiteAnalysis_adjoint_single,
      finiteAnalysis_normalized_column _ (gramBasis_images_orthogonal A)]
  · rw [finiteGramDiagonal_single_outside A n (not_lt.mp hn),
      finiteAnalysis_adjoint_single_outside _ n (not_lt.mp hn),map_zero,map_zero]

/-- Exact finite-dimensional singular data, with no finite-dimensional target hypothesis. -/
theorem approximationNumber_finiteGram (A : E →L[ℂ] F) (n : ℕ) :
    approximationNumber A n = approximationNumber (finiteGramDiagonal A) n := by
  let R := finiteAnalysis (fun i => gramBasis A i)
  let C := finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))
  have hR : ‖R‖ ≤ 1 := (gramBasis_analysis_contractions A).1
  have hC : ‖C‖ ≤ 1 := (gramBasis_analysis_contractions A).2
  have hR' : ‖R.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map R).trans_le hR
  have hC' : ‖C.adjoint‖ ≤ 1 := (ContinuousLinearMap.adjoint.norm_map C).trans_le hC
  apply le_antisymm
  · calc
      _ = approximationNumber (C.adjoint ∘L finiteGramDiagonal A ∘L R) n :=
        congrArg (fun T => approximationNumber T n) (finiteGram_factorization A)
      _ ≤ _ := approximationNumber_comp_contractions C.adjoint (finiteGramDiagonal A) R hC' hR n
  · calc
      _ = approximationNumber (C ∘L A ∘L R.adjoint) n :=
        congrArg (fun T => approximationNumber T n) (finiteGram_diagonal_factorization A)
      _ ≤ _ := approximationNumber_comp_contractions C A R.adjoint hC hR' n

/-- Every positive-power approximation sum is exactly the finite sum of Gram column lengths. -/
theorem finiteGram_power_sum (A : E →L[ℂ] F) (p : ℝ) (hp : 0 < p) :
    (∑' n, (approximationNumber A n : ℝ)^p) =
      ∑ i : Fin (Module.finrank ℂ E), ‖A (gramBasis A i)‖^p := by
  calc
    _ = ∑' n, (approximationNumber (finiteGramDiagonal A) n : ℝ)^p :=
      tsum_congr (fun n => by rw [approximationNumber_finiteGram])
    _ = ∑ n ∈ Finset.range (Module.finrank ℂ E), ‖finiteGramWeights A n‖^p :=
      diagonalTruncation_power_sum _ _ p hp
    _ = ∑ i : Fin (Module.finrank ℂ E), ‖finiteGramWeights A i.val‖^p :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = _ := Finset.sum_congr rfl (fun i _hi => by simp [finiteGramWeights_at])

/-- Every positive Schatten class contains the actual finite-source operator. -/
theorem finiteDim_schatten (A : E →L[ℂ] F) (p : ℝ) (hp : 0 < p) : Schatten p A := by
  have hd : FiniteRank (finiteGramDiagonal A) := ⟨Module.finrank ℂ E,by
    simpa only [finiteGramDiagonal,Finset.card_range] using rank_diagonalTruncation_le (finiteGramWeights A) (Finset.range (Module.finrank ℂ E))⟩
  have hs := finiteRankSchatten (finiteGramDiagonal A) hd p hp
  rw [finiteGram_factorization A]
  exact schatten_comp hs _ _

end FiniteGramFactorization

section ApproximationSquareEnergy
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Literal extended square-sum of the rank≤n approximation numbers, starting at n=0. -/
def approximationSquareEnergy (T : E →L[ℂ] F) : ℝ≥0∞ :=
  ∑' n, (approximationNumber T n : ℝ≥0∞)^2

theorem approximationSquareEnergy_eq_ofReal_tsum (T : E →L[ℂ] F) (hT : Schatten 2 T) :
    approximationSquareEnergy T = ENNReal.ofReal (∑' n, (approximationNumber T n : ℝ)^2) := by
  have hs : Summable (fun n => (approximationNumber T n : ℝ)^2) := by simpa only [Real.rpow_two] using hT.2.2
  calc
    _ = ∑' n, ENNReal.ofReal ((approximationNumber T n : ℝ)^2) := tsum_congr (fun n => by
      rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_coe_nnreal])
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs).symm

variable [CompleteSpace E]

/-- Finite ONB column energy is the ordinary finite column square sum. -/
theorem columnEnergy_finiteBasis {N : ℕ} (T : E →L[ℂ] F) (v : OrthonormalBasis (Fin N) ℂ E) :
    columnEnergy T v.toHilbertBasis = ∑ i, ENNReal.ofReal (‖T (v i)‖^2) := by
  unfold columnEnergy
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show v.toHilbertBasis i = v i from congrFun v.coe_toHilbertBasis i]
  rw [← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _)]

variable [CompleteSpace F] [FiniteDimensional ℂ E]

/-- Exact finite-source Hilbert–Schmidt identity, with arbitrary complete target and arbitrary source Hilbert basis. -/
theorem finiteDim_approximationSquareEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) :
    approximationSquareEnergy T = columnEnergy T b := by
  have he : (∑' n, (approximationNumber T n : ℝ)^2) =
      ∑ i : Fin (Module.finrank ℂ E), ‖T (gramBasis T i)‖^2 := by
    simpa only [Real.rpow_two] using finiteGram_power_sum T 2 (by norm_num)
  calc
    _ = ENNReal.ofReal (∑' n, (approximationNumber T n : ℝ)^2) :=
      approximationSquareEnergy_eq_ofReal_tsum T (finiteDim_schatten T 2 (by norm_num))
    _ = ENNReal.ofReal (∑ i : Fin (Module.finrank ℂ E), ‖T (gramBasis T i)‖^2) := congrArg ENNReal.ofReal he
    _ = ∑ i : Fin (Module.finrank ℂ E), ENNReal.ofReal (‖T (gramBasis T i)‖^2) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _hi => sq_nonneg _)
    _ = columnEnergy T (gramBasis T).toHilbertBasis := (columnEnergy_finiteBasis T (gramBasis T)).symm
    _ = _ := columnEnergy_indep T _ b

end ApproximationSquareEnergy

section HilbertBasisCuts
variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The actual finite span of selected Hilbert basis vectors. -/
def basisCutSpace (b : HilbertBasis I ℂ E) (s : Finset I) : Submodule ℂ E :=
  Submodule.span ℂ (b '' (s : Set I))

instance basisCutFinite (b : HilbertBasis I ℂ E) (s : Finset I) :
    FiniteDimensional ℂ (basisCutSpace b s) := FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image b)
instance basisCutComplete (b : HilbertBasis I ℂ E) (s : Finset I) :
    CompleteSpace (basisCutSpace b s) := FiniteDimensional.complete ℂ _

/-- Mathlib's finite-span ONB, transported only across equality of the literal span sets. -/
def basisCutBasis (b : HilbertBasis I ℂ E) (s : Finset I) : OrthonormalBasis s ℂ (basisCutSpace b s) := by
  classical
  exact (OrthonormalBasis.span b.orthonormal s).map (LinearIsometryEquiv.ofEq _ _ (by
    rw [Finset.coe_image]
    rfl))

@[simp] theorem basisCutBasis_coe (b : HilbertBasis I ℂ E) (s : Finset I) (i : s) :
    (basisCutBasis b s i).val = b i.val := by
  classical
  simp only [basisCutBasis,OrthonormalBasis.map_apply,LinearIsometryEquiv.coe_ofEq_apply,OrthonormalBasis.span_apply]

/-- Actual ambient orthogonal basis cut. -/
def basisProjection (b : HilbertBasis I ℂ E) (s : Finset I) : E →L[ℂ] E :=
  (basisCutSpace b s).starProjection

theorem norm_basisProjection_le_one (b : HilbertBasis I ℂ E) (s : Finset I) :
    ‖basisProjection b s‖ ≤ 1 := (basisCutSpace b s).starProjection_norm_le

theorem basisProjection_apply (b : HilbertBasis I ℂ E) (s : Finset I) (x : E) :
    basisProjection b s x = ∑ i : s, inner ℂ (b i.val) x • b i.val := by
  rw [basisProjection,(basisCutBasis b s).starProjection_eq_sum_rankOne]
  simp only [sum_apply,InnerProductSpace.rankOne_apply,basisCutBasis_coe]

open scoped Classical in
/-- The projection retains precisely the chosen actual basis columns. -/
theorem basisProjection_basis (b : HilbertBasis I ℂ E) (s : Finset I) (j : I) :
    basisProjection b s (b j) = if j ∈ s then b j else 0 := by
  classical
  rw [basisProjection_apply]
  split_ifs with hj
  · let k : s := ⟨j,hj⟩
    rw [Finset.sum_eq_single k]
    · change inner ℂ (b j) (b j) • b j = b j
      rw [orthonormal_iff_ite.mp b.orthonormal j j,ite_eq_left rfl,one_smul]
    · intro i _hi hik
      have hij : i.val ≠ j := fun he => hik (Subtype.ext he)
      rw [orthonormal_iff_ite.mp b.orthonormal i.val j,ite_eq_right hij,zero_smul]
    · simp
  · apply Finset.sum_eq_zero
    intro i _hi
    have hij : i.val ≠ j := fun he => hj (he ▸ i.property)
    rw [orthonormal_iff_ite.mp b.orthonormal i.val j,ite_eq_right hij,zero_smul]

/-- Restrict the operator to the finite source span, with its actual inherited Hilbert norm. -/
def basisRestriction (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (s : Finset I) :
    basisCutSpace b s →L[ℂ] F := T ∘L (basisCutSpace b s).subtypeL

variable [CompleteSpace F]

/-- The exact finite-source identity applied to an arbitrary finite selection of the original basis. -/
theorem basisRestriction_energy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (s : Finset I) :
    approximationSquareEnergy (basisRestriction T b s) = ∑ i ∈ s, ‖T (b i)‖ₑ^2 := by
  rw [finiteDim_approximationSquareEnergy _ (basisCutBasis b s).toHilbertBasis,columnEnergy,tsum_fintype]
  calc
    _ = ∑ i : s, ‖T (b i.val)‖ₑ^2 := Finset.sum_congr rfl (fun i _hi => by
      rw [show (basisCutBasis b s).toHilbertBasis i = basisCutBasis b s i from
        congrFun (basisCutBasis b s).coe_toHilbertBasis i]
      change ‖T (basisCutBasis b s i).val‖ₑ^2 = _
      rw [basisCutBasis_coe])
    _ = _ := Finset.sum_coe_sort s (fun i => ‖T (b i)‖ₑ^2)

omit [CompleteSpace F] in
/-- Finite restriction cannot increase an approximation number. -/
theorem approximationNumber_basisRestriction_le (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E)
    (s : Finset I) (n : ℕ) : approximationNumber (basisRestriction T b s) n ≤ approximationNumber T n := by
  have hI : ‖(basisCutSpace b s).subtypeL‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x.val‖ ≤ 1*‖x‖
    rw [one_mul]
    exact le_rfl
  have hn : ‖(basisCutSpace b s).subtypeL‖₊ ≤ 1 := by exact_mod_cast hI
  exact (approximationNumber_comp_right T (basisCutSpace b s).subtypeL n).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (NNReal.coe_nonneg _))

omit [CompleteSpace F] in
/-- The ambient zero extension of the finite restriction also cannot increase its approximation numbers. -/
theorem approximationNumber_basisCut_le (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E)
    (s : Finset I) (n : ℕ) :
    approximationNumber (T ∘L basisProjection b s) n ≤ approximationNumber (basisRestriction T b s) n := by
  have hn : ‖(basisCutSpace b s).orthogonalProjectionOnto‖₊ ≤ 1 := by
    exact_mod_cast (basisCutSpace b s).orthogonalProjectionOnto_norm_le
  have he : T ∘L basisProjection b s = basisRestriction T b s ∘L (basisCutSpace b s).orthogonalProjectionOnto := rfl
  rw [he]
  exact (approximationNumber_comp_right (basisRestriction T b s) (basisCutSpace b s).orthogonalProjectionOnto n).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (NNReal.coe_nonneg _))

omit [CompleteSpace F] in
/-- Error-column energy is exactly the omitted column tail, for arbitrary basis index types. -/
theorem columnEnergy_basisCut_error (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (s : Finset I) :
    columnEnergy (T-T ∘L basisProjection b s) b = ∑' i : {i : I // i ∉ s}, ‖T (b i.val)‖ₑ^2 := by
  classical
  unfold columnEnergy
  calc
    _ = ∑' i : I, ({i : I | i ∉ s} : Set I).indicator (fun i => ‖T (b i)‖ₑ^2) i := by
      apply tsum_congr
      intro i
      simp only [sub_apply,ContinuousLinearMap.comp_apply,basisProjection_basis]
      by_cases hi : i ∈ s <;> simp [hi]
    _ = _ := (tsum_subtype {i : I | i ∉ s} (fun i => ‖T (b i)‖ₑ^2)).symm

end HilbertBasisCuts

section FullHilbertSchmidtBridge
variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Finite basis cuts converge in actual operator norm whenever literal column energy is finite. -/
theorem basisCut_tendsto (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (hT : columnEnergy T b ≠ ∞) :
    Tendsto (fun s : Finset I => T ∘L basisProjection b s) atTop (𝓝 T) := by
  have ht : Tendsto (fun s : Finset I => ∑' i : {i : I // i ∉ s}, ‖T (b i.val)‖ₑ^2) atTop (𝓝 0) :=
    ENNReal.tendsto_tsum_compl_atTop_zero hT
  have hb (s : Finset I) : ENNReal.ofReal (‖T-T ∘L basisProjection b s‖^2) ≤
      ∑' i : {i : I // i ∉ s}, ‖T (b i.val)‖ₑ^2 := by
    calc
      _ = ‖T-T ∘L basisProjection b s‖ₑ^2 := by
        rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (T-T ∘L basisProjection b s))]
      _ ≤ columnEnergy (T-T ∘L basisProjection b s) b := opENorm_sq_le_columnEnergy _ b
      _ = _ := columnEnergy_basisCut_error T b s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε^2) := ENNReal.ofReal_pos.mpr hε2
  filter_upwards [Filter.Tendsto.eventually_lt_const hpos ht] with s hs
  have he : ‖T-T ∘L basisProjection b s‖^2 < ε^2 :=
    (ENNReal.ofReal_lt_ofReal_iff hε2).mp ((hb s).trans_lt hs)
  rw [dist_eq_norm,norm_sub_rev]
  nlinarith [norm_nonneg (T-T ∘L basisProjection b s)]

/-- Finite column energy gives genuine compactness via actual finite-source restrictions. -/
theorem compact_of_columnEnergy_ne_top (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E)
    (hT : columnEnergy T b ≠ ∞) : IsCompactOperator T := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto (basisCut_tendsto T b hT)
  apply Eventually.of_forall
  intro s
  have hc := (finiteDim_schatten (basisRestriction T b s) 2 (by norm_num)).2.1
  change IsCompactOperator (basisRestriction T b s ∘L (basisCutSpace b s).orthogonalProjectionOnto)
  exact hc.comp_clm _

omit [CompleteSpace E] in
/-- Every finite column sum is bounded by the full approximation-square energy, including divergent energy. -/
theorem columnEnergy_le_approximationSquareEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) :
    columnEnergy T b ≤ approximationSquareEnergy T := by
  unfold columnEnergy
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← basisRestriction_energy T b s]
  unfold approximationSquareEnergy
  apply ENNReal.tsum_le_tsum
  intro n
  apply pow_le_pow_left₀ zero_le
  exact_mod_cast approximationNumber_basisRestriction_le T b s n

omit [CompleteSpace E] in
/-- Finite approximation-square sums of a basis cut are controlled by the entire original column energy. -/
theorem basisCut_partial_approximationSquare_le (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E)
    (s : Finset I) (r : Finset ℕ) :
    (∑ n ∈ r, (approximationNumber (T ∘L basisProjection b s) n : ℝ≥0∞)^2) ≤ columnEnergy T b := by
  calc
    _ ≤ ∑ n ∈ r, (approximationNumber (basisRestriction T b s) n : ℝ≥0∞)^2 := Finset.sum_le_sum (fun n _hn => by
      apply pow_le_pow_left₀ zero_le
      exact_mod_cast approximationNumber_basisCut_le T b s n)
    _ ≤ approximationSquareEnergy (basisRestriction T b s) := ENNReal.sum_le_tsum r
    _ = ∑ i ∈ s, ‖T (b i)‖ₑ^2 := basisRestriction_energy T b s
    _ ≤ _ := ENNReal.sum_le_tsum s

/-- Exact infinite-source Hilbert–Schmidt reconciliation, with extended sums and arbitrary basis index types. -/
theorem approximationSquareEnergy_eq_columnEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) :
    approximationSquareEnergy T = columnEnergy T b := by
  apply le_antisymm
  · by_cases ht : columnEnergy T b = ∞
    · rw [ht]
      exact le_top
    · have hlim := basisCut_tendsto T b ht
      unfold approximationSquareEnergy
      rw [ENNReal.tsum_eq_iSup_sum]
      apply iSup_le
      intro r
      have hc : Continuous (fun A : E →L[ℂ] F => ∑ n ∈ r, (approximationNumber A n : ℝ≥0∞)^2) := by
        apply continuous_finsetSum r
        intro n _hn
        have hscalar : Continuous (fun A : E →L[ℂ] F => ENNReal.ofReal ((approximationNumber A n : ℝ)^2)) :=
          ENNReal.continuous_ofReal.comp ((continuous_approximationNumber (E := E) (F := F) n).pow 2)
        apply hscalar.congr
        intro A
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg (approximationNumber A n)),ENNReal.ofReal_coe_nnreal]
      exact le_of_tendsto (hc.tendsto T |>.comp hlim)
        (Eventually.of_forall (fun s => basisCut_partial_approximationSquare_le T b s r))
  · exact columnEnergy_le_approximationSquareEnergy T b

/-- The actual approximation-number Schatten predicate agrees with finite literal column energy. -/
theorem schatten_two_iff_columnEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) :
    Schatten 2 T ↔ columnEnergy T b < ∞ := by
  constructor
  · intro hT
    rw [← approximationSquareEnergy_eq_columnEnergy T b,approximationSquareEnergy_eq_ofReal_tsum T hT]
    exact ENNReal.ofReal_lt_top
  · intro hT
    refine ⟨by norm_num,compact_of_columnEnergy_ne_top T b hT.ne,?_⟩
    have he : approximationSquareEnergy T ≠ ∞ := by rw [approximationSquareEnergy_eq_columnEnergy T b]; exact hT.ne
    have hs := ENNReal.summable_toReal he
    simpa only [approximationSquareEnergy,ENNReal.toReal_pow,ENNReal.coe_toReal,Real.rpow_two] using hs

/-- Exact HS gauge square, with compactness and summability justified by the actual predicate. -/
theorem schattenNorm_two_sq_columnEnergy (T : E →L[ℂ] F) (b : HilbertBasis I ℂ E) (hT : Schatten 2 T) :
    ENNReal.ofReal (schattenNorm 2 T^2) = columnEnergy T b := by
  have he : schattenNorm 2 T^2 = ∑' n, (approximationNumber T n : ℝ)^2 := by
    simpa only [Real.rpow_two] using (schattenNorm_rpow (A := T) (by norm_num : (0 : ℝ) < 2))
  rw [he,← approximationSquareEnergy_eq_ofReal_tsum T hT,approximationSquareEnergy_eq_columnEnergy T b]

end FullHilbertSchmidtBridge

section ClosedCoefficientAnalysis
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Native l² membership is exactly finite literal extended coefficient energy. -/
theorem memlp_two_iff_energy {G : Type*} [NormedAddCommGroup G] (f : I → G) :
    Memℓp f 2 ↔ (∑' i, ENNReal.ofReal (‖f i‖^2)) < ∞ := by
  constructor
  · intro hf
    have hs : Summable (fun i => ‖f i‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hf
    exact hs.tsum_ofReal_lt_top
  · intro hf
    have hs := ENNReal.summable_toReal hf.ne
    have hs' : Summable (fun i => ‖f i‖^2) := hs.congr (fun i => ENNReal.toReal_ofReal (sq_nonneg ‖f i‖))
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs'

/-- The literal coordinate-equality graph, as a linear subspace of the actual product. -/
def coefficientGraph (c : I → H →L[ℂ] ℂ) (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] K) : Submodule ℂ (H × K) where
  carrier := {z | ∀ i, U.symm z.2 i = c i z.1}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro x y hx hy i
    change U.symm (x.2+y.2) i = c i (x.1+y.1)
    rw [map_add,map_add,lp.coeFn_add,Pi.add_apply,hx i,hy i]
  smul_mem' := by
    intro r z hz i
    change U.symm (r • z.2) i = c i (r • z.1)
    rw [map_smul,map_smul,lp.coeFn_smul,Pi.smul_apply,hz i]

/-- The coordinate graph has a unique output at every input where an output exists. -/
theorem coefficientGraph_functional (c : I → H →L[ℂ] ℂ) (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] K) :
    ∀ z : H × K, z ∈ coefficientGraph c U → z.1 = 0 → z.2 = 0 := by
  intro z hz hx
  apply U.symm.injective
  apply lp.ext
  funext i
  simp only [map_zero,lp.coeFn_zero,Pi.zero_apply]
  rw [hz i,hx,map_zero]

/-- Arbitrary intersections of actual continuous coordinate equalities give a closed graph. -/
theorem coefficientGraph_closed (c : I → H →L[ℂ] ℂ) (U : lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] K) :
    IsClosed (coefficientGraph c U : Set (H × K)) := by
  change IsClosed {z : H × K | ∀ i, U.symm z.2 i = c i z.1}
  have he : {z : H × K | ∀ i, U.symm z.2 i = c i z.1} =
      ⋂ i, {z : H × K | U.symm z.2 i = c i z.1} := by ext z; simp
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous.comp (U.symm.continuous.comp continuous_snd))
    ((c i).continuous.comp continuous_fst)

end ClosedCoefficientAnalysis

/-- The full native closed-analysis input, with its graph and exact finite-energy domain both proved. -/
theorem closedAnalysis : ClosedAnalysisObligation := by
  intro H K I _ _ _ _ _ _ c U
  let g := coefficientGraph c U
  let Q := g.toLinearPMap
  have hg : Q.graph = g := g.toLinearPMap_graph_eq (coefficientGraph_functional c U)
  refine ⟨Q,?_,?_,?_⟩
  · change IsClosed (Q.graph : Set (H × K))
    rw [hg]
    exact coefficientGraph_closed c U
  · intro x y
    rw [hg]
    rfl
  · intro x
    rw [LinearPMap.mem_domain_iff,hg]
    change (∃ y : K, ∀ i, U.symm y i = c i x) ↔ (∑' i, ENNReal.ofReal (‖c i x‖^2)) < ∞
    constructor
    · rintro ⟨y,hy⟩
      apply (memlp_two_iff_energy _).mp
      have he : (fun i => c i x) = (U.symm y : I → ℂ) := funext (fun i => (hy i).symm)
      rw [he]
      exact lp.memℓp (U.symm y)
    · intro hx
      let a : lp (fun _ : I => ℂ) 2 := ⟨fun i => c i x,(memlp_two_iff_energy _).mpr hx⟩
      refine ⟨U a,?_⟩
      intro i
      rw [U.symm_apply_apply]


section HilbertColumnOperators
variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Actual column synthesis, using Mathlib's native bounded Hölder pairing in l². -/
def columnOperator (b : HilbertBasis I ℂ E) (f : lp (fun _ : I => F) 2) : E →L[ℂ] F :=
  ((lp.dualPairing (𝕜 := ℂ) 2 2 (fun _ : I =>
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F))
    (K := 1) (fun _ => ContinuousLinearMap.opNorm_lsmul_le)).flip f) ∘L
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- Its value is the literal unconditional column series. -/
theorem columnOperator_apply (b : HilbertBasis I ℂ E) (f : lp (fun _ : I => F) 2) (x : E) :
    columnOperator b f x = ∑' i, inner ℂ (b i) x • f i := by
  change (∑' i, (b.repr x i) • f i) = _
  apply tsum_congr
  intro i
  rw [b.repr_apply_apply]

@[simp] theorem columnOperator_basis (b : HilbertBasis I ℂ E) (f : lp (fun _ : I => F) 2) (i : I) :
    columnOperator b f (b i) = f i := by
  classical
  rw [columnOperator_apply,tsum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal i i,ite_eq_left rfl,one_smul]
  · intro j hji
    rw [orthonormal_iff_ite.mp b.orthonormal j i,ite_eq_right hji,zero_smul]

/-- The actual synthesis energy is the finite native l² column norm square. -/
theorem columnOperator_energy (b : HilbertBasis I ℂ E) (f : lp (fun _ : I => F) 2) :
    columnEnergy (columnOperator b f) b = ENNReal.ofReal (‖f‖^2) := by
  have hs : HasSum (fun i => ‖f i‖^2) (‖f‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) f
  unfold columnEnergy
  simp_rw [columnOperator_basis]
  calc
    _ = ∑' i, ENNReal.ofReal (‖f i‖^2) := tsum_congr (fun i => by
      rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (f i))])
    _ = _ := by rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖f i‖) hs.summable,hs.tsum_eq]

variable [CompleteSpace E]

/-- Square-summable columns give a genuine compact S₂ operator, with exact gauge. -/
theorem columnOperator_schatten (b : HilbertBasis I ℂ E) (f : lp (fun _ : I => F) 2) :
    Schatten 2 (columnOperator b f) ∧ ENNReal.ofReal (schattenNorm 2 (columnOperator b f)^2) =
      ∑' i, ENNReal.ofReal (‖f i‖^2) := by
  have hs : Schatten 2 (columnOperator b f) := (schatten_two_iff_columnEnergy _ b).mpr (by
    rw [columnOperator_energy]
    exact ENNReal.ofReal_lt_top)
  refine ⟨hs,?_⟩
  rw [schattenNorm_two_sq_columnEnergy _ b hs,columnEnergy]
  apply tsum_congr
  intro i
  rw [columnOperator_basis,← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (f i))]

/-- A finite-energy family supplies an actual operator with exactly the prescribed columns. -/
theorem exists_columnOperator (b : HilbertBasis I ℂ E) (v : I → F)
    (hv : (∑' i, ENNReal.ofReal (‖v i‖^2)) < ∞) :
    ∃ T : E →L[ℂ] F, (∀ i, T (b i) = v i) ∧ Schatten 2 T ∧
      ENNReal.ofReal (schattenNorm 2 T^2) = ∑' i, ENNReal.ofReal (‖v i‖^2) := by
  let f : lp (fun _ : I => F) 2 := ⟨v,(memlp_two_iff_energy v).mpr hv⟩
  exact ⟨columnOperator b f,columnOperator_basis b f,columnOperator_schatten b f⟩

end HilbertColumnOperators

section ConjugateHilbertBasis
variable {I : Type*}

/-- The literal native L² star reverses the complex inner product by conjugation. -/
theorem inner_boundary_star (f g : BoundaryL2) :
    inner ℂ (star f) (star g) = conj (inner ℂ f g) := by
  rw [L2.inner_def,L2.inner_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f,Lp.coeFn_star g] with t hf hg
  change (star f) t = conj (f t) at hf
  change (star g) t = conj (g t) at hg
  simp only [RCLike.inner_apply,hf,hg,map_mul,starRingEnd_self_apply]

/-- Actual boundary star between the model and conjugate-model spaces, as an antilinear isometry. -/
def modelStarIsometry (u : BoundaryLInf) : Model u →ₗᵢ⋆[ℂ] ConjugateModel u where
  toFun f := ⟨star f.val,star_mem_conjugateModel u f⟩
  map_add' f g := Subtype.ext (boundary_star_add f.val g.val)
  map_smul' c f := Subtype.ext (boundary_star_smul c f.val)
  norm_map' f := boundary_norm_star f.val

@[simp] theorem modelStarIsometry_apply (u : BoundaryLInf) (f : Model u) :
    (modelStarIsometry u f).val = star f.val := rfl

theorem modelStar_inner (u : BoundaryLInf) (f g : Model u) :
    inner ℂ (modelStarIsometry u f) (modelStarIsometry u g) = conj (inner ℂ f g) := inner_boundary_star f.val g.val

theorem conjugateBasis_orthonormal (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) :
    Orthonormal ℂ (fun i => modelStarIsometry u (b i)) := by
  refine ⟨fun i => ((modelStarIsometry u).norm_map (b i)).trans (b.orthonormal.norm_eq_one i),?_⟩
  intro i j hij
  rw [modelStar_inner,b.orthonormal.inner_eq_zero hij,map_zero]

theorem conjugateBasis_total (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) :
    (Submodule.span ℂ (Set.range (fun i => modelStarIsometry u (b i)))).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  let sx : Model u := ⟨star x.val,star_mem_model_of_conjugateModel u x⟩
  have he : modelStarIsometry u sx = x := Subtype.ext (star_star x.val)
  have hz : sx = 0 := by
    apply b.repr.injective
    rw [map_zero]
    apply lp.ext
    funext i
    simp only [b.repr_apply_apply,lp.coeFn_zero,Pi.zero_apply]
    have hh : inner ℂ (modelStarIsometry u (b i)) x = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i,rfl⟩)
    have hi := modelStar_inner u (b i) sx
    rw [he] at hi
    rw [hi] at hh
    simpa only [starRingEnd_self_apply,map_zero] using congrArg conj hh
  have hn : ‖star x.val‖ = 0 := by change ‖sx‖ = 0; rw [hz,norm_zero]
  rw [boundary_norm_star] at hn
  exact norm_eq_zero.mp hn

/-- The literal conjugates of any source Hilbert basis form a Hilbert basis of the conjugate model. -/
def conjugateBasis (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) : HilbertBasis I ℂ (ConjugateModel u) :=
  HilbertBasis.mkOfOrthogonalEqBot (conjugateBasis_orthonormal u b) (conjugateBasis_total u b)

@[simp] theorem conjugateBasis_apply (u : BoundaryLInf) (b : HilbertBasis I ℂ (Model u)) (i : I) :
    conjugateBasis u b i = modelStarIsometry u (b i) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (conjugateBasis_orthonormal u b) (conjugateBasis_total u b)) i

end ConjugateHilbertBasis

section HilbertBasisOperatorExt
variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Continuous linear maps are determined by their actual Hilbert basis columns. -/
theorem clm_eq_of_hilbertBasis (b : HilbertBasis I ℂ E) (A B : E →L[ℂ] F)
    (h : ∀ i, A (b i) = B (b i)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  have ha := A.hasSum (b.hasSum_repr x)
  have hb := B.hasSum (b.hasSum_repr x)
  have he : (fun i => A (b.repr x i • b i)) = (fun i => B (b.repr x i • b i)) := by
    funext i
    rw [map_smul,map_smul,h i]
  rw [he] at ha
  exact ha.unique hb

end HilbertBasisOperatorExt

section THOMatrixModel

/-- Actual L² product followed by the literal conjugate-model projection. -/
def thoColumn (u : BoundaryLInf) (b : MatrixData u) (σ : BoundaryL2) (j : b.Index) : ConjugateModel u :=
  (conjugateModel u).orthogonalProjectionOnto (coreMultiply σ ⟨(b.basis j).val,b.bounded j⟩)

theorem thoColumn_inner (u : BoundaryLInf) (b : MatrixData u) (σ : BoundaryL2) (j : b.Index)
    (g : ConjugateModel u) : inner ℂ g (thoColumn u b σ j) = coreForm σ (b.basis j).val g.val := by
  rw [coreForm_eq_inner_left σ _ _ (b.bounded j)]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left g _

theorem bounded_conjugateBasis (u : BoundaryLInf) (b : MatrixData u) (i : b.Index) :
    IsBounded (conjugateBasis u b.basis i).val := by
  rw [conjugateBasis_apply,modelStarIsometry_apply]
  exact (b.bounded i).star.ae_eq (Lp.coeFn_star _).symm

/-- The matrix is the actual conjugate of the prescribed integral coefficients, with no lost constant mode. -/
theorem thoColumn_coefficient (u : BoundaryLInf) (b : MatrixData u) (η : Ambient u) (i j : b.Index) :
    inner ℂ (conjugateBasis u b.basis i) (thoColumn u b (star η.val) j) = conj (b.coefficient (i,j) η) := by
  rw [thoColumn_inner,b.coefficient_eq,← integral_conj]
  simp only [conjugateBasis_apply,modelStarIsometry_apply,coreForm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star η.val,Lp.coeFn_star (b.basis i).val] with t hη hi
  change (star η.val) t = conj (η.val t) at hη
  change (star (b.basis i).val) t = conj ((b.basis i).val t) at hi
  rw [hη,hi]
  simp only [map_mul,starRingEnd_self_apply]
  ring

/-- Exact extended matrix/column energy, including divergent energy. -/
theorem thoColumns_energy (u : BoundaryLInf) (b : MatrixData u) (η : Ambient u) :
    (∑' j, ENNReal.ofReal (‖thoColumn u b (star η.val) j‖^2)) = matrixEnergy b η := by
  have he (j : b.Index) : ENNReal.ofReal (‖thoColumn u b (star η.val) j‖^2) =
      ∑' i, ENNReal.ofReal (‖b.coefficient (i,j) η‖^2) := by
    calc
      _ = ‖thoColumn u b (star η.val) j‖ₑ^2 := by
        rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (thoColumn u b (star η.val) j))]
      _ = ∑' i, ‖inner ℂ (conjugateBasis u b.basis i) (thoColumn u b (star η.val) j)‖ₑ^2 :=
        (tsum_basis_inner_enorm_sq (conjugateBasis u b.basis) _).symm
      _ = _ := tsum_congr (fun i => by
        rw [thoColumn_coefficient,← ofReal_norm,Complex.norm_conj,
          ← ENNReal.ofReal_pow (norm_nonneg (b.coefficient (i,j) η))])
  calc
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖b.coefficient (i,j) η‖^2) := tsum_congr he
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖b.coefficient (i,j) η‖^2) := ENNReal.tsum_comm
    _ = _ := by rw [matrixEnergy,ENNReal.tsum_prod']

/-- Any represented THO has precisely these actual projected product columns. -/
theorem representsTHO_columns (u : BoundaryLInf) (b : MatrixData u) (σ : BoundaryL2)
    (B : Model u →L[ℂ] ConjugateModel u) (hB : RepresentsTHO u σ B) (j : b.Index) :
    B (b.basis j) = thoColumn u b σ j := by
  apply (conjugateBasis u b.basis).repr.injective
  apply lp.ext
  funext i
  rw [(conjugateBasis u b.basis).repr_apply_apply,(conjugateBasis u b.basis).repr_apply_apply]
  rw [hB (b.basis j) (conjugateBasis u b.basis i) (b.bounded j) (bounded_conjugateBasis u b i),thoColumn_inner]

/-- Correct basis columns suffice for the full bounded-test THO form, without bounded symbol assumptions. -/
theorem representsTHO_of_columns (u : BoundaryLInf) (b : MatrixData u) (σ : BoundaryL2)
    (B : Model u →L[ℂ] ConjugateModel u) (hB : ∀ j, B (b.basis j) = thoColumn u b σ j) :
    RepresentsTHO u σ B := by
  intro f g _hf hg
  let v := multiply (hg.toLp g.val) (star σ)
  let L := innerSL ℂ g ∘L B
  let R := innerSL ℂ v ∘L (model u).subtypeL
  have he : L = R := clm_eq_of_hilbertBasis b.basis L R (fun j => by
    change inner ℂ g (B (b.basis j)) = inner ℂ v (b.basis j).val
    rw [hB j,thoColumn_inner,coreForm_eq_inner_right σ _ _ hg])
  have hv := congrArg (fun A => A f) he
  change inner ℂ g (B f) = inner ℂ v f.val at hv
  exact hv.trans (coreForm_eq_inner_right σ f.val g.val hg).symm

/-- Literal coefficient matrix energy agrees with the energy of any represented THO. -/
theorem representsTHO_columnEnergy (u : BoundaryLInf) (b : MatrixData u) (η : Ambient u)
    (B : Model u →L[ℂ] ConjugateModel u) (hB : RepresentsTHO u (star η.val) B) :
    columnEnergy B b.basis = matrixEnergy b η := by
  unfold columnEnergy
  calc
    _ = ∑' j, ENNReal.ofReal (‖thoColumn u b (star η.val) j‖^2) := tsum_congr (fun j => by
      rw [representsTHO_columns u b (star η.val) B hB j,← ofReal_norm,
        ENNReal.ofReal_pow (norm_nonneg (thoColumn u b (star η.val) j))])
    _ = _ := thoColumns_energy u b η

/-- The full actual THO Hilbert–Schmidt matrix criterion, constructed from native products and column synthesis. -/
theorem matrixOperator : MatrixOperatorObligation := by
  intro u _hu _hn b η
  constructor
  · constructor
    · rintro ⟨B,hB,hs⟩
      have he := (schatten_two_iff_columnEnergy B b.basis).mp hs
      rwa [representsTHO_columnEnergy u b η B hB] at he
    · intro he
      have hv : (∑' j, ENNReal.ofReal (‖thoColumn u b (star η.val) j‖^2)) < ∞ := by
        rw [thoColumns_energy]
        exact he
      obtain ⟨B,hB,hs,_hg⟩ := exists_columnOperator b.basis (thoColumn u b (star η.val)) hv
      exact ⟨B,representsTHO_of_columns u b (star η.val) B hB,hs⟩
  · intro B hB hs
    exact (schattenNorm_two_sq_columnEnergy B b.basis hs).trans (representsTHO_columnEnergy u b η B hB)

end THOMatrixModel

section ClassicalFourierBases

theorem hardyMode_orthonormal : Orthonormal ℂ hardyMode := by
  constructor
  · intro n
    change ‖fourierBasis (T := 1) (n : ℤ)‖ = 1
    exact (fourierBasis (T := 1)).orthonormal.norm_eq_one _
  · intro i j hij
    change inner ℂ (fourierBasis (T := 1) (i : ℤ)) (fourierBasis (T := 1) (j : ℤ)) = 0
    exact (fourierBasis (T := 1)).orthonormal.inner_eq_zero (by exact_mod_cast hij)

/-- The native positive Fourier basis of H², retaining its constant vector. -/
def hardyBasis : HilbertBasis ℕ ℂ Hardy := HilbertBasis.mk hardyMode_orthonormal (by
  have hd := hardyModes_dense
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
  exact hd.ge)

@[simp] theorem hardyBasis_apply (n : ℕ) : hardyBasis n = hardyMode n :=
  congrFun (HilbertBasis.coe_mk hardyMode_orthonormal _) n

/-- The native strictly negative Fourier character, with index0 corresponding to frequency−1. -/
def negativeMode (n : ℕ) : ↥hardy.orthogonal :=
  ⟨fourierBasis (T := 1) (-(n : ℤ)-1),fourierBasis_mem_negative (by omega)⟩

theorem negativeMode_orthonormal : Orthonormal ℂ negativeMode := by
  constructor
  · intro n
    change ‖fourierBasis (T := 1) (-(n : ℤ)-1)‖ = 1
    exact (fourierBasis (T := 1)).orthonormal.norm_eq_one _
  · intro i j hij
    change inner ℂ (fourierBasis (T := 1) (-(i : ℤ)-1)) (fourierBasis (T := 1) (-(j : ℤ)-1)) = 0
    exact (fourierBasis (T := 1)).orthonormal.inner_eq_zero (by intro h; apply hij; omega)

theorem negativeModes_total : (Submodule.span ℂ (Set.range negativeMode)).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply Subtype.ext
  apply (fourierBasis (T := 1)).repr.injective
  change (fourierBasis (T := 1)).repr f.val = (fourierBasis (T := 1)).repr (0 : BoundaryL2)
  rw [map_zero]
  apply lp.ext
  funext k
  simp only [fourierBasis_repr,lp.coeFn_zero,Pi.zero_apply]
  by_cases hk : 0 ≤ k
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact (mem_hardy_orthogonal_iff _).mp f.property n
  · obtain ⟨n,hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -k-1)
    have he : k = -(n : ℤ)-1 := by omega
    rw [he]
    have hz : inner ℂ (negativeMode n) f = 0 :=
      (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨n,rfl⟩)
    change inner ℂ (fourierBasis (T := 1) (-(n : ℤ)-1)) f.val = 0 at hz
    simpa only [← HilbertBasis.repr_apply_apply,fourierBasis_repr] using hz

/-- The actual negative Hardy complement has the complete strictly negative Fourier basis. -/
def negativeBasis : HilbertBasis ℕ ℂ ↥hardy.orthogonal :=
  HilbertBasis.mkOfOrthogonalEqBot negativeMode_orthonormal negativeModes_total

@[simp] theorem negativeBasis_apply (n : ℕ) : negativeBasis n = negativeMode n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot negativeMode_orthonormal negativeModes_total) n

/-- Bounded Fourier multiplication shifts the coefficients of every L² vector. -/
theorem fourierCoeff_mode_multiply (m n : ℤ) (f : BoundaryL2) :
    fourierCoeff (multiply (mode m) f) n = fourierCoeff f (n-m) := by
  have hm : mode m =ᵐ[circleMeasure] fourier (T := 1) m := ContinuousMap.coeFn_toLp _ _
  have he : multiply (mode m) f =ᵐ[circleMeasure] fun t => fourier (T := 1) m t*f t := by
    filter_upwards [multiply_ae (mode m) f,hm] with t hp hmt
    rw [hp,hmt]
  rw [fourierCoeff_congr_ae he,fourierCoeff,fourierCoeff]
  congr 1
  funext t
  rw [smul_eq_mul,smul_eq_mul,← mul_assoc,← fourier_add]
  congr 3
  ring

end ClassicalFourierBases


section ClassicalHankelMatrix

theorem bounded_hardyBasis (j : ℕ) : IsBounded (hardyBasis j).val := by
  rw [hardyBasis_apply]
  exact bounded_fourierBasis (j : ℤ)

theorem bounded_negativeBasis (i : ℕ) : IsBounded (negativeBasis i).val := by
  rw [negativeBasis_apply]
  exact bounded_fourierBasis (-(i : ℤ)-1)

/-- Actual projected L² product on the jth positive Fourier character. -/
def hankelColumn (σ : BoundaryL2) (j : ℕ) : ↥hardy.orthogonal :=
  hardy.orthogonal.orthogonalProjectionOnto
    (coreMultiply σ ⟨(hardyBasis j).val,bounded_hardyBasis j⟩)

theorem hankelColumn_inner (σ : BoundaryL2) (j : ℕ) (v : ↥hardy.orthogonal) :
    inner ℂ v (hankelColumn σ j) = coreForm σ (hardyBasis j).val v.val := by
  rw [coreForm_eq_inner_left σ _ _ (bounded_hardyBasis j)]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left v _

/-- The strictly negative/positive Hankel matrix has entries conjugate(a_(i+j)). -/
theorem hankelColumn_coefficient (g : BoundaryL2) (i j : ℕ) :
    inner ℂ (negativeBasis i) (hankelColumn (star (multiply coordinate g)) j) =
      conj (fourierCoeff g ((i+j : ℕ) : ℤ)) := by
  rw [hankelColumn_inner,coreForm_eq_inner_left _ _ _ (bounded_hardyBasis j)]
  simp only [hardyBasis_apply,negativeBasis_apply]
  change inner ℂ (fourierBasis (T := 1) (-(i : ℤ)-1))
    (coreMultiply (star (multiply coordinate g)) ⟨fourierBasis (T := 1) (j : ℤ),bounded_fourierBasis (j : ℤ)⟩) = _
  rw [coreMultiply_fourierBasis,← HilbertBasis.repr_apply_apply,fourierBasis_repr,
    fourierCoeff_mode_multiply,fourierCoeff_star_L2]
  change conj (fourierCoeff (multiply (mode 1) g) (-(-(i : ℤ)-1-(j : ℤ)))) = _
  rw [fourierCoeff_mode_multiply]
  congr 2
  push_cast
  ring

/-- Extended antidiagonal count: frequency n occurs exactly n+1 times. -/
theorem tsum_antidiagonal_energy (f : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, ∑' i : ℕ, f (i+j)) = ∑' n : ℕ, (n+1 : ℝ≥0∞)*f n := by
  rw [← ENNReal.tsum_prod' (f := fun p : ℕ × ℕ => f (p.2+p.1))]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
    (fun p : ℕ × ℕ => f (p.2+p.1)),ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [tsum_fintype]
  have he : ∀ a : ↥(Finset.antidiagonal n), f (a.val.2+a.val.1) = f n := by
    intro a
    congr 1
    have ha := Finset.mem_antidiagonal.mp a.property
    omega
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_coe,Finset.Nat.card_antidiagonal,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

/-- Actual projected Hankel columns have the full weighted Taylor coefficient energy. -/
theorem hankelColumns_energy (g : BoundaryL2) :
    (∑' j, ENNReal.ofReal (‖hankelColumn (star (multiply coordinate g)) j‖^2)) =
      classicalCoefficientEnergy g := by
  have he (j : ℕ) : ENNReal.ofReal (‖hankelColumn (star (multiply coordinate g)) j‖^2) =
      ∑' i : ℕ, ENNReal.ofReal (‖fourierCoeff g ((i+j : ℕ) : ℤ)‖^2) := by
    calc
      _ = ‖hankelColumn (star (multiply coordinate g)) j‖ₑ^2 := by
        rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (hankelColumn _ j))]
      _ = ∑' i, ‖inner ℂ (negativeBasis i) (hankelColumn (star (multiply coordinate g)) j)‖ₑ^2 :=
        (tsum_basis_inner_enorm_sq negativeBasis _).symm
      _ = _ := tsum_congr (fun i => by
        rw [hankelColumn_coefficient,← ofReal_norm,Complex.norm_conj,
          ← ENNReal.ofReal_pow (norm_nonneg (fourierCoeff g ((i+j : ℕ) : ℤ)))])
  calc
    _ = ∑' j : ℕ, ∑' i : ℕ, ENNReal.ofReal (‖fourierCoeff g ((i+j : ℕ) : ℤ)‖^2) := tsum_congr he
    _ = _ := by
      rw [tsum_antidiagonal_energy (fun n => ENNReal.ofReal (‖fourierCoeff g (n : ℤ)‖^2)),classicalCoefficientEnergy]
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_cast

/-- Agreement on bounded Fourier tests determines every column of a represented Hankel operator. -/
theorem representsHankel_columns (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (j : ℕ) : H (hardyBasis j) = hankelColumn σ j := by
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  rw [negativeBasis.repr_apply_apply,negativeBasis.repr_apply_apply,
    hH (hardyBasis j) (negativeBasis i) (bounded_hardyBasis j)
      (bounded_negativeBasis i),hankelColumn_inner]

/-- Bounded opposite tests make the raw L² symbol form continuous in the Hardy input. -/
theorem representsHankel_of_columns (σ : BoundaryL2) (H : HankelOperator)
    (hH : ∀ j, H (hardyBasis j) = hankelColumn σ j) : RepresentsHankel σ H := by
  intro f v _hf hv
  let w := multiply (hv.toLp v.val) (star σ)
  let L := innerSL ℂ v ∘L H
  let R := innerSL ℂ w ∘L hardy.subtypeL
  have he : L = R := clm_eq_of_hilbertBasis hardyBasis L R (fun j => by
    change inner ℂ v (H (hardyBasis j)) = inner ℂ w (hardyBasis j).val
    rw [hH j,hankelColumn_inner,coreForm_eq_inner_right σ _ _ hv])
  have h := congrArg (fun A => A f) he
  change inner ℂ v (H f) = inner ℂ w f.val at h
  exact h.trans (coreForm_eq_inner_right σ f.val v.val hv).symm

theorem representsHankel_columnEnergy (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) :
    columnEnergy H hardyBasis = classicalCoefficientEnergy g := by
  unfold columnEnergy
  calc
    _ = ∑' j, ENNReal.ofReal (‖hankelColumn (star (multiply coordinate g)) j‖^2) := tsum_congr (fun j => by
      rw [representsHankel_columns _ H hH j,← ofReal_norm,
        ENNReal.ofReal_pow (norm_nonneg (hankelColumn _ j))])
    _ = _ := hankelColumns_energy g

/-- The classical Hankel Hilbert–Schmidt membership criterion; analyticity is not needed for its nonnegative matrix. -/
theorem classicalHankel_schatten_two (g : BoundaryL2) :
    HasSchattenHankel 2 (star (multiply coordinate g)) ↔ classicalCoefficientEnergy g < ∞ := by
  constructor
  · rintro ⟨H,hH,hs⟩
    have he := (schatten_two_iff_columnEnergy H hardyBasis).mp hs
    rwa [representsHankel_columnEnergy g H hH] at he
  · intro he
    have hv : (∑' j, ENNReal.ofReal (‖hankelColumn (star (multiply coordinate g)) j‖^2)) < ∞ := by
      rw [hankelColumns_energy]
      exact he
    obtain ⟨H,hH,hs,_hg⟩ := exists_columnOperator hardyBasis (hankelColumn (star (multiply coordinate g))) hv
    exact ⟨H,representsHankel_of_columns _ H hH,hs⟩

theorem classicalHankel_norm_two (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H) (hs : Schatten 2 H) :
    ENNReal.ofReal (schattenNorm 2 H^2) = classicalCoefficientEnergy g :=
  (schattenNorm_two_sq_columnEnergy H hardyBasis hs).trans (representsHankel_columnEnergy g H hH)

end ClassicalHankelMatrix


section ClassicalDirichletBoundary

/-- Fourier Parseval in the extended nonnegative integral form, for every L² vector. -/
theorem fourierParseval_lintegral (f : BoundaryL2) :
    (∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂circleMeasure) =
      ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeff f n‖^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖f t‖)),← tsum_sq_fourierCoeff f]
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖fourierCoeff f n‖)
    (hasSum_sq_fourierCoeff f).summable

theorem fourier_position_add (n : ℤ) (x y : Boundary) :
    fourier (T := 1) n (x+y) = fourier n x*fourier n y := by
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]

/-- Actual Haar-preserving translation of the native L² class. -/
def boundaryTranslate (h : Boundary) : BoundaryL2 →ₗᵢ[ℂ] BoundaryL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun s => s+h) (measurePreserving_add_right circleMeasure h)

theorem boundaryTranslate_ae (h : Boundary) (g : BoundaryL2) :
    boundaryTranslate h g =ᵐ[circleMeasure] fun s => g (s+h) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right circleMeasure h)

theorem boundaryTranslate_fourierBasis (h : Boundary) (n : ℤ) :
    boundaryTranslate h (fourierBasis (T := 1) n) =
      fourier (T := 1) n h • fourierBasis (T := 1) n := by
  apply Lp.ext
  filter_upwards [boundaryTranslate_ae h (fourierBasis (T := 1) n),
    (measurePreserving_add_right circleMeasure h).quasiMeasurePreserving.ae_eq_comp (fourierBasis_ae n),
    Lp.coeFn_smul (fourier (T := 1) n h) (fourierBasis (T := 1) n),fourierBasis_ae n]
    with s ht hn hs hb
  rw [ht,hs]
  change (fourierBasis (T := 1) n) (s+h) = fourier n h*(fourierBasis (T := 1) n) s
  simp only [Function.comp_apply] at hn
  rw [hn,hb,fourier_position_add,mul_comm]

theorem fourier_mul_conj (n : ℤ) (h : Boundary) :
    fourier (T := 1) n h*conj (fourier n h) = 1 := by
  rw [← fourier_neg,← fourier_add]
  simp

theorem fourierCoeff_translate (h : Boundary) (g : BoundaryL2) (n : ℤ) :
    fourierCoeff (boundaryTranslate h g) n = fourier (T := 1) n h*fourierCoeff g n := by
  have he := (boundaryTranslate h).inner_map_map (fourierBasis (T := 1) n) g
  rw [boundaryTranslate_fourierBasis,inner_smul_left,← HilbertBasis.repr_apply_apply,
    ← HilbertBasis.repr_apply_apply,fourierBasis_repr,fourierBasis_repr] at he
  calc
    _ = (fourier (T := 1) n h*conj (fourier n h))*fourierCoeff (boundaryTranslate h g) n := by
      rw [fourier_mul_conj,one_mul]
    _ = _ := by rw [mul_assoc,he]

/-- The actual L² difference-quotient slice; zero denominators use Lean's ordinary total division. -/
def boundarySlice (h : Boundary) (g : BoundaryL2) : BoundaryL2 :=
  (fourier (T := 1) 1 h-1)⁻¹ • (fourier (T := 1) 1 h • boundaryTranslate h g-g)

def geometricMultiplier (n : ℤ) (h : Boundary) : ℂ :=
  (fourier (T := 1) (n+1) h-1)/(fourier (T := 1) 1 h-1)

theorem geometricMultiplier_measurable (n : ℤ) : Measurable (geometricMultiplier n) :=
  (((fourier (T := 1) (n+1)).continuous.measurable).sub measurable_const).div
    (((fourier (T := 1) 1).continuous.measurable).sub measurable_const)

theorem boundarySlice_ae (h : Boundary) (g : BoundaryL2) :
    boundarySlice h g =ᵐ[circleMeasure] fun s =>
      (fourier (T := 1) 1 h*g (s+h)-g s)/(fourier (T := 1) 1 h-1) := by
  filter_upwards [Lp.coeFn_smul (fourier (T := 1) 1 h-1)⁻¹
      (fourier (T := 1) 1 h • boundaryTranslate h g-g),
    Lp.coeFn_sub (fourier (T := 1) 1 h • boundaryTranslate h g) g,
    Lp.coeFn_smul (fourier (T := 1) 1 h) (boundaryTranslate h g),boundaryTranslate_ae h g]
    with s h1 h2 h3 h4
  change ((fourier (T := 1) 1 h-1)⁻¹ • (fourier (T := 1) 1 h • boundaryTranslate h g-g)) s = _
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at h1 h2 h3
  rw [h1,h2,h3,h4]
  simp only [div_eq_mul_inv,mul_comm]

theorem fourierCoeff_boundarySlice (h : Boundary) (g : BoundaryL2) (n : ℤ) :
    fourierCoeff (boundarySlice h g) n = geometricMultiplier n h*fourierCoeff g n := by
  simp only [boundarySlice,← fourierBasis_repr,map_smul,map_sub,lp.coeFn_smul,lp.coeFn_sub,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  simp only [fourierBasis_repr,fourierCoeff_translate,geometricMultiplier,fourier_add,div_eq_mul_inv]
  ring


/-- Negative coefficients vanish before the extended Parseval sum is reindexed. -/
theorem boundarySlice_Parseval (h : Boundary) (g : BoundaryL2) (hg : g ∈ hardy) :
    (∫⁻ s, ENNReal.ofReal (‖(fourier (T := 1) 1 h*g (s+h)-g s)/
      (fourier (T := 1) 1 h-1)‖^2) ∂circleMeasure) =
      ∑' n : ℕ, ENNReal.ofReal (‖geometricMultiplier (n : ℤ) h*fourierCoeff g (n : ℤ)‖^2) := by
  have he := lintegral_congr_ae ((boundarySlice_ae h g).fun_comp (fun z : ℂ => ENNReal.ofReal (‖z‖^2)))
  simp only [Function.comp_apply] at he
  rw [← he,fourierParseval_lintegral]
  simp only [fourierCoeff_boundarySlice]
  symm
  apply (show Function.Injective (fun n : ℕ => (n : ℤ)) from Nat.cast_injective).tsum_eq (f := fun n : ℤ => ENNReal.ofReal (‖geometricMultiplier n h*fourierCoeff g n‖^2))
  intro n hn
  by_contra h
  have hneg : n < 0 := by
    by_contra hnneg
    obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
    exact h ⟨k,hk.symm⟩
  have hz := (mem_hardy_iff g).mp hg n hneg
  simp only [Function.mem_support,hz,mul_zero,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero,ne_eq,not_true_eq_false] at hn

/-- The finite geometric Fourier polynomial has exactly n+1 orthonormal terms. -/
def geometricPolynomial (n : ℕ) : BoundaryL2 := ∑ k ∈ Finset.range (n+1), fourierBasis (T := 1) (k : ℤ)

theorem geometricPolynomial_norm_sq (n : ℕ) : ‖geometricPolynomial n‖^2 = (n+1 : ℝ) := by
  have hon : Orthonormal ℂ (fun k : ℕ => fourierBasis (T := 1) (k : ℤ)) :=
    (fourierBasis (T := 1)).orthonormal.comp (fun n : ℕ => (n : ℤ)) Nat.cast_injective
  have hi := hon.inner_sum (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (Finset.range (n+1))
  simp only [one_smul,starRingEnd_apply,star_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hi
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (geometricPolynomial n) (geometricPolynomial n)).re = _
  change (inner ℂ (∑ k ∈ Finset.range (n+1),fourierBasis (T := 1) (k : ℤ))
    (∑ k ∈ Finset.range (n+1),fourierBasis (T := 1) (k : ℤ))).re = _
  rw [hi]
  norm_cast

theorem geometricPolynomial_ae (n : ℕ) :
    geometricPolynomial n =ᵐ[circleMeasure] fun h => ∑ k ∈ Finset.range (n+1), fourier (T := 1) (k : ℤ) h := by
  have he := Lp.coeFn_finsetSum (Finset.range (n+1)) (fun k : ℕ => fourierBasis (T := 1) (k : ℤ))
  filter_upwards [he,ae_all_iff.mpr (fun k : ℕ => fourierBasis_ae (k : ℤ))] with h hs hb
  change (∑ k ∈ Finset.range (n+1), fourierBasis (T := 1) (k : ℤ)) h = _
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => hb k)

instance circleMeasure_nullSingleton : NullSingletonClass circleMeasure := by
  have hv : circleMeasure = (volume : Measure Boundary) := by
    simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  constructor
  intro x
  rw [hv,← Metric.closedBall_zero,AddCircle.volume_closedBall]
  simp

theorem geometricMultiplier_ae (n : ℕ) :
    geometricMultiplier (n : ℤ) =ᵐ[circleMeasure] geometricPolynomial n := by
  filter_upwards [circleMeasure.ae_ne (0 : Boundary),geometricPolynomial_ae n] with h hh hp
  have he : fourier (T := 1) 1 h ≠ 1 := by
    intro he
    apply hh
    apply AddCircle.injective_toCircle (T := 1) one_ne_zero
    apply Subtype.ext
    simpa only [fourier_one,AddCircle.toCircle_zero,Circle.coe_one] using he
  rw [hp]
  simp only [geometricMultiplier,← Nat.cast_add_one,fourier_nat_pow]
  exact (geom_sum_eq he (n+1)).symm

theorem fourier_lintegral_norm_sq (f : BoundaryL2) :
    (∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂circleMeasure) = ENNReal.ofReal (‖f‖^2) := by
  rw [fourierParseval_lintegral]
  calc
    _ = ∑' n : ℤ, ‖inner ℂ (fourierBasis (T := 1) n) f‖ₑ^2 := tsum_congr (fun n => by
      rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply,← ofReal_norm,
        ENNReal.ofReal_pow (norm_nonneg (inner ℂ (fourierBasis (T := 1) n) f))])
    _ = ‖f‖ₑ^2 := tsum_basis_inner_enorm_sq (fourierBasis (T := 1)) f
    _ = _ := by rw [← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg f)]

/-- The geometric multiplier has boundary energy n+1; h=0 is excluded only a.e. -/
theorem geometricMultiplier_energy (n : ℕ) :
    (∫⁻ h, ENNReal.ofReal (‖geometricMultiplier (n : ℤ) h‖^2) ∂circleMeasure) =
      ENNReal.ofReal (n+1 : ℝ) := by
  have he := lintegral_congr_ae ((geometricMultiplier_ae n).fun_comp (fun z : ℂ => ENNReal.ofReal (‖z‖^2)))
  simp only [Function.comp_apply] at he
  rw [he,fourier_lintegral_norm_sq,geometricPolynomial_norm_sq]


/-- Literal boundary divided difference, including its ordinary zero-denominator value. -/
def dirichletQuotient (g : BoundaryL2) (t s : Boundary) : ℂ :=
  (fourier (T := 1) 1 t*g t-fourier (T := 1) 1 s*g s)/
    (fourier (T := 1) 1 t-fourier (T := 1) 1 s)

theorem dirichletQuotient_measurable (g : BoundaryL2) :
    Measurable (fun p : Boundary × Boundary => ENNReal.ofReal (‖dirichletQuotient g p.1 p.2‖^2)) := by
  have hg : Measurable (g : Boundary → ℂ) := (Lp.stronglyMeasurable g).measurable
  have he : Measurable (fourier (T := 1) 1) := (fourier (T := 1) 1).continuous.measurable
  exact ENNReal.measurable_ofReal.comp
    (((((he.comp measurable_fst).mul (hg.comp measurable_fst)).sub
      ((he.comp measurable_snd).mul (hg.comp measurable_snd))).div
      ((he.comp measurable_fst).sub (he.comp measurable_snd))).norm.pow_const 2)

theorem dirichletQuotient_shear (g : BoundaryL2) (h s : Boundary) :
    dirichletQuotient g (h+s) s =
      (fourier (T := 1) 1 h*g (s+h)-g s)/(fourier (T := 1) 1 h-1) := by
  have he : fourier (T := 1) 1 s ≠ 0 := by
    intro hz
    have hh := fourier_mul_conj 1 s
    rw [hz,zero_mul] at hh
    exact zero_ne_one hh
  unfold dirichletQuotient
  rw [fourier_position_add,add_comm h s]
  calc
    _ = (fourier (T := 1) 1 s*(fourier (T := 1) 1 h*g (s+h)-g s))/
        (fourier (T := 1) 1 s*(fourier (T := 1) 1 h-1)) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ he

/-- Haar shear rewrites the original double boundary integral as actual L² slices. -/
theorem dirichletBoundary_shear (g : BoundaryL2) :
    (∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖dirichletQuotient g t s‖^2) ∂circleMeasure ∂circleMeasure) =
      ∫⁻ h, ∫⁻ s, ENNReal.ofReal (‖(fourier (T := 1) 1 h*g (s+h)-g s)/
        (fourier (T := 1) 1 h-1)‖^2) ∂circleMeasure ∂circleMeasure := by
  let F : Boundary × Boundary → ℝ≥0∞ := fun p => ENNReal.ofReal (‖dirichletQuotient g p.1 p.2‖^2)
  have hF : Measurable F := dirichletQuotient_measurable g
  have hs := measurePreserving_add_prod circleMeasure circleMeasure
  calc
    _ = ∫⁻ p, F p ∂circleMeasure.prod circleMeasure := (lintegral_prod F hF.aemeasurable).symm
    _ = ∫⁻ p, F (p.1+p.2,p.2) ∂circleMeasure.prod circleMeasure :=
      (hs.lintegral_comp hF).symm
    _ = ∫⁻ h, ∫⁻ s, F (h+s,s) ∂circleMeasure ∂circleMeasure :=
      lintegral_prod _ (hF.comp hs.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro h
      apply lintegral_congr
      intro s
      exact congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖^2)) (dirichletQuotient_shear g h s)

/-- Exact classical boundary Dirichlet identity, valid also when both energies are infinite. -/
theorem classicalDirichlet_boundary (g : BoundaryL2) (hg : g ∈ hardy) :
    (∫⁻ t, ∫⁻ s, ENNReal.ofReal (‖dirichletQuotient g t s‖^2) ∂circleMeasure ∂circleMeasure) =
      classicalCoefficientEnergy g := by
  rw [dirichletBoundary_shear]
  have he : ∀ h : Boundary,
      (∫⁻ s, ENNReal.ofReal (‖(fourier (T := 1) 1 h*g (s+h)-g s)/
        (fourier (T := 1) 1 h-1)‖^2) ∂circleMeasure) =
        ∑' n : ℕ, ENNReal.ofReal (‖geometricMultiplier (n : ℤ) h*fourierCoeff g (n : ℤ)‖^2) :=
    fun h => boundarySlice_Parseval h g hg
  simp_rw [he]
  rw [lintegral_tsum]
  · unfold classicalCoefficientEnergy
    apply tsum_congr
    intro n
    calc
      _ = ∫⁻ h, ENNReal.ofReal (‖geometricMultiplier (n : ℤ) h‖^2)*
          ENNReal.ofReal (‖fourierCoeff g (n : ℤ)‖^2) ∂circleMeasure :=
        lintegral_congr (fun h => by
          rw [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖geometricMultiplier (n : ℤ) h‖)])
      _ = ENNReal.ofReal (n+1 : ℝ)*ENNReal.ofReal (‖fourierCoeff g (n : ℤ)‖^2) := by
        rw [lintegral_mul_const _ ((geometricMultiplier_measurable (n : ℤ)).norm.pow_const 2 |>.ennreal_ofReal),
          geometricMultiplier_energy]
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  · intro n
    have hm : Measurable (geometricMultiplier (n : ℤ)) :=
      (((fourier (T := 1) ((n : ℤ)+1)).continuous.measurable).sub measurable_const).div
        (((fourier (T := 1) 1).continuous.measurable).sub measurable_const)
    exact (ENNReal.measurable_ofReal.comp ((hm.mul measurable_const).norm.pow_const 2)).aemeasurable

/-- Classical membership, exact Schatten gauge and boundary energy are all established. -/
theorem classicalDirichlet : ClassicalDirichletObligation where
  membership g _hg := classicalHankel_schatten_two g
  norm g _hg H hH hs := classicalHankel_norm_two g H hH hs
  boundary g hg := classicalDirichlet_boundary g hg

end ClassicalDirichletBoundary

section RemovableKernelCalculus

/-- The continuous diagonal is forced by the three ordinary complex difference quotients. -/
theorem removableCalculus : RemovableCalculusObligation := by
  intro v a b F hv ha hb hcont hfrac
  have ho : IsOpen disk := isOpen_lt continuous_norm continuous_const
  have off (z : ℂ) (hz : z ∈ disk) (w : ℂ) (hw : w ∈ disk) (hne : z ≠ w) :
      F z w = (z*a z-w*a w+v z*(w*b w)-v w*(z*b z))/(z-w) := by
    rw [hfrac z hz w hw hne]
    congr 1
    ring
  have diag (z : ℂ) (hz : z ∈ disk) : F z z =
      deriv (fun t => t*a t) z+deriv v z*(z*b z)-v z*deriv (fun t => t*b t) z := by
    have da : DifferentiableAt ℂ a z := (ha z hz).differentiableAt (ho.mem_nhds hz)
    have db : DifferentiableAt ℂ b z := (hb z hz).differentiableAt (ho.mem_nhds hz)
    have dv : DifferentiableAt ℂ v z := (hv z hz).differentiableAt (ho.mem_nhds hz)
    have ht := (((differentiableAt_id.mul da).hasDerivAt.tendsto_slope).add
      (dv.hasDerivAt.tendsto_slope.mul_const (z*b z))).sub
        ((differentiableAt_id.mul db).hasDerivAt.tendsto_slope.const_mul (v z))
    have he : (fun w => F z w) =ᶠ[𝓝[≠] z]
        (fun w => slope (fun t => t*a t) z w+slope v z w*(z*b z)-v z*slope (fun t => t*b t) z w) := by
      filter_upwards [(show ∀ᶠ w in 𝓝 z, w ∈ disk from ho.mem_nhds hz).filter_mono nhdsWithin_le_nhds,
        (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] z, w ≠ z)] with w hw hne
      have hnz : z ≠ w := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,ne_eq,eq_comm] using hne
      rw [off z hz w hw hnz,slope_def_field,slope_def_field,slope_def_field]
      field_simp
      ring
    exact tendsto_nhds_unique ((hcont z hz).tendsto.mono_left nhdsWithin_le_nhds) (ht.congr' he.symm)
  constructor
  · intro z hz w hw
    split_ifs with hzw
    · subst w
      exact diag z hz
    · exact off z hz w hw hzw
  · intro z hz
    rw [diag z hz]
    have da : DifferentiableAt ℂ a z := (ha z hz).differentiableAt (ho.mem_nhds hz)
    have db : DifferentiableAt ℂ b z := (hb z hz).differentiableAt (ho.mem_nhds hz)
    have dv : DifferentiableAt ℂ v z := (hv z hz).differentiableAt (ho.mem_nhds hz)
    have hx := ((hasDerivAt_id z).fun_mul (da.hasDerivAt.fun_add (dv.hasDerivAt.fun_mul db.hasDerivAt))).deriv
    have hA := ((hasDerivAt_id z).fun_mul da.hasDerivAt).deriv
    have hB := ((hasDerivAt_id z).fun_mul db.hasDerivAt).deriv
    simp only [id_eq] at hx hA hB
    rw [hx,hA,hB]
    ring

end RemovableKernelCalculus

section ActualEnergyKernels

/-- Every square-model vector has its literal two orthogonal model components. -/
theorem squareModel_decomposition (u : BoundaryLInf) (hu : IsInner u) (η : Ambient u) :
    η.val = eta₁ u η.val+multiply u (eta₂ u η.val) := by
  let p := (model u).orthogonalProjectionOnto η.val
  let h : Hardy := ⟨η.val-p.val,hardy.sub_mem η.property.1 p.property.1⟩
  have hz : (model u).orthogonalProjectionOnto h.val = 0 := by
    change (model u).orthogonalProjectionOnto (η.val-p.val) = 0
    rw [map_sub,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,sub_self]
  obtain ⟨q,hq⟩ := innerFactor_of_modelProjection_zero u hu h hz
  have hmul : multiply u q.val ∈ model (multiplyInf u u) := by
    rw [← hq]
    exact (model (multiplyInf u u)).sub_mem η.property (model_mem_squareModel u hu p)
  have hp := modelProjection_multiply_inner u u hu hu q
  have he : multiply u q.val = multiply u (((model u).orthogonalProjectionOnto q.val).val) := by
    have hval := congrArg Subtype.val hp
    exact (Submodule.starProjection_eq_self_iff.mpr hmul).symm.trans hval
  have hqmodel : q.val ∈ model u := by
    have hqe := (innerMultiplyIsometry u hu).injective he
    rw [hqe]
    exact ((model u).orthogonalProjectionOnto q.val).property
  let b : Model u := ⟨q.val,hqmodel⟩
  have hη : η.val = p.val+multiply u b.val := by
    change η.val-p.val = multiply u b.val at hq
    exact sub_eq_iff_eq_add.mp hq |>.trans (add_comm _ _)
  have hneg : (model u).orthogonalProjectionOnto (multiply (star u) p.val) = 0 := by
    apply (model u).orthogonalProjectionOnto_eq_zero_iff.mpr
    exact Submodule.orthogonal_le (show model u ≤ hardy from inf_le_left)
      ((mem_model_iff_spectrum _ _).mp p.property).2
  have hb : (model u).orthogonalProjectionOnto (multiply (star u) η.val) = b := by
    rw [hη,map_add,multiply_star_cancel u hu.2,map_add,hneg,zero_add]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self b
  change η.val = p.val+multiply u (((model u).orthogonalProjectionOnto (multiply (star u) η.val)).val)
  rw [hb]
  exact hη

/-- The Hardy projection of bar(u)η is exactly the second model component. -/
theorem hardyProjection_star_ambient (u : BoundaryLInf) (hu : IsInner u) (η : Ambient u) :
    (hardy.orthogonalProjectionOnto (multiply (star u) η.val)).val = eta₂ u η.val := by
  have hη := squareModel_decomposition u hu η
  have hneg : hardy.orthogonalProjectionOnto (multiply (star u) (eta₁ u η.val)) = 0 := by
    apply hardy.orthogonalProjectionOnto_eq_zero_iff.mpr
    exact ((mem_model_iff_spectrum _ _).mp ((model u).orthogonalProjectionOnto η.val).property).2
  have hb : eta₂ u η.val ∈ hardy := ((model u).orthogonalProjectionOnto (multiply (star u) η.val)).property.1
  nth_rw 1 [hη]
  rw [map_add,multiply_star_cancel u hu.2,map_add,hneg,zero_add]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨eta₂ u η.val,hb⟩ : Hardy))


/-- A fixed bounded model kernel turns the raw two-kernel integral into an actual model vector. -/
def energyKernelSection (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) (z : Disk) : Model u :=
  (model u).orthogonalProjectionOnto
    (multiply (star ((bounded_modelReproducingKernel u hu z).toLp (modelReproducingKernel u hu z).val)) η)

theorem FKernel_eq_section (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) (z w : Disk) :
    FKernel u η z.val w.val = analyticValue (energyKernelSection u hu η z).val w.val := by
  rw [← inner_modelReproducingKernel u hu w (energyKernelSection u hu η z)]
  let az := (bounded_modelReproducingKernel u hu z).toLp (modelReproducingKernel u hu z).val
  have hp : FKernel u η z.val w.val = inner ℂ (modelReproducingKernel u hu w).val
      (multiply (star az) η) := by
    rw [FKernel,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiply_ae (star az) η,Lp.coeFn_star az,
      (bounded_modelReproducingKernel u hu z).coeFn_toLp,
      modelReproducingKernel_ae u hu z,modelReproducingKernel_ae u hu w]
      with t hm ha haz hz hw
    change (star az) t = conj (az t) at ha
    change az t = (modelReproducingKernel u hu z).val t at haz
    simp only [RCLike.inner_apply,hm,ha,haz,hz,hw,map_mul]
    ring
  rw [hp]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (modelReproducingKernel u hu w) _).symm

theorem FKernel_symmetric (u : BoundaryLInf) (η : BoundaryL2) (z w : ℂ) :
    FKernel u η z w = FKernel u η w z := by
  unfold FKernel
  congr 1
  funext t
  rw [mul_comm (kernelBoundary u z t) (kernelBoundary u w t)]

/-- Both actual sections lie in K_u, without a finite-energy or bounded-symbol hypothesis. -/
theorem FKernel_sections (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) :
    (∀ w ∈ disk, ∃ f : Model u, ∀ z ∈ disk, analyticValue f.val z = FKernel u η z w) ∧
    (∀ z ∈ disk, ∃ f : Model u, ∀ w ∈ disk, analyticValue f.val w = FKernel u η z w) := by
  constructor
  · intro w hw
    refine ⟨energyKernelSection u hu η ⟨w,hw⟩,?_⟩
    intro z hz
    rw [FKernel_symmetric u η z w]
    exact (FKernel_eq_section u hu η ⟨w,hw⟩ ⟨z,hz⟩).symm
  · intro z hz
    exact ⟨energyKernelSection u hu η ⟨z,hz⟩,fun w hw => (FKernel_eq_section u hu η ⟨z,hz⟩ ⟨w,hw⟩).symm⟩

/-- The honest bounded Hardy product of the two Szegő kernels. -/
def szegoProduct (z w : Disk) : BoundaryL2 :=
  multiply ((bounded_szegoKernel z).toLp (szegoKernel z).val) (szegoKernel w).val

theorem szegoProduct_mem_hardy (z w : Disk) : szegoProduct z w ∈ hardy := by
  have he : toL2 ((bounded_szegoKernel z).toLp (szegoKernel z).val) = (szegoKernel z).val :=
    Lp.ext ((toL2_ae _).trans (bounded_szegoKernel z).coeFn_toLp)
  exact multiply_mem_hardy _ (he.symm ▸ (szegoKernel z).property) _ (szegoKernel w).property

theorem szegoProduct_ae (z w : Disk) :
    szegoProduct z w =ᵐ[circleMeasure] fun t =>
      (1-conj z.val*fourier (T := 1) 1 t)⁻¹*(1-conj w.val*fourier (T := 1) 1 t)⁻¹ := by
  filter_upwards [multiply_ae ((bounded_szegoKernel z).toLp (szegoKernel z).val) (szegoKernel w).val,
    (bounded_szegoKernel z).coeFn_toLp,szegoKernel_ae z,szegoKernel_ae w] with t hm ha hz hw
  change multiply ((bounded_szegoKernel z).toLp (szegoKernel z).val) (szegoKernel w).val t = _
  rw [hm,ha,hz,hw]

/-- Off-diagonal elementary partial fractions in the actual L² Hardy space. -/
theorem szegoProduct_fractions (z w : Disk) (hne : z.val ≠ w.val) :
    szegoProduct z w = (conj z.val-conj w.val)⁻¹ •
      (conj z.val • (szegoKernel z).val-conj w.val • (szegoKernel w).val) := by
  apply Lp.ext
  filter_upwards [szegoProduct_ae z w,Lp.coeFn_smul (conj z.val-conj w.val)⁻¹
      (conj z.val • (szegoKernel z).val-conj w.val • (szegoKernel w).val),
    Lp.coeFn_sub (conj z.val • (szegoKernel z).val) (conj w.val • (szegoKernel w).val),
    Lp.coeFn_smul (conj z.val) (szegoKernel z).val,Lp.coeFn_smul (conj w.val) (szegoKernel w).val,
    szegoKernel_ae z,szegoKernel_ae w] with t hp hs hd hz hw hzt hwt
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply] at hs hd hz hw
  rw [hp,hs,hd,hz,hw,hzt,hwt]
  have hz0 : (1-conj z.val*fourier (T := 1) 1 t) ≠ 0 := by
    have hh := kernelDenominator_norm_lower z t
    intro he
    rw [he,norm_zero] at hh
    linarith [show ‖z.val‖ < 1 from z.property]
  have hw0 : (1-conj w.val*fourier (T := 1) 1 t) ≠ 0 := by
    have hh := kernelDenominator_norm_lower w t
    intro he
    rw [he,norm_zero] at hh
    linarith [show ‖w.val‖ < 1 from w.property]
  have hconj : conj z.val-conj w.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (by simpa only [Complex.conj_conj] using congrArg conj he))
  field_simp [hz0,hw0,hconj]
  field_simp [hz0,hw0,hconj]
  ring

/-- The product-kernel pairing is the ordinary divided difference of zf(z). -/
theorem inner_szegoProduct (z w : Disk) (hne : z.val ≠ w.val) (f : Hardy) :
    inner ℂ (szegoProduct z w) f.val =
      (z.val*analyticValue f.val z.val-w.val*analyticValue f.val w.val)/(z.val-w.val) := by
  have hz : inner ℂ (szegoKernel z).val f.val = analyticValue f.val z.val := inner_szegoKernel z f
  have hw : inner ℂ (szegoKernel w).val f.val = analyticValue f.val w.val := inner_szegoKernel w f
  rw [szegoProduct_fractions z w hne,inner_smul_left,inner_sub_left,inner_smul_left,inner_smul_left,hz,hw]
  simp only [map_inv₀,map_sub,Complex.conj_conj,div_eq_mul_inv]
  ring


/-- Actual bounded product of the two model reproducing kernels. -/
def modelKernelProduct (u : BoundaryLInf) (hu : IsInner u) (z w : Disk) : BoundaryL2 :=
  multiply ((bounded_modelReproducingKernel u hu z).toLp (modelReproducingKernel u hu z).val)
    (modelReproducingKernel u hu w).val

theorem modelKernelProduct_ae (u : BoundaryLInf) (hu : IsInner u) (z w : Disk) :
    modelKernelProduct u hu z w =ᵐ[circleMeasure] fun t =>
      kernelBoundary u z.val t*kernelBoundary u w.val t := by
  filter_upwards [multiply_ae ((bounded_modelReproducingKernel u hu z).toLp (modelReproducingKernel u hu z).val)
      (modelReproducingKernel u hu w).val,
    (bounded_modelReproducingKernel u hu z).coeFn_toLp,
    modelReproducingKernel_ae u hu z,modelReproducingKernel_ae u hu w] with t hm ha hz hw
  change multiply ((bounded_modelReproducingKernel u hu z).toLp (modelReproducingKernel u hu z).val)
    (modelReproducingKernel u hu w).val t = _
  rw [hm,ha,hz,hw]

/-- Expansion contains honest Hardy products; its u² term is killed by ambient orthogonality. -/
theorem modelKernelProduct_expansion (u : BoundaryLInf) (hu : IsInner u) (z w : Disk) :
    modelKernelProduct u hu z w =
      szegoProduct z w-(conj (innerValue u z.val)+conj (innerValue u w.val)) • multiply u (szegoProduct z w)+
        (conj (innerValue u z.val)*conj (innerValue u w.val)) • multiply (multiplyInf u u) (szegoProduct z w) := by
  let S := szegoProduct z w
  let a := conj (innerValue u z.val)+conj (innerValue u w.val)
  let c := conj (innerValue u z.val)*conj (innerValue u w.val)
  apply Lp.ext
  filter_upwards [modelKernelProduct_ae u hu z w,szegoProduct_ae z w,
    Lp.coeFn_add (S-a • multiply u S) (c • multiply (multiplyInf u u) S),
    Lp.coeFn_sub S (a • multiply u S),Lp.coeFn_smul a (multiply u S),
    Lp.coeFn_smul c (multiply (multiplyInf u u) S),multiply_ae u S,
    multiply_ae (multiplyInf u u) S,multiplyInf_ae u u] with t hp hs hsum hd ha hc hm hm2 hu2
  change modelKernelProduct u hu z w t = (S-a • multiply u S+c • multiply (multiplyInf u u) S) t
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hsum hd ha hc
  change S t = _ at hs
  rw [hp,hsum,hd,ha,hc,hm,hm2,hu2,hs]
  simp only [a,c,kernelBoundary,div_eq_mul_inv]
  ring

theorem FKernel_eq_inner_product (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) (z w : Disk) :
    FKernel u η z.val w.val = inner ℂ (modelKernelProduct u hu z w) η := by
  rw [FKernel,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modelKernelProduct_ae u hu z w] with t ht
  rw [RCLike.inner_apply,ht]

theorem inner_szegoProduct_multiply (u : BoundaryLInf) (hu : IsInner u) (η : Ambient u) (z w : Disk) :
    inner ℂ (multiply u (szegoProduct z w)) η.val = inner ℂ (szegoProduct z w) (eta₂ u η.val) := by
  rw [inner_multiply_left]
  have hp := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨szegoProduct z w,szegoProduct_mem_hardy z w⟩ : Hardy) (multiply (star u) η.val)
  change inner ℂ (szegoProduct z w) (hardy.orthogonalProjectionOnto (multiply (star u) η.val)).val = _ at hp
  rw [hardyProjection_star_ambient u hu η] at hp
  exact hp.symm

/-- Literal raw kernel partial fractions, before taking the removable diagonal. -/
theorem FKernel_fractions (u : BoundaryLInf) (hu : IsInner u) (η : Ambient u) (z w : Disk)
    (hne : z.val ≠ w.val) :
    FKernel u η.val z.val w.val =
      (z.val*analyticValue η.val z.val-w.val*analyticValue η.val w.val-
        (innerValue u z.val+innerValue u w.val)*
          (z.val*analyticValue (eta₂ u η.val) z.val-w.val*analyticValue (eta₂ u η.val) w.val))/(z.val-w.val) := by
  rw [FKernel_eq_inner_product u hu,modelKernelProduct_expansion,
    inner_add_left,inner_sub_left,inner_smul_left,inner_smul_left,
    inner_multiply_model (multiplyInf u u) η ⟨szegoProduct z w,szegoProduct_mem_hardy z w⟩,
    inner_szegoProduct_multiply u hu η]
  simp only [map_add,map_mul,Complex.conj_conj,mul_zero,add_zero]
  rw [inner_szegoProduct z w hne ⟨η.val,η.property.1⟩,
    inner_szegoProduct z w hne ⟨eta₂ u η.val,((model u).orthogonalProjectionOnto (multiply (star u) η.val)).property.1⟩]
  ring


theorem analyticValue_coordinate_multiply (f : Hardy) (z : Disk) :
    analyticValue (multiply coordinate f.val) z.val = z.val*analyticValue f.val z.val := by
  have hcoord : toL2 coordinate ∈ hardy := by
    change toL2 (mode 1) ∈ hardy
    rw [toL2_mode]
    exact fourierBasis_mem_hardy 1
  rw [analyticValue_multiply coordinate hcoord f z]
  have hc : innerValue coordinate z.val = z.val := by
    change analyticValue (toL2 (mode 1)) z.val = z.val
    rw [toL2_mode]
    simpa only [Nat.cast_one,pow_one] using analyticValue_fourierBasis 1 z.val
  rw [hc]

/-- All raw source-specific energy kernel calculations on the literal native spaces. -/
theorem kernelCalculus : KernelCalculusObligation where
  decomposition u hu _hn η := squareModel_decomposition u hu η
  value u hu _hn η z hz := by
    calc
      _ = analyticValue (eta₁ u η.val+multiply u (eta₂ u η.val)) z :=
        congrArg (fun f => analyticValue f z) (squareModel_decomposition u hu η)
      _ = _ := by
        rw [analyticValue_add _ _ hz,
          analyticValue_multiply u hu.1 ⟨eta₂ u η.val,
            ((model u).orthogonalProjectionOnto (multiply (star u) η.val)).property.1⟩ ⟨z,hz⟩]
  hvalue u _hu _hn η z hz :=
    analyticValue_coordinate_multiply ⟨eta₁ u η.val,((model u).orthogonalProjectionOnto η.val).property.1⟩ ⟨z,hz⟩
  gvalue u _hu _hn η z hz :=
    analyticValue_coordinate_multiply ⟨eta₂ u η.val,
      ((model u).orthogonalProjectionOnto (multiply (star u) η.val)).property.1⟩ ⟨z,hz⟩
  differentiable u _hu _hn η :=
    ⟨differentiableOn_analyticValue (toL2 u),differentiableOn_analyticValue (eta₁ u η.val),
      differentiableOn_analyticValue (eta₂ u η.val)⟩
  continuous_diagonal u hu _hn η z hz := by
    let f := energyKernelSection u hu η.val ⟨z,hz⟩
    have he : FKernel u η.val z =ᶠ[𝓝 z] analyticValue f.val := by
      have ho : IsOpen disk := isOpen_lt continuous_norm continuous_const
      filter_upwards [ho.mem_nhds hz] with w hw
      exact FKernel_eq_section u hu η.val ⟨z,hz⟩ ⟨w,hw⟩
    exact (continuousAt_congr he).mpr ((analyticOnNhd_analyticValue f.val z hz).continuousAt)
  fractions u hu _hn η z hz w hw hne := FKernel_fractions u hu η ⟨z,hz⟩ ⟨w,hw⟩ hne

end ActualEnergyKernels


/-- The one-atom reduction after discharging its core, ideal and generic scalar inputs.
Regularization, triangular/WOT and Schatten/model inputs are supplied separately. -/
theorem oneAtomSplitting (hT : TriangularBoundObligation)
    (hW : SchattenWeakSubsequenceObligation) (hR : AtomicRegularizationObligation)
    (hN : SchattenNormLaws) (hDim : SingleAtomDimensionObligation)
    (hM : SingleAtomMeasureObligation) (hB : AtomicBoundaryConclusion) :
    OneAtomConclusion :=
  Reduction.oneAtomSplitting hT hW hR denseCoreExtension coreLaws idealLaws hN scalarCompact hDim hM hB adjointLaws

/-- General gluing with the actual inverse/core model and generic spectral inputs proved.
Corona-witness existence is a separate mathematical input to this reduction. -/
theorem analyticGluing (hCo : CoronaWitnessObligation) : AnalyticGluingConclusion :=
  Reduction.analyticGluing coreLaws hCo gluingGraph denseCoreSet coordinateResolutionLaws finiteBlockSchatten constantCoreLaws scalarSplit

/-- The idempotent structure follows from the proved actual gluing model once corona witnesses exist. -/
theorem coronaStructure (hCo : CoronaWitnessObligation) : CoronaStructureObligation := by
  intro m hm u hu hc
  obtain ⟨hi,hn,hb⟩ := hCo m hm u hu hc
  refine ⟨hi,hn,hb,?_⟩
  intro a ha
  obtain ⟨W,_hf,_hinv,_hcore,_hclass,hedata,_hsplit⟩ := (analyticGluing hCo m hm u hu hc).2 a ha
  obtain ⟨E,hE,hcomp,hrange,_hcoord,hunique⟩ := hedata
  exact ⟨E,hE,hcomp,hrange,hunique⟩

/-- Interpolating-symbol classification from normalized-kernel Riesz synthesis. -/
theorem interpolatingClassification (hR : RieszObligation) : InterpolatingConclusion :=
  Reduction.interpolatingClassification hR dualDiagonal diagonalLaws idealLaws

/-- The perturbed-kernel reduction uses the proved core and ideal interfaces. -/
theorem perturbedKernelBasisClassification (hL : AnalyticLiftObligation)
    (hK : KernelRemainderObligation) : PerturbedBasisConclusion :=
  Reduction.perturbedKernelBasisClassification coreLaws hL hK diagonalLaws idealLaws

/-- Finite-atom classification using compression and uniform vector gluing. -/
theorem finiteAtomClassification (hS : CoronaStructureObligation) (hD : DistinctAtomCoronaObligation)
    (hOne : OneAtomObligation) (hDim : SingleAtomDimensionObligation)
    (hAng : AngularUniquenessObligation) (hN : SchattenNormLaws) : FiniteAtomConclusion :=
  Reduction.finiteAtomClassification coreLaws idealLaws hS hD atomCompression hOne vectorGluing scalarCompact hDim hAng hN

/-- The general structure input may itself be supplied by the separate corona-witness theorem. -/
theorem finiteAtomClassification_fromCorona (hCo : CoronaWitnessObligation) (hD : DistinctAtomCoronaObligation)
    (hOne : OneAtomObligation) (hDim : SingleAtomDimensionObligation)
    (hAng : AngularUniquenessObligation) (hN : SchattenNormLaws) : FiniteAtomConclusion :=
  finiteAtomClassification (coronaStructure hCo) hD hOne hDim hAng hN

/-- The coanalytic consequences now use the proved native core and adjoint interfaces. -/
theorem coanalyticBesov (p : ℝ) (h : BesovConclusion p) : CoanalyticBesovConclusion p :=
  Reduction.coanalyticBesov coreLaws adjointLaws p h

theorem coanalyticCompact (h : CompactConclusion) : CoanalyticCompactConclusion :=
  Reduction.coanalyticCompact coreLaws adjointLaws h

/-- The pure-type polynomial reduction retains its actual models and own polynomial computations. -/
theorem polynomialClassification (hP : PolynomialModels) (hM : MultiplicationLaws)
    (hT : TrigonometricUniqueness) (hS : PolynomialSymbolMeaning) (hQ : AtomicQuadraticWitness) :
    PolynomialConclusion :=
  Reduction.polynomialClassification coreLaws idealLaws unitaryIdealLaws hP hM hT hS hQ

/-- The energy and differential reductions now supply the actual canonical THO transfer. -/
theorem hilbertSchmidtEnergy (hB : MatrixDataObligation) (hP : BoundaryParsevalObligation)
    (hT : TensorSectionObligation) (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : HilbertSchmidtConclusion :=
  Reduction.hilbertSchmidtEnergy hB closedAnalysis l2CoordinateLaws matrixOperator hP hT kernelCalculus removableCalculus hF hTests canonicalTHO

theorem differentialRealization (hB : MatrixDataObligation) (hP : BoundaryParsevalObligation)
    (hT : TensorSectionObligation) (hF : GraphFormObligation) (hTests : KernelCoefficientObligation) : DifferentialConclusion :=
  Reduction.differentialRealization hB closedAnalysis l2CoordinateLaws matrixOperator hP hT kernelCalculus removableCalculus hF hTests canonicalTHO

/-- The analytic classifications now retain only their actual classical classification inputs. -/
theorem besovClassification (p : ℝ) (hp : 0 < p) (hP : PellerObligation p) : BesovConclusion p :=
  Reduction.besovClassification exactHankel p hp hP

theorem compactClassification (hH : HartmanObligation) : CompactConclusion :=
  Reduction.compactClassification exactHankel hH

theorem analyticDirichletEnergy : AnalyticDirichletConclusion :=
  Reduction.analyticDirichletEnergy exactHankel classicalDirichlet

/-- The example and splitting reductions supply actual scalar ambiguity and ideal/core laws. -/
theorem unboundedComponentsExample (h3 : InterpolatingConclusion) (hLog : Nonempty LogExampleData) :
    UnboundedComponentsConclusion :=
  Reduction.unboundedComponentsExample h3 coreLaws scalarAmbiguity boundedCoreNorm hLog

theorem blaschkeSplitting (h4 : PerturbedBasisConclusion) (hShift : ShiftSymbolLaws)
    (hAlt : AlternatingInterpolationObligation) (hDiv : AlternatingDivergenceObligation) :
    BlaschkeSplittingConclusion :=
  Reduction.blaschkeSplitting h4 coreLaws scalarSplit hShift hAlt hDiv

end TTO.Paper.Proved
