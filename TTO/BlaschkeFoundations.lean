/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.InterpolationFoundations
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Actual Blaschke model vectors, complete Hardy division, and full Theorem3. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem blaschkeFactor_self (a : Disk) : blaschkeFactor a a.val = 0 := by
  unfold blaschkeFactor
  split <;> simp_all

theorem blaschkeNodes_zero (u : BoundaryLInf) (a : ℕ → Disk) (ha : HasBlaschkeZeros u a) (n : ℕ) :
    innerValue u (a n).val = 0 := by
  obtain ⟨α,_hα,hv⟩ := ha.2
  rw [hv _ (a n).property,tprod_of_exists_eq_zero ⟨n,blaschkeFactor_self (a n)⟩,mul_zero]

def blaschkeNodeModel (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (ha : HasBlaschkeZeros u a) (n : ℕ) : Model u :=
  ⟨(hardyNodeVector (a n)).val,hardyNodeVector_mem_model u hu (a n) (blaschkeNodes_zero u a ha n)⟩

theorem blaschkeNodeModel_kernel (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (ha : HasBlaschkeZeros u a) (n : ℕ) : NodeKernel (a n) (blaschkeNodeModel u hu a ha n).val :=
  nodeKernel_hardyNodeVector (a n)

theorem finiteRieszModelBounds (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (ha : Interpolating a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      (∑ n ∈ s, ‖c n‖^2) ≤ C^2*‖∑ n ∈ s, c n • blaschkeNodeModel u hu a hz n‖^2 ∧
      ‖∑ n ∈ s, c n • blaschkeNodeModel u hu a hz n‖^2 ≤ C^2*(∑ n ∈ s, ‖c n‖^2) := by
  obtain ⟨C,hC,hb⟩ := finiteRieszKernelBounds a ha
  refine ⟨C,hC,fun s c => ?_⟩
  have he : modelHardyIsometry u (∑ n ∈ s, c n • blaschkeNodeModel u hu a hz n) =
      ∑ n ∈ s, c n • hardyNodeVector (a n) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_smul]
    rfl
  have heNorm := congrArg norm he
  rw [LinearIsometry.norm_map] at heNorm
  rw [heNorm]
  exact hb s c

/-- A genuine Hardy division intermediate, proved below without an added hypothesis.
It contains neither interpolation estimates nor a model-space basis/classification conclusion. -/
def BlaschkeHardyDivisionObligation : Prop :=
  ∀ u : BoundaryLInf, IsInner u → ∀ a : ℕ → Disk, Function.Injective a →
    HasBlaschkeZeros u a → ∀ f : Hardy,
      (∀ n, analyticValue f.val (a n).val = 0) → ∃ g : Hardy, multiply u g.val = f.val

/-- Hardy division implies totality by the actual model-space orthogonality. -/
theorem blaschkeNodes_dense_of_division (hD : BlaschkeHardyDivisionObligation)
    (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk) (hi : Function.Injective a)
    (hz : HasBlaschkeZeros u a) :
    Dense (Submodule.span ℂ (Set.range (blaschkeNodeModel u hu a hz)) : Set (Model u)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hv : ∀ n, analyticValue f.val (a n).val = 0 := by
    intro n
    have hinner := (Submodule.mem_orthogonal _ _).mp hf _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n)))
    change inner ℂ (blaschkeNodeModel u hu a hz n).val (modelHardyIsometry u f).val = 0 at hinner
    rw [inner_nodeKernel (a n) _ (blaschkeNodeModel_kernel u hu a hz n) (modelHardyIsometry u f)] at hinner
    have han : ‖(a n).val‖ < 1 := (a n).property
    have hs : 0 < 1-‖(a n).val‖^2 := by
      nlinarith [norm_nonneg (a n).val]
    have hs' : (Real.sqrt (1-‖(a n).val‖^2) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hs))
    exact (mul_eq_zero.mp hinner).resolve_left hs'
  obtain ⟨g,hg⟩ := hD u hu a hi hz (modelHardyIsometry u f) hv
  have he : inner ℂ f.val f.val = 0 := by
    calc
      inner ℂ f.val f.val = inner ℂ (multiply u g.val) f.val := congrArg (fun x => inner ℂ x f.val) hg.symm
      _ = 0 := inner_multiply_model u f g
  exact Subtype.ext (inner_self_eq_zero.mp he)

/-- Parameterized helper reduction through genuine Hardy division, discharged below. -/
theorem riesz_of_hardyDivision (hD : BlaschkeHardyDivisionObligation) : RieszObligation := by
  intro u hu _hn a hi hz ha
  obtain ⟨C,hC,hb⟩ := finiteRieszModelBounds u hu a hz ha
  let k := blaschkeNodeModel u hu a hz
  let S := synthesisOperator k C hC (fun s c => (hb s c).2)
  have hAnti := synthesis_antilipschitz k C hC hb
  have hRange : S.range = ⊤ := (synthesis_range k C hC hb).trans
    (Submodule.dense_iff_topologicalClosure_eq_top.mp (blaschkeNodes_dense_of_division hD u hu a hi hz))
  let R := ContinuousLinearEquiv.ofBijective S (LinearMap.ker_eq_bot.mpr hAnti.injective) hRange
  refine ⟨R,fun n => ?_⟩
  change NodeKernel (a n) (S (lp.single 2 n (1 : ℂ))).val
  rw [show S (lp.single 2 n (1 : ℂ)) = k n from synthesis_single k C hC hb n]
  exact blaschkeNodeModel_kernel u hu a hz n

theorem interpolatingClassification_of_hardyDivision (hD : BlaschkeHardyDivisionObligation) :
    InterpolatingConclusion := interpolatingClassification (riesz_of_hardyDivision hD)

/-- A bounded representative of the actual Szegő kernel. -/
def szegoBoundary (a : Disk) : BoundaryLInf := (bounded_szegoKernel a).toLp (szegoKernel a).val

theorem szegoBoundary_toL2 (a : Disk) : toL2 (szegoBoundary a) = (szegoKernel a).val :=
  Lp.ext ((toL2_ae _).trans (bounded_szegoKernel a).coeFn_toLp)

/-- The genuine boundary quotient f/(z-a), defined by bounded multipliers. -/
def singleZeroQuotient (a : Disk) (f : BoundaryL2) : BoundaryL2 :=
  multiply (star coordinate) (multiply (star (szegoBoundary a)) f)

theorem singleZeroQuotient_first (a : Disk) (f : Hardy) :
    fourierCoeff (singleZeroQuotient a f.val) (-1) = analyticValue f.val a.val := by
  rw [singleZeroQuotient,fourierCoeff_backwardShift]
  change fourierCoeff (multiply (star (szegoBoundary a)) f.val) 0 = _
  rw [fourierCoeff_multiply_star]
  have hmode : fourierBasis (T := 1) (0 : ℤ) = constL2 1 := by
    simpa only [one_smul] using (constL2_fourier 1).symm
  have hm : multiply (szegoBoundary a) (fourierBasis (T := 1) (0 : ℤ)) = (szegoKernel a).val := by
    rw [hmode]
    exact (boundaryInclusion_apply _).trans (szegoBoundary_toL2 a)
  rw [hm]
  exact inner_szegoKernel a f

theorem singleZeroQuotient_identity (a : Disk) (f : BoundaryL2) :
    multiply coordinate (singleZeroQuotient a f) - a.val • singleZeroQuotient a f = f := by
  let q := singleZeroQuotient a f
  have hq : q =ᵐ[circleMeasure] fun t => conj (fourier (T := 1) 1 t)*(conj (szegoBoundary a t)*f t) := by
    filter_upwards [multiply_ae (star coordinate) (multiply (star (szegoBoundary a)) f),
      multiply_ae (star (szegoBoundary a)) f,Lp.coeFn_star coordinate,Lp.coeFn_star (szegoBoundary a),coordinate_ae]
      with t h1 h2 hc hs he
    change (star coordinate) t = conj (coordinate t) at hc
    change (star (szegoBoundary a)) t = conj (szegoBoundary a t) at hs
    change (singleZeroQuotient a f) t = _
    rw [singleZeroQuotient,h1,h2,hc,hs,he]
  have hsa : szegoBoundary a =ᵐ[circleMeasure] fun t => (1-conj a.val*fourier (T := 1) 1 t)⁻¹ :=
    (bounded_szegoKernel a).coeFn_toLp.trans (szegoKernel_ae a)
  apply Lp.ext
  filter_upwards [hq,hsa,multiply_ae coordinate q,coordinate_ae,Lp.coeFn_sub (multiply coordinate q) (a.val • q),
    Lp.coeFn_smul a.val q] with t hqt hat hm he hsub hsm
  change (multiply coordinate q-a.val • q) t = f t
  rw [hsub]
  change (multiply coordinate q) t-(a.val • q) t = f t
  rw [hm,he,hsm]
  change fourier (T := 1) 1 t*q t-a.val*q t = f t
  rw [hqt]
  have hd : (1-conj a.val*fourier (T := 1) 1 t)*szegoBoundary a t = 1 := by
    rw [hat]
    exact mul_inv_cancel₀ (kernelDenominator_ne_zero a t)
  have hc := congrArg conj hd
  simp only [map_mul,map_sub,map_one,Complex.conj_conj] at hc
  have hz := fourier_mul_conj 1 t
  calc
    fourier (T := 1) 1 t*(conj (fourier 1 t)*(conj (szegoBoundary a t)*f t))-
        a.val*(conj (fourier 1 t)*(conj (szegoBoundary a t)*f t)) =
      ((fourier (T := 1) 1 t*conj (fourier 1 t)-a.val*conj (fourier 1 t))*conj (szegoBoundary a t))*f t := by ring
    _ = f t := by rw [hz,hc,one_mul]

/-- Actual division by one disk zero preserves Hardy membership. -/
theorem singleZeroQuotient_hardy (a : Disk) (f : Hardy) (hf : analyticValue f.val a.val = 0) :
    singleZeroQuotient a f.val ∈ hardy := by
  let q := singleZeroQuotient a f.val
  have hfirst : fourierCoeff q (-1) = 0 := (singleZeroQuotient_first a f).trans hf
  have hstep (n : ℤ) (hn : n < 0) : fourierCoeff q (n-1) = a.val*fourierCoeff q n := by
    have he := congrArg (fun v : BoundaryL2 => fourierCoeff v n) (singleZeroQuotient_identity a f.val)
    rw [fourierCoeff_sub_L2] at he
    change fourierCoeff (multiply (mode 1) q) n - fourierCoeff (a.val • q) n = fourierCoeff f.val n at he
    rw [fourierCoeff_mode_multiply,(mem_hardy_iff f.val).mp f.property n hn] at he
    have hsc : fourierCoeff (a.val • q) n = a.val*fourierCoeff q n := by
      simp only [← fourierBasis_repr,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    rw [hsc] at he
    exact sub_eq_zero.mp he
  have hneg : ∀ k : ℕ, fourierCoeff q (Int.negSucc k) = 0 := by
    intro k
    induction k with
    | zero => exact hfirst
    | succ k ih =>
      have he := hstep (Int.negSucc k) (by omega)
      rw [ih,mul_zero] at he
      have hi : Int.negSucc (k+1) = Int.negSucc k-1 := by omega
      rw [hi]
      exact he
  apply (mem_hardy_iff _).mpr
  intro n hn
  obtain ⟨k,rfl⟩ := Int.eq_negSucc_of_lt_zero hn
  exact hneg k

theorem hardy_divide_single_zero (a : Disk) (f : Hardy) (hf : analyticValue f.val a.val = 0) :
    ∃ q : Hardy, multiply coordinate q.val-a.val • q.val = f.val :=
  ⟨⟨singleZeroQuotient a f.val,singleZeroQuotient_hardy a f hf⟩,singleZeroQuotient_identity a f.val⟩

/-- Equal-length vectors give the conjugate scalar norm symmetry used by disk factors. -/
theorem norm_sub_conj_of_norm_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (a : ℂ) (hxy : ‖x‖ = ‖y‖) : ‖x-a • y‖ = ‖y-conj a • x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hi : RCLike.re (inner ℂ x (a • y)) = RCLike.re (inner ℂ y (conj a • x)) := by
    rw [inner_smul_right,inner_smul_right,← inner_conj_symm (𝕜 := ℂ) y x,← map_mul]
    exact (Complex.conj_re _).symm
  rw [norm_sub_sq (𝕜 := ℂ),norm_sub_sq (𝕜 := ℂ),hi,norm_smul,norm_smul,Complex.norm_conj,hxy]

/-- The first character is an actual inner boundary function. -/
theorem coordinate_isInner : IsInner coordinate := by
  refine ⟨?_,coordinate_unimodular⟩
  change toL2 (mode 1) ∈ hardy
  rw [toL2_mode]
  exact fourierBasis_mem_hardy 1

/-- The Hardy quotient by the disk automorphism (z-a)/(1-conj(a)z).
The canonical Blaschke phase has modulus one and is deliberately not absorbed here. -/
def singleBlaschkeQuotient (a : Disk) (f : BoundaryL2) : BoundaryL2 :=
  singleZeroQuotient a f - conj a.val • multiply coordinate (singleZeroQuotient a f)

theorem singleBlaschkeQuotient_hardy (a : Disk) (f : Hardy) (hf : analyticValue f.val a.val = 0) :
    singleBlaschkeQuotient a f.val ∈ hardy :=
  hardy.sub_mem (singleZeroQuotient_hardy a f hf)
    (hardy.smul_mem _ (mode_multiply_hardy ⟨_,singleZeroQuotient_hardy a f hf⟩ 1))

/-- The disk-factor quotient preserves the exact native H² norm. -/
theorem singleBlaschkeQuotient_norm (a : Disk) (f : BoundaryL2) :
    ‖singleBlaschkeQuotient a f‖ = ‖f‖ := by
  have hn : ‖multiply coordinate (singleZeroQuotient a f)‖ = ‖singleZeroQuotient a f‖ :=
    (innerMultiplyIsometry coordinate coordinate_isInner).norm_map _
  have he := norm_sub_conj_of_norm_eq _ _ a.val hn
  rw [singleZeroQuotient_identity] at he
  exact he.symm

/-- Denominator-cleared identity for the genuine automorphism quotient. -/
theorem singleBlaschkeQuotient_identity (a : Disk) (f : BoundaryL2) :
    multiply coordinate (singleBlaschkeQuotient a f)-a.val • singleBlaschkeQuotient a f =
      f-conj a.val • multiply coordinate f := by
  let q := singleZeroQuotient a f
  have hq : multiply coordinate q-a.val • q = f := singleZeroQuotient_identity a f
  calc
    multiply coordinate (singleBlaschkeQuotient a f)-a.val • singleBlaschkeQuotient a f =
      (multiply coordinate q-a.val • q)-conj a.val • multiply coordinate (multiply coordinate q-a.val • q) := by
        simp only [singleBlaschkeQuotient,map_sub,map_smul]
        module
    _ = f-conj a.val • multiply coordinate f := by rw [hq]

theorem blaschkePhase_norm (a : Disk) : ‖blaschkePhase a‖ = 1 := by
  unfold blaschkePhase
  split_ifs with ha
  · exact norm_one
  · rw [norm_neg,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg a.val)]
    exact div_self (norm_ne_zero_iff.mpr ha)

theorem blaschkeDenominator_ne_zero (a z : Disk) : 1-conj a.val*z.val ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one,norm_mul,Complex.norm_conj] at hn
  have ha : ‖a.val‖ < 1 := a.property
  have hz : ‖z.val‖ < 1 := z.property
  have hp := mul_le_mul_of_nonneg_left hz.le (norm_nonneg a.val)
  linarith

theorem singleBlaschkeQuotient_value (a : Disk) (f : Hardy) (hf : analyticValue f.val a.val = 0) (z : Disk) :
    (z.val-a.val)*analyticValue (singleBlaschkeQuotient a f.val) z.val =
      (1-conj a.val*z.val)*analyticValue f.val z.val := by
  have he := congrArg (fun v : BoundaryL2 => analyticValue v z.val) (singleBlaschkeQuotient_identity a f.val)
  rw [analyticValue_sub _ _ z.property,analyticValue_sub _ _ z.property,
    analyticValue_smul _ _ z.property,analyticValue_smul _ _ z.property,
    analyticValue_coordinate_multiply ⟨_,singleBlaschkeQuotient_hardy a f hf⟩,
    analyticValue_coordinate_multiply f] at he
  linear_combination he

/-- One canonical normalized Blaschke factor can be divided out with exactly preserved H² norm. -/
theorem hardy_divide_blaschkeFactor (a : Disk) (f : Hardy) (hf : analyticValue f.val a.val = 0) :
    ∃ q : Hardy, ‖q‖ = ‖f‖ ∧ ∀ z : Disk,
      analyticValue f.val z.val = blaschkeFactor a z.val*analyticValue q.val z.val := by
  let h : Hardy := ⟨singleBlaschkeQuotient a f.val,singleBlaschkeQuotient_hardy a f hf⟩
  let q : Hardy := (blaschkePhase a)⁻¹ • h
  refine ⟨q,?_,fun z => ?_⟩
  · change ‖(blaschkePhase a)⁻¹ • singleBlaschkeQuotient a f.val‖ = ‖f.val‖
    rw [norm_smul,norm_inv,blaschkePhase_norm,inv_one,one_mul,singleBlaschkeQuotient_norm]
  · have he := singleBlaschkeQuotient_value a f hf z
    have hb := blaschkeFactor_clear a z.property
    have hp := blaschkePhase_ne_zero a
    change analyticValue f.val z.val = blaschkeFactor a z.val*analyticValue ((blaschkePhase a)⁻¹ • h.val) z.val
    rw [analyticValue_smul _ _ z.property]
    apply mul_right_cancel₀ (blaschkeDenominator_ne_zero a z)
    calc
      analyticValue f.val z.val*(1-conj a.val*z.val) = (z.val-a.val)*analyticValue h.val z.val := by
        simpa only [mul_comm] using he.symm
      _ = (blaschkeFactor a z.val*((blaschkePhase a)⁻¹*analyticValue h.val z.val))*(1-conj a.val*z.val) := by
        calc
          _ = (blaschkePhase a*(z.val-a.val))*((blaschkePhase a)⁻¹*analyticValue h.val z.val) := by
            field_simp
          _ = _ := by rw [← hb]; ring

theorem blaschkeFactor_ne_zero (a z : Disk) (hne : z ≠ a) : blaschkeFactor a z.val ≠ 0 := by
  intro he
  have hc := blaschkeFactor_clear a z.property
  rw [he,zero_mul] at hc
  have hv := (mul_eq_zero.mp hc.symm).resolve_left (blaschkePhase_ne_zero a)
  exact hne (Subtype.ext (sub_eq_zero.mp hv))

/-- Any finite collection of distinct zeros can be divided out with exactly preserved norm.
The constant is independent of both the number and location of these zeros. -/
theorem hardy_divide_finite_blaschke (a : ℕ → Disk) (hi : Function.Injective a) (s : Finset ℕ)
    (f : Hardy) (hv : ∀ n ∈ s, analyticValue f.val (a n).val = 0) :
    ∃ q : Hardy, ‖q‖ = ‖f‖ ∧ ∀ z : Disk,
      analyticValue f.val z.val = (∏ n ∈ s, blaschkeFactor (a n) z.val)*analyticValue q.val z.val := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f,rfl,fun z => by simp⟩
  | @insert n s hn ih =>
    obtain ⟨g,hgnorm,hg⟩ := hardy_divide_blaschkeFactor (a n) f (hv n (Finset.mem_insert_self _ _))
    have hgv : ∀ m ∈ s, analyticValue g.val (a m).val = 0 := by
      intro m hm
      have he := hg (a m)
      rw [hv m (Finset.mem_insert_of_mem hm)] at he
      have hmn : a m ≠ a n := fun heq => hn ((hi heq) ▸ hm)
      exact (mul_eq_zero.mp he.symm).resolve_left (blaschkeFactor_ne_zero (a n) (a m) hmn)
    obtain ⟨q,hqnorm,hq⟩ := ih g hgv
    refine ⟨q,hqnorm.trans hgnorm,fun z => ?_⟩
    rw [hg z,hq z,Finset.prod_insert hn,mul_assoc]

/-- Uniformly norm-bounded native Hardy quotients along the initial segments of a simple zero set. -/
theorem hardy_blaschke_prefix_quotients (a : ℕ → Disk) (hi : Function.Injective a) (f : Hardy)
    (hv : ∀ n, analyticValue f.val (a n).val = 0) :
    ∃ q : ℕ → Hardy, (∀ N, ‖q N‖ = ‖f‖) ∧ ∀ N, ∀ z : Disk,
      analyticValue f.val z.val = (∏ n ∈ Finset.range N, blaschkeFactor (a n) z.val)*analyticValue (q N).val z.val := by
  have he (N : ℕ) := hardy_divide_finite_blaschke a hi (Finset.range N) f (fun n _ => hv n)
  choose q hqnorm hq using he
  exact ⟨q,hqnorm,hq⟩

instance hardy_separable : TopologicalSpace.SeparableSpace Hardy := by
  have hs := (((Set.countable_range (fun n : ℕ => fourierBasis (T := 1) (n : ℤ))).isSeparable).span (R := ℂ)).closure
  exact hs.separableSpace

/-- A bounded Hardy sequence has one subsequence converging at every disk evaluation. -/
theorem hardy_bounded_subsequence (q : ℕ → Hardy) (M : ℝ) (hq : ∀ n, ‖q n‖ ≤ M) :
    ∃ f : Hardy, ‖f‖ ≤ M ∧ ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ z : Disk,
      Tendsto (fun n => analyticValue (q (r n)).val z.val) atTop (𝓝 (analyticValue f.val z.val)) := by
  let v : ℕ → WeakDual ℂ Hardy := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ Hardy (q n))
  have hv (n : ℕ) : v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ Hardy) M := by
    rw [Set.mem_preimage,Metric.mem_closedBall]
    change dist (InnerProductSpace.toDual ℂ Hardy (q n)) (0 : StrongDual ℂ Hardy) ≤ M
    rw [dist_zero_right,(InnerProductSpace.toDual ℂ Hardy).norm_map]
    exact hq n
  obtain ⟨l,hl,r,hr,hlim⟩ := (WeakDual.isSeqCompact_closedBall (𝕜 := ℂ) (E := Hardy) 0 M) hv
  let f := (InnerProductSpace.toDual ℂ Hardy).symm (WeakDual.toStrongDual l)
  refine ⟨f,?_,r,hr,fun z => ?_⟩
  · change ‖(InnerProductSpace.toDual ℂ Hardy).symm (WeakDual.toStrongDual l)‖ ≤ M
    rw [(InnerProductSpace.toDual ℂ Hardy).symm.norm_map]
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hl
  · have ht := ((WeakDual.eval_continuous (𝕜 := ℂ) (szegoKernel z)).tendsto l).comp hlim
    have hc := Complex.continuous_conj.continuousAt.tendsto.comp ht
    convert hc using 1
    · funext n
      change analyticValue (q (r n)).val z.val = conj (inner ℂ (q (r n)) (szegoKernel z))
      rw [inner_conj_symm,inner_szegoKernel]
    · congr 1
      change analyticValue f.val z.val = conj ((WeakDual.toStrongDual l) (szegoKernel z))
      rw [← InnerProductSpace.toDual_symm_apply,inner_conj_symm]
      exact (inner_szegoKernel z f).symm

theorem blaschkePhase_mul_node (a : Disk) : blaschkePhase a*a.val = -(‖a.val‖ : ℂ) := by
  unfold blaschkePhase
  split_ifs with ha
  · simp [ha]
  · rw [neg_mul,div_mul_cancel₀ _ ha]

theorem blaschkePhase_node_conj (a : Disk) : conj a.val = -(‖a.val‖ : ℂ)*blaschkePhase a := by
  have hp := congrArg conj (blaschkePhase_mul_node a)
  simp only [map_mul,map_neg,Complex.conj_ofReal] at hp
  have hu : blaschkePhase a*conj (blaschkePhase a) = 1 := by
    rw [Complex.mul_conj',blaschkePhase_norm]
    norm_num
  calc
    conj a.val = (blaschkePhase a*conj (blaschkePhase a))*conj a.val := by rw [hu,one_mul]
    _ = blaschkePhase a*(conj (blaschkePhase a)*conj a.val) := by ring
    _ = -(‖a.val‖ : ℂ)*blaschkePhase a := by rw [hp]; ring

theorem blaschkeFactor_one_sub_clear (a z : Disk) :
    (1-blaschkeFactor a z.val)*(1-conj a.val*z.val) =
      ((1-‖a.val‖ : ℝ) : ℂ)*(1-blaschkePhase a*z.val) := by
  have hb := blaschkeFactor_clear a z.property
  have hp := blaschkePhase_mul_node a
  have hc := blaschkePhase_node_conj a
  rw [sub_mul,one_mul,hb,hc]
  push_cast
  linear_combination hp

/-- A uniform-on-each-fixed-disk-point summable deviation bound for canonical factors. -/
theorem blaschkeFactor_deviation (a z : Disk) :
    ‖1-blaschkeFactor a z.val‖ ≤ ((1+‖z.val‖)/(1-‖z.val‖))*(1-‖a.val‖) := by
  have ha : ‖a.val‖ < 1 := a.property
  have hz : ‖z.val‖ < 1 := z.property
  have hda : 0 ≤ 1-‖a.val‖ := sub_nonneg.mpr ha.le
  have hd : 1-‖z.val‖ ≤ ‖1-conj a.val*z.val‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) (conj a.val*z.val)
    rw [norm_one,norm_mul,Complex.norm_conj] at hn
    have hm := mul_le_mul_of_nonneg_right ha.le (norm_nonneg z.val)
    linarith
  have hn := congrArg norm (blaschkeFactor_one_sub_clear a z)
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hda] at hn
  have hb : ‖1-blaschkePhase a*z.val‖ ≤ 1+‖z.val‖ := by
    have he := norm_sub_le (1 : ℂ) (blaschkePhase a*z.val)
    simpa only [norm_one,norm_mul,blaschkePhase_norm,one_mul] using he
  have he : ‖1-blaschkeFactor a z.val‖*(1-‖z.val‖) ≤ (1-‖a.val‖)*(1+‖z.val‖) :=
    (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans (hn.le.trans (mul_le_mul_of_nonneg_left hb hda))
  have he' := (le_div_iff₀ (sub_pos.mpr hz)).mpr he
  convert he' using 1; ring

theorem blaschkeFactors_multipliable (a : ℕ → Disk) (ha : Summable (fun n => 1-‖(a n).val‖)) (z : Disk) :
    Multipliable (fun n => blaschkeFactor (a n) z.val) := by
  have hs : Summable (fun n => ‖1-blaschkeFactor (a n) z.val‖) :=
    (ha.mul_left ((1+‖z.val‖)/(1-‖z.val‖))).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => blaschkeFactor_deviation (a n) z)
  simpa only [sub_sub_cancel] using multipliable_one_sub_of_summable hs

/-- Infinite simple Blaschke Hardy division, proved from norm-preserving prefix quotients. -/
theorem blaschkeHardyDivision : BlaschkeHardyDivisionObligation := by
  intro u hu a hi hz f hv
  obtain ⟨qs,hqnorm,hq⟩ := hardy_blaschke_prefix_quotients a hi f hv
  obtain ⟨q,_hqbound,r,hr,hweak⟩ := hardy_bounded_subsequence qs ‖f‖ (fun n => (hqnorm n).le)
  obtain ⟨α,hα,huval⟩ := hz.2
  have hαne : α ≠ 0 := by intro he; rw [he,norm_zero] at hα; norm_num at hα
  let g : Hardy := α⁻¹ • q
  refine ⟨g,?_⟩
  have hm : multiply u g.val ∈ hardy := multiply_mem_hardy u hu.1 g.val g.property
  have he : (⟨multiply u g.val,hm⟩ : Hardy) = f := by
    apply hardy_analyticValue_injective
    intro z hzd
    let w : Disk := ⟨z,hzd⟩
    have hp := (blaschkeFactors_multipliable a hz.1 w).tendsto_prod_tprod_nat
    have hpq := (hp.comp hr.tendsto_atTop).mul (hweak w)
    have hconst : Tendsto (fun n => (∏ i ∈ Finset.range (r n), blaschkeFactor (a i) w.val)*
        analyticValue (qs (r n)).val w.val) atTop (𝓝 (analyticValue f.val w.val)) := by
      convert tendsto_const_nhds (x := analyticValue f.val w.val) using 1
      funext n
      exact (hq (r n) w).symm
    have hlim := tendsto_nhds_unique hpq hconst
    change analyticValue (multiply u g.val) w.val = analyticValue f.val w.val
    rw [analyticValue_multiply u hu.1 g w,huval _ w.property]
    change (α*(∏' i, blaschkeFactor (a i) w.val))*analyticValue (α⁻¹ • q.val) w.val = _
    rw [analyticValue_smul _ _ w.property]
    calc
      (α*(∏' i, blaschkeFactor (a i) w.val))*(α⁻¹*analyticValue q.val w.val) =
        (α*α⁻¹)*((∏' i, blaschkeFactor (a i) w.val)*analyticValue q.val w.val) := by ring
      _ = analyticValue f.val w.val := by rw [mul_inv_cancel₀ hαne,one_mul]; exact hlim
  exact congrArg (fun v : Hardy => v.val) he

theorem riesz : RieszObligation := riesz_of_hardyDivision blaschkeHardyDivision

/-- Full Theorem3, with all original hypotheses and no open proof parameters. -/
theorem interpolatingClassificationTheorem : InterpolatingConclusion := interpolatingClassification riesz

end TTO.Paper.Proved
