/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.WeakOperatorFoundations
public import TTO.PolynomialMeaningFoundations

/-! Literal Blaschke factors and Malmquist vectors. Repeated zeros are retained. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The actual normalized disk Blaschke factor as an L∞ boundary vector. -/
def blaschkeBoundary (a : Disk) : BoundaryLInf :=
  blaschkePhase a • (multiplyInf coordinate (szegoBoundary a)-a.val • szegoBoundary a)

theorem szegoBoundary_ae (a : Disk) :
    szegoBoundary a =ᵐ[circleMeasure] fun t => (1-conj a.val*fourier (T := 1) 1 t)⁻¹ :=
  (bounded_szegoKernel a).coeFn_toLp.trans (szegoKernel_ae a)

theorem blaschkeBoundary_ae (a : Disk) : blaschkeBoundary a =ᵐ[circleMeasure] fun t =>
    blaschkePhase a*(fourier (T := 1) 1 t-a.val)*(1-conj a.val*fourier (T := 1) 1 t)⁻¹ := by
  filter_upwards [Lp.coeFn_smul (blaschkePhase a)
      (multiplyInf coordinate (szegoBoundary a)-a.val • szegoBoundary a),
    Lp.coeFn_sub (multiplyInf coordinate (szegoBoundary a)) (a.val • szegoBoundary a),
    multiplyInf_ae coordinate (szegoBoundary a),Lp.coeFn_smul a.val (szegoBoundary a),
    szegoBoundary_ae a,coordinate_ae] with t hp hs hm ha hk hc
  change (blaschkePhase a • (multiplyInf coordinate (szegoBoundary a)-a.val • szegoBoundary a)) t = _
  rw [hp]
  change blaschkePhase a*((multiplyInf coordinate (szegoBoundary a)-a.val • szegoBoundary a) t) = _
  rw [hs]
  change blaschkePhase a*(multiplyInf coordinate (szegoBoundary a) t-(a.val • szegoBoundary a) t) = _
  rw [hm,ha]
  change blaschkePhase a*(coordinate t*szegoBoundary a t-a.val*szegoBoundary a t) = _
  rw [hk,hc]
  ring

theorem blaschkeBoundary_toL2 (a : Disk) :
    toL2 (blaschkeBoundary a) =
      blaschkePhase a • (multiply coordinate (szegoKernel a).val-a.val • (szegoKernel a).val) := by
  rw [← boundaryInclusion_apply]
  simp only [blaschkeBoundary,map_smul,map_sub,boundaryInclusion_apply,toL2_multiplyInf,szegoBoundary_toL2]

theorem blaschkeBoundary_hardy (a : Disk) : toL2 (blaschkeBoundary a) ∈ hardy := by
  rw [blaschkeBoundary_toL2]
  exact hardy.smul_mem _ (hardy.sub_mem
    (multiply_mem_hardy coordinate coordinate_isInner.1 _ (szegoKernel a).property)
    (hardy.smul_mem _ (szegoKernel a).property))

/-- Its literal analytic evaluation is the normalized Blaschke factor, including a=0. -/
theorem innerValue_blaschkeBoundary (a z : Disk) :
    innerValue (blaschkeBoundary a) z.val = blaschkeFactor a z.val := by
  unfold innerValue
  rw [blaschkeBoundary_toL2,analyticValue_smul _ _ z.property,analyticValue_sub _ _ z.property,
    analyticValue_smul _ _ z.property,analyticValue_coordinate_multiply (szegoKernel a),
    analyticValue_szegoKernel a z.property]
  have hd := blaschkeDenominator_ne_zero a z
  apply mul_right_cancel₀ hd
  rw [blaschkeFactor_clear a z.property]
  calc
    _ = blaschkePhase a*(z.val-a.val)*
        ((1-conj a.val*z.val)⁻¹*(1-conj a.val*z.val)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd,mul_one]

theorem blaschkeBoundary_isInner (a : Disk) : IsInner (blaschkeBoundary a) := by
  refine ⟨blaschkeBoundary_hardy a,?_⟩
  filter_upwards [blaschkeBoundary_ae a] with t ht
  rw [ht,norm_mul,norm_mul,blaschkePhase_norm,one_mul,norm_inv]
  have hz : ‖fourier (T := 1) 1 t‖ = 1 := by simp
  have he : ‖fourier (T := 1) 1 t-a.val‖ = ‖1-conj a.val*fourier (T := 1) 1 t‖ := by
    simpa only [smul_eq_mul,mul_one] using
      norm_sub_conj_of_norm_eq (fourier (T := 1) 1 t) (1 : ℂ) a.val (by simp)
  have hd : 1-conj a.val*fourier (T := 1) 1 t ≠ 0 := by
    intro heq
    have hn := congrArg norm (sub_eq_zero.mp heq)
    rw [norm_one,norm_mul,Complex.norm_conj,hz,mul_one] at hn
    exact (ne_of_lt a.property) hn.symm
  rw [he,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd)]

/-- One actual boundary factor can be divided out with exact Hardy norm. -/
theorem hardy_divide_blaschkeBoundary (a : Disk) (f : Hardy)
    (hf : analyticValue f.val a.val = 0) :
    ∃ q : Hardy, ‖q‖ = ‖f‖ ∧ multiply (blaschkeBoundary a) q.val = f.val := by
  obtain ⟨q,hqn,hq⟩ := hardy_divide_blaschkeFactor a f hf
  refine ⟨q,hqn,?_⟩
  have hh := multiply_mem_hardy (blaschkeBoundary a) (blaschkeBoundary_hardy a) q.val q.property
  have he : (⟨multiply (blaschkeBoundary a) q.val,hh⟩ : Hardy) = f := by
    apply hardy_analyticValue_injective
    intro z hz
    rw [analyticValue_multiply _ (blaschkeBoundary_hardy a) q ⟨z,hz⟩,
      innerValue_blaschkeBoundary a ⟨z,hz⟩]
    exact (hq ⟨z,hz⟩).symm
  exact congrArg Subtype.val he

/-- The actual finite prefix, with the normalization of each factor. -/
def blaschkePrefix (a : ℕ → Disk) : ℕ → BoundaryLInf
  | 0 => constLInf 1
  | n+1 => multiplyInf (blaschkePrefix a n) (blaschkeBoundary (a n))

theorem blaschkePrefix_isInner (a : ℕ → Disk) (n : ℕ) : IsInner (blaschkePrefix a n) := by
  induction n with
  | zero => exact isInner_constLInf_one
  | succ n ih => exact isInner_multiplyInf _ _ ih (blaschkeBoundary_isInner (a n))

theorem innerValue_blaschkePrefix (a : ℕ → Disk) (n : ℕ) (z : Disk) :
    innerValue (blaschkePrefix a n) z.val = ∏ j ∈ Finset.range n, blaschkeFactor (a j) z.val := by
  induction n with
  | zero =>
    change analyticValue (toL2 (constLInf 1)) z.val = _
    rw [toL2_constLInf]
    rw [constL2_fourier,one_smul]
    simpa using analyticValue_fourierBasis 0 z.val
  | succ n ih =>
    change analyticValue (toL2 (multiplyInf (blaschkePrefix a n) (blaschkeBoundary (a n)))) z.val = _
    rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkePrefix_isInner a n).1
      ⟨toL2 (blaschkeBoundary (a n)),blaschkeBoundary_hardy (a n)⟩ z]
    change innerValue (blaschkePrefix a n) z.val*innerValue (blaschkeBoundary (a n)) z.val = _
    rw [ih,innerValue_blaschkeBoundary,Finset.prod_range_succ]

/-- Equality of actual bounded analytic boundary vectors follows from equality on the disk. -/
theorem boundedHardy_boundary_ext (u v : BoundaryLInf) (hu : toL2 u ∈ hardy) (hv : toL2 v ∈ hardy)
    (h : ∀ z : Disk, innerValue u z.val = innerValue v z.val) : u = v := by
  have he : (⟨toL2 u,hu⟩ : Hardy) = ⟨toL2 v,hv⟩ := by
    apply hardy_analyticValue_injective
    intro z hz
    exact h ⟨z,hz⟩
  have h2 : toL2 u = toL2 v := congrArg Subtype.val he
  apply Lp.ext
  have ha := toL2_ae u
  rw [h2] at ha
  exact ha.symm.trans (toL2_ae v)

theorem multiply_constLInf_one (f : BoundaryL2) : multiply (constLInf 1) f = f := by
  apply Lp.ext
  filter_upwards [multiply_ae (constLInf 1) f,(memLp_const (1 : ℂ)).coeFn_toLp] with t hm h1
  change constLInf 1 t = 1 at h1
  rw [hm,h1,one_mul]

/-- Prefixes can be split at their first factor without imposing distinctness. -/
theorem blaschkePrefix_shift (a : ℕ → Disk) (n : ℕ) :
    blaschkePrefix a (n+1) = multiplyInf (blaschkeBoundary (a 0))
      (blaschkePrefix (fun j => a (j+1)) n) := by
  apply boundedHardy_boundary_ext _ _ (blaschkePrefix_isInner a (n+1)).1
    (isInner_multiplyInf _ _ (blaschkeBoundary_isInner (a 0))
      (blaschkePrefix_isInner (fun j => a (j+1)) n)).1
  intro z
  rw [innerValue_blaschkePrefix]
  change _ = analyticValue (toL2 (multiplyInf _ _)) z.val
  rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkeBoundary_hardy (a 0))
    ⟨toL2 (blaschkePrefix (fun j => a (j+1)) n),(blaschkePrefix_isInner _ _).1⟩ z]
  change _ = innerValue (blaschkeBoundary (a 0)) z.val*
    innerValue (blaschkePrefix (fun j => a (j+1)) n) z.val
  rw [innerValue_blaschkeBoundary,innerValue_blaschkePrefix]
  simpa only [mul_comm] using Finset.prod_range_succ' (fun j => blaschkeFactor (a j) z.val) n

/-- Literal normalized node evaluation, including its real nonzero normalization. -/
theorem inner_hardyNodeVector (a : Disk) (f : Hardy) :
    inner ℂ (hardyNodeVector a) f = (Real.sqrt (1-‖a.val‖^2) : ℂ)*analyticValue f.val a.val := by
  change inner ℂ ((Real.sqrt (1-‖a.val‖^2) : ℂ) • (szegoKernel a).val) f.val = _
  rw [inner_smul_left]
  change conj (Real.sqrt (1-‖a.val‖^2) : ℂ)*inner ℂ (szegoKernel a) f = _
  rw [Complex.conj_ofReal,inner_szegoKernel]

theorem inner_hardyNodeVector_eq_zero_iff (a : Disk) (f : Hardy) :
    inner ℂ (hardyNodeVector a) f = 0 ↔ analyticValue f.val a.val = 0 := by
  rw [inner_hardyNodeVector,mul_eq_zero]
  have ha : ‖a.val‖ < 1 := a.property
  have hs : (Real.sqrt (1-‖a.val‖^2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by nlinarith [ha,norm_nonneg a.val])).ne'
  simp only [hs,false_or]

theorem inner_hardyNodeVector_blaschke (a : Disk) (f : Hardy) :
    inner ℂ (hardyNodeVector a) (hardyMultiply (blaschkeBoundary a) (blaschkeBoundary_hardy a) f) = 0 := by
  rw [inner_hardyNodeVector,hardyMultiply_apply,
    analyticValue_multiply _ (blaschkeBoundary_hardy a) f a,innerValue_blaschkeBoundary,
    blaschkeFactor_self,zero_mul,mul_zero]

/-- The actual prefix-times-normalized-kernel Malmquist vector in Hardy space. -/
def malmquistHardy (a : ℕ → Disk) (n : ℕ) : Hardy :=
  ⟨multiply (blaschkePrefix a n) (hardyNodeVector (a n)).val,
    multiply_mem_hardy _ (blaschkePrefix_isInner a n).1 _ (hardyNodeVector (a n)).property⟩

theorem malmquistHardy_zero (a : ℕ → Disk) : malmquistHardy a 0 = hardyNodeVector (a 0) := by
  apply Subtype.ext
  exact multiply_constLInf_one _

theorem malmquistHardy_succ (a : ℕ → Disk) (n : ℕ) :
    malmquistHardy a (n+1) = hardyMultiply (blaschkeBoundary (a 0)) (blaschkeBoundary_hardy (a 0))
      (malmquistHardy (fun j => a (j+1)) n) := by
  apply Subtype.ext
  change multiply (blaschkePrefix a (n+1)) (hardyNodeVector (a (n+1))).val =
    multiply (blaschkeBoundary (a 0)) (multiply (blaschkePrefix (fun j => a (j+1)) n)
      (hardyNodeVector (a (n+1))).val)
  rw [blaschkePrefix_shift,multiply_assoc]

theorem norm_malmquistHardy (a : ℕ → Disk) (n : ℕ) : ‖malmquistHardy a n‖ = 1 := by
  change ‖innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n)
    (hardyNodeVector (a n)).val‖ = 1
  rw [LinearIsometry.norm_map]
  exact norm_hardyNodeVector (a n)

/-- Malmquist orthogonality uses successive factors, and allows repeated nodes. -/
theorem malmquistHardy_orthonormal (a : ℕ → Disk) : Orthonormal ℂ (malmquistHardy a) := by
  have ho : ∀ (n : ℕ) (a : ℕ → Disk) (m : ℕ), n < m →
      inner ℂ (malmquistHardy a n) (malmquistHardy a m) = 0 := by
    intro n
    induction n with
    | zero =>
      intro a m hm
      cases m with
      | zero => omega
      | succ m => rw [malmquistHardy_zero,malmquistHardy_succ]; exact inner_hardyNodeVector_blaschke _ _
    | succ n ih =>
      intro a m hm
      cases m with
      | zero => omega
      | succ m =>
        rw [malmquistHardy_succ,malmquistHardy_succ]
        change inner ℂ
          (innerMultiplyIsometry (blaschkeBoundary (a 0)) (blaschkeBoundary_isInner (a 0))
            (malmquistHardy (fun j => a (j+1)) n).val)
          (innerMultiplyIsometry (blaschkeBoundary (a 0)) (blaschkeBoundary_isInner (a 0))
            (malmquistHardy (fun j => a (j+1)) m).val) = 0
        rw [LinearIsometry.inner_map_map]
        exact ih _ _ (Nat.lt_of_succ_lt_succ hm)
  refine ⟨norm_malmquistHardy a,?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i a j h
  · rw [← inner_conj_symm (𝕜 := ℂ)]
    simp only [ho j a i h,map_zero]

/-- Orthogonality to a finite prefix gives actual norm-preserving successive division.
The next quotient zero is read from the next Malmquist vector; no distinctness is used. -/
theorem hardy_divide_malmquist_prefix (a : ℕ → Disk) (N : ℕ) (f : Hardy)
    (hf : ∀ n < N, inner ℂ (malmquistHardy a n) f = 0) :
    ∃ q : Hardy, ‖q‖ = ‖f‖ ∧ multiply (blaschkePrefix a N) q.val = f.val := by
  induction N generalizing a f with
  | zero => exact ⟨f,rfl,multiply_constLInf_one _⟩
  | succ N ih =>
    have hz : analyticValue f.val (a 0).val = 0 := by
      apply (inner_hardyNodeVector_eq_zero_iff (a 0) f).mp
      simpa only [malmquistHardy_zero] using hf 0 (by omega)
    obtain ⟨g,hgn,hg⟩ := hardy_divide_blaschkeBoundary (a 0) f hz
    have hge : hardyMultiply (blaschkeBoundary (a 0)) (blaschkeBoundary_hardy (a 0)) g = f :=
      Subtype.ext hg
    have htail : ∀ n < N, inner ℂ (malmquistHardy (fun j => a (j+1)) n) g = 0 := by
      intro n hn
      have h := hf (n+1) (by omega)
      rw [malmquistHardy_succ,← hge] at h
      change inner ℂ
        (innerMultiplyIsometry (blaschkeBoundary (a 0)) (blaschkeBoundary_isInner (a 0))
          (malmquistHardy (fun j => a (j+1)) n).val)
        (innerMultiplyIsometry (blaschkeBoundary (a 0)) (blaschkeBoundary_isInner (a 0)) g.val) = 0 at h
      rwa [LinearIsometry.inner_map_map] at h
    obtain ⟨q,hqn,hq⟩ := ih (fun j => a (j+1)) g htail
    refine ⟨q,hqn.trans hgn,?_⟩
    rw [blaschkePrefix_shift,← multiply_assoc,hq]
    exact hg

/-- A tail Blaschke product is realized by an actual Hardy vector using weak limits of the
literal inner prefixes. This does not assert an unproved boundary-factorization theorem. -/
theorem hardy_blaschke_tail (a : ℕ → Disk) (ha : Summable (fun n => 1-‖(a n).val‖)) (k : ℕ) :
    ∃ f : Hardy, ∀ z : Disk, analyticValue f.val z.val = ∏' n, blaschkeFactor (a (n+k)) z.val := by
  let tail : ℕ → Disk := fun n => a (n+k)
  let q : ℕ → Hardy := fun n => ⟨toL2 (blaschkePrefix tail n),(blaschkePrefix_isInner tail n).1⟩
  have hn (n : ℕ) : ‖q n‖ ≤ ‖constL2 1‖ := by
    change ‖toL2 (blaschkePrefix tail n)‖ ≤ ‖constL2 1‖
    rw [← boundaryInclusion_apply]
    change ‖innerMultiplyIsometry (blaschkePrefix tail n) (blaschkePrefix_isInner tail n) (constL2 1)‖ ≤ _
    rw [LinearIsometry.norm_map]
  obtain ⟨f,_hfn,r,hr,hweak⟩ := hardy_bounded_subsequence q ‖constL2 1‖ hn
  have ht : Summable (fun n => 1-‖(tail n).val‖) :=
    ha.comp_injective (fun i j hij => Nat.add_right_cancel hij)
  refine ⟨f,fun z => ?_⟩
  have hp := ((blaschkeFactors_multipliable tail ht z).tendsto_prod_tprod_nat).comp hr.tendsto_atTop
  have he : (fun n => ∏ j ∈ Finset.range (r n), blaschkeFactor (tail j) z.val) =
      fun n => analyticValue (q (r n)).val z.val := by
    funext n
    exact (innerValue_blaschkePrefix tail (r n) z).symm
  change Tendsto (fun n => ∏ j ∈ Finset.range (r n), blaschkeFactor (tail j) z.val) _ _ at hp
  rw [he] at hp
  exact tendsto_nhds_unique (hweak z) hp

/-- Every literal finite prefix divides the given actual Blaschke inner function, also at
repeated nodes; the residual is a genuine Hardy vector. -/
theorem blaschke_inner_prefix_factor (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) :
    ∃ f : Hardy, multiply (blaschkePrefix a n) f.val = toL2 u := by
  obtain ⟨r,hr⟩ := hardy_blaschke_tail a hz.1 n
  obtain ⟨α,_hα,huval⟩ := hz.2
  let f : Hardy := α • r
  refine ⟨f,?_⟩
  have hh := multiply_mem_hardy _ (blaschkePrefix_isInner a n).1 f.val f.property
  have he : (⟨multiply (blaschkePrefix a n) f.val,hh⟩ : Hardy) = ⟨toL2 u,hu.1⟩ := by
    apply hardy_analyticValue_injective
    intro z hzd
    let w : Disk := ⟨z,hzd⟩
    rw [analyticValue_multiply _ (blaschkePrefix_isInner a n).1 f w,
      innerValue_blaschkePrefix]
    change _ = innerValue u w.val
    rw [huval _ w.property]
    change (∏ j ∈ Finset.range n, blaschkeFactor (a j) w.val)*analyticValue (α • r.val) w.val = _
    rw [analyticValue_smul _ _ w.property,hr]
    have ht : Summable (fun j => 1-‖(a (j+n)).val‖) :=
      hz.1.comp_injective (fun i j hij => Nat.add_right_cancel hij)
    have hp := Multipliable.prod_mul_tprod_nat_mul'
      (f := fun j => blaschkeFactor (a j) w.val) (k := n)
      (blaschkeFactors_multipliable (fun j => a (j+n)) ht w)
    calc
      _ = α*((∏ j ∈ Finset.range n, blaschkeFactor (a j) w.val)*
          ∏' j, blaschkeFactor (a (j+n)) w.val) := by ring
      _ = _ := by rw [hp]
  exact congrArg Subtype.val he

theorem multiply_mode_toL2 (u : BoundaryLInf) (j : ℤ) :
    multiply u (fourierBasis (T := 1) j) = multiply (mode j) (toL2 u) := by
  rw [← toL2_mode,← toL2_multiplyInf,multiplyInf_comm,toL2_multiplyInf]

/-- Every literal Malmquist vector belongs to the actual model, even at repeated zeros. -/
theorem malmquistHardy_mem_model_of_prefix_factor (u : BoundaryLInf) (a : ℕ → Disk)
    (n : ℕ) (hfactor : ∃ r : Hardy, multiply (blaschkePrefix a (n+1)) r.val = toL2 u) :
    (malmquistHardy a n).val ∈ model u := by
  obtain ⟨r,hr⟩ := hfactor
  refine ⟨(malmquistHardy a n).property,(Submodule.mem_orthogonal' _ _).mpr ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j,rfl⟩ := hy
    have he : multiply u (fourierBasis (T := 1) (j : ℤ)) =
        multiply (blaschkePrefix a n) (multiply (blaschkeBoundary (a n)) (multiply (mode (j : ℤ)) r.val)) := by
      rw [multiply_mode_toL2,← hr]
      change multiply (mode (j : ℤ)) (multiply (multiplyInf (blaschkePrefix a n) (blaschkeBoundary (a n))) r.val) = _
      rw [multiply_comm (mode (j : ℤ)),← multiply_assoc]
    change inner ℂ (malmquistHardy a n).val (multiply u (fourierBasis (T := 1) (j : ℤ))) = 0
    rw [he]
    change inner ℂ
      (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n) (hardyNodeVector (a n)).val)
      (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n)
        (multiply (blaschkeBoundary (a n)) (multiply (mode (j : ℤ)) r.val))) = 0
    rw [LinearIsometry.inner_map_map]
    change inner ℂ (hardyNodeVector (a n))
      (hardyMultiply (blaschkeBoundary (a n)) (blaschkeBoundary_hardy (a n))
        ⟨multiply (mode (j : ℤ)) r.val,mode_multiply_hardy r j⟩) = 0
    exact inner_hardyNodeVector_blaschke _ _
  | zero => simp
  | add x y hx hy hx' hy' => rw [inner_add_right,hx',hy',add_zero]
  | smul c x hx hx' => rw [inner_smul_right,hx',mul_zero]

/-- Membership for a full Blaschke product, retaining repeated nodes. -/
theorem malmquistHardy_mem_model (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) : (malmquistHardy a n).val ∈ model u :=
  malmquistHardy_mem_model_of_prefix_factor u a n (blaschke_inner_prefix_factor u hu a hz (n+1))

/-- Total Malmquist orthogonality forces genuine division by the full Blaschke product.
This uses successive quotients rather than a distinct-node vanishing hypothesis. -/
theorem hardy_divide_malmquist (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (f : Hardy)
    (hf : ∀ n, inner ℂ (malmquistHardy a n) f = 0) :
    ∃ g : Hardy, multiply u g.val = f.val := by
  have hdiv (N : ℕ) := hardy_divide_malmquist_prefix a N f (fun n _ => hf n)
  choose qs hqnorm hq using hdiv
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
      have he := congrArg (fun v : BoundaryL2 => analyticValue v w.val) (hq (r n))
      rw [analyticValue_multiply _ (blaschkePrefix_isInner a (r n)).1 (qs (r n)) w,
        innerValue_blaschkePrefix] at he
      exact he
    have hlim := tendsto_nhds_unique hpq hconst
    change analyticValue (multiply u g.val) w.val = analyticValue f.val w.val
    rw [analyticValue_multiply u hu.1 g w,huval _ w.property]
    change (α*(∏' i, blaschkeFactor (a i) w.val))*analyticValue (α⁻¹ • q.val) w.val = _
    rw [analyticValue_smul _ _ w.property]
    calc
      (α*(∏' i, blaschkeFactor (a i) w.val))*(α⁻¹*analyticValue q.val w.val) =
        (α*α⁻¹)*((∏' i, blaschkeFactor (a i) w.val)*analyticValue q.val w.val) := by ring
      _ = analyticValue f.val w.val := by rw [mul_inv_cancel₀ hαne,one_mul]; exact hlim
  exact congrArg Subtype.val he

/-- The actual Malmquist family with codomain the native model space. -/
def malmquistModel (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) : Model u :=
  ⟨(malmquistHardy a n).val,malmquistHardy_mem_model u hu a hz n⟩

theorem malmquistModel_orthonormal (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) : Orthonormal ℂ (malmquistModel u hu a hz) := by
  constructor
  · intro n
    exact norm_malmquistHardy a n
  · intro i j hij
    exact (malmquistHardy_orthonormal a).2 hij

theorem malmquistModel_dense (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) :
    Dense (Submodule.span ℂ (Set.range (malmquistModel u hu a hz)) : Set (Model u)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have ho (n : ℕ) : inner ℂ (malmquistHardy a n) (modelHardyIsometry u f) = 0 := by
    exact (Submodule.mem_orthogonal _ _).mp hf _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n)))
  obtain ⟨g,hg⟩ := hardy_divide_malmquist u hu a hz (modelHardyIsometry u f) ho
  have he : inner ℂ f.val f.val = 0 := by
    calc
      inner ℂ f.val f.val = inner ℂ (multiply u g.val) f.val := congrArg (fun x => inner ℂ x f.val) hg.symm
      _ = 0 := inner_multiply_model u f g
  exact Subtype.ext (inner_self_eq_zero.mp he)

/-- The genuine Malmquist Hilbert basis, without any distinctness or interpolation hypothesis. -/
def malmquistBasis (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) : HilbertBasis ℕ ℂ (Model u) :=
  HilbertBasis.mk (malmquistModel_orthonormal u hu a hz)
    (by
      rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (malmquistModel_dense u hu a hz)])

@[simp] theorem malmquistBasis_apply (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) : malmquistBasis u hu a hz n = malmquistModel u hu a hz n := by
  exact congrFun (HilbertBasis.coe_mk (malmquistModel_orthonormal u hu a hz) _) n

/-- The normalized Hardy node has the literal first-coordinate shift expectation. -/
theorem inner_hardyNodeVector_shift (a : Disk) :
    inner ℂ (hardyNodeVector a).val (multiply coordinate (hardyNodeVector a).val) = a.val := by
  change inner ℂ (hardyNodeVector a)
    (hardyMultiply coordinate coordinate_isInner.1 (hardyNodeVector a)) = _
  rw [inner_hardyNodeVector,hardyMultiply_apply,analyticValue_coordinate_multiply]
  calc
    _ = a.val*((Real.sqrt (1-‖a.val‖^2) : ℂ)*analyticValue (hardyNodeVector a).val a.val) := by ring
    _ = a.val*inner ℂ (hardyNodeVector a) (hardyNodeVector a) := by rw [inner_hardyNodeVector]
    _ = a.val := by rw [inner_self_eq_norm_sq_to_K,norm_hardyNodeVector]; simp

/-- Inner prefix multiplication preserves that shift expectation. -/
theorem inner_malmquistHardy_shift (a : ℕ → Disk) (n : ℕ) :
    inner ℂ (malmquistHardy a n).val (multiply coordinate (malmquistHardy a n).val) = (a n).val := by
  change inner ℂ (multiply (blaschkePrefix a n) (hardyNodeVector (a n)).val)
    (multiply coordinate (multiply (blaschkePrefix a n) (hardyNodeVector (a n)).val)) = _
  rw [multiply_comm coordinate]
  change inner ℂ (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n)
      (hardyNodeVector (a n)).val)
    (innerMultiplyIsometry (blaschkePrefix a n) (blaschkePrefix_isInner a n)
      (multiply coordinate (hardyNodeVector (a n)).val)) = _
  rw [LinearIsometry.inner_map_map]
  exact inner_hardyNodeVector_shift (a n)

/-- Exact ambient residual energy; compression to K_u can only decrease it. -/
theorem malmquistHardy_shift_residual_sq (a : ℕ → Disk) (n : ℕ) :
    ‖multiply coordinate (malmquistHardy a n).val-(a n).val • (malmquistHardy a n).val‖^2 =
      1-‖(a n).val‖^2 := by
  have he : ‖(malmquistHardy a n).val‖ = 1 := norm_malmquistHardy a n
  have hz : ‖multiply coordinate (malmquistHardy a n).val‖ = 1 := by
    change ‖innerMultiplyIsometry coordinate coordinate_isInner (malmquistHardy a n).val‖ = _
    rw [LinearIsometry.norm_map,he]
  have hrev : inner ℂ (multiply coordinate (malmquistHardy a n).val) (malmquistHardy a n).val =
      conj (a n).val := by
    rw [← inner_conj_symm (𝕜 := ℂ),inner_malmquistHardy_shift]
  rw [norm_sub_sq (𝕜 := ℂ),hz,inner_smul_right,hrev,Complex.mul_conj',norm_smul,he,mul_one]
  simp only [one_pow,← Complex.ofReal_pow]
  change 1-2*‖(a n).val‖^2+‖(a n).val‖^2 = 1-‖(a n).val‖^2
  ring

/-- The actual unitary synthesized from the literal Malmquist Hilbert basis. -/
def malmquistUnitary (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) : SequenceL2 ≃ₗᵢ[ℂ] Model u := (malmquistBasis u hu a hz).repr.symm

/-- The actual bounded native diagonal of the disk nodes. -/
def malmquistDiagonal (a : ℕ → Disk) : SequenceOperator :=
  diagonalOperator (fun n => (a n).val) 1 zero_le_one (fun n => (a n).property.le)

theorem malmquistDiagonal_isDiagonal (a : ℕ → Disk) : Diagonal (fun n => (a n).val) (malmquistDiagonal a) :=
  diagonalOperator_isDiagonal _ _ _ _

theorem malmquist_diagonal_basis (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) :
    unitaryConjugate (malmquistUnitary u hu a hz) (malmquistDiagonal a)
      (malmquistBasis u hu a hz n) = (a n).val • malmquistBasis u hu a hz n := by
  change (malmquistBasis u hu a hz).repr.symm
    (malmquistDiagonal a ((malmquistBasis u hu a hz).repr (malmquistBasis u hu a hz n))) = _
  rw [HilbertBasis.repr_self,malmquistDiagonal_isDiagonal,map_smul,HilbertBasis.repr_symm_single]

/-- The literal compressed shift residual has summable-column majorant 1-|a_n|². -/
theorem malmquist_shift_column_sq_le (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) (n : ℕ) :
    ‖(boundedSymbolOperator u coordinate-
      unitaryConjugate (malmquistUnitary u hu a hz) (malmquistDiagonal a))
        (malmquistBasis u hu a hz n)‖^2 ≤ 1-‖(a n).val‖^2 := by
  rw [sub_apply,malmquist_diagonal_basis]
  have hP : (boundedSymbolOperator u coordinate) (malmquistBasis u hu a hz n)-
      (a n).val • malmquistBasis u hu a hz n =
      (model u).orthogonalProjectionOnto
        (multiply coordinate (malmquistHardy a n).val-(a n).val • (malmquistHardy a n).val) := by
    rw [malmquistBasis_apply,map_sub,map_smul]
    change _ = (model u).orthogonalProjectionOnto (multiply coordinate (malmquistModel u hu a hz n).val)-
      (a n).val • (model u).orthogonalProjectionOnto (malmquistModel u hu a hz n).val
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rfl
  rw [hP]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((model u).norm_orthogonalProjectionOnto_apply_le _) 2).trans_eq (malmquistHardy_shift_residual_sq a n)

/-- The native compressed shift is its actual Malmquist node diagonal modulo S₂.
This is the ℕ-indexed repeated-node model; arbitrary countable index transport is separate. -/
theorem malmquist_shift_schatten (u : BoundaryLInf) (hu : IsInner u) (a : ℕ → Disk)
    (hz : HasBlaschkeZeros u a) :
    Schatten 2 (boundedSymbolOperator u coordinate-
      unitaryConjugate (malmquistUnitary u hu a hz) (malmquistDiagonal a)) := by
  let K := boundedSymbolOperator u coordinate-
    unitaryConjugate (malmquistUnitary u hu a hz) (malmquistDiagonal a)
  have hb (n : ℕ) : 0 ≤ 1-‖(a n).val‖^2 := by
    have hn : ‖(a n).val‖ < 1 := (a n).property
    nlinarith [norm_nonneg (a n).val]
  have hs : Summable (fun n => 1-‖(a n).val‖^2) :=
    (hz.1.mul_left 2).of_nonneg_of_le hb (fun n => by
      have hn : ‖(a n).val‖ < 1 := (a n).property
      nlinarith [norm_nonneg (a n).val])
  have hcol : Summable (fun n => ‖K (malmquistBasis u hu a hz n)‖^2) :=
    hs.of_nonneg_of_le (fun n => sq_nonneg _) (malmquist_shift_column_sq_le u hu a hz)
  apply (schatten_two_iff_columnEnergy K (malmquistBasis u hu a hz)).mpr
  unfold columnEnergy
  have he : (∑' n, ‖K (malmquistBasis u hu a hz n)‖ₑ^2) =
      ENNReal.ofReal (∑' n, ‖K (malmquistBasis u hu a hz n)‖^2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖K (malmquistBasis u hu a hz n)‖) hcol]
    apply tsum_congr
    intro n
    rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (K (malmquistBasis u hu a hz n)))]
  rw [he]
  exact ENNReal.ofReal_lt_top

theorem malmquist_toL2_smul (c : ℂ) (u : BoundaryLInf) : toL2 (c • u) = c • toL2 u := by
  rw [← boundaryInclusion_apply,map_smul,boundaryInclusion_apply]

/-- The literal finite-prefix splitting formula in L∞. -/
theorem blaschkePrefix_add (a : ℕ → Disk) (n k : ℕ) :
    blaschkePrefix a (n+k) = multiplyInf (blaschkePrefix a n)
      (blaschkePrefix (fun j => a (j+n)) k) := by
  apply boundedHardy_boundary_ext _ _ (blaschkePrefix_isInner a (n+k)).1
    (isInner_multiplyInf _ _ (blaschkePrefix_isInner a n) (blaschkePrefix_isInner _ k)).1
  intro z
  rw [innerValue_blaschkePrefix]
  change _ = analyticValue (toL2 (multiplyInf _ _)) z.val
  rw [toL2_multiplyInf,analyticValue_multiply _ (blaschkePrefix_isInner a n).1
    ⟨toL2 (blaschkePrefix (fun j => a (j+n)) k),(blaschkePrefix_isInner _ _).1⟩ z]
  change _ = innerValue (blaschkePrefix a n) z.val*innerValue (blaschkePrefix (fun j => a (j+n)) k) z.val
  rw [innerValue_blaschkePrefix,innerValue_blaschkePrefix]
  simpa only [Nat.add_comm] using Finset.prod_range_add (fun j => blaschkeFactor (a j) z.val) n k

/-- Extend only to use finite prefixes; no extra zeros enter the finite model. -/
def finiteNodesExtension {N : ℕ} (a : Fin N → Disk) (n : ℕ) : Disk :=
  if hn : n < N then a ⟨n,hn⟩ else origin

@[simp] theorem finiteNodesExtension_at {N : ℕ} (a : Fin N → Disk) (i : Fin N) :
    finiteNodesExtension a i.val = a i := by simp [finiteNodesExtension,i.isLt]

theorem finiteBlaschke_eq_scalar_prefix (u : BoundaryLInf) (hu : IsInner u) {N : ℕ}
    (a : Fin N → Disk) (hz : HasBlaschkeZeros u a) :
    ∃ α : ℂ, ‖α‖ = 1 ∧ u = α • blaschkePrefix (finiteNodesExtension a) N := by
  obtain ⟨α,hα,hval⟩ := hz.2
  refine ⟨α,hα,?_⟩
  have hv : toL2 (α • blaschkePrefix (finiteNodesExtension a) N) ∈ hardy := by
    rw [malmquist_toL2_smul]
    exact hardy.smul_mem _ (blaschkePrefix_isInner _ N).1
  apply boundedHardy_boundary_ext _ _ hu.1 hv
  intro z
  change _ = analyticValue (toL2 (α • blaschkePrefix (finiteNodesExtension a) N)) z.val
  rw [malmquist_toL2_smul,analyticValue_smul _ _ z.property]
  change innerValue u z.val = α*innerValue (blaschkePrefix (finiteNodesExtension a) N) z.val
  rw [hval _ z.property,innerValue_blaschkePrefix,tprod_fintype]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [finiteNodesExtension_at]

/-- Any prefix lying inside a finite Blaschke zero list divides the actual inner symbol. -/
theorem finiteBlaschke_prefix_factor (u : BoundaryLInf) (hu : IsInner u) {N : ℕ}
    (a : Fin N → Disk) (hz : HasBlaschkeZeros u a) (n : ℕ) (hn : n ≤ N) :
    ∃ r : Hardy, multiply (blaschkePrefix (finiteNodesExtension a) n) r.val = toL2 u := by
  obtain ⟨α,_hα,huEq⟩ := finiteBlaschke_eq_scalar_prefix u hu a hz
  let b := finiteNodesExtension a
  let r : Hardy := α • ⟨toL2 (blaschkePrefix (fun j => b (j+n)) (N-n)),(blaschkePrefix_isInner _ _).1⟩
  refine ⟨r,?_⟩
  change multiply (blaschkePrefix b n) (α • toL2 (blaschkePrefix (fun j => b (j+n)) (N-n))) = _
  rw [map_smul,← toL2_multiplyInf,← blaschkePrefix_add,Nat.add_sub_of_le hn]
  rw [huEq,malmquist_toL2_smul]

/-- The genuine finite Malmquist family in K_u, including the degree-zero empty family. -/
def finiteMalmquistModel (u : BoundaryLInf) (hu : IsInner u) {N : ℕ} (a : Fin N → Disk)
    (hz : HasBlaschkeZeros u a) (i : Fin N) : Model u :=
  ⟨(malmquistHardy (finiteNodesExtension a) i.val).val,
    malmquistHardy_mem_model_of_prefix_factor u (finiteNodesExtension a) i.val
      (finiteBlaschke_prefix_factor u hu a hz (i.val+1) i.isLt)⟩

theorem finiteMalmquistModel_orthonormal (u : BoundaryLInf) (hu : IsInner u) {N : ℕ}
    (a : Fin N → Disk) (hz : HasBlaschkeZeros u a) : Orthonormal ℂ (finiteMalmquistModel u hu a hz) := by
  constructor
  · intro i
    exact norm_malmquistHardy (finiteNodesExtension a) i.val
  · intro i j hij
    exact (malmquistHardy_orthonormal (finiteNodesExtension a)).2 (Fin.val_injective.ne hij)

theorem finiteMalmquistModel_dense (u : BoundaryLInf) (hu : IsInner u) {N : ℕ}
    (a : Fin N → Disk) (hz : HasBlaschkeZeros u a) :
    Dense (Submodule.span ℂ (Set.range (finiteMalmquistModel u hu a hz)) : Set (Model u)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have ho (n : ℕ) (hn : n < N) :
      inner ℂ (malmquistHardy (finiteNodesExtension a) n) (modelHardyIsometry u f) = 0 := by
    exact (Submodule.mem_orthogonal _ _).mp hf _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (⟨n,hn⟩ : Fin N))))
  obtain ⟨r,_hrn,hr⟩ := hardy_divide_malmquist_prefix (finiteNodesExtension a) N (modelHardyIsometry u f) ho
  obtain ⟨α,hα,huEq⟩ := finiteBlaschke_eq_scalar_prefix u hu a hz
  have hαne : α ≠ 0 := by intro h; rw [h,norm_zero] at hα; norm_num at hα
  let g : Hardy := α⁻¹ • r
  have hg : multiply u g.val = f.val := by
    conv_lhs => rw [huEq]
    apply Lp.ext
    filter_upwards [multiply_ae (α • blaschkePrefix (finiteNodesExtension a) N) g.val,
      Lp.coeFn_smul α (blaschkePrefix (finiteNodesExtension a) N),
      Lp.coeFn_smul α⁻¹ r.val,multiply_ae (blaschkePrefix (finiteNodesExtension a) N) r.val]
      with t hm hαp hgr hp
    change multiply (α • blaschkePrefix (finiteNodesExtension a) N) (α⁻¹ • r.val) t =
      (α • blaschkePrefix (finiteNodesExtension a) N) t*((α⁻¹ • r.val) t) at hm
    change (α⁻¹ • r.val) t = α⁻¹*r.val t at hgr
    change (α • blaschkePrefix (finiteNodesExtension a) N) t = α*blaschkePrefix (finiteNodesExtension a) N t at hαp
    change multiply (α • blaschkePrefix (finiteNodesExtension a) N) (α⁻¹ • r.val) t = f.val t
    rw [hm,hαp,hgr]
    calc
      _ = (α*α⁻¹)*(blaschkePrefix (finiteNodesExtension a) N t*r.val t) := by ring
      _ = f.val t := by rw [mul_inv_cancel₀ hαne,one_mul,← hp,hr]; rfl
  have he : inner ℂ f.val f.val = 0 := by
    calc
      inner ℂ f.val f.val = inner ℂ (multiply u g.val) f.val := congrArg (fun x => inner ℂ x f.val) hg.symm
      _ = 0 := inner_multiply_model u f g
  exact Subtype.ext (inner_self_eq_zero.mp he)

/-- Actual finite Malmquist basis, preserving repeated zeros and the empty case. -/
def finiteMalmquistBasis (u : BoundaryLInf) (hu : IsInner u) {N : ℕ} (a : Fin N → Disk)
    (hz : HasBlaschkeZeros u a) : HilbertBasis (Fin N) ℂ (Model u) :=
  HilbertBasis.mk (finiteMalmquistModel_orthonormal u hu a hz)
    (by rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (finiteMalmquistModel_dense u hu a hz)])

@[simp] theorem finiteMalmquistBasis_apply (u : BoundaryLInf) (hu : IsInner u) {N : ℕ}
    (a : Fin N → Disk) (hz : HasBlaschkeZeros u a) (i : Fin N) :
    finiteMalmquistBasis u hu a hz i = finiteMalmquistModel u hu a hz i := by
  exact congrFun (HilbertBasis.coe_mk (finiteMalmquistModel_orthonormal u hu a hz) _) i

/-- The column estimate only needs the literal Malmquist vector to lie in the model. -/
theorem compressedShift_malmquist_column_sq_le (u : BoundaryLInf) (a : ℕ → Disk) (n : ℕ)
    (f : Model u) (hf : f.val = (malmquistHardy a n).val) :
    ‖boundedSymbolOperator u coordinate f-(a n).val • f‖^2 ≤ 1-‖(a n).val‖^2 := by
  have hp : boundedSymbolOperator u coordinate f-(a n).val • f =
      (model u).orthogonalProjectionOnto (multiply coordinate f.val-(a n).val • f.val) := by
    rw [map_sub,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rfl
  rw [hp]
  apply (pow_le_pow_left₀ (norm_nonneg _) ((model u).norm_orthogonalProjectionOnto_apply_le _) 2).trans_eq
  rw [hf]
  exact malmquistHardy_shift_residual_sq a n

/-- Relabel a genuine model Hilbert basis; this only permutes its actual vectors. -/
def relabelModelBasis {ι κ : Type} (u : BoundaryLInf) (b : HilbertBasis ι ℂ (Model u))
    (e : κ ≃ ι) : HilbertBasis κ ℂ (Model u) :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨j,rfl⟩; exact Set.mem_range_self (e j)
      · rintro ⟨i,rfl⟩; exact ⟨e.symm i,by simp⟩
    rw [hr,b.dense_span])

@[simp] theorem relabelModelBasis_apply {ι κ : Type} (u : BoundaryLInf)
    (b : HilbertBasis ι ℂ (Model u)) (e : κ ≃ ι) (i : κ) : relabelModelBasis u b e i = b (e i) := by
  exact congrFun (HilbertBasis.coe_mk (b.orthonormal.comp e e.injective) _) i

theorem hasBlaschkeZeros_relabel {ι κ : Type} (u : BoundaryLInf) (a : ι → Disk)
    (e : κ ≃ ι) (hz : HasBlaschkeZeros u a) : HasBlaschkeZeros u (a ∘ e) := by
  constructor
  · exact e.summable_iff.mpr hz.1
  · obtain ⟨α,hα,hv⟩ := hz.2
    refine ⟨α,hα,fun z hz => ?_⟩
    rw [hv _ hz]
    congr 1
    exact (e.tprod_eq (fun i => blaschkeFactor (a i) z)).symm

/-- A Hilbert basis with the sharp residual column bound exists for countable-index Blaschke models, including finite/empty lists and repeated zeros. -/
theorem exists_blaschke_model_basis (u : BoundaryLInf) (hu : IsInner u) {ι : Type}
    (a : ι → Disk) (hc : Countable ι) (hz : HasBlaschkeZeros u a) :
    ∃ b : HilbertBasis ι ℂ (Model u), ∀ i,
      ‖boundedSymbolOperator u coordinate (b i)-(a i).val • b i‖^2 ≤ 1-‖(a i).val‖^2 := by
  classical
  let : Countable ι := hc
  rcases finite_or_infinite ι with hfin | hinf
  · let : Finite ι := hfin
    let : Fintype ι := Fintype.ofFinite ι
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let af : Fin (Fintype.card ι) → Disk := a ∘ e.symm
    have hzf := hasBlaschkeZeros_relabel u a e.symm hz
    let b := finiteMalmquistBasis u hu af hzf
    refine ⟨relabelModelBasis u b e,fun i => ?_⟩
    rw [relabelModelBasis_apply]
    have he : (b (e i)).val = (malmquistHardy (finiteNodesExtension af) (e i).val).val := by
      rw [finiteMalmquistBasis_apply]; rfl
    have h := compressedShift_malmquist_column_sq_le u (finiteNodesExtension af) (e i).val (b (e i)) he
    simpa only [finiteNodesExtension_at,af,Function.comp_apply,Equiv.symm_apply_apply] using h
  · let : Infinite ι := hinf
    let e : ℕ ≃ ι := Classical.choice (inferInstance : Nonempty (ℕ ≃ ι))
    let an : ℕ → Disk := a ∘ e
    have hzn := hasBlaschkeZeros_relabel u a e hz
    let b := malmquistBasis u hu an hzn
    refine ⟨relabelModelBasis u b e.symm,fun i => ?_⟩
    rw [relabelModelBasis_apply]
    have he : (b (e.symm i)).val = (malmquistHardy an (e.symm i)).val := by
      rw [malmquistBasis_apply]; rfl
    have h := compressedShift_malmquist_column_sq_le u an (e.symm i) (b (e.symm i)) he
    simpa only [an,Function.comp_apply,Equiv.apply_symm_apply] using h

/-- The actual native arbitrary-index node diagonal, with its uniform disk bound. -/
def diskNodeDiagonal {ι : Type} (a : ι → Disk) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lp.mapCLM 2 (fun i => ContinuousLinearMap.lsmul ℂ ℂ (a i).val) zero_le_one
    (fun i => (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℂ) (E := ℂ) (a i).val).trans (a i).property.le)

@[simp] theorem diskNodeDiagonal_apply {ι : Type} (a : ι → Disk)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) : diskNodeDiagonal a x i = (a i).val*x i := rfl

theorem diskNodeDiagonal_isDiagonal {ι : Type} (a : ι → Disk) :
    IndexedDiagonal (fun i => (a i).val) (diskNodeDiagonal a) := by
  classical
  intro i
  apply lp.ext
  funext j
  simp only [diskNodeDiagonal_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases h : j = i
  · subst j; rfl
  · simp [lp.single_apply,Pi.single_eq_of_ne h]

theorem diskNodeDiagonal_conjugate_basis {ι : Type} (u : BoundaryLInf) (a : ι → Disk)
    (b : HilbertBasis ι ℂ (Model u)) (i : ι) :
    unitaryConjugate b.repr.symm (diskNodeDiagonal a) (b i) = (a i).val • b i := by
  classical
  change b.repr.symm (diskNodeDiagonal a (b.repr (b i))) = _
  rw [b.repr_self,diskNodeDiagonal_isDiagonal,map_smul,b.repr_symm_single]

/-- The FULL countable-index pure Blaschke compressed-shift model modulo native S₂.
The polynomial comparison is proved separately below by the direct Lipschitz column estimate. -/
theorem blaschke_shift_model (u : BoundaryLInf) (hu : IsInner u) {ι : Type}
    (a : ι → Disk) (hc : Countable ι) (hz : HasBlaschkeZeros u a) :
    ∃ U : lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] Model u,
    ∃ D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
      IndexedDiagonal (fun i => (a i).val) D ∧
      ∃ K : Model u →L[ℂ] Model u, Schatten 2 K ∧ boundedSymbolOperator u coordinate = unitaryConjugate U D+K := by
  obtain ⟨b,hb⟩ := exists_blaschke_model_basis u hu a hc hz
  let K := boundedSymbolOperator u coordinate-unitaryConjugate b.repr.symm (diskNodeDiagonal a)
  refine ⟨b.repr.symm,diskNodeDiagonal a,diskNodeDiagonal_isDiagonal a,K,?_,?_⟩
  · have hn (i : ι) : 0 ≤ 1-‖(a i).val‖^2 := by
      have hi : ‖(a i).val‖ < 1 := (a i).property
      nlinarith [norm_nonneg (a i).val]
    have hs : Summable (fun i => 1-‖(a i).val‖^2) :=
      (hz.1.mul_left 2).of_nonneg_of_le hn (fun i => by
        have hi : ‖(a i).val‖ < 1 := (a i).property
        nlinarith [norm_nonneg (a i).val])
    have hcol : Summable (fun i => ‖K (b i)‖^2) := hs.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
      change ‖(boundedSymbolOperator u coordinate-unitaryConjugate b.repr.symm (diskNodeDiagonal a)) (b i)‖^2 ≤ _
      rw [sub_apply,diskNodeDiagonal_conjugate_basis]
      exact hb i)
    apply (schatten_two_iff_columnEnergy K b).mpr
    unfold columnEnergy
    have he : (∑' i, ‖K (b i)‖ₑ^2) = ENNReal.ofReal (∑' i, ‖K (b i)‖^2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖K (b i)‖) hcol]
      apply tsum_congr
      intro i
      rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (K (b i)))]
    rw [he]
    exact ENNReal.ofReal_lt_top
  · dsimp [K]
    abel

/-- The basis also retains its LITERAL ambient column identity, which polynomial comparison
uses before compression. This is stronger data than the compressed-shift bound alone. -/
theorem exists_blaschke_model_basis_ambient (u : BoundaryLInf) (hu : IsInner u) {ι : Type}
    (a : ι → Disk) (hc : Countable ι) (hz : HasBlaschkeZeros u a) :
    ∃ b : HilbertBasis ι ℂ (Model u), ∀ i,
      ‖multiply coordinate (b i).val-(a i).val • (b i).val‖^2 = 1-‖(a i).val‖^2 := by
  classical
  let : Countable ι := hc
  rcases finite_or_infinite ι with hfin | hinf
  · let : Finite ι := hfin
    let : Fintype ι := Fintype.ofFinite ι
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let af : Fin (Fintype.card ι) → Disk := a ∘ e.symm
    have hzf := hasBlaschkeZeros_relabel u a e.symm hz
    let b := finiteMalmquistBasis u hu af hzf
    refine ⟨relabelModelBasis u b e,fun i => ?_⟩
    rw [relabelModelBasis_apply]
    have he : (b (e i)).val = (malmquistHardy (finiteNodesExtension af) (e i).val).val := by
      rw [finiteMalmquistBasis_apply]; rfl
    rw [he]
    have h := malmquistHardy_shift_residual_sq (finiteNodesExtension af) (e i).val
    simpa only [finiteNodesExtension_at,af,Function.comp_apply,Equiv.symm_apply_apply] using h
  · let : Infinite ι := hinf
    let e : ℕ ≃ ι := Classical.choice (inferInstance : Nonempty (ℕ ≃ ι))
    let an : ℕ → Disk := a ∘ e
    have hzn := hasBlaschkeZeros_relabel u a e hz
    let b := malmquistBasis u hu an hzn
    refine ⟨relabelModelBasis u b e.symm,fun i => ?_⟩
    rw [relabelModelBasis_apply]
    have he : (b (e.symm i)).val = (malmquistHardy an (e.symm i)).val := by
      rw [malmquistBasis_apply]; rfl
    rw [he]
    have h := malmquistHardy_shift_residual_sq an (e.symm i)
    simpa only [an,Function.comp_apply,Equiv.apply_symm_apply] using h

/-- Elementary power comparison on the closed disk. -/
theorem norm_pow_sub_pow_le_on_unit {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z^n-w^n‖ ≤ (n : ℝ)*‖z-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwp : ‖w‖^n ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
    calc
      ‖z^(n+1)-w^(n+1)‖ = ‖z*(z^n-w^n)+(z-w)*w^n‖ := by congr 1; ring
      _ ≤ ‖z*(z^n-w^n)‖+‖(z-w)*w^n‖ := norm_add_le _ _
      _ = ‖z‖*‖z^n-w^n‖+‖z-w‖*‖w‖^n := by rw [norm_mul,norm_mul,norm_pow]
      _ ≤ (n : ℝ)*‖z-w‖+‖z-w‖ := by
        have h1 := (mul_le_mul_of_nonneg_right hz (norm_nonneg (z^n-w^n))).trans (by simpa using ih)
        have h2 := mul_le_mul_of_nonneg_left hwp (norm_nonneg (z-w))
        nlinarith
      _ = ((n+1 : ℕ) : ℝ)*‖z-w‖ := by push_cast; ring

/-- A mixed monomial has closed-disk Lipschitz constant j+k. -/
theorem norm_bimonomial_sub_le_on_unit {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (j k : ℕ) :
    ‖z^j*conj z^k-w^j*conj w^k‖ ≤ ((j : ℝ)+(k : ℝ))*‖z-w‖ := by
  have hj := norm_pow_sub_pow_le_on_unit hz hw j
  have hk := norm_pow_sub_pow_le_on_unit (z := conj z) (w := conj w)
    (by simpa using hz) (by simpa using hw) k
  rw [← map_sub,Complex.norm_conj] at hk
  have hzpow : ‖conj z^k‖ ≤ 1 := by rw [norm_pow,Complex.norm_conj]; exact pow_le_one₀ (norm_nonneg z) hz
  have hwpow : ‖w^j‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg w) hw
  calc
    _ = ‖(z^j-w^j)*conj z^k+w^j*(conj z^k-conj w^k)‖ := by congr 1; ring
    _ ≤ ‖(z^j-w^j)*conj z^k‖+‖w^j*(conj z^k-conj w^k)‖ := norm_add_le _ _
    _ = ‖z^j-w^j‖*‖conj z^k‖+‖w^j‖*‖conj z^k-conj w^k‖ := by rw [norm_mul,norm_mul]
    _ ≤ (j : ℝ)*‖z-w‖+(k : ℝ)*‖z-w‖ := by
      have h1 := (mul_le_mul_of_nonneg_left hzpow (norm_nonneg (z^j-w^j))).trans (by simpa using hj)
      have h2 := (mul_le_mul_of_nonneg_right hwpow (norm_nonneg (conj z^k-conj w^k))).trans (by simpa using hk)
      exact add_le_add h1 h2
    _ = _ := by ring

def biPolynomialNormBound (q : BiPolynomial) : ℝ := q.sum (fun _ c => ‖c‖)
def biPolynomialLipschitzBound (q : BiPolynomial) : ℝ :=
  q.sum (fun jk c => ‖c‖*((jk.1 : ℝ)+(jk.2 : ℝ)))

theorem biPolynomialNormBound_nonneg (q : BiPolynomial) : 0 ≤ biPolynomialNormBound q := by
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem biPolynomialLipschitzBound_nonneg (q : BiPolynomial) : 0 ≤ biPolynomialLipschitzBound q := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem norm_polynomialValue_le_on_unit (q : BiPolynomial) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖polynomialValue q z‖ ≤ biPolynomialNormBound q := by
  classical
  unfold polynomialValue biPolynomialNormBound Finsupp.sum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk _
  rw [norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_conj]
  have hj : ‖z‖^jk.1 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  have hk : ‖z‖^jk.2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  calc
    ‖q jk‖*‖z‖^jk.1*‖z‖^jk.2 ≤ ‖q jk‖*1*1 := by gcongr
    _ = ‖q jk‖ := by ring

theorem norm_polynomialValue_sub_le_on_unit (q : BiPolynomial) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖polynomialValue q z-polynomialValue q w‖ ≤ biPolynomialLipschitzBound q*‖z-w‖ := by
  classical
  unfold polynomialValue biPolynomialLipschitzBound Finsupp.sum
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk _
  calc
    ‖q jk*z^jk.1*conj z^jk.2-q jk*w^jk.1*conj w^jk.2‖ =
        ‖q jk*(z^jk.1*conj z^jk.2-w^jk.1*conj w^jk.2)‖ := by congr 1; ring
    _ ≤ ‖q jk‖*(((jk.1 : ℝ)+(jk.2 : ℝ))*‖z-w‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_bimonomial_sub_le_on_unit hz hw _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The literal L∞ polynomial already used in the polynomialSymbol definition. -/
def biPolynomialBoundary (q : BiPolynomial) : BoundaryLInf :=
  q.sum (fun jk c => c • multiplyInf (powerInf coordinate jk.1) (powerInf (star coordinate) jk.2))

@[simp] theorem toL2_biPolynomialBoundary (q : BiPolynomial) :
    toL2 (biPolynomialBoundary q) = polynomialSymbol q := rfl

theorem biPolynomialBoundary_ae (q : BiPolynomial) :
    biPolynomialBoundary q =ᵐ[circleMeasure] fun t => polynomialValue q (fourier (T := 1) 1 t) :=
  (toL2_ae (biPolynomialBoundary q)).symm.trans (polynomialSymbol_ae q)

/-- The actual polynomial compression is compared before projection to the literal shift
residual. This holds for every model vector, not only a selected basis. -/
theorem polynomial_column_norm_le (u : BoundaryLInf) (q : BiPolynomial) (a : Disk) (f : Model u) :
    ‖boundedSymbolOperator u (biPolynomialBoundary q) f-polynomialValue q a.val • f‖ ≤
      biPolynomialLipschitzBound q*‖multiply coordinate f.val-a.val • f.val‖ := by
  have hp : boundedSymbolOperator u (biPolynomialBoundary q) f-polynomialValue q a.val • f =
      (model u).orthogonalProjectionOnto
        (multiply (biPolynomialBoundary q) f.val-polynomialValue q a.val • f.val) := by
    rw [map_sub,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rfl
  rw [hp]
  apply ((model u).norm_orthogonalProjectionOnto_apply_le _).trans
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_ae (biPolynomialBoundary q) f.val,multiply_ae coordinate f.val,
    Lp.coeFn_sub (multiply (biPolynomialBoundary q) f.val) (polynomialValue q a.val • f.val),
    Lp.coeFn_sub (multiply coordinate f.val) (a.val • f.val),
    Lp.coeFn_smul (polynomialValue q a.val) f.val,Lp.coeFn_smul a.val f.val,
    biPolynomialBoundary_ae q,coordinate_ae] with t hmq hmz hsq hsz hcq hca hq hz
  rw [hsq,hsz]
  change ‖multiply (biPolynomialBoundary q) f.val t-(polynomialValue q a.val • f.val) t‖ ≤
    biPolynomialLipschitzBound q*‖multiply coordinate f.val t-(a.val • f.val) t‖
  rw [hmq,hmz,hcq,hca]
  change ‖biPolynomialBoundary q t*f.val t-polynomialValue q a.val*f.val t‖ ≤
    biPolynomialLipschitzBound q*‖coordinate t*f.val t-a.val*f.val t‖
  rw [hq,hz,← sub_mul,← sub_mul,norm_mul,norm_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (norm_polynomialValue_sub_le_on_unit q (by simp) a.property.le) (norm_nonneg (f.val t))

/-- The actual arbitrary-index bounded diagonal of polynomial values at disk nodes. -/
def polynomialNodeDiagonal {ι : Type} (q : BiPolynomial) (a : ι → Disk) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lp.mapCLM 2 (fun i => ContinuousLinearMap.lsmul ℂ ℂ (polynomialValue q (a i).val))
    (biPolynomialNormBound_nonneg q)
    (fun i => (ContinuousLinearMap.opNorm_lsmul_apply_le (𝕜 := ℂ) (E := ℂ) _).trans
      (norm_polynomialValue_le_on_unit q (a i).property.le))

@[simp] theorem polynomialNodeDiagonal_apply {ι : Type} (q : BiPolynomial) (a : ι → Disk)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    polynomialNodeDiagonal q a x i = polynomialValue q (a i).val*x i := rfl

theorem polynomialNodeDiagonal_isDiagonal {ι : Type} (q : BiPolynomial) (a : ι → Disk) :
    IndexedDiagonal (fun i => polynomialValue q (a i).val) (polynomialNodeDiagonal q a) := by
  classical
  intro i
  apply lp.ext
  funext j
  simp only [polynomialNodeDiagonal_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases h : j = i
  · subst j; rfl
  · simp [lp.single_apply,Pi.single_eq_of_ne h]

theorem polynomialNodeDiagonal_conjugate_basis {ι : Type} (u : BoundaryLInf) (q : BiPolynomial)
    (a : ι → Disk) (b : HilbertBasis ι ℂ (Model u)) (i : ι) :
    unitaryConjugate b.repr.symm (polynomialNodeDiagonal q a) (b i) = polynomialValue q (a i).val • b i := by
  classical
  change b.repr.symm (polynomialNodeDiagonal q a (b.repr (b i))) = _
  rw [b.repr_self,polynomialNodeDiagonal_isDiagonal,map_smul,b.repr_symm_single]

/-- The full pure-Blaschke polynomial model, proved by literal Lipschitz columns
rather than identifying mixed symbols with noncommuting polynomials in the compressed shift. -/
theorem polynomialBlaschkeModel :
    ∀ u : BoundaryLInf, IsInner u → Nonconstant u →
    ∀ ι : Type, ∀ a : ι → Disk, Countable ι → HasBlaschkeZeros u a → ∀ q : BiPolynomial,
      ∃ A : Model u →L[ℂ] Model u, RepresentsTTO u (polynomialSymbol q) A ∧
      ∃ U : lp (fun _ : ι => ℂ) 2 ≃ₗᵢ[ℂ] Model u,
      ∃ D : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
        IndexedDiagonal (fun i => polynomialValue q (a i).val) D ∧
      ∃ K : Model u →L[ℂ] Model u, Schatten 2 K ∧ A = unitaryConjugate U D+K := by
  intro u hu _hn ι a hc hz q
  obtain ⟨b,hb⟩ := exists_blaschke_model_basis_ambient u hu a hc hz
  let A := boundedSymbolOperator u (biPolynomialBoundary q)
  let K := A-unitaryConjugate b.repr.symm (polynomialNodeDiagonal q a)
  have hA : RepresentsTTO u (polynomialSymbol q) A := boundedSymbolOperator_represents u (biPolynomialBoundary q)
  refine ⟨A,hA,b.repr.symm,polynomialNodeDiagonal q a,polynomialNodeDiagonal_isDiagonal q a,K,?_,?_⟩
  · have hn (i : ι) : 0 ≤ 1-‖(a i).val‖^2 := by
      have hi : ‖(a i).val‖ < 1 := (a i).property
      nlinarith [norm_nonneg (a i).val]
    have hs : Summable (fun i => 1-‖(a i).val‖^2) :=
      (hz.1.mul_left 2).of_nonneg_of_le hn (fun i => by
        have hi : ‖(a i).val‖ < 1 := (a i).property
        nlinarith [norm_nonneg (a i).val])
    have hcol_bound (i : ι) : ‖K (b i)‖^2 ≤ biPolynomialLipschitzBound q^2*(1-‖(a i).val‖^2) := by
      change ‖(boundedSymbolOperator u (biPolynomialBoundary q)-
        unitaryConjugate b.repr.symm (polynomialNodeDiagonal q a)) (b i)‖^2 ≤ _
      rw [sub_apply,polynomialNodeDiagonal_conjugate_basis]
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (polynomial_column_norm_le u q (a i) (b i)) 2
      rwa [mul_pow,hb i] at h
    have hcol : Summable (fun i => ‖K (b i)‖^2) :=
      (hs.mul_left (biPolynomialLipschitzBound q^2)).of_nonneg_of_le (fun i => sq_nonneg _) hcol_bound
    apply (schatten_two_iff_columnEnergy K b).mpr
    unfold columnEnergy
    have he : (∑' i, ‖K (b i)‖ₑ^2) = ENNReal.ofReal (∑' i, ‖K (b i)‖^2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖K (b i)‖) hcol]
      apply tsum_congr
      intro i
      rw [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg (K (b i)))]
    rw [he]
    exact ENNReal.ofReal_lt_top
  · dsimp [K]
    abel

end TTO.Paper.Proved
