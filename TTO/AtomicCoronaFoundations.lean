/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SingleAtomConstruction
public import TTO.SchattenNormFoundations
public import Mathlib.RingTheory.Coprime.Lemmas

/-! Bounded analytic Bézout functions for finite families of distinct atomic singular factors.
This special construction does not assert the general corona theorem. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Actual functions on the disk which admit an analytic extension to a neighborhood
of each disk point and one uniform norm bound. All algebra operations are pointwise. -/
def boundedDiskAnalytic : Subalgebra ℂ (Disk → ℂ) where
  carrier := {f | ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F disk ∧
    (∀ z : Disk, F z.val = f z) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Disk, ‖f z‖ ≤ M}
  algebraMap_mem' c := ⟨fun _ => c,fun _ _ => analyticAt_const,fun _ => rfl,
    ‖c‖,norm_nonneg c,fun _ => le_rfl⟩
  add_mem' := by
    rintro f g ⟨F,hF,hFe,M,hM,hMb⟩ ⟨G,hG,hGe,N,hN,hNb⟩
    refine ⟨fun z => F z+G z,fun z hz => (hF z hz).add (hG z hz),?_,
      M+N,add_nonneg hM hN,?_⟩
    · intro z
      simp only [Pi.add_apply,hFe z,hGe z]
    · intro z
      exact (norm_add_le (f z) (g z)).trans (add_le_add (hMb z) (hNb z))
  mul_mem' := by
    rintro f g ⟨F,hF,hFe,M,hM,hMb⟩ ⟨G,hG,hGe,N,hN,hNb⟩
    refine ⟨fun z => F z*G z,fun z hz => (hF z hz).mul (hG z hz),?_,
      M*N,mul_nonneg hM hN,?_⟩
    · intro z
      simp only [Pi.mul_apply,hFe z,hGe z]
    · intro z
      rw [Pi.mul_apply,norm_mul]
      exact mul_le_mul (hMb z) (hNb z) (norm_nonneg _) hM

abbrev DiskBoundedAnalytic := ↥boundedDiskAnalytic

instance : CoeFun DiskBoundedAnalytic (fun _ => Disk → ℂ) := ⟨Subtype.val⟩

def diskAnalyticOfFunction (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z ∈ disk, ‖F z‖ ≤ M) : DiskBoundedAnalytic :=
  ⟨fun z => F z.val,F,hF,fun _ => rfl,M,hM,fun z => hb z.val z.property⟩

@[simp] theorem diskAnalyticOfFunction_apply (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z ∈ disk, ‖F z‖ ≤ M) (z : Disk) :
    diskAnalyticOfFunction F hF M hM hb z = F z.val := rfl

def diskAnalyticOfBoundary (u : BoundaryLInf) (hu : toL2 u ∈ hardy) : DiskBoundedAnalytic :=
  diskAnalyticOfFunction (innerValue u) (analyticOnNhd_analyticValue (toL2 u))
    ‖u‖ (norm_nonneg u) (fun z hz => norm_innerValue_le u hu ⟨z,hz⟩)

@[simp] theorem diskAnalyticOfBoundary_apply (u : BoundaryLInf) (hu : toL2 u ∈ hardy) (z : Disk) :
    diskAnalyticOfBoundary u hu z = innerValue u z.val := rfl

/-- The disk algebra here has actual native L∞ Hardy boundary representatives,
with precisely the same point evaluations. -/
theorem diskAnalytic_exists_boundary (f : DiskBoundedAnalytic) :
    ∃ a : BoundaryLInf, toL2 a ∈ hardy ∧ ∀ z : Disk, innerValue a z.val = f z := by
  obtain ⟨F,hF,hFe,M,_hM,hMb⟩ := f.property
  have hb : ∀ z ∈ disk, ‖F z‖ ≤ M := by
    intro z hz
    rw [hFe ⟨z,hz⟩]
    exact hMb ⟨z,hz⟩
  obtain ⟨a,ha,hv,_hae,_hn⟩ := exists_boundedAnalyticBoundary F hF M hb
  exact ⟨a,ha,fun z => (hv z.val z.property).trans (hFe z)⟩

/-- The pinned finite cofactor Bézout algebra applies in the actual bounded analytic
function subalgebra, so its coefficients retain both analyticity and boundedness. -/
theorem diskAnalytic_cofactor_bezout {m : ℕ} (hm : 0 < m) (u : Fin m → DiskBoundedAnalytic)
    (hcop : Pairwise (fun i j => IsCoprime (u i) (u j))) :
    ∃ a : Fin m → DiskBoundedAnalytic, (∑ j, a j*∏ k ∈ ({j}ᶜ : Finset (Fin m)), u k) = 1 := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  exact exists_sum_eq_one_iff_pairwise_coprime'.mpr hcop

def diskAnalyticEval (z : Disk) : DiskBoundedAnalytic →+* ℂ where
  toFun f := f z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem diskAnalyticEval_apply (z : Disk) (f : DiskBoundedAnalytic) :
    diskAnalyticEval z f = f z := rfl

/-- A uniformly nonvanishing actual bounded analytic disk function has a bounded
analytic inverse; this is ordinary analytic division, not a corona input. -/
def diskAnalyticInv (f : DiskBoundedAnalytic) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ z : Disk, ε ≤ ‖f z‖) : DiskBoundedAnalytic :=
  ⟨fun z => (f z)⁻¹,by
    obtain ⟨F,hF,hFe,_M,_hM,_hMb⟩ := f.property
    refine ⟨fun z => (F z)⁻¹,?_,?_,ε⁻¹,by positivity,?_⟩
    · intro z hz
      apply (hF z hz).inv
      have hn : 0 < ‖f ⟨z,hz⟩‖ := hε.trans_le (hf ⟨z,hz⟩)
      rw [hFe ⟨z,hz⟩]
      exact norm_pos_iff.mp hn
    · intro z
      exact congrArg (fun w : ℂ => w⁻¹) (hFe z)
    · intro z
      rw [norm_inv]
      exact inv_anti₀ hε (hf z)⟩

@[simp] theorem diskAnalyticInv_apply (f : DiskBoundedAnalytic) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ z : Disk, ε ≤ ‖f z‖) (z : Disk) :
    diskAnalyticInv f ε hε hf z = (f z)⁻¹ := rfl

theorem diskAnalyticInv_mul (f : DiskBoundedAnalytic) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ z : Disk, ε ≤ ‖f z‖) :
    diskAnalyticInv f ε hε hf * f = 1 := by
  apply Subtype.ext
  funext z
  change (f z)⁻¹ * f z = 1
  exact inv_mul_cancel₀ (norm_pos_iff.mp (hε.trans_le (hf z)))

def atomDiskAnalytic (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (ζ : Boundary) : DiskBoundedAnalytic :=
  diskAnalyticOfFunction (atomDiskFunction ℓ ζ) (analyticOnNhd_atomDiskFunction ℓ ζ) 1 zero_le_one
    (fun _ hz => norm_atomDiskFunction_le_one ℓ hℓ ζ hz)

@[simp] theorem atomDiskAnalytic_apply (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (ζ : Boundary) (z : Disk) :
    atomDiskAnalytic ℓ hℓ ζ z = atomDiskFunction ℓ ζ z.val := rfl


theorem atom_herglotz_norm_le_of_far (ζ : Boundary) (z : Disk)
    (d : ℝ) (hd : 0 < d) (hfar : d ≤ ‖fourier (T := 1) 1 ζ-z.val‖) :
    ‖(fourier (T := 1) 1 ζ+z.val)/(fourier (T := 1) 1 ζ-z.val)‖ ≤ 2/d := by
  have hz : ‖z.val‖ < 1 := z.property
  have hnum : ‖fourier (T := 1) 1 ζ+z.val‖ ≤ 2 := by
    have hn := norm_add_le (fourier (T := 1) 1 ζ) z.val
    have he : ‖fourier (T := 1) 1 ζ‖ = 1 := by simp
    rw [he] at hn
    linarith
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hd hfar)

theorem atomDiskFunction_one_sub_le_two (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (ζ : Boundary) (z : Disk) :
    ‖1-atomDiskFunction ℓ ζ z.val‖ ≤ 2 := by
  have h := norm_sub_le (1 : ℂ) (atomDiskFunction ℓ ζ z.val)
  rw [norm_one] at h
  linarith [norm_atomDiskFunction_le_one ℓ hℓ ζ z.property]

theorem atomDiskFunction_far_deviation (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (ζ : Boundary)
    (d : ℝ) (hd : 0 < d) (hsmall : ℓ ≤ d/32) (z : Disk)
    (hfar : d/2 ≤ ‖fourier (T := 1) 1 ζ-z.val‖) :
    ‖1-atomDiskFunction ℓ ζ z.val‖ ≤ 1/4 := by
  have hH := atom_herglotz_norm_le_of_far ζ z (d/2) (by positivity) hfar
  have hx : ‖-(ℓ : ℂ)*(fourier (T := 1) 1 ζ+z.val)/(fourier (T := 1) 1 ζ-z.val)‖ ≤ 1/8 := by
    rw [mul_div_assoc,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hℓ]
    calc
      _ ≤ ℓ*(2/(d/2)) := mul_le_mul_of_nonneg_left hH hℓ
      _ ≤ (d/32)*(2/(d/2)) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = 1/8 := by field_simp; ring
  rw [norm_sub_rev,atomDiskFunction]
  exact (Complex.norm_exp_sub_one_le (hx.trans (by norm_num))).trans (by linarith)

theorem atom_small_roots_deviation_product
    (ℓ r : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (ζ η : Boundary)
    (d : ℝ) (hd : 0 < d)
    (hsep : d ≤ ‖fourier (T := 1) 1 ζ-fourier (T := 1) 1 η‖)
    (hℓs : ℓ ≤ d/32) (hrs : r ≤ d/32) (z : Disk) :
    ‖(1-atomDiskFunction ℓ ζ z.val)*(1-atomDiskFunction r η z.val)‖ ≤ 1/2 := by
  have hfar : d/2 ≤ ‖fourier (T := 1) 1 ζ-z.val‖ ∨
      d/2 ≤ ‖fourier (T := 1) 1 η-z.val‖ := by
    have ht : ‖fourier (T := 1) 1 ζ-fourier (T := 1) 1 η‖ ≤
        ‖fourier (T := 1) 1 ζ-z.val‖+‖fourier (T := 1) 1 η-z.val‖ := by
      calc
        _ = ‖(fourier (T := 1) 1 ζ-z.val)+(z.val-fourier (T := 1) 1 η)‖ := by congr 1; ring
        _ ≤ ‖fourier (T := 1) 1 ζ-z.val‖+‖z.val-fourier (T := 1) 1 η‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev z.val (fourier (T := 1) 1 η)]
    by_contra h
    push Not at h
    linarith
  rw [norm_mul]
  rcases hfar with h | h
  · calc
      _ ≤ (1/4 : ℝ)*2 := mul_le_mul (atomDiskFunction_far_deviation ℓ hℓ ζ d hd hℓs z h)
        (atomDiskFunction_one_sub_le_two r hr η z) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · calc
      _ ≤ 2*(1/4 : ℝ) := mul_le_mul (atomDiskFunction_one_sub_le_two ℓ hℓ ζ z)
        (atomDiskFunction_far_deviation r hr η d hd hrs z h) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num

/-- Two sufficiently small canonical atomic roots admit an explicit bounded analytic
Bézout identity by ordinary inversion of one uniformly nonvanishing denominator. -/
theorem atom_small_roots_isCoprime
    (ℓ r : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (ζ η : Boundary)
    (d : ℝ) (hd : 0 < d)
    (hsep : d ≤ ‖fourier (T := 1) 1 ζ-fourier (T := 1) 1 η‖)
    (hℓs : ℓ ≤ d/32) (hrs : r ≤ d/32) :
    IsCoprime (atomDiskAnalytic ℓ hℓ ζ) (atomDiskAnalytic r hr η) := by
  let f := atomDiskAnalytic ℓ hℓ ζ
  let g := atomDiskAnalytic r hr η
  let D := f+g-f*g
  have hD : ∀ z : Disk, (1/2 : ℝ) ≤ ‖D z‖ := by
    intro z
    have hp := atom_small_roots_deviation_product ℓ r hℓ hr ζ η d hd hsep hℓs hrs z
    have he : D z = 1-(1-atomDiskFunction ℓ ζ z.val)*(1-atomDiskFunction r η z.val) := by
      change atomDiskFunction ℓ ζ z.val+atomDiskFunction r η z.val-
        atomDiskFunction ℓ ζ z.val*atomDiskFunction r η z.val = _
      ring
    have ht := norm_add_le
      (1-(1-atomDiskFunction ℓ ζ z.val)*(1-atomDiskFunction r η z.val))
      ((1-atomDiskFunction ℓ ζ z.val)*(1-atomDiskFunction r η z.val))
    rw [sub_add_cancel,norm_one,← he] at ht
    linarith
  let Q := diskAnalyticInv D (1/2) (by norm_num) hD
  refine ⟨Q*(1-g),Q,?_⟩
  calc
    Q*(1-g)*f+Q*g = Q*D := by dsimp [D]; ring
    _ = 1 := diskAnalyticInv_mul D (1/2) (by norm_num) hD


theorem exists_nat_atom_root_small (ℓ d : ℝ) (hd : 0 < d) :
    ∃ N : ℕ, 0 < N ∧ ℓ/(N : ℝ) ≤ d/32 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (32*ℓ/d)
  refine ⟨N+1,Nat.succ_pos N,?_⟩
  have hNp : 0 < ((N+1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  apply (div_le_iff₀ hNp).mpr
  have hm := (div_lt_iff₀ hd).mp hN
  push_cast
  nlinarith

theorem atomDiskFunction_root_pow (ℓ : ℝ) (N : ℕ) (hN : 0 < N) (ζ : Boundary) (z : ℂ) :
    (atomDiskFunction (ℓ/(N : ℝ)) ζ z)^N = atomDiskFunction ℓ ζ z := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hc : (N : ℂ)*(-((ℓ/(N : ℝ) : ℝ) : ℂ)) = -(ℓ : ℂ) := by
    push_cast
    field_simp
  unfold atomDiskFunction
  simp only [mul_div_assoc]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [← mul_assoc,hc]

/-- Pairwise coprimality for the actual inner disk functions of two distinct single
atoms, obtained by small canonical integer roots and finite ring powers. -/
theorem singleAtom_pair_isCoprime (u v : BoundaryLInf) (hu : IsInner u) (hv : IsInner v)
    (ζ η : Boundary) (hζη : ζ ≠ η) (hU : SingleAtom u ζ) (hV : SingleAtom v η) :
    IsCoprime (diskAnalyticOfBoundary u hu.1) (diskAnalyticOfBoundary v hv.1) := by
  classical
  obtain ⟨ℓ,hℓ,α,hα,hvalU⟩ := hU
  obtain ⟨r,hr,β,hβ,hvalV⟩ := hV
  let d := ‖fourier (T := 1) 1 ζ-fourier (T := 1) 1 η‖
  have hd : 0 < d := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (fun h => hζη (circleCharacter_injective h))
  obtain ⟨N,hN,hNs⟩ := exists_nat_atom_root_small ℓ d hd
  obtain ⟨M,hM,hMs⟩ := exists_nat_atom_root_small r d hd
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hMr : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let f := atomDiskAnalytic (ℓ/(N : ℝ)) (div_nonneg hℓ.le hNr.le) ζ
  let g := atomDiskAnalytic (r/(M : ℝ)) (div_nonneg hr.le hMr.le) η
  have hfg : IsCoprime f g :=
    atom_small_roots_isCoprime _ _ (div_nonneg hℓ.le hNr.le) (div_nonneg hr.le hMr.le)
      ζ η d hd le_rfl hNs hMs
  obtain ⟨A,B,hAB⟩ := hfg.pow (m := N) (n := M)
  let a : DiskBoundedAnalytic := algebraMap ℂ DiskBoundedAnalytic α
  let b : DiskBoundedAnalytic := algebraMap ℂ DiskBoundedAnalytic β
  let ai : DiskBoundedAnalytic := algebraMap ℂ DiskBoundedAnalytic α⁻¹
  let bi : DiskBoundedAnalytic := algebraMap ℂ DiskBoundedAnalytic β⁻¹
  have hα0 : α ≠ 0 := by intro h; rw [h,norm_zero] at hα; norm_num at hα
  have hβ0 : β ≠ 0 := by intro h; rw [h,norm_zero] at hβ; norm_num at hβ
  have hai : ai*a = 1 := by
    dsimp [ai,a]
    rw [← map_mul,inv_mul_cancel₀ hα0,map_one]
  have hbi : bi*b = 1 := by
    dsimp [bi,b]
    rw [← map_mul,inv_mul_cancel₀ hβ0,map_one]
  have hUpow : diskAnalyticOfBoundary u hu.1 = a*f^N := by
    apply Subtype.ext
    funext z
    change innerValue u z.val = α*(atomDiskFunction (ℓ/(N : ℝ)) ζ z.val)^N
    rw [atomDiskFunction_root_pow ℓ N hN]
    exact hvalU z.val z.property
  have hVpow : diskAnalyticOfBoundary v hv.1 = b*g^M := by
    apply Subtype.ext
    funext z
    change innerValue v z.val = β*(atomDiskFunction (r/(M : ℝ)) η z.val)^M
    rw [atomDiskFunction_root_pow r M hM]
    exact hvalV z.val z.property
  refine ⟨ai*A,bi*B,?_⟩
  rw [hUpow,hVpow]
  calc
    ai*A*(a*f^N)+bi*B*(b*g^M) = (ai*a)*(A*f^N)+(bi*b)*(B*g^M) := by ring
    _ = 1 := by rw [hai,hbi,one_mul,one_mul,hAB]


theorem innerValue_constLInf (c : ℂ) (z : Disk) : innerValue (constLInf c) z.val = c := by
  change analyticValue (toL2 (constLInf c)) z.val = c
  rw [toL2_constLInf]
  rw [constL2_fourier,analyticValue_smul c (fourierBasis (T := 1) 0) z.property]
  have hz : analyticValue (fourierBasis (T := 1) 0) z.val = 1 := by
    simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z.val
  rw [hz,mul_one]

theorem innerValue_innerListProduct (l : List BoundaryLInf)
    (hl : ∀ a ∈ l, IsInner a) (z : Disk) :
    innerValue (l.foldr multiplyInf (constLInf 1)) z.val =
      (l.map (fun a => innerValue a z.val)).prod := by
  induction l with
  | nil => exact innerValue_constLInf 1 z
  | cons a l ih =>
    have ha : IsInner a := hl a (by simp)
    have ht : ∀ b ∈ l, IsInner b := fun b hb => hl b (by simp [hb])
    change innerValue (multiplyInf a (l.foldr multiplyInf (constLInf 1))) z.val =
      innerValue a z.val*(l.map (fun b => innerValue b z.val)).prod
    rw [innerValue_multiplyInf _ _ ha.1 (isInner_listProduct l ht).1 z,ih ht]

theorem innerValue_cofactor_product {m : ℕ} (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j)) (j : Fin m) (z : Disk) :
    innerValue (cofactor u j) z.val =
      ∏ k ∈ ({j}ᶜ : Finset (Fin m)), innerValue (u k) z.val := by
  classical
  let v : Fin m → BoundaryLInf := fun k => if k = j then constLInf 1 else u k
  have hv : ∀ k, IsInner (v k) := by
    intro k
    dsimp [v]
    split_ifs
    · exact isInner_constLInf_one
    · exact hu k
  have he := innerValue_innerListProduct (List.ofFn v) (by
    intro a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact hv k) z
  change innerValue ((List.ofFn v).foldr multiplyInf (constLInf 1)) z.val = _
  rw [he]
  simp only [List.map_ofFn,List.prod_ofFn,v,Function.comp_apply]
  have hvv (k : Fin m) : innerValue (if k = j then constLInf 1 else u k) z.val =
      if k = j then 1 else innerValue (u k) z.val := by
    split_ifs
    · exact innerValue_constLInf 1 z
    · rfl
  simp_rw [hvv]
  rw [Finset.prod_ite]
  simp
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext k
  simp

/-- Actual native bounded analytic cofactor Bézout witnesses for every finite
positive-arity family of distinct single-atom inner factors. -/
theorem finiteAtom_bezout (m : ℕ) (hm : 0 < m) (u : Fin m → BoundaryLInf)
    (ζ : Fin m → Boundary) (hζ : Function.Injective ζ)
    (hu : ∀ j, IsInner (u j) ∧ SingleAtom (u j) (ζ j)) :
    ∃ a : Fin m → BoundaryLInf, Bezout u a := by
  classical
  let U : Fin m → DiskBoundedAnalytic := fun j => diskAnalyticOfBoundary (u j) (hu j).1.1
  have hcop : Pairwise (fun i j => IsCoprime (U i) (U j)) := by
    intro i j hij
    exact singleAtom_pair_isCoprime (u i) (u j) (hu i).1 (hu j).1 (ζ i) (ζ j)
      (fun h => hij (hζ h)) (hu i).2 (hu j).2
  obtain ⟨A,hA⟩ := diskAnalytic_cofactor_bezout hm U hcop
  choose a ha hav using fun j => diskAnalytic_exists_boundary (A j)
  refine ⟨a,ha,?_⟩
  intro z hz
  let w : Disk := ⟨z,hz⟩
  have he := congrArg (diskAnalyticEval w) hA
  simp only [map_sum,map_mul,map_prod,map_one,diskAnalyticEval_apply] at he
  change (∑ j, innerValue (a j) w.val*innerValue (cofactor u j) w.val) = 1
  calc
    _ = ∑ j, A j w * ∏ k ∈ ({j}ᶜ : Finset (Fin m)), U k w := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hav j w,innerValue_cofactor_product u (fun k => (hu k).1) j w]
      rfl
    _ = 1 := he


/-- The already proved literal gluing model supplies the complete idempotent structure
for one fixed inner family as soon as its actual Bézout witnesses are available. -/
theorem coronaStructure_at_bezout {m : ℕ} (hm : 0 < m) (u : Fin m → BoundaryLInf)
    (hu : ∀ j, IsInner (u j) ∧ Nonconstant (u j))
    (hb : ∃ a : Fin m → BoundaryLInf, Bezout u a) :
    IsInner (finiteProduct u) ∧ Nonconstant (finiteProduct u) ∧
      (∃ a : Fin m → BoundaryLInf, Bezout u a) ∧
      ∀ a, Bezout u a → ∃ E, RepresentsIdempotents u a E ∧
        ComplementaryIdempotents E ∧ IdempotentRanges u E ∧
        ∀ a' E', Bezout u a' → RepresentsIdempotents u a' E' → E' = E := by
  let hi : ∀ j, IsInner (u j) := fun j => (hu j).1
  refine ⟨isInner_finiteProduct u hi,nonconstant_finiteProduct hm u hu,hb,?_⟩
  intro a ha
  let W := gluingEquiv u a hi ha
  let d := gluingGraphData u a hi ha
  let E := coordinateResolution W
  have he : RepresentsIdempotents u a E := d.coordinate_symbol a ha
  refine ⟨E,he,⟨coordinateResolution_sum W,coordinateResolution_idempotent W,
    coordinateResolution_disjoint W⟩,?_,?_⟩
  · intro j
    change (coordinateResolution W j).toLinearMap.range.map (model (finiteProduct u)).subtype = _
    rw [coordinateResolution_range W j]
    ext f
    constructor
    · rintro ⟨x,⟨g,rfl⟩,rfl⟩
      exact ⟨g,(d.single_formula j g).symm⟩
    · rintro ⟨g,rfl⟩
      exact ⟨W (finiteSingle (fun i => Model (u i)) j g),⟨g,rfl⟩,d.single_formula j g⟩
  · intro a' E' ha' hE'
    exact gluing_idempotents_eq u a hi ha a' ha' E' hE'


set_option maxHeartbeats 400000 in
/-- Full T6 with the distinct-atom corona functions constructed above.
The sole remaining proof parameter is the paper's genuinely open uniform one-atom
splitting lemma; it is not an approved external assumption or an unconditional proof. -/
theorem finiteAtomClassification_of_oneAtom (hOne : OneAtomObligation) : FiniteAtomConclusion := by
  classical
  let hC : CoreLaws := coreLaws
  let hI : IdealLaws := idealLaws
  let hD : DistinctAtomCoronaObligation := distinctAtomCorona
  let hComp : AtomCompressionObligation := atomCompression
  let hV : VectorGluingObligation := vectorGluing
  let hScalar : ScalarCompactObligation := scalarCompact
  let hDim : SingleAtomDimensionObligation := singleAtomDimension
  let hAng : AngularUniquenessObligation := angularUniqueness
  let hN : SchattenNormLaws := schattenNormLaws
  intro m hm u ζ hζ hu
  have hui : ∀ j, IsInner (u j) ∧ Nonconstant (u j) := fun j => ⟨(hu j).1, (hu j).2.1⟩
  have hcoro := hD m hm u ζ hζ (fun j => ⟨(hu j).1, (hu j).2.2⟩)
  obtain ⟨hut, hnt, ha0, hstruct⟩ := coronaStructure_at_bezout hm u hui
    (finiteAtom_bezout m hm u ζ hζ (fun j => ⟨(hu j).1, (hu j).2.2⟩))
  refine ⟨hut, hnt, ha0, hstruct, ?_⟩
  intro p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨τ, hτ, hone⟩ := hOne p hp
  obtain ⟨K, hK, hglue⟩ := hV m hm u hui hcoro p hp0
  refine ⟨1 + 2 * K * τ, by positivity, ?_⟩
  intro a ha E hE φ ψ
  obtain ⟨E₀, hE₀, he₀, hr₀, hind⟩ := hstruct a ha
  have heq := hind a E ha hE
  subst E
  obtain ⟨hvec, hsplit⟩ := hglue a ha E₀ hE₀
  have hdim : ∀ j, ¬FiniteDimensional ℂ (Model (u j)) :=
    fun j => hDim (u j) (hu j).1 (hu j).2.1 (ζ j) (hu j).2.2
  have localData : ∀ A : Model (finiteProduct u) →L[ℂ] Model (finiteProduct u),
      RepresentsTTO (finiteProduct u) (splitSymbol φ.val ψ.val) A → Schatten p A →
      ∃ c : Fin m → ℂ, ∀ j, ∃ X Y : Model (u j) →L[ℂ] Model (u j),
        RepresentsTTO (u j) φ.val X ∧ RepresentsTTO (u j) (star ψ.val) Y ∧
        Schatten p (X - c j • ContinuousLinearMap.id ℂ _) ∧
        Schatten p (Y + c j • ContinuousLinearMap.id ℂ _) ∧
        schattenNorm p (X - c j • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
        AngularLimit (analyticValue φ.val) (ζ j) (c j) ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj (c j)) := by
    intro A he hs
    have hx : ∀ j, ∃ c : ℂ, ∃ X Y : Model (u j) →L[ℂ] Model (u j),
        RepresentsTTO (u j) φ.val X ∧ RepresentsTTO (u j) (star ψ.val) Y ∧
        Schatten p (X - c • ContinuousLinearMap.id ℂ _) ∧
        Schatten p (Y + c • ContinuousLinearMap.id ℂ _) ∧
        schattenNorm p (X - c • ContinuousLinearMap.id ℂ _) ≤ τ * schattenNorm p A ∧
        AngularLimit (analyticValue φ.val) (ζ j) c ∧
        AngularLimit (analyticValue ψ.val) (ζ j) (-conj c) := by
      intro j
      obtain ⟨Aj, hj, hsj, hnj⟩ := hComp m hm u ζ hζ hu φ ψ p hp0 A he hs j
      obtain ⟨c, X, Y, hX, hY, hsX, hsY, hnX, _, haX, haY⟩ :=
        hone (u j) (hu j).1 (hu j).2.1 (ζ j) (hu j).2.2 φ ψ Aj hj hsj
      exact ⟨c, X, Y, hX, hY, hsX, hsY,
        hnX.trans (mul_le_mul_of_nonneg_left hnj hτ.le), haX, haY⟩
    choose c X Y hX hY hsX hsY hnX haX haY using hx
    exact ⟨c, fun j => ⟨X j, Y j, hX j, hY j, hsX j, hsY j, hnX j, haX j, haY j⟩⟩
  have hlocal (c : Fin m → ℂ) :
      Remainders p (finiteProduct u) φ.val ψ.val E₀ c →
      ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) :=
    fun h => (hvec φ c).1.mp h.1
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨A, he, hs⟩
      obtain ⟨c, hd⟩ := localData A he hs
      have hl : ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) := by
        intro j
        obtain ⟨X, Y, hx, _, hsx, _⟩ := hd j
        exact ⟨X, hx, hsx⟩
      exact ⟨c, analytic_remainder_pair hC hI _ hut hnt p _ _ A _ he hs ((hvec φ c).1.mpr hl)⟩
    · rintro ⟨c, hc⟩
      exact hasSchatten_of_remainders hC hI p _ _ _ E₀ c hc
  · intro c d hc hd
    funext j
    exact scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1 (hdim j)
      φ.val p (c j) (d j) (hlocal c hc j) (hlocal d hd j)
  · intro A he hs
    obtain ⟨c₀, hd⟩ := localData A he hs
    have hl₀ : ∀ j, AnalyticRemainder p (u j) φ.val (c₀ j • ContinuousLinearMap.id ℂ _) := by
      intro j
      obtain ⟨X, Y, hx, _, hsx, _⟩ := hd j
      exact ⟨X, hx, hsx⟩
    have localAngle (j : Fin m) (c : ℂ) :
        AnalyticRemainder p (u j) φ.val (c • ContinuousLinearMap.id ℂ _) ↔
        AngularLimit (analyticValue φ.val) (ζ j) c := by
      obtain ⟨X, Y, hx, hy, hsx, hsy, hnX, haX, haY⟩ := hd j
      constructor
      · intro hc
        have hcc := scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1
          (hdim j) φ.val p c (c₀ j) hc (hl₀ j)
        exact hcc.symm ▸ haX
      · intro hc
        have hcc := hAng _ (ζ j) c (c₀ j) hc haX
        exact hcc.symm ▸ hl₀ j
    have hpair (c : Fin m → ℂ) : Remainders p (finiteProduct u) φ.val ψ.val E₀ c ↔
        ∀ j, AnalyticRemainder p (u j) φ.val (c j • ContinuousLinearMap.id ℂ _) := by
      constructor
      · exact hlocal c
      · intro hl
        exact analytic_remainder_pair hC hI _ hut hnt p _ _ A _ he hs ((hvec φ c).1.mpr hl)
    have hscalar (c : ℂ) :
        (AnalyticRemainder p (finiteProduct u) φ.val (c • ContinuousLinearMap.id ℂ _) ∧
          CoanalyticRemainder p (finiteProduct u) ψ.val (c • ContinuousLinearMap.id ℂ _)) ↔
        ∀ j, AngularLimit (analyticValue φ.val) (ζ j) c := by
      have hc := constant_correction E₀ he₀ c
      constructor
      · intro hrem
        have hrem' : Remainders p (finiteProduct u) φ.val ψ.val E₀ (fun _ => c) := by
          simpa only [Remainders, hc] using hrem
        exact fun j => (localAngle j c).mp ((hpair _).mp hrem' j)
      · intro hang
        have hl := fun j => (localAngle j c).mpr (hang j)
        have hrem' := (hpair (fun _ => c)).mpr hl
        simpa only [Remainders, hc] using hrem'
    refine ⟨hpair, ?_, ?_, hscalar, ?_⟩
    · intro c hc
      have hcc : ∀ j, c j = c₀ j := fun j =>
        scalar_remainder_unique hC hI hScalar (u j) (hu j).1 (hu j).2.1 (hdim j)
          φ.val p (c j) (c₀ j) ((hpair c).mp hc j) (hl₀ j)
      constructor
      · intro j
        obtain ⟨X, Y, hx, hy, hsx, hsy, hnX, haX, haY⟩ := hd j
        exact ⟨(hcc j).symm ▸ haX, (hcc j).symm ▸ haY⟩
      · intro X Y hx hy hsx hsy
        have hB : 0 ≤ τ * schattenNorm p A := mul_nonneg hτ.le (schattenNorm_nonneg p A)
        have hxbound : schattenNorm p (X - correction E₀ c) ≤ K * (τ * schattenNorm p A) := by
          apply (hvec φ c).2 (τ * schattenNorm p A) hB X hx
          intro j
          obtain ⟨Xj, Yj, hxj, hyj, hsxj, hsyj, hnxj, haj, hbj⟩ := hd j
          exact ⟨Xj, hxj, (hcc j).symm ▸ hsxj, (hcc j).symm ▸ hnxj⟩
        have hsum : A = X + Y := hC.unique _ hut hnt _ A (X + Y) he (hC.add _ _ _ X Y hx hy)
        have hyalg : Y + correction E₀ c = A - (X - correction E₀ c) := by rw [hsum]; abel
        have hybound : schattenNorm p (Y + correction E₀ c) ≤
            schattenNorm p A + schattenNorm p (X - correction E₀ c) := by
          rw [hyalg]
          exact hN.sub_bound p A _ hp.le hs hsx
        nlinarith only [hxbound, hybound]
    · exact (hsplit φ ψ A he hs).trans ⟨by
        rintro ⟨c, hc⟩
        exact ⟨c, fun j => (localAngle j c).mp (hc j)⟩, by
        rintro ⟨c, hc⟩
        exact ⟨c, fun j => (localAngle j c).mpr (hc j)⟩⟩
    · have h0 : (0 : ℂ) • ContinuousLinearMap.id ℂ (Model (finiteProduct u)) = 0 := by
        ext x
        simp
      have hp0 := hscalar 0
      rw [h0] at hp0
      exact (zero_remainders p (finiteProduct u) φ.val ψ.val).symm.trans hp0


end TTO.Paper.Proved
