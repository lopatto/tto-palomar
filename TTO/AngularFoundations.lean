/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.AtomicFoundations

/-! Nontrivial angular approaches and the actual single-atom measure/dimension facts. -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

/-- A radial approach belongs to every fixed Stolz region of aperture M>1. -/
theorem radial_tendsto_stolz (ζ : Boundary) (M : ℝ) (hM : 1 < M) :
    Tendsto (fun r : ℝ => (r : ℂ)*fourier (T := 1) 1 ζ) (𝓝[<] (1 : ℝ)) (StolzFilter ζ M) := by
  let e := fourier (T := 1) 1 ζ
  have he : ‖e‖ = 1 := by simp only [e,fourier_apply,Circle.norm_coe]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · have ht := (Complex.continuous_ofReal.mul_const e).tendsto (1 : ℝ)
    simpa only [Complex.ofReal_one,one_mul] using ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hn : ‖(r : ℂ)*e‖ = r := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1.le,he,mul_one]
    have hd : ‖(r : ℂ)*e-e‖ = 1-r := by
      rw [← sub_one_mul,norm_mul,he,mul_one,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_of_nonpos (sub_neg.mpr hr.2).le]
      ring
    refine ⟨?_,?_⟩
    · change ‖(r : ℂ)*e‖ < 1
      rw [hn]
      exact hr.2
    · change ‖(r : ℂ)*e-e‖ ≤ M*(1-‖(r : ℂ)*e‖)
      rw [hn,hd]
      nlinarith [mul_nonneg (sub_nonneg.mpr hM.le) (sub_pos.mpr hr.2).le]

theorem stolz_neBot (ζ : Boundary) (M : ℝ) (hM : 1 < M) : NeBot (StolzFilter ζ M) :=
  (radial_tendsto_stolz ζ M hM).neBot

/-- Ordinary angular limit uniqueness, with the nontrivial approach filter proved. -/
theorem angularUniqueness : AngularUniquenessObligation := by
  intro f ζ c d hc hd
  let : NeBot (StolzFilter ζ 2) := stolz_neBot ζ 2 (by norm_num)
  have hc' : Tendsto f (StolzFilter ζ 2) (𝓝 c) := hc 2 (by norm_num)
  have hd' : Tendsto f (StolzFilter ζ 2) (𝓝 d) := hd 2 (by norm_num)
  exact tendsto_nhds_unique hc' hd'

theorem coordinateBoundary : CoordinateBoundaryObligation := by
  refine ⟨?_,fun ζ M _hM => ?_⟩
  · change toL2 (mode 1) ∈ hardy
    rw [toL2_mode]
    exact fourierBasis_mem_hardy 1
  · have he : analyticValue (toL2 coordinate) = fun z => z := by
      funext z
      change analyticValue (toL2 (mode 1)) z = z
      rw [toL2_mode]
      simpa only [Nat.cast_one,pow_one] using analyticValue_fourierBasis 1 z
    rw [he]
    exact nhdsWithin_le_nhds

/-- The actual point mass and unimodular phase give the single-atom canonical measure. -/
theorem singleAtomMeasure : SingleAtomMeasureObligation := by
  intro u _hu ζ hs
  obtain ⟨ℓ,hℓ,α,hα,hval⟩ := hs
  let μ : Measure Boundary := ENNReal.ofReal ℓ • Measure.dirac ζ
  have hfinite : finiteSingular μ := by
    refine ⟨?_,?_⟩
    · simp only [μ,Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ ζ)]
      change ENNReal.ofReal ℓ*1 < ∞
      rw [mul_one]
      exact ENNReal.ofReal_lt_top
    · exact Measure.MutuallySingular.smul (ENNReal.ofReal ℓ) (mutuallySingular_dirac ζ circleMeasure)
  refine ⟨μ,⟨hfinite,fun _ => none,?_,α,hα,?_⟩,?_⟩
  · simp only [Option.elim_none,summable_zero]
  · intro z hz
    rw [hval z hz]
    simp only [Option.elim_none,tprod_one,mul_one]
    congr 1
    unfold singularInnerValue
    change Complex.exp (-(ℓ : ℂ)*(fourier (T := 1) 1 ζ+z)/(fourier (T := 1) 1 ζ-z)) =
      Complex.exp (-((1 : ℝ) : ℂ)*(∫ t,
        (fourier (T := 1) 1 t+z)/(fourier (T := 1) 1 t-z) ∂(ENNReal.ofReal ℓ • Measure.dirac ζ)))
    rw [integral_smul_measure,integral_dirac]
    simp only [ENNReal.toReal_ofReal hℓ.le,Complex.ofReal_one]
    rw [← Complex.coe_smul]
    congr 1
    change -(ℓ : ℂ)*(fourier (T := 1) 1 ζ+z)/(fourier (T := 1) 1 ζ-z) =
      -(1 : ℂ)*((ℓ : ℂ)*((fourier (T := 1) 1 ζ+z)/(fourier (T := 1) 1 ζ-z)))
    ring
  · simp only [μ,Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_singleton ζ)]
    change 0 < ENNReal.ofReal ℓ*1
    rw [mul_one]
    exact ENNReal.ofReal_pos.mpr hℓ

/-- L6 rules out finite dimensionality at an actual positive single atom. -/
theorem singleAtomDimension : SingleAtomDimensionObligation := by
  intro u hu hn ζ hs hdim
  let : FiniteDimensional ℂ (Model u) := hdim
  obtain ⟨μ,hμ,hζ⟩ := singleAtomMeasure u hu ζ hs
  let φ : Hardy := ⟨constL2 1,constantCoreLaws.hardy 1⟩
  have hrep : RepresentsTTO u φ.val (ContinuousLinearMap.id ℂ (Model u)) := by
    simpa only [one_smul] using constantCoreLaws.represents u 1
  have hcompact : IsCompactOperator (ContinuousLinearMap.id ℂ (Model u)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have hzero := compactScalarAngularLimitTheorem u hu hn μ hμ ζ hζ φ 0
    ⟨ContinuousLinearMap.id ℂ (Model u),hrep,by
      have he : ContinuousLinearMap.id ℂ (Model u)-(0 : ℂ) • ContinuousLinearMap.id ℂ (Model u) =
          ContinuousLinearMap.id ℂ (Model u) := by ext f; simp
      rw [he]
      exact hcompact⟩
  have hval : analyticValue φ.val = fun _ => (1 : ℂ) := by
    funext z
    change analyticValue (constL2 1) z = 1
    rw [constL2_fourier,one_smul]
    simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z
  have hone : AngularLimit (analyticValue φ.val) ζ 1 := by
    rw [hval]
    exact fun _ _ => tendsto_const_nhds
  have hbad : (0 : ℂ) = 1 := angularUniqueness _ ζ 0 1 hzero hone
  norm_num at hbad


theorem innerValue_listProduct (l : List BoundaryLInf) (hl : ∀ a ∈ l, IsInner a) (z : Disk) :
    innerValue (l.foldr multiplyInf (constLInf 1)) z.val = (l.map (fun a => innerValue a z.val)).prod := by
  induction l with
  | nil =>
    change analyticValue (toL2 (constLInf 1)) z.val = 1
    rw [toL2_constLInf,constL2_fourier,one_smul]
    simpa only [Nat.cast_zero,pow_zero] using analyticValue_fourierBasis 0 z.val
  | cons a l ih =>
    have htail : ∀ b ∈ l, IsInner b := fun b hb => hl b (List.mem_cons_of_mem a hb)
    simp only [List.foldr_cons,List.map_cons,List.prod_cons]
    rw [innerValue_multiplyInf a _ (hl a (List.mem_cons_self)).1 (isInner_listProduct l htail).1 z,ih htail]

theorem innerValue_finiteProduct {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ i, IsInner (u i)) (z : Disk) :
    innerValue (finiteProduct u) z.val = ∏ i, innerValue (u i) z.val := by
  have h := innerValue_listProduct (List.ofFn u) (fun a ha => by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hu i) z
  simpa only [finiteProduct,List.map_ofFn,List.prod_ofFn,Function.comp_apply] using h

theorem innerValue_cofactor {m : ℕ} (u : Fin m → BoundaryLInf) (hu : ∀ i, IsInner (u i))
    (j : Fin m) (z : Disk) : innerValue (cofactor u j) z.val = ∏ i, if i=j then 1 else innerValue (u i) z.val := by
  classical
  unfold cofactor
  rw [innerValue_finiteProduct _ (fun i => by split_ifs; exact isInner_constLInf_one; exact hu i)]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · change innerValue (finiteProduct (fun _ : Fin 0 => constLInf 1)) z.val = 1
    rw [innerValue_finiteProduct _ (fun _ => isInner_constLInf_one)]
    exact Finset.prod_empty
  · rfl

theorem singleAtom_norm_formula (u : BoundaryLInf) (ζ : Boundary) (ℓ : ℝ) (α : ℂ) (hα : ‖α‖ = 1)
    (hf : ∀ z ∈ disk, innerValue u z = α*Complex.exp (-(ℓ : ℂ)*
      (fourier (T := 1) 1 ζ+z)/(fourier (T := 1) 1 ζ-z))) (z : Disk) :
    ‖innerValue u z.val‖ = Real.exp (-ℓ*atomicPoissonKernel z.val ζ) := by
  rw [hf z.val z.property,norm_mul,hα,one_mul,Complex.norm_exp]
  have he : -(ℓ : ℂ)*(fourier (T := 1) 1 ζ+z.val)/(fourier (T := 1) 1 ζ-z.val) =
      -(ℓ : ℂ)*((fourier (T := 1) 1 ζ+z.val)/(fourier (T := 1) 1 ζ-z.val)) := by ring
  rw [he]
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    neg_zero,zero_mul,sub_zero]
  rw [herglotz_re z.val _ (by simp only [fourier_apply,Circle.norm_coe])]
  rfl

/-- Distinct boundary atoms give the manuscript's actual uniform cofactor corona lower bound. -/
theorem distinctAtomCorona : DistinctAtomCoronaObligation := by
  classical
  intro m hm u ζ hζ hu
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  choose ℓ hℓ α hα hval using (fun i => (hu i).2)
  let e := fun i => fourier (T := 1) 1 (ζ i)
  have hei : Function.Injective e := by
    intro i j he
    apply hζ
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.coe_injective
    simpa only [e,fourier_one] using he
  let d : Fin m × Fin m → ℝ := fun p => if p.1=p.2 then 1 else ‖e p.1-e p.2‖
  have hd : ∀ p, 0 < d p := by
    intro p
    dsimp only [d]
    split_ifs with hp
    · exact zero_lt_one
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hp (hei h)))
  obtain ⟨p,hmin⟩ := Finite.exists_min d
  let r := d p/2
  have hr : 0 < r := div_pos (hd p) (by norm_num)
  have hsep (i j : Fin m) (hij : i≠j) : 2*r ≤ ‖e i-e j‖ := by
    have h := hmin (i,j)
    simp only [d,ite_eq_right hij] at h
    dsimp only [r]
    linarith
  let b := fun i => Real.exp (-ℓ i/r^2)
  let ε := ∏ i, b i
  have hε : 0 < ε := Finset.prod_pos (fun i _ => Real.exp_pos _)
  refine ⟨ε,hε,fun z hz => ?_⟩
  obtain ⟨j,hnear⟩ := Finite.exists_min (fun i => ‖e i-z‖)
  have hdist (i : Fin m) (hij : i≠j) : r ≤ ‖e i-z‖ := by
    have hs := hsep i j hij
    have ht : ‖e i-e j‖ ≤ ‖e i-z‖+‖z-e j‖ := by
      simpa only [dist_eq_norm] using dist_triangle (e i) z (e j)
    rw [norm_sub_rev z (e j)] at ht
    have hn := hnear i
    linarith
  have hbound (i : Fin m) : b i ≤ ‖if i=j then 1 else innerValue (u i) z‖ := by
    by_cases hij : i=j
    · rw [ite_eq_left hij]
      change Real.exp (-ℓ i/r^2) ≤ ‖(1 : ℂ)‖
      rw [norm_one,Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hℓ i).le) (sq_nonneg r)
    · rw [ite_eq_right hij,singleAtom_norm_formula (u i) (ζ i) (ℓ i) (α i) (hα i) (hval i) ⟨z,hz⟩]
      apply Real.exp_le_exp.mpr
      have hi := hdist i hij
      have hp : atomicPoissonKernel z (ζ i) ≤ 1/r^2 := by
        change (1-‖z‖^2)/‖e i-z‖^2 ≤ 1/r^2
        apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hr hi)) (sq_pos_of_pos hr)).mpr
        simp only [one_mul]
        calc
          (1-‖z‖^2)*r^2 ≤ 1*r^2 := mul_le_mul_of_nonneg_right (by linarith [sq_nonneg ‖z‖]) (sq_nonneg r)
          _ ≤ ‖e i-z‖^2 := by simpa only [one_mul] using pow_le_pow_left₀ hr.le hi 2
      change -ℓ i/r^2 ≤ -ℓ i*atomicPoissonKernel z (ζ i)
      have h := mul_le_mul_of_nonneg_left hp (hℓ i).le
      rw [div_eq_mul_inv] at h ⊢
      nlinarith
  have hco : ε ≤ ‖innerValue (cofactor u j) z‖ := by
    rw [innerValue_cofactor u (fun i => (hu i).1) j ⟨z,hz⟩,norm_prod]
    exact Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) (fun i _ => hbound i)
  exact hco.trans (Finset.single_le_sum (f := fun i : Fin m => ‖innerValue (cofactor u i) z‖)
    (fun i _ => norm_nonneg _) (Finset.mem_univ j))


/-- The one-atom theorem now retains only its substantive regularization/triangular/WOT/norm inputs. -/
theorem oneAtomSplitting_of_regularization (hT : TriangularBoundObligation)
    (hW : SchattenWeakSubsequenceObligation) (hR : AtomicRegularizationObligation)
    (hN : SchattenNormLaws) : OneAtomConclusion :=
  oneAtomSplitting hT hW hR hN singleAtomDimension singleAtomMeasure compactScalarAngularLimitTheorem

/-- Actual finite-atom geometry is proved; analytic witnesses, one-atom splitting and sharp norm remain. -/
theorem finiteAtomClassification_of_witness (hCo : CoronaWitnessObligation)
    (hOne : OneAtomObligation) (hN : SchattenNormLaws) : FiniteAtomConclusion :=
  finiteAtomClassification_fromCorona hCo distinctAtomCorona hOne singleAtomDimension angularUniqueness hN

end TTO.Paper.Proved
