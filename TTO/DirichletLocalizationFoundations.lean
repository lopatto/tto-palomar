/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CenteredDirichletFoundations

/-! Actual arbitrary-dimensional low-p localization and dyadic frequency differences. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- The literal initial coordinate embedding, including zero-dimensional domains. -/
def prefixCoordinateEmbedding (r R : ℕ) (h : r≤R) : Fin r ↪ Fin R where
  toFun i := ⟨i.val,i.isLt.trans_le h⟩
  inj' _i _j hij := Fin.ext (congrArg (fun x : Fin R => x.val) hij)

def prefixCoordinateInclusion (r R : ℕ) (h : r≤R) :
    EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin R) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (prefixCoordinateEmbedding r R h)

theorem prefixCoordinateInclusion_single (r R : ℕ) (h : r≤R) (i : Fin r) :
    prefixCoordinateInclusion r R h (EuclideanSpace.single i (1 : ℂ))=
      EuclideanSpace.single (prefixCoordinateEmbedding r R h i) (1 : ℂ) :=
  LinearIsometry.piLpExtendByZero_apply_single (p := 2) (𝕜 := ℂ) (E := ℂ) _ i 1

theorem prefixCoordinateInclusion_apply (r R : ℕ) (h : r≤R)
    (f : EuclideanSpace ℂ (Fin r)) (i : Fin r) :
    prefixCoordinateInclusion r R h f (prefixCoordinateEmbedding r R h i)=f i := by
  change Function.extend (prefixCoordinateEmbedding r R h) (WithLp.ofLp f) 0
    (prefixCoordinateEmbedding r R h i)=f i
  rw [(prefixCoordinateEmbedding r R h).injective.extend_apply]

theorem prefixCoordinateInclusion_apply_zero (r R : ℕ) (h : r≤R)
    (f : EuclideanSpace ℂ (Fin r)) (i : Fin R) (hi : r ≤ i.val) :
    prefixCoordinateInclusion r R h f i=0 := by
  apply LinearIsometry.piLpExtendByZero_apply_eq_zero
  rintro ⟨j,hj⟩
  have he := congrArg Fin.val hj
  change j.val=i.val at he
  omega

/-- The native adjoint is actual coordinate restriction, with no representative convention. -/
theorem prefixCoordinateInclusion_adjoint_apply (r R : ℕ) (h : r≤R)
    (f : EuclideanSpace ℂ (Fin R)) (i : Fin r) :
    (prefixCoordinateInclusion r R h).toContinuousLinearMap.adjoint f i=
      f (prefixCoordinateEmbedding r R h i) := by
  have he := ContinuousLinearMap.adjoint_inner_right
    (prefixCoordinateInclusion r R h).toContinuousLinearMap (EuclideanSpace.single i (1 : ℂ)) f
  rw [LinearIsometry.coe_toContinuousLinearMap,prefixCoordinateInclusion_single] at he
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using he

/-- Exact native prefix compression of a rectangular matrix. -/
def prefixCompression (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) :
    EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  (prefixCoordinateInclusion r R hr).toContinuousLinearMap.adjoint ∘L A ∘L
    (prefixCoordinateInclusion c C hc).toContinuousLinearMap

theorem prefixCompression_single_apply (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) (i : Fin r) (j : Fin c) :
    prefixCompression r c R C hr hc A (EuclideanSpace.single j (1 : ℂ)) i=
      A (EuclideanSpace.single (prefixCoordinateEmbedding c C hc j) (1 : ℂ))
        (prefixCoordinateEmbedding r R hr i) := by
  rw [prefixCompression,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,prefixCoordinateInclusion_single,
    prefixCoordinateInclusion_adjoint_apply]

theorem prefixCoordinateInclusion_adjoint_single (r R : ℕ) (h : r≤R) (i : Fin r) :
    (prefixCoordinateInclusion r R h).toContinuousLinearMap.adjoint
      (EuclideanSpace.single (prefixCoordinateEmbedding r R h i) (1 : ℂ))=
        EuclideanSpace.single i (1 : ℂ) := by
  apply PiLp.ext
  intro j
  rw [prefixCoordinateInclusion_adjoint_apply]
  simp only [PiLp.single_apply,Fin.ext_iff,prefixCoordinateEmbedding]
  rfl

theorem prefixCoordinateInclusion_adjoint_single_zero (r R : ℕ) (h : r≤R) (i : Fin R)
    (hi : r ≤ i.val) :
    (prefixCoordinateInclusion r R h).toContinuousLinearMap.adjoint (EuclideanSpace.single i (1 : ℂ))=0 := by
  apply PiLp.ext
  intro j
  rw [prefixCoordinateInclusion_adjoint_apply]
  have he : prefixCoordinateEmbedding r R h j≠i := by
    intro he
    have hv := congrArg Fin.val he
    change j.val=i.val at hv
    omega
  simp only [PiLp.single_apply,ite_eq_right he,PiLp.zero_apply]

/-- Actual zero extension on the output and native adjoint restriction on the input. -/
def prefixExtension (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (B : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R) :=
  (prefixCoordinateInclusion r R hr).toContinuousLinearMap ∘L B ∘L
    (prefixCoordinateInclusion c C hc).toContinuousLinearMap.adjoint

theorem prefixExtension_single_apply (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (B : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i : Fin R) (j : Fin C) :
    prefixExtension r c R C hr hc B (EuclideanSpace.single j (1 : ℂ)) i=
      if hi : i.val<r then if hj : j.val<c then B (EuclideanSpace.single ⟨j.val,hj⟩ (1 : ℂ)) ⟨i.val,hi⟩ else 0 else 0 := by
  rw [prefixExtension,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  by_cases hi : i.val<r
  · rw [dite_eq_left hi]
    by_cases hj : j.val<c
    · rw [dite_eq_left hj]
      let i₀ : Fin r := ⟨i.val,hi⟩
      let j₀ : Fin c := ⟨j.val,hj⟩
      have heI : prefixCoordinateEmbedding r R hr i₀=i := Fin.ext rfl
      have heJ : prefixCoordinateEmbedding c C hc j₀=j := Fin.ext rfl
      have hAdj : (prefixCoordinateInclusion c C hc).toContinuousLinearMap.adjoint
          (EuclideanSpace.single j (1 : ℂ))=EuclideanSpace.single j₀ (1 : ℂ) := by
        rw [← heJ]
        exact prefixCoordinateInclusion_adjoint_single c C hc j₀
      rw [hAdj]
      have hApp := prefixCoordinateInclusion_apply r R hr (B (EuclideanSpace.single j₀ (1 : ℂ))) i₀
      rw [heI] at hApp
      exact hApp
    · rw [dite_eq_right hj,prefixCoordinateInclusion_adjoint_single_zero _ _ _ _ (Nat.le_of_not_gt hj),map_zero,map_zero]
      rfl
  · rw [dite_eq_right hi,prefixCoordinateInclusion_apply_zero _ _ _ _ _ (Nat.le_of_not_gt hi)]

/-- The finite signed mask factors EXACTLY through its supported initial coordinate block. -/
theorem dirichletProductSchur_prefix_factorization (m N r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchurOffset r c (dirichletProductShift m N) (dirichletProductPolynomial m N) A=
      prefixExtension (min r (dirichletProductShift m N+1)) (min c (dirichletProductShift m N+1)) r c
        (min_le_left _ _) (min_le_left _ _)
        (polynomialHankelSchurOffset _ _ (dirichletProductShift m N) (dirichletProductPolynomial m N)
          (prefixCompression _ _ r c (min_le_left _ _) (min_le_left _ _) A)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [prefixExtension_single_apply]
  by_cases hi : i.val<min r (dirichletProductShift m N+1)
  · rw [dite_eq_left hi]
    by_cases hj : j.val<min c (dirichletProductShift m N+1)
    · rw [dite_eq_left hj,polynomialHankelSchurOffset_single_apply,polynomialHankelSchurOffset_single_apply,
        prefixCompression_single_apply]
      rfl
    · rw [dite_eq_right hj]
      exact dirichletProductSchur_single_apply_zero m N r c A i j (by omega)
  · rw [dite_eq_right hi]
    exact dirichletProductSchur_single_apply_zero m N r c A i j (by omega)

/-- Native two-sided contractions cannot increase any positive Schatten gauge of a finite map. -/
theorem euclidean_schattenNorm_comp_contractions_le (r c R C : ℕ)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R))
    (L : EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (J : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin C))
    (hL : ‖L‖≤1) (hJ : ‖J‖≤1) (p : ℝ) (hp : 0<p) :
    schattenNorm p (L ∘L A ∘L J)≤schattenNorm p A := by
  have h := schattenNorm_comp_le (finiteDim_schatten A p hp) L J
  have hProd : ‖L‖*‖J‖≤1 := by
    simpa only [one_mul] using mul_le_mul hL hJ (norm_nonneg J) zero_le_one
  exact h.trans ((mul_le_mul_of_nonneg_right hProd (Reduction.schattenNorm_nonneg p A)).trans_eq (one_mul _))

theorem schattenNorm_prefixCompression_le (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (A : EuclideanSpace ℂ (Fin C) →L[ℂ] EuclideanSpace ℂ (Fin R)) (p : ℝ) (hp : 0<p) :
    schattenNorm p (prefixCompression r c R C hr hc A)≤schattenNorm p A := by
  exact euclidean_schattenNorm_comp_contractions_le r c R C A _ _
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le (norm_isometry_clm_le_one _))
    (norm_isometry_clm_le_one _) p hp

theorem schattenNorm_prefixExtension_le (r c R C : ℕ) (hr : r≤R) (hc : c≤C)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (p : ℝ) (hp : 0<p) :
    schattenNorm p (prefixExtension r c R C hr hc A)≤schattenNorm p A := by
  exact euclidean_schattenNorm_comp_contractions_le R C r c A _ _
    (norm_isometry_clm_le_one _)
    ((ContinuousLinearMap.adjoint.norm_map _).trans_le (norm_isometry_clm_le_one _)) p hp

/-- The SAME low-p localization constant works in arbitrary ambient dimensions.
Finite frequency support is proved to factor through genuine native coordinate contractions. -/
theorem dirichletProductSchur_schattenNorm_rpow_le_all_dimensions (m N r c : ℕ) (hN : 0<N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelSchurOffset r c (dirichletProductShift m N)
      (dirichletProductPolynomial m N) A)^p≤dirichletProductSchurConstant m p*schattenNorm p A^p := by
  let r₀ : ℕ := min r (dirichletProductShift m N+1)
  let c₀ : ℕ := min c (dirichletProductShift m N+1)
  have hr : r₀≤r := min_le_left _ _
  have hc : c₀≤c := min_le_left _ _
  let A₀ := prefixCompression r₀ c₀ r c hr hc A
  let B₀ := polynomialHankelSchurOffset r₀ c₀ (dirichletProductShift m N) (dirichletProductPolynomial m N) A₀
  have hSize : r₀+c₀≤2*dirichletProductShift m N+2 := by
    dsimp only [r₀,c₀]
    linarith [min_le_right r (dirichletProductShift m N+1),min_le_right c (dirichletProductShift m N+1)]
  have hExt := schattenNorm_prefixExtension_le r₀ c₀ r c hr hc B₀ p hp
  have hComp := schattenNorm_prefixCompression_le r₀ c₀ r c hr hc A p hp
  have hSmall := dirichletProductSchur_schattenNorm_rpow_le m N r₀ c₀ hN hSize A₀ p hp hp1 hOrder
  rw [dirichletProductSchur_prefix_factorization]
  calc
    _ ≤ schattenNorm p B₀^p := Real.rpow_le_rpow (Reduction.schattenNorm_nonneg _ _) hExt hp.le
    _ ≤ dirichletProductSchurConstant m p*schattenNorm p A₀^p := hSmall
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Reduction.schattenNorm_nonneg _ _) hComp hp.le)
      (dirichletProductSchurConstant_pos m p hOrder).le

/-- Smoothing order and multiplier constant are chosen before every ambient dimension and scale. -/
theorem exists_uniform_dirichletProductSchur_bound_all_dimensions (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ m : ℕ,∃ C : ℝ,0 < C ∧ ∀ N r c : ℕ,0 < N →
      ∀ A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r),
        schattenNorm p (polynomialHankelSchurOffset r c (dirichletProductShift m N)
          (dirichletProductPolynomial m N) A)^p≤C*schattenNorm p A^p := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/p)
  have hOrder : 1<((m+1 : ℕ) : ℝ)*p := by
    have h := (div_lt_iff₀ hp).mp hm
    push_cast
    nlinarith
  exact ⟨m,dirichletProductSchurConstant m p,dirichletProductSchurConstant_pos m p hOrder,
    fun N r c hN A => dirichletProductSchur_schattenNorm_rpow_le_all_dimensions m N r c hN A p hp hp1 hOrder⟩

/-- Literal nonnegative-frequency coefficients of the full signed low-pass kernel. -/
def dirichletLowpassWeight (m N k : ℕ) : ℂ :=
  (dirichletProductPolynomial m N).coeff (dirichletProductShift m N+k)

def dyadicDirichletWeight (m j k : ℕ) : ℂ :=
  dirichletLowpassWeight m (2^(j+1)) k-dirichletLowpassWeight m (2^j) k

def dyadicDirichletLowpass (m j r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
  polynomialHankelSchurOffset r c (dirichletProductShift m (2^j)) (dirichletProductPolynomial m (2^j)) A

def dyadicDirichletBand (m j r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
  dyadicDirichletLowpass m (j+1) r c A-dyadicDirichletLowpass m j r c A

theorem dirichletProductShift_mono (m : ℕ) {N M : ℕ} (h : N≤M) :
    dirichletProductShift m N≤dirichletProductShift m M :=
  Nat.add_le_add (Nat.mul_le_mul_left (m+2) h) (Nat.mul_le_mul_left m h)

/-- The band has an actual low-frequency gap, including the constant coefficient. -/
theorem dyadicDirichletWeight_low_zero (m j k : ℕ) (hk : k≤2*(2^j)) :
    dyadicDirichletWeight m j k=0 := by
  have hHigh : k≤2*(2^(j+1)) := by rw [pow_succ]; omega
  rw [dyadicDirichletWeight,dirichletLowpassWeight,dirichletLowpassWeight,
    dirichletProductPolynomial_coeff_plateau m _ k hHigh,
    dirichletProductPolynomial_coeff_plateau m _ k hk,sub_self]

/-- The band is finitely supported above as well; no unproved spectral cutoff is assumed. -/
theorem dyadicDirichletWeight_high_zero (m j k : ℕ)
    (hk : dirichletProductShift m (2^(j+1))<k) : dyadicDirichletWeight m j k=0 := by
  have hScale : 2^j≤2^(j+1) := by rw [pow_succ]; omega
  have hSmall : dirichletProductShift m (2^j)<k := (dirichletProductShift_mono m hScale).trans_lt hk
  rw [dyadicDirichletWeight,dirichletLowpassWeight,dirichletLowpassWeight,
    dirichletProductPolynomial_coeff_zero m _ k hk,
    dirichletProductPolynomial_coeff_zero m _ k hSmall,sub_self]

/-- Actual matrix entries of the dyadic band are its literal coefficient differences. -/
theorem dyadicDirichletBand_single_apply (m j r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i : Fin r) (k : Fin c) :
    dyadicDirichletBand m j r c A (EuclideanSpace.single k (1 : ℂ)) i=
      dyadicDirichletWeight m j (i.val+k.val)*A (EuclideanSpace.single k (1 : ℂ)) i := by
  rw [dyadicDirichletBand,sub_apply,PiLp.sub_apply]
  rw [dyadicDirichletLowpass,dyadicDirichletLowpass,
    polynomialHankelSchurOffset_single_apply,polynomialHankelSchurOffset_single_apply]
  simp only [dyadicDirichletWeight,dirichletLowpassWeight,Nat.add_assoc]
  ring

/-- Uniform low-p band localization in arbitrary dimensions. It is NOT a sum-over-scales lower estimate. -/
theorem dyadicDirichletBand_schattenNorm_rpow_le (m j r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (dyadicDirichletBand m j r c A)^p≤
      (2*dirichletProductSchurConstant m p)*schattenNorm p A^p := by
  have hPos (k : ℕ) : 0<2^k := Nat.two_pow_pos k
  have hUp := dirichletProductSchur_schattenNorm_rpow_le_all_dimensions m (2^(j+1)) r c
    (hPos _) A p hp hp1 hOrder
  have hLo := dirichletProductSchur_schattenNorm_rpow_le_all_dimensions m (2^j) r c
    (hPos _) A p hp hp1 hOrder
  have hNeg : schattenNorm p (-dyadicDirichletLowpass m j r c A)=
      schattenNorm p (dyadicDirichletLowpass m j r c A) := by
    simp only [schattenNorm,approximationNumber_neg]
  calc
    _ ≤ schattenNorm p (dyadicDirichletLowpass m (j+1) r c A)^p+
        schattenNorm p (dyadicDirichletLowpass m j r c A)^p := by
      simpa only [dyadicDirichletBand,sub_eq_add_neg,hNeg] using
        finite_schattenNorm_add_rpow_le (dyadicDirichletLowpass m (j+1) r c A)
          (-dyadicDirichletLowpass m j r c A) p hp hp1
    _ ≤ dirichletProductSchurConstant m p*schattenNorm p A^p+
        dirichletProductSchurConstant m p*schattenNorm p A^p := add_le_add hUp hLo
    _ = _ := by ring

/-- Exact coefficient telescoping, with the base low-pass carrying the constant modes. -/
theorem dyadicDirichletWeight_telescope (m J k : ℕ) :
    dirichletLowpassWeight m 1 k+∑ j∈Finset.range J,dyadicDirichletWeight m j k=
      dirichletLowpassWeight m (2^J) k := by
  induction J with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,add_zero,pow_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih,dyadicDirichletWeight]
    abel

/-- Exact native operator telescoping for every finite rectangular matrix. -/
theorem dyadicDirichletBand_telescope (m J r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    dyadicDirichletLowpass m 0 r c A+∑ j∈Finset.range J,dyadicDirichletBand m j r c A=
      dyadicDirichletLowpass m J r c A := by
  induction J with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,add_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih,dyadicDirichletBand]
    abel

/-- A sufficiently large finite dyadic resolution recovers the original operator EXACTLY. -/
theorem dyadicDirichletBand_resolution (m J r c : ℕ) (hSize : r+c≤2*(2^J)+2)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    dyadicDirichletLowpass m 0 r c A+∑ j∈Finset.range J,dyadicDirichletBand m j r c A=A := by
  rw [dyadicDirichletBand_telescope]
  exact dirichletProductSchur_eq_self m (2^J) r c hSize A

end TTO.Paper.Proved
