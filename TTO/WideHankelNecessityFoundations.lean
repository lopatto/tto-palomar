/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PolynomialBesovSynthesisFoundations
public import TTO.PositiveWideKernelFoundations
public import TTO.HankelStrongNecessityFoundations
public import TTO.DirichletLocalizationFoundations

/-! Supported wide Hankel masks and controlled polynomial approximation. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem wideSchur_single_apply_zero (m N r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (i : Fin r) (j : Fin c) (h : wideDirichletProductShift m N < i.val+j.val) :
    polynomialHankelSchurOffset r c (wideDirichletProductShift m N)
      (wideDirichletProductPolynomial m N) A (EuclideanSpace.single j (1 : ℂ)) i=0 := by
  rw [polynomialHankelSchurOffset_single_apply,Nat.add_assoc,
    wideDirichletProductPolynomial_coeff_zero m N (i.val+j.val) h,zero_mul]

theorem wideSchur_prefix_factorization (m N r c : ℕ)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    polynomialHankelSchurOffset r c (wideDirichletProductShift m N)
      (wideDirichletProductPolynomial m N) A=
      prefixExtension (min r (wideDirichletProductShift m N+1))
        (min c (wideDirichletProductShift m N+1)) r c (min_le_left _ _) (min_le_left _ _)
        (polynomialHankelSchurOffset _ _ (wideDirichletProductShift m N)
          (wideDirichletProductPolynomial m N)
          (prefixCompression _ _ r c (min_le_left _ _) (min_le_left _ _) A)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin c) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  rw [prefixExtension_single_apply]
  by_cases hi : i.val<min r (wideDirichletProductShift m N+1)
  · rw [dite_eq_left hi]
    by_cases hj : j.val<min c (wideDirichletProductShift m N+1)
    · rw [dite_eq_left hj,polynomialHankelSchurOffset_single_apply,
        polynomialHankelSchurOffset_single_apply,prefixCompression_single_apply]
      rfl
    · rw [dite_eq_right hj]
      exact wideSchur_single_apply_zero m N r c A i j (by omega)
  · rw [dite_eq_right hi]
    exact wideSchur_single_apply_zero m N r c A i j (by omega)

theorem wide_schur_schattenNorm_rpow_le (m N r c : ℕ) (hm : 1≤m) (hN : 10≤N)
    (A : EuclideanSpace ℂ (Fin c) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hOrder : 1<((m+1 : ℕ) : ℝ)*p) :
    schattenNorm p (polynomialHankelSchurOffset r c (wideDirichletProductShift m N)
      (wideDirichletProductPolynomial m N) A)^p≤wideLocalSchurConstant m p*schattenNorm p A^p := by
  let rr := min r (wideDirichletProductShift m N+1)
  let cc := min c (wideDirichletProductShift m N+1)
  let B := prefixCompression rr cc r c (min_le_left _ _) (min_le_left _ _) A
  have hShape : 0+rr+cc≤250*m*N := by
    have hr := min_le_right r (wideDirichletProductShift m N+1)
    have hc := min_le_right c (wideDirichletProductShift m N+1)
    rw [wideDirichletProductShift_eq] at hr hc
    dsimp only [rr,cc]
    rw [wideDirichletProductShift_eq]
    nlinarith
  have hNorm : schattenNorm p (polynomialHankelSchurOffset r c
      (wideDirichletProductShift m N) (wideDirichletProductPolynomial m N) A)≤
        schattenNorm p (polynomialHankelSchurOffset rr cc (wideDirichletProductShift m N)
          (wideDirichletProductPolynomial m N) B) := by
    rw [wideSchur_prefix_factorization]
    exact schattenNorm_prefixExtension_le rr cc r c (min_le_left _ _) (min_le_left _ _) _ p hp
  have hLocal := wide_local_schur_schattenNorm_rpow_le m N N rr cc 0 (by omega)
    le_rfl (by omega) hShape B p hp hp1 hOrder
  simp only [add_zero] at hLocal
  calc
    _ ≤ schattenNorm p (polynomialHankelSchurOffset rr cc (wideDirichletProductShift m N)
        (wideDirichletProductPolynomial m N) B)^p :=
      Real.rpow_le_rpow (schattenNorm_nonneg p _) hNorm hp.le
    _ ≤ wideLocalSchurConstant m p*schattenNorm p B^p := hLocal
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (schattenNorm_nonneg p B)
        (schattenNorm_prefixCompression_le rr cc r c (min_le_left _ _) (min_le_left _ _) A p hp) hp.le)
      (wideLocalSchurConstant_pos m p hOrder).le

def wideHankelPolynomial (m N : ℕ) (g : BoundaryL2) : Polynomial ℂ :=
  finiteHardyPolynomial (wideDirichletProductShift m N+1)
    (fun k => wideDirichletPositiveWeight m N k*fourierCoeff g (k : ℤ))

theorem wideHankelPolynomial_coeff (m N : ℕ) (g : BoundaryL2) (k : ℕ) :
    (wideHankelPolynomial m N g).coeff k=
      wideDirichletPositiveWeight m N k*fourierCoeff g (k : ℤ) := by
  classical
  by_cases hk : k<wideDirichletProductShift m N+1
  · simp [wideHankelPolynomial,finiteHardyPolynomial,Polynomial.coeff_monomial,
      Finset.mem_range,hk]
  · have hW : wideDirichletPositiveWeight m N k=0 :=
      wideDirichletProductPolynomial_coeff_zero m N k (by omega)
    simp [wideHankelPolynomial,finiteHardyPolynomial,Polynomial.coeff_monomial,
      Finset.mem_range,hk,hW]

theorem wideHankelPolynomial_matrix_eq (m N K : ℕ) (g : BoundaryL2) :
    polynomialHankelRectangleOffset K K 0 (wideHankelPolynomial m N g)=
      polynomialHankelSchurOffset K K (wideDirichletProductShift m N)
        (wideDirichletProductPolynomial m N)
        (finiteHankelCoefficientMatrix K (fun k => fourierCoeff g (k : ℤ))) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin K) ℂ).toBasis.ext
  intro j
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe]
  apply PiLp.ext
  intro i
  simp only [polynomialHankelRectangleOffset_single_apply,wideHankelPolynomial_coeff,
    polynomialHankelSchurOffset_single_apply,finiteHankelCoefficientMatrix_entry,
    zero_add,wideDirichletPositiveWeight,Nat.add_assoc]

theorem wideHankelPolynomial_schatten_rpow_le (m N : ℕ) (hm : 1≤m) (hN : 10≤N)
    (g : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hOrder : 1<((m+1 : ℕ) : ℝ)*p)
    (hS : Schatten p H) (K : ℕ) :
    schattenNorm p (polynomialHankelRectangleOffset K K 0 (wideHankelPolynomial m N g))^p≤
      wideLocalSchurConstant m p*schattenNorm p H^p := by
  rw [wideHankelPolynomial_matrix_eq]
  apply (wide_schur_schattenNorm_rpow_le m N K K hm hN _ p hp hp1 hOrder).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (schattenNorm_nonneg p _)
      (finiteHankelCoefficientMatrix_schatten_le g H hH hS K).2 hp.le)
    (wideLocalSchurConstant_pos m p hOrder).le

theorem exists_wideHankelPolynomial_besovEnergy_bound (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,∀ H : HankelOperator,
      RepresentsHankel (star (multiply coordinate g)) H → Schatten p H →
        ∀ N : ℕ,10≤N →
          besovEnergy p (wideHankelPolynomial (besovOrder p) N g).eval≤
            ENNReal.ofReal (C*schattenNorm p H^p) := by
  let m := besovOrder p
  have hm : 1≤m := by dsimp only [m,besovOrder]; omega
  have hOrder : 1<((m+1 : ℕ) : ℝ)*p := by
    have h := (besovOrder_product_bounds p hp).1
    dsimp only [m]
    push_cast
    nlinarith
  obtain ⟨M,hM,C,hC,hFinite⟩ := exists_polynomial_besov_hankel_bound p hp hp1
  refine ⟨C*wideLocalSchurConstant m p,
    mul_pos hC (wideLocalSchurConstant_pos m p hOrder),?_⟩
  intro g H hH hS N hN
  let P := wideHankelPolynomial m N g
  let K := 150*m*thinWideScale (M*(P.natDegree+1))
  have hE : besovEnergy p P.eval≤
      ENNReal.ofReal (C*schattenNorm p (polynomialHankelRectangleOffset K K 0 P)^p) :=
    hFinite P
  have hMat := wideHankelPolynomial_schatten_rpow_le m N hm hN g H hH p hp hp1 hOrder hS K
  calc
    _ ≤ ENNReal.ofReal (C*schattenNorm p (polynomialHankelRectangleOffset K K 0 P)^p) := hE
    _ ≤ ENNReal.ofReal (C*(wideLocalSchurConstant m p*schattenNorm p H^p)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hMat hC.le)
    _ = _ := by congr 1; ring

theorem hardyBasis_repr_wideHankelPolynomial (m N : ℕ) (g : BoundaryL2) (k : ℕ) :
    hardyBasis.repr (polynomialBoundary (wideHankelPolynomial m N g)) k=
      wideDirichletPositiveWeight m N k*fourierCoeff g (k : ℤ) := by
  classical
  rw [wideHankelPolynomial,polynomialBoundary_finiteHardyPolynomial]
  simp only [map_sum,map_smul,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,hardyBasis.repr_self,lp.single_apply,Pi.single_apply,smul_eq_mul]
  by_cases hk : k<wideDirichletProductShift m N+1
  · simp [Finset.mem_range,hk]
  · have hW : wideDirichletPositiveWeight m N k=0 :=
      wideDirichletProductPolynomial_coeff_zero m N k (by omega)
    simp [Finset.mem_range,hk,hW]

theorem tendsto_wideHankelPolynomial_hardy (m : ℕ) (hm : 1≤m) (g : Hardy) :
    Tendsto (fun N : ℕ => polynomialBoundary (wideHankelPolynomial m (N+10) g.val))
      atTop (𝓝 g) := by
  let C := positiveWideCoefficientConstant m
  have hC : 0<C := positiveWideCoefficientConstant_pos m hm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun N : ℕ =>
      ‖polynomialBoundary (wideHankelPolynomial m (N+10) g.val)-g‖^2) atTop (𝓝 0) := by
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕:=atTop)
      (f:=fun N (k : ℕ) =>
        ‖(wideDirichletPositiveWeight m (N+10) k-1)*hardyBasis.repr g k‖^2)
      (g:=fun _ => 0) (bound:=fun k : ℕ => (C+1)^2*‖hardyBasis.repr g k‖^2) ?_ ?_ ?_
    · rw [tsum_zero] at hdom
      refine hdom.congr' (Eventually.of_forall fun N => ?_)
      have h := lp.norm_rpow_eq_tsum (p:=2) (by norm_num)
        (hardyBasis.repr (polynomialBoundary (wideHankelPolynomial m (N+10) g.val)-g))
      rw [ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] at h
      calc
        _ = ∑' k : ℕ,‖hardyBasis.repr
            (polynomialBoundary (wideHankelPolynomial m (N+10) g.val)-g) k‖^2 := by
          apply tsum_congr
          intro k
          rw [Real.rpow_two,map_sub,lp.coeFn_sub,Pi.sub_apply,
            hardyBasis_repr_wideHankelPolynomial,← hardyBasis_repr_eq_fourierCoeff]
          ring_nf
        _ = _ := h.symm
    · have hs : Summable (fun k : ℕ => ‖hardyBasis.repr g k‖^2) := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          (lp.memℓp (hardyBasis.repr g)).summable (by norm_num)
      exact hs.mul_left _
    · intro k
      have he : ∀ᶠ N : ℕ in atTop,
          ‖(wideDirichletPositiveWeight m (N+10) k-1)*hardyBasis.repr g k‖^2=0 := by
        filter_upwards [eventually_ge_atTop k] with N hN
        have hk : k≤(99*m+2)*(N+10) := by nlinarith
        simp only [wideDirichletPositiveWeight,
          wideDirichletProductPolynomial_coeff_plateau m (N+10) k hk,
          sub_self,zero_mul,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]
      exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
    · exact Eventually.of_forall fun N k => by
        have hW : ‖wideDirichletPositiveWeight m (N+10) k-1‖≤C+1 := by
          have h := norm_sub_le (wideDirichletPositiveWeight m (N+10) k) (1 : ℂ)
          simp only [norm_one] at h
          exact h.trans (add_le_add (norm_wideDirichletPositiveWeight_le m (N+10) k hm (by omega)) le_rfl)
        rw [norm_pow,norm_norm,norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤C+1)).2 hW) (sq_nonneg _)
  have hroot := hsq.sqrt
  simpa only [Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using hroot

theorem norm_iteratedDeriv_analyticValue_le (f : BoundaryL2) (n : ℕ) (w : ℂ)
    (hw : w∈disk) :
    ‖iteratedDeriv n (analyticValue f) w‖≤
      ((n.factorial : ℝ)/(((1-‖w‖)/2)^(n+1)))*‖f‖ := by
  let R : ℝ := (1-‖w‖)/2
  have hw1 : ‖w‖<1 := hw
  have hR : 0<R := by dsimp only [R]; linarith
  have hNorm (z : ℂ) (hz : z∈Metric.closedBall w R) : ‖z‖≤R+‖w‖ := by
    have hDist : ‖z-w‖≤R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have hTri : ‖z‖≤‖z-w‖+‖w‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z-w) w
    exact hTri.trans (add_le_add hDist le_rfl)
  have hSub : Metric.closedBall w R⊆disk := by
    intro z hz
    change ‖z‖<1
    have h := hNorm z hz
    dsimp only [R] at h
    linarith
  have hBound (z : ℂ) (hz : z∈Metric.sphere w R) : ‖analyticValue f z‖≤‖f‖/R := by
    have hc := Metric.sphere_subset_closedBall hz
    have hGap : R≤1-‖z‖ := by
      have h := hNorm z hc
      dsimp only [R] at *
      linarith
    exact (norm_analyticValue_le f (hSub hc)).trans
      (div_le_div_of_nonneg_left (norm_nonneg f) hR hGap)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    ((analyticOnNhd_analyticValue f).differentiableOn.diffContOnCl_ball hSub) hBound
  apply h.trans_eq
  change (n.factorial : ℝ)*(‖f‖/R)/R^n=((n.factorial : ℝ)/R^(n+1))*‖f‖
  rw [pow_succ]
  field_simp

theorem iteratedDeriv_analyticValue_sub (f g : BoundaryL2) (n : ℕ) (w : ℂ) (hw : w∈disk) :
    iteratedDeriv n (analyticValue (f-g)) w=
      iteratedDeriv n (analyticValue f) w-iteratedDeriv n (analyticValue g) w := by
  have he : analyticValue (f-g) =ᶠ[𝓝 w] analyticValue f-analyticValue g := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
    exact analyticValue_sub f g hz
  exact (Filter.EventuallyEq.iteratedDeriv_eq n he).trans
    (iteratedDeriv_sub ((analyticOnNhd_analyticValue f) w hw).contDiffAt
      ((analyticOnNhd_analyticValue g) w hw).contDiffAt)

theorem tendsto_iteratedDeriv_analyticValue_of_hardy (F : ℕ → Hardy) (g : Hardy)
    (hF : Tendsto F atTop (𝓝 g)) (n : ℕ) (w : ℂ) (hw : w∈disk) :
    Tendsto (fun N => iteratedDeriv n (analyticValue (F N).val) w) atTop
      (𝓝 (iteratedDeriv n (analyticValue g.val) w)) := by
  let C : ℝ := (n.factorial : ℝ)/(((1-‖w‖)/2)^(n+1))
  have hNorm : Tendsto (fun N => ‖F N-g‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hF.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g))).norm
  have hUpper : Tendsto (fun N => C*‖F N-g‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hNorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hUpper
  have h := norm_iteratedDeriv_analyticValue_le ((F N-g).val) n w hw
  change ‖iteratedDeriv n (analyticValue ((F N).val-g.val)) w‖≤C*‖F N-g‖ at h
  rw [iteratedDeriv_analyticValue_sub _ _ n w hw] at h
  exact h

theorem iteratedDeriv_analyticValue_polynomialBoundary (P : Polynomial ℂ)
    (n : ℕ) (w : ℂ) (hw : w∈disk) :
    iteratedDeriv n (analyticValue (polynomialBoundary P).val) w=iteratedDeriv n P.eval w := by
  apply Filter.EventuallyEq.iteratedDeriv_eq n
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
  exact analyticValue_polynomialBoundary P hz

theorem tendsto_iteratedDeriv_wideHankelPolynomial (m : ℕ) (hm : 1≤m) (g : Hardy)
    (n : ℕ) (w : ℂ) (hw : w∈disk) :
    Tendsto (fun N : ℕ => iteratedDeriv n (wideHankelPolynomial m (N+10) g.val).eval w)
      atTop (𝓝 (iteratedDeriv n (analyticValue g.val) w)) := by
  have h := tendsto_iteratedDeriv_analyticValue_of_hardy _ g
    (tendsto_wideHankelPolynomial_hardy m hm g) n w hw
  exact h.congr' (Eventually.of_forall fun N =>
    iteratedDeriv_analyticValue_polynomialBoundary (wideHankelPolynomial m (N+10) g.val) n w hw)

theorem besovEnergy_le_of_polynomial_derivative_limits (P : ℕ → Polynomial ℂ)
    (F : ℂ → ℂ) (p : ℝ) (hp : 0<p) (B : ℝ) (hB : 0≤B)
    (hBound : ∀ N,besovEnergy p (P N).eval≤ENNReal.ofReal B)
    (hLim : ∀ n : ℕ,∀ z∈disk,Tendsto
      (fun N => iteratedDeriv n (P N).eval z) atTop (𝓝 (iteratedDeriv n F z))) :
    besovEnergy p F≤ENNReal.ofReal (2*B) := by
  let m := besovOrder p
  let J : ℕ → ℝ≥0∞ := fun N =>
    ∑ j∈Finset.range m,ENNReal.ofReal (‖iteratedDeriv j (P N).eval 0‖^p)
  let JF : ℝ≥0∞ := ∑ j∈Finset.range m,ENNReal.ofReal (‖iteratedDeriv j F 0‖^p)
  let Φ : ℕ → ℂ → ℝ≥0∞ := fun N z =>
    ENNReal.ofReal (‖iteratedDeriv m (P N).eval z‖^p*(1-‖z‖^2)^((m : ℝ)*p-2))
  have hJetLim : Tendsto J atTop (𝓝 JF) := by
    apply tendsto_finsetSum
    intro j _
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hLim j 0 (by norm_num [disk])).norm.rpow_const (Or.inr hp.le))
  have hJetBound (N : ℕ) : J N≤ENNReal.ofReal B := by
    apply (le_add_of_nonneg_right (by positivity) : J N≤J N+∫⁻ z,Φ N z ∂diskArea).trans
    exact hBound N
  have hJet : JF≤ENNReal.ofReal B :=
    le_of_tendsto hJetLim (Eventually.of_forall hJetBound)
  have hMeas (N : ℕ) : AEMeasurable (Φ N) diskArea := by
    have hD : Continuous (iteratedDeriv m (P N).eval) := by
      rw [← polynomialIteratedDerivative_eval]
      fun_prop
    exact (((hD.norm.measurable.pow_const p).mul
      ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const _)).ennreal_ofReal).aemeasurable
  have hEq : (fun z => liminf (fun N => Φ N z) atTop)=ᵐ[diskArea]
      (fun z => ENNReal.ofReal (‖iteratedDeriv m F z‖^p*(1-‖z‖^2)^((m : ℝ)*p-2))) := by
    filter_upwards [ae_mem_diskArea] with z hz
    have h := (ENNReal.continuous_ofReal.tendsto _).comp
      (((hLim m z hz).norm.rpow_const (Or.inr hp.le)).mul_const
        ((1-‖z‖^2)^((m : ℝ)*p-2)))
    exact h.liminf_eq
  have hFatou := lintegral_liminf_le' (u:=(atTop : Filter ℕ)) hMeas
  rw [lintegral_congr_ae hEq] at hFatou
  have hAreaBound (N : ℕ) : (∫⁻ z,Φ N z ∂diskArea)≤ENNReal.ofReal B := by
    apply (le_add_of_nonneg_left (by positivity) :
      (∫⁻ z,Φ N z ∂diskArea)≤J N+∫⁻ z,Φ N z ∂diskArea).trans
    exact hBound N
  have hArea := hFatou.trans
    (liminf_le_of_frequently_le' (Eventually.of_forall hAreaBound).frequently)
  change JF+(∫⁻ z,ENNReal.ofReal (‖iteratedDeriv m F z‖^p*
    (1-‖z‖^2)^((m : ℝ)*p-2)) ∂diskArea)≤_
  calc
    _ ≤ ENNReal.ofReal B+ENNReal.ofReal B := add_le_add hJet hArea
    _ = _ := by rw [← ENNReal.ofReal_add hB hB]; congr 1; ring

theorem exists_hankel_besov_energy_le_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,g∈hardy → ∀ H : HankelOperator,
      RepresentsHankel (star (multiply coordinate g)) H → Schatten p H →
        besovEnergy p (analyticValue g)≤ENNReal.ofReal (C*schattenNorm p H^p) := by
  obtain ⟨C,hC,hBound⟩ := exists_wideHankelPolynomial_besovEnergy_bound p hp hp1
  have hm : 1≤besovOrder p := by simp only [besovOrder]; omega
  refine ⟨2*C,by positivity,?_⟩
  intro g hg H hH hS
  let x : Hardy := ⟨g,hg⟩
  have h := besovEnergy_le_of_polynomial_derivative_limits
    (fun N => wideHankelPolynomial (besovOrder p) (N+10) g) (analyticValue g)
    p hp (C*schattenNorm p H^p)
    (mul_nonneg hC.le (Real.rpow_nonneg (schattenNorm_nonneg p H) p))
    (fun N => hBound g H hH hS (N+10) (by omega))
    (fun n z hz => tendsto_iteratedDeriv_wideHankelPolynomial (besovOrder p) hm x n z hz)
  simpa only [mul_assoc] using h

theorem inBesov_of_schattenHankel_low (g : BoundaryL2) (hg : g∈hardy)
    (H : HankelOperator) (hH : RepresentsHankel (star (multiply coordinate g)) H)
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (hS : Schatten p H) : InBesov p g := by
  obtain ⟨C,hC,hBound⟩ := exists_hankel_besov_energy_le_low p hp hp1
  exact ⟨hg,lt_of_le_of_lt (hBound g hg H hH hS) (by finiteness)⟩

theorem exists_besovNorm_le_hankel_low (p : ℝ) (hp : 0<p) (hp1 : p≤1) :
    ∃ C : ℝ,0<C ∧ ∀ g : BoundaryL2,g∈hardy → ∀ H : HankelOperator,
      RepresentsHankel (star (multiply coordinate g)) H → Schatten p H →
        besovNorm p g≤C*schattenNorm p H := by
  obtain ⟨C,hC,hBound⟩ := exists_hankel_besov_energy_le_low p hp hp1
  refine ⟨C^(1/p),Real.rpow_pos_of_pos hC _,?_⟩
  intro g hg H hH hS
  have hENonneg : 0≤C*schattenNorm p H^p :=
    mul_nonneg hC.le (Real.rpow_nonneg (schattenNorm_nonneg p H) p)
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBound g hg H hH hS)
  rw [ENNReal.toReal_ofReal hENonneg] at hReal
  have h := Real.rpow_le_rpow ENNReal.toReal_nonneg hReal (one_div_pos.mpr hp).le
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg (schattenNorm_nonneg p H) p),
    ← Real.rpow_mul (schattenNorm_nonneg p H),
    mul_one_div_cancel hp.ne',Real.rpow_one] at h
  exact h

end TTO.Paper.Proved
