/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.CompactHankelFoundations
public import TTO.ContinuousHankelFoundations

/-! Contractive full-symbol Poisson smoothing and its actual Hankel operators. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Use the native operator structures for the aliased Hardy operator space. -/
local instance poissonHankelOperatorNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance poissonHankelOperatorNormedSpace : NormedSpace ℂ HankelOperator := inferInstance

theorem coreForm_bounded_symbol (a : BoundaryLInf) (f g : BoundaryL2) :
    coreForm (toL2 a) f g=inner ℂ g (multiply a f) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toL2_ae a,multiply_ae a f] with t ha hm
  simp only [RCLike.inner_apply,ha,hm]

theorem norm_poissonAverage_toL2_le (a : BoundaryLInf) (w : Disk) :
    ‖poissonAverage w (toL2 a)‖≤‖a‖ := by
  let k := (szegoKernel w).val
  let δ := 1-‖w.val‖^2
  have hδ : 0<δ := by
    have hw : ‖w.val‖<1 := w.property
    dsimp [δ]
    nlinarith [norm_nonneg w.val]
  have hk : ‖k‖^2=δ⁻¹ := norm_szegoKernel_sq w
  rw [poissonAverage_core,coreForm_bounded_symbol,norm_mul]
  change ‖((δ : ℝ) : ℂ)‖*‖inner ℂ k (multiply a k)‖≤‖a‖
  rw [Complex.norm_real,Real.norm_of_nonneg hδ.le]
  calc
    δ*‖inner ℂ k (multiply a k)‖ ≤ δ*(‖k‖*‖multiply a k‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hδ.le
    _ ≤ δ*(‖k‖*(‖a‖*‖k‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_multiply_le a k) (norm_nonneg k)) hδ.le
    _ = ‖a‖ := by rw [show δ*(‖k‖*(‖a‖*‖k‖))=‖a‖*(δ*‖k‖^2) by ring,hk,mul_inv_cancel₀ (ne_of_gt hδ),mul_one]

theorem poissonAverage_star (w : Disk) (f : BoundaryL2) :
    poissonAverage w (star f)=conj (poissonAverage w f) := by
  rw [poissonAverage_integral,poissonAverage_integral,← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with t ht
  change (star f) t=conj (f t) at ht
  rw [ht,map_mul,Complex.conj_ofReal]

theorem hankelRadialContinuous_eval (g : Hardy) (n : ℕ) (t : Boundary) :
    hankelRadialContinuous g n t=analyticValue g.val
      ((hankelRadius n : ℂ)*fourier (T:=1) 1 t) := by
  rw [hankelRadialContinuous,← ContinuousMap.tsum_apply (summable_hankelRadialContinuous g n) t]
  have hz : ‖(hankelRadius n : ℂ)*fourier (T:=1) 1 t‖<1 := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hankelRadius_mem n).1.le,
      fourier_one,Circle.norm_coe,mul_one] using (hankelRadius_mem n).2
  rw [← (hasSum_analyticValue g.val hz).tsum_eq]
  congr 1
  funext k
  simp only [hardyRadialCoeff,ContinuousMap.smul_apply,smul_eq_mul,fourier_apply,
    natCast_zsmul,AddCircle.toCircle_nsmul,Circle.coe_pow,one_zsmul,mul_pow]
  ring

def fullRadialSymbol (φ ψ : Hardy) (n : ℕ) : C(Boundary,ℂ) :=
  hankelRadialContinuous φ n+star (hankelRadialContinuous ψ n)

theorem fullRadialSymbol_poisson (a : BoundaryLInf) (φ ψ : Hardy)
    (ha : toL2 a=φ.val+star ψ.val) (n : ℕ) (t : Boundary) :
    fullRadialSymbol φ ψ n t=poissonAverage
      ⟨(hankelRadius n : ℂ)*fourier (T:=1) 1 t,by
        change ‖(hankelRadius n : ℂ)*fourier (T:=1) 1 t‖<1
        simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hankelRadius_mem n).1.le,
          fourier_one,Circle.norm_coe,mul_one] using (hankelRadius_mem n).2⟩ (toL2 a) := by
  change hankelRadialContinuous φ n t+conj (hankelRadialContinuous ψ n t)=_
  rw [ha,map_add,poissonAverage_hardy,poissonAverage_star,poissonAverage_hardy,
    hankelRadialContinuous_eval,hankelRadialContinuous_eval]

theorem norm_fullRadialSymbol_le (a : BoundaryLInf) (φ ψ : Hardy)
    (ha : toL2 a=φ.val+star ψ.val) (n : ℕ) : ‖fullRadialSymbol φ ψ n‖≤‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
  intro t
  rw [fullRadialSymbol_poisson a φ ψ ha]
  exact norm_poissonAverage_toL2_le a _

theorem fullRadialSymbol_toL2 (φ ψ : Hardy) (n : ℕ) :
    ContinuousMap.toLp 2 circleMeasure ℂ (fullRadialSymbol φ ψ n)=
      (hardyRadialBoundary φ (hankelRadius n)).val+star (hardyRadialBoundary ψ (hankelRadius n)).val := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure (fullRadialSymbol φ ψ n),
    Lp.coeFn_add (hardyRadialBoundary φ (hankelRadius n)).val
      (star (hardyRadialBoundary ψ (hankelRadius n)).val),
    Lp.coeFn_star (hardyRadialBoundary ψ (hankelRadius n)).val,
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure (hankelRadialContinuous φ n),
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure (hankelRadialContinuous ψ n)] with t hc ha hs hφ hψ
  rw [hankelRadialContinuous_toL2] at hφ hψ
  rw [hc,ha]
  change hankelRadialContinuous φ n t+conj (hankelRadialContinuous ψ n t)=
    (hardyRadialBoundary φ (hankelRadius n)).val t+(star (hardyRadialBoundary ψ (hankelRadius n)).val) t
  rw [hs]
  change _=(hardyRadialBoundary φ (hankelRadius n)).val t+conj ((hardyRadialBoundary ψ (hankelRadius n)).val t)
  rw [hφ,hψ]


theorem fourierCoeff_add_boundary (f g : BoundaryL2) (k : ℤ) :
    fourierCoeff (f+g) k=fourierCoeff f k+fourierCoeff g k := by
  simp only [← fourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]

theorem fullRadialSymbol_negative_coefficient (φ ψ : Hardy) (n k : ℕ) (hk : 0<k) :
    fourierCoeff (ContinuousMap.toLp 2 circleMeasure ℂ (fullRadialSymbol φ ψ n)) (-(k : ℤ)) =
      (hankelRadius n : ℂ)^k*fourierCoeff (φ.val+star ψ.val) (-(k : ℤ)) := by
  rw [fullRadialSymbol_toL2,fourierCoeff_add_boundary,fourierCoeff_add_boundary,
    fourierCoeff_star_L2,fourierCoeff_star_L2]
  have hφ : fourierCoeff φ.val (-(k : ℤ))=0 :=
    (mem_hardy_iff φ.val).mp φ.property _ (by omega)
  have hφr : fourierCoeff (hardyRadialBoundary φ (hankelRadius n)).val (-(k : ℤ))=0 :=
    (mem_hardy_iff _).mp (hardyRadialBoundary φ (hankelRadius n)).property _ (by omega)
  rw [hφ,hφr,zero_add,zero_add,neg_neg,
    fourierCoeff_hardyRadialBoundary ψ _ (hankelRadius_mem n).1.le (hankelRadius_mem n).2]
  simp only [map_mul,map_pow,Complex.conj_ofReal]

theorem representsHankel_general_coefficient (σ : BoundaryL2) (H : HankelOperator)
    (hH : RepresentsHankel σ H) (i j : ℕ) :
    inner ℂ (negativeBasis i) (H (hardyBasis j))=
      fourierCoeff σ (-((i+j+1 : ℕ) : ℤ)) := by
  rw [hH _ _ (bounded_hardyBasis j) (bounded_negativeBasis i),
    coreForm_eq_inner_left _ _ _ (bounded_hardyBasis j)]
  simp only [hardyBasis_apply,negativeBasis_apply]
  change inner ℂ (fourierBasis (T:=1) (-(i : ℤ)-1))
    (coreMultiply σ ⟨fourierBasis (T:=1) (j : ℤ),bounded_fourierBasis (j : ℤ)⟩)=_
  rw [coreMultiply_fourierBasis,← HilbertBasis.repr_apply_apply,fourierBasis_repr,
    fourierCoeff_mode_multiply]
  congr 1
  push_cast
  ring

theorem hankelRadialOperator_entry (H : HankelOperator) (n i j : ℕ) :
    inner ℂ (negativeBasis i) (hankelRadialOperator H n (hardyBasis j))=
      (hankelRadius n : ℂ)^(i+j)*inner ℂ (negativeBasis i) (H (hardyBasis j)) := by
  rw [← HilbertBasis.repr_apply_apply]
  change negativeBasis.repr
    (negativeBasis.repr.symm ((hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L
      hankelRadialDiagonal n) (hardyBasis.repr (hardyBasis j)))) i=_
  rw [LinearIsometryEquiv.apply_symm_apply,hardyBasis.repr_self]
  change hankelRadialDiagonal n
    (hankelSequenceOperator H (hankelRadialDiagonal n (lp.single 2 j 1))) i=_
  rw [hankelRadialDiagonal_diagonal n j,map_smul,map_smul]
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rw [diagonal_apply _ _ (hankelRadialDiagonal_diagonal n)]
  change (hankelRadius n : ℂ)^j*((hankelRadius n : ℂ)^i*
    negativeBasis.repr (H (hardyBasis.repr.symm (lp.single 2 j 1))) i)=_
  rw [hardyBasis.repr_symm_single,HilbertBasis.repr_apply_apply,pow_add]
  ring

theorem fullRadialSymbol_hankel (a : BoundaryLInf) (φ ψ : Hardy)
    (ha : toL2 a=φ.val+star ψ.val) (n : ℕ) :
    continuousHankelSymbolMap (fullRadialSymbol φ ψ n)=
      (hankelRadius n : ℂ) • hankelRadialOperator (boundedHankelOperator a) n := by
  apply ContinuousLinearMap.ext_on hardyModes_dense
  rintro _ ⟨j,rfl⟩
  rw [← hardyBasis_apply]
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply]
  change inner ℂ (negativeBasis i) (continuousHankelSymbolMap (fullRadialSymbol φ ψ n) (hardyBasis j))=
    inner ℂ (negativeBasis i) ((hankelRadius n : ℂ) • hankelRadialOperator (boundedHankelOperator a) n (hardyBasis j))
  rw [representsHankel_general_coefficient _ _ (continuousHankelSymbolMap_represents _) i j,
    fullRadialSymbol_negative_coefficient _ _ _ _ (by omega),
    inner_smul_right,hankelRadialOperator_entry,
    representsHankel_general_coefficient _ _ (boundedHankelOperator_represents a) i j,
    ha,pow_succ]
  ring


theorem fullRadialSymbol_hankel_error_le (a : BoundaryLInf) (φ ψ : Hardy)
    (ha : toL2 a=φ.val+star ψ.val) (n : ℕ) :
    ‖continuousHankelSymbolMap (fullRadialSymbol φ ψ n)-boundedHankelOperator a‖ ≤
      ‖hankelRadialOperator (boundedHankelOperator a) n-boundedHankelOperator a‖+
        |hankelRadius n-1| *‖boundedHankelOperator a‖ := by
  rw [fullRadialSymbol_hankel a φ ψ ha]
  let H := boundedHankelOperator a
  let r := hankelRadius n
  have hr : |r|≤1 := by dsimp [r]; rw [abs_of_pos (hankelRadius_mem n).1]; exact (hankelRadius_mem n).2.le
  have hid : (r : ℂ) • hankelRadialOperator H n-H=
      (r : ℂ) • (hankelRadialOperator H n-H)+((r : ℂ)-1) • H := by
    simp only [smul_sub,sub_smul,one_smul]
    abel
  change ‖(r : ℂ) • hankelRadialOperator H n-H‖≤_
  rw [hid]
  calc
    _ ≤ ‖(r : ℂ) • (hankelRadialOperator H n-H)‖+‖((r : ℂ)-1) • H‖ := norm_add_le _ _
    _ = |r| *‖hankelRadialOperator H n-H‖+|r-1| *‖H‖ := by
      rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        ← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ ‖hankelRadialOperator H n-H‖+|r-1| *‖H‖ := by
      have hm : |r| * ‖hankelRadialOperator H n-H‖≤‖hankelRadialOperator H n-H‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (norm_nonneg (hankelRadialOperator H n-H))
      exact add_le_add hm le_rfl

theorem tendsto_norm_fullRadialSymbol_hankel_sub (a : BoundaryLInf) (φ ψ : Hardy)
    (ha : toL2 a=φ.val+star ψ.val) (hC : IsCompactOperator (boundedHankelOperator a)) :
    Tendsto (fun n => ‖continuousHankelSymbolMap (fullRadialSymbol φ ψ n)-boundedHankelOperator a‖)
      atTop (𝓝 0) := by
  have h1 := tendsto_norm_hankelRadialOperator_sub (boundedHankelOperator a) hC
  have h2 : Tendsto (fun n => |hankelRadius n-1| *‖boundedHankelOperator a‖) atTop (𝓝 0) := by
    have h := (((tendsto_hankelRadius.mono_right nhdsWithin_le_nhds).sub_const 1).abs).mul_const ‖boundedHankelOperator a‖
    simpa only [sub_self,abs_zero,zero_mul] using h
  apply squeeze_zero (fun n => norm_nonneg _) (fullRadialSymbol_hankel_error_le a φ ψ ha)
  simpa only [add_zero] using h1.add h2

/-- Norm-controlled continuous-symbol approximation of every compact represented bounded-symbol Hankel. -/
theorem exists_contracting_continuous_hankel_approximation (a : BoundaryLInf) (H : HankelOperator)
    (hH : RepresentsHankel (toL2 a) H) (hC : IsCompactOperator H) :
    ∃ b : ℕ → C(Boundary,ℂ),(∀ n,‖b n‖≤‖a‖) ∧
      (∀ n,IsCompactOperator (continuousHankelSymbolMap (b n))) ∧
      Tendsto (fun n => ‖continuousHankelSymbolMap (b n)-H‖) atTop (𝓝 0) := by
  have he : H=boundedHankelOperator a :=
    representsHankel_unique _ H _ hH (boundedHankelOperator_represents a)
  subst H
  obtain ⟨φ,ψ,ha⟩ := hardy_symbol_decomposition (toL2 a)
  exact ⟨fullRadialSymbol φ ψ, norm_fullRadialSymbol_le a φ ψ ha,
    (fun n => compact_continuousHankelSymbolMap _),
    tendsto_norm_fullRadialSymbol_hankel_sub a φ ψ ha hC⟩

theorem exists_contracting_continuous_hankel_approximation_lt (a : BoundaryLInf) (H : HankelOperator)
    (hH : RepresentsHankel (toL2 a) H) (hC : IsCompactOperator H) (ε : ℝ) (hε : 0<ε) :
    ∃ b : C(Boundary,ℂ),‖b‖≤‖a‖ ∧
      IsCompactOperator (continuousHankelSymbolMap b) ∧ ‖continuousHankelSymbolMap b-H‖<ε := by
  obtain ⟨b,hb,hbc,hbt⟩ := exists_contracting_continuous_hankel_approximation a H hH hC
  have he : ∀ᶠ n in atTop,‖continuousHankelSymbolMap (b n)-H‖<ε :=
    hbt.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨b n,hb n,hbc n,hn⟩

end TTO.Paper.Proved
