/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.DerivativeSzegoFrameFoundations
public import TTO.WeightedRadialRecoveryFoundations

/-! Pointwise identification of the actual derivative-kernel Hankel pairing.
This is an intermediate identity, with the operator matrix stated explicitly. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem sum_nat_succ_complex (n : ℕ) :
    (∑ i ∈ range (n+1), ((i : ℂ)+1)) = ((n : ℂ)+1)*((n : ℂ)+2)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ,ih]
    push_cast
    ring

theorem sum_antidiagonal_succ_product (n : ℕ) :
    (∑ p ∈ antidiagonal n, ((p.1 : ℂ)+1)*((p.2 : ℂ)+1)) =
      ((n : ℂ)+1)*((n : ℂ)+2)*((n : ℂ)+3)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.Nat.sum_antidiagonal_succ']
    have he : (∑ p ∈ antidiagonal n, ((p.1 : ℂ)+1)*(((p.2+1 : ℕ) : ℂ)+1)) =
        (∑ p ∈ antidiagonal n, ((p.1 : ℂ)+1)*((p.2 : ℂ)+1))+
          ∑ p ∈ antidiagonal n, ((p.1 : ℂ)+1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      push_cast
      ring
    rw [he,ih,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,sum_nat_succ_complex]
    push_cast
    ring

theorem diskTaylorCoeff_id_mul (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    diskTaylorCoeff (fun z => z*F z) (n+1) = diskTaylorCoeff F n := by
  unfold diskTaylorCoeff
  rw [iteratedDeriv_fun_mul (by fun_prop) hF.contDiffAt]
  have he : (∑ i ∈ range (n+1+1),
      ((n+1).choose i : ℂ)*iteratedDeriv i (fun z : ℂ => z) 0*
        iteratedDeriv (n+1-i) F 0) =
      ((n+1 : ℕ) : ℂ)*iteratedDeriv n F 0 := by
    rw [sum_eq_single 1]
    · simp only [iteratedDeriv_fun_id_zero,ite_true,mul_one,Nat.choose_one_right,
        Nat.add_sub_cancel]
    · intro i hi hi1
      rw [iteratedDeriv_fun_id_zero,ite_eq_right hi1,mul_zero,zero_mul]
    · intro h
      exact (h (mem_range.mpr (by omega))).elim
  rw [he,Nat.factorial_succ,Nat.cast_mul]
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp

theorem diskTaylorCoeff_radialEulerTransform (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G disk) (n : ℕ) :
    diskTaylorCoeff (radialEulerTransform G) n =
      (((n : ℂ)+3)/6)*diskTaylorCoeff G n := by
  have h0 : (0 : ℂ) ∈ disk := by norm_num [disk]
  have hG0 := hG 0 h0
  have hD0 := hG0.deriv
  have hZ0 : AnalyticAt ℂ (fun z => z*deriv G z) 0 := analyticAt_id.mul hD0
  have hAdd : iteratedDeriv n (fun z => z*deriv G z+3*G z) 0 =
      iteratedDeriv n (fun z => z*deriv G z) 0+3*iteratedDeriv n G 0 := by
    have he := iteratedDeriv_add (n := n) (f := fun z => z*deriv G z) (g := fun z => 3*G z)
      hZ0.contDiffAt ((analyticAt_const.mul hG0).contDiffAt)
    simpa only [Pi.add_apply,iteratedDeriv_const_mul_field] using! he
  have hLin : diskTaylorCoeff (radialEulerTransform G) n =
      (diskTaylorCoeff (fun z => z*deriv G z) n+3*diskTaylorCoeff G n)/6 := by
    unfold radialEulerTransform diskTaylorCoeff
    rw [iteratedDeriv_div_const,hAdd]
    ring
  rw [hLin]
  cases n with
  | zero => simp [diskTaylorCoeff]; ring
  | succ n =>
    rw [diskTaylorCoeff_id_mul _ hD0,diskTaylorCoeff_deriv]
    push_cast
    ring

theorem tsum_antidiagonal_of_summable (f : ℕ × ℕ → ℂ) (hf : Summable f) :
    (∑' i : ℕ, ∑' j : ℕ, f (i,j)) =
      ∑' n : ℕ, ∑ p ∈ antidiagonal n, f p := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hSigma : Summable (fun p : Σ n : ℕ, antidiagonal n => f p.2.val) := by
    exact e.summable_iff.mpr hf
  calc
    _ = ∑' p : ℕ × ℕ, f p := hf.tsum_prod.symm
    _ = ∑' p : Σ n : ℕ, antidiagonal n, f p.2.val := (e.tsum_eq f).symm
    _ = ∑' n : ℕ, ∑' p : antidiagonal n, f p.val :=
      Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hSigma
    _ = _ := by
      apply tsum_congr
      intro n
      exact (antidiagonal n).tsum_subtype f

theorem norm_hankelDerivative_term_le (g : BoundaryL2) (z : Disk) (i j : ℕ) :
    ‖(((i : ℂ)+1)*((j : ℂ)+1)*fourierCoeff g ((i+j+2 : ℕ) : ℤ))*z.val^(i+j)‖ ≤
      ‖g‖*((((i : ℝ)+1)*‖z.val‖^i)*(((j : ℝ)+1)*‖z.val‖^j)) := by
  have hn (n : ℕ) : ‖(n : ℂ)+1‖=(n : ℝ)+1 := by
    rw [show (n : ℂ)+1=((n+1 : ℕ) : ℂ) from by push_cast; rfl,Complex.norm_natCast]
    push_cast
    rfl
  calc
    _ = (((i : ℝ)+1)*((j : ℝ)+1)*‖fourierCoeff g ((i+j+2 : ℕ) : ℤ)‖)*‖z.val‖^(i+j) := by
      simp only [norm_mul,norm_pow,hn]
    _ ≤ (((i : ℝ)+1)*((j : ℝ)+1)*‖g‖)*‖z.val‖^(i+j) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_fourierCoeff_le g ((i+j+2 : ℕ) : ℤ))
          (mul_nonneg (by positivity) (by positivity))) (pow_nonneg (norm_nonneg z.val) (i+j))
    _ = _ := by rw [pow_add]; ring

/-- Absolute summability makes the antidiagonal regrouping an actual equality. -/
theorem summable_hankelDerivative_terms (g : BoundaryL2) (z : Disk) :
    Summable (fun p : ℕ × ℕ =>
      (((p.1 : ℂ)+1)*((p.2 : ℂ)+1)*fourierCoeff g ((p.1+p.2+2 : ℕ) : ℤ))*
        z.val^(p.1+p.2)) := by
  let c : ℕ → ℝ := fun n => ((n : ℝ)+1)*‖z.val‖^n
  have hc : Summable c := summable_nat_succ_geometric ‖z.val‖ (norm_nonneg z.val) z.property
  have hc0 (n : ℕ) : 0 ≤ c n :=
    mul_nonneg (by positivity) (pow_nonneg (norm_nonneg z.val) n)
  have hp : Summable (fun p : ℕ × ℕ => c p.1*c p.2) := hc.mul_of_nonneg hc hc0 hc0
  have hB : Summable (fun p : ℕ × ℕ => ‖g‖*(c p.1*c p.2)) := hp.mul_left ‖g‖
  exact Summable.of_norm_bounded hB (fun p => norm_hankelDerivative_term_le g z p.1 p.2)

/-- The matrix uses positive Fourier coefficients, as for the adjoint of the actual
two-step Hankel tail. No ideal membership is needed for this pointwise identity. -/
theorem hankel_derivative_pairing (A : Hardy →L[ℂ] Hardy) (g : BoundaryL2)
    (hA : ∀ i j : ℕ, inner ℂ (hardyBasis i) (A (hardyBasis j)) =
      fourierCoeff g ((i+j+2 : ℕ) : ℤ)) (z : Disk) :
    inner ℂ (derivativeSzegoKernel z)
        (A (derivativeSzegoKernel (szegoConjugatePoint z))) =
      radialEulerTransform (deriv (deriv (analyticValue g))) z.val := by
  let b : ℕ × ℕ → ℂ := fun p =>
    (((p.1 : ℂ)+1)*((p.2 : ℂ)+1)*fourierCoeff g ((p.1+p.2+2 : ℕ) : ℤ))*
      z.val^(p.1+p.2)
  have hrow (i : ℕ) :
      fourierCoeff (A (derivativeSzegoKernel (szegoConjugatePoint z))).val (i : ℤ) =
        ∑' j : ℕ, derivativeSzegoCoeff (szegoConjugatePoint z) j*
          fourierCoeff g ((i+j+2 : ℕ) : ℤ) := by
    rw [← hardyBasis_repr_eq_fourierCoeff,HilbertBasis.repr_apply_apply]
    change ((innerSL ℂ (hardyBasis i)).comp A)
      (derivativeSzegoKernel (szegoConjugatePoint z))=_
    rw [derivativeSzegoKernel,ContinuousLinearMap.map_tsum _
      (summable_derivativeSzegoKernel (szegoConjugatePoint z))]
    apply tsum_congr
    intro j
    change inner ℂ (hardyBasis i)
      (A (derivativeSzegoCoeff (szegoConjugatePoint z) j • hardyBasis j))=_
    rw [map_smul,inner_smul_right (𝕜 := ℂ) (E := Hardy),hA]
  have hpair : inner ℂ (derivativeSzegoKernel z)
      (A (derivativeSzegoKernel (szegoConjugatePoint z))) =
      ∑' i : ℕ, ∑' j : ℕ, b (i,j) := by
    rw [inner_derivativeSzegoKernel,derivativeSzegoValue]
    apply tsum_congr
    intro i
    rw [hrow,← tsum_mul_left,← tsum_mul_right]
    apply tsum_congr
    intro j
    simp only [derivativeSzegoCoeff,szegoConjugatePoint,Complex.conj_conj,b,pow_add]
    ring
  have hanti (n : ℕ) :
      (∑ p ∈ antidiagonal n, b p) =
      (((n : ℂ)+1)*((n : ℂ)+2)*((n : ℂ)+3)/6)*
        fourierCoeff g ((n+2 : ℕ) : ℤ)*z.val^n := by
    calc
      _ = (∑ p ∈ antidiagonal n, ((p.1 : ℂ)+1)*((p.2 : ℂ)+1))*
          fourierCoeff g ((n+2 : ℕ) : ℤ)*z.val^n := by
        rw [sum_mul,sum_mul]
        apply sum_congr rfl
        intro p hp
        have he := Finset.mem_antidiagonal.mp hp
        simp only [b,he]
      _ = _ := by rw [sum_antidiagonal_succ_product]
  have hG : AnalyticOnNhd ℂ (deriv (deriv (analyticValue g))) disk :=
    fun w hw => ((analyticOnNhd_analyticValue g w hw).deriv).deriv
  have hE := analyticOnNhd_radialEulerTransform _ hG
  have hcoef (n : ℕ) :
      diskTaylorCoeff (radialEulerTransform (deriv (deriv (analyticValue g)))) n =
      (((n : ℂ)+1)*((n : ℂ)+2)*((n : ℂ)+3)/6)*
        fourierCoeff g ((n+2 : ℕ) : ℤ) := by
    rw [diskTaylorCoeff_radialEulerTransform _ hG,diskTaylorCoeff_deriv,
      diskTaylorCoeff_deriv,diskTaylorCoeff_analyticValue]
    simp only [Nat.add_assoc,show (1:ℕ)+1=2 from rfl]
    push_cast
    ring
  rw [hpair,tsum_antidiagonal_of_summable b (summable_hankelDerivative_terms g z)]
  simp_rw [hanti]
  have hs := hasSum_diskTaylorCoeff _ hE z.property
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  rw [hcoef]


end TTO.Paper.Proved
