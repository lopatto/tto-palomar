/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto, The Tau Ceti contributors
-/
module

public import TTO.SchattenNormFoundations
public import Mathlib.Analysis.Complex.Hadamard

/-! Finite weighted orthonormal-pair dual estimates for a later Schatten interpolation proof.
No triangular-truncation or interpolation theorem is assumed here. -/

@[expose] public section
noncomputable section
open Filter Finset
open scoped NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- A complex scalar admits a norming phase, including the zero scalar. -/
theorem exists_complex_norming_phase (z : ℂ) :
    ∃ ρ : ℂ, ‖ρ‖ ≤ 1 ∧ ρ * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp only [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self hn]
    exact le_rfl
  · rw [div_mul_eq_mul_div, Complex.conj_mul']
    field_simp

/-- Complex prefix norm bounds survive nonnegative decreasing real weights.
The real Abel comparison is the already attributed weighted_prefix_comparison. -/
theorem complex_weighted_prefix_bound (z : ℕ → ℂ) (g w : ℕ → ℝ) (N : ℕ)
    (hprefix : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ ∑ i ∈ range k, g i)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ‖∑ i ∈ range N, (w i : ℂ) * z i‖ ≤ ∑ i ∈ range N, w i * g i := by
  obtain ⟨ρ, hρ, hrot⟩ := exists_complex_norming_phase
    (∑ i ∈ range N, (w i : ℂ) * z i)
  let f : ℕ → ℝ := fun i => (ρ * z i).re
  have hp (k : ℕ) (hk : k ≤ N) :
      ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i := by
    calc
      ∑ i ∈ range k, f i = (ρ * ∑ i ∈ range k, z i).re := by
        simp only [f, mul_sum, Complex.re_sum]
      _ ≤ ‖ρ * ∑ i ∈ range k, z i‖ := Complex.re_le_norm _
      _ = ‖ρ‖ * ‖∑ i ∈ range k, z i‖ := norm_mul _ _
      _ ≤ ‖∑ i ∈ range k, z i‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hρ
      _ ≤ ∑ i ∈ range k, g i := hprefix k hk
  have hreal : (∑ i ∈ range N, w i * f i) =
      ‖∑ i ∈ range N, (w i : ℂ) * z i‖ := by
    calc
      _ = (ρ * ∑ i ∈ range N, (w i : ℂ) * z i).re := by
        simp only [mul_sum, Complex.re_sum]
        apply sum_congr rfl
        intro i hi
        simp only [f, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        ring
      _ = _ := by rw [hrot]; rfl
  rw [← hreal]
  exact weighted_prefix_comparison hp hw hw0

section FinitePair
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- A decreasing weighted orthonormal-pair functional is bounded by the same singular weights. -/
theorem finite_weighted_orthonormalPair_bound (A : E →L[ℂ] F) {N : ℕ}
    (u : Fin N → F) (v : Fin N → E)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (w : ℕ → ℝ)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ‖∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))‖ ≤
      ∑ n ∈ range N, w n * (approximationNumber A n : ℝ) := by
  let z : ℕ → ℂ := fun n =>
    if hn : n < N then inner ℂ (u ⟨n,hn⟩) (A (v ⟨n,hn⟩)) else 0
  have hprefix (k : ℕ) (hk : k ≤ N) :
      ‖∑ n ∈ range k, z n‖ ≤ ∑ n ∈ range k, (approximationNumber A n : ℝ) := by
    let e : Fin k → Fin N := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) hij
    have h := finite_kyFan_upper A (u ∘ e) (v ∘ e) (hu.comp e he) (hv.comp e he)
    have hsum : (∑ n ∈ range k, z n) =
        ∑ i : Fin k, inner ℂ (u (e i)) (A (v (e i))) := by
      rw [← Fin.sum_univ_eq_sum_range z k]
      apply sum_congr rfl
      intro i hi
      simp only [z, dite_eq_left (lt_of_lt_of_le i.isLt hk), e]
    simpa only [hsum, Fintype.card_fin, Function.comp_apply] using h
  have hsum : (∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))) =
      ∑ n ∈ range N, (w n : ℂ) * z n := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => (w n : ℂ) * z n) N]
    apply sum_congr rfl
    intro i hi
    simp only [z, dite_eq_left i.isLt]
  rw [hsum]
  exact complex_weighted_prefix_bound z (fun n => (approximationNumber A n : ℝ))
    w N hprefix hw hw0

/-- Finite weighted orthonormal-pair Hölder estimate, without any trace-ideal hypothesis.
Weights need only be nonnegative and decreasing on their actual finite range. -/
theorem finite_weighted_orthonormalPair_holder (A : E →L[ℂ] F) {N : ℕ}
    (u : Fin N → F) (v : Fin N → E)
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (p q : ℝ) (hpq : p.HolderConjugate q) (w : ℕ → ℝ)
    (hw0 : ∀ i < N, 0 ≤ w i) (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) :
    ‖∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))‖ ≤
      (∑ n ∈ range N, w n^q)^(1/q) * schattenNorm p A := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.univ_eq_empty, sum_empty, norm_zero, range_zero]
    rw [Real.zero_rpow (one_div_ne_zero hpq.symm.pos.ne'), zero_mul]
  have hlast : 0 ≤ w (N-1) := hw0 _ (by omega)
  have hweighted := finite_weighted_orthonormalPair_bound A u v hu hv w hw hlast
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := range N)
    (f := w) (g := fun n => (approximationNumber A n : ℝ)) hpq.symm
    (fun i hi => hw0 i (mem_range.mp hi)) (fun i hi => (approximationNumber A i).coe_nonneg)
  have hpart : (∑ n ∈ range N, (approximationNumber A n : ℝ)^p)^(1/p) ≤ schattenNorm p A := by
    apply Real.rpow_le_rpow (sum_nonneg (fun i hi =>
      Real.rpow_nonneg (approximationNumber A i).coe_nonneg p)) _ (one_div_nonneg.mpr hpq.pos.le)
    exact Summable.sum_le_tsum _ (fun i hi =>
      Real.rpow_nonneg (approximationNumber A i).coe_nonneg p) (finiteDim_schatten A p hpq.pos).2.2
  exact (hweighted.trans hh).trans
    (mul_le_mul_of_nonneg_left hpart (Real.rpow_nonneg
      (sum_nonneg (fun i hi => Real.rpow_nonneg (hw0 i (mem_range.mp hi)) q)) _))

end FinitePair
/- The finite exponential-family formulas below adapt the narrow scalar part of
TauCeti/MeasureTheory/Integral/RieszThorin.lean, revision
d7dad3786f4cb95dbc0b2f5a2e47a989c1ebadad (Apache-2.0).
No Tau module is imported and no commutative interpolation theorem is assumed. -/
namespace FiniteThorin
open Complex

/-- A finite scalar Lp norm written without any measure-space carrier. -/
def vectorNorm {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℂ) : ℝ :=
  (∑ i, ‖x i‖^p)^(1/p)

/-- The actual bilinear finite-coordinate pairing used in the three-lines proof. -/
def pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (x : ι → ℂ) (y : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, M i j * x i * y j

/-- Complex powers with the original phase; zero coordinates stay zero. -/
def power (w c : ℂ) : ℂ :=
  c / (‖c‖ : ℂ) * exp (w * (Real.log ‖c‖ : ℂ))

@[simp] theorem power_one (c : ℂ) : power 1 c = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [power]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [power, one_mul, ← ofReal_exp, Real.exp_log hpos,
      div_mul_cancel₀ _ (ofReal_ne_zero.mpr hpos.ne')]

@[simp] theorem power_zero (w : ℂ) : power w 0 = 0 := by simp [power]

theorem norm_power_le (w c : ℂ) : ‖power w c‖ ≤ ‖c‖^w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [power_zero, norm_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [power, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul, Real.rpow_def_of_pos hpos]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact le_of_eq (congrArg Real.exp (mul_comm _ _))

theorem norm_power_le_exp (w c : ℂ) :
    ‖power w c‖ ≤ Real.exp (|w.re| * |Real.log ‖c‖|) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [power_zero, norm_zero]
    exact (Real.exp_pos _).le
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [power, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul]
    apply Real.exp_le_exp.mpr
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact (le_abs_self _).trans (abs_mul _ _).le

/-- An affine analytic exponent fixed to equal one at the interpolation point. -/
def exponent (p a₀ a₁ θ : ℝ) (z : ℂ) : ℂ :=
  1 + (z - (θ : ℂ)) * (p * (a₁-a₀) : ℝ)

@[simp] theorem exponent_self (p a₀ a₁ θ : ℝ) :
    exponent p a₀ a₁ θ (θ : ℂ) = 1 := by simp [exponent]

theorem exponent_re (p a₀ a₁ θ : ℝ) (z : ℂ) :
    (exponent p a₀ a₁ θ z).re = 1 + (z.re-θ)*(p*(a₁-a₀)) := by
  simp only [exponent, add_re, one_re, mul_re, sub_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero]

theorem exponent_re_left (p a₀ a₁ θ : ℝ)
    (hmean : p*((1-θ)*a₀+θ*a₁)=1) (z : ℂ) (hz : z.re=0) :
    (exponent p a₀ a₁ θ z).re = p*a₀ := by
  rw [exponent_re, hz]
  nlinarith [hmean]

theorem exponent_re_right (p a₀ a₁ θ : ℝ)
    (hmean : p*((1-θ)*a₀+θ*a₁)=1) (z : ℂ) (hz : z.re=1) :
    (exponent p a₀ a₁ θ z).re = p*a₁ := by
  rw [exponent_re, hz]
  nlinarith [hmean]

theorem abs_re_exponent_le (p a₀ a₁ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    |(exponent p a₀ a₁ θ z).re| ≤ 1+|p*(a₁-a₀)| := by
  rw [exponent_re]
  have hh : |z.re-θ| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hz.1,hθ.2], by linarith [hz.2,hθ.1]⟩
  calc
    _ ≤ |(1 : ℝ)|+|(z.re-θ)*(p*(a₁-a₀))| := abs_add_le _ _
    _ ≤ 1+1*|p*(a₁-a₀)| := by rw [abs_one, abs_mul]; gcongr
    _ = _ := by ring

theorem norm_power_exponent_le (p a₀ a₁ θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) :
    ‖power (exponent p a₀ a₁ θ z) c‖ ≤
      Real.exp ((1+|p*(a₁-a₀)|)*|Real.log ‖c‖|) :=
  (norm_power_le_exp _ _).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (abs_re_exponent_le p a₀ a₁ θ hθ hz) (abs_nonneg _)))

/-- The endpoint family has norm at most one by an actual finite power-sum estimate. -/
theorem vectorNorm_power_le_one {ι : Type*} [Fintype ι] (x : ι → ℂ)
    (p r : ℝ) (hr : 0 < r) (w : ℂ) (hw : w.re*r=p)
    (hx : ∑ i, ‖x i‖^p ≤ 1) :
    vectorNorm r (fun i => power w (x i)) ≤ 1 := by
  have hs : ∑ i, ‖power w (x i)‖^r ≤ 1 := by
    calc
      _ ≤ ∑ i, (‖x i‖^w.re)^r :=
        sum_le_sum (fun i _ => Real.rpow_le_rpow (norm_nonneg (power w (x i)))
          (norm_power_le w (x i)) hr.le)
      _ = ∑ i, ‖x i‖^p := by
        apply sum_congr rfl
        intro i hi
        rw [← Real.rpow_mul (norm_nonneg (x i)), hw]
      _ ≤ 1 := hx
  simpa only [vectorNorm, Real.one_rpow] using Real.rpow_le_rpow
    (sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) r)) hs
    (one_div_nonneg.mpr hr.le)

theorem vectorNorm_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℂ) :
    0 ≤ vectorNorm p x :=
  Real.rpow_nonneg (sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p)) _

/-- Endpoint control for a bilinear pairing of two finite unit vectors. -/
theorem pairing_le_of_unit_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (r s C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ x y, ‖pairing M x y‖ ≤ C * vectorNorm r x * vectorNorm s y)
    (x : ι → ℂ) (y : κ → ℂ)
    (hx : vectorNorm r x ≤ 1) (hy : vectorNorm s y ≤ 1) :
    ‖pairing M x y‖ ≤ C := by
  calc
    _ ≤ C * vectorNorm r x * vectorNorm s y := hB x y
    _ ≤ C * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hx hC) hy
      (vectorNorm_nonneg s y) (by simpa only [mul_one] using hC)
    _ = C := by ring

/-- A normalized finite-coordinate bilinear Thorin estimate.
Every analytic family and endpoint norm is explicit; no operator interpolation result is input. -/
theorem normalized_bilinear_interpolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (p₀ p₁ q₀ q₁ p q θ C₀ C₁ : ℝ)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p*((1-θ)*(1/p₀)+θ*(1/p₁))=1)
    (hq : q*((1-θ)*(1/q₀)+θ*(1/q₁))=1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (h₀ : ∀ x y, ‖pairing M x y‖ ≤ C₀ * vectorNorm p₀ x * vectorNorm q₀ y)
    (h₁ : ∀ x y, ‖pairing M x y‖ ≤ C₁ * vectorNorm p₁ x * vectorNorm q₁ y)
    (x : ι → ℂ) (y : κ → ℂ)
    (hx : ∑ i, ‖x i‖^p ≤ 1) (hy : ∑ j, ‖y j‖^q ≤ 1) :
    ‖pairing M x y‖ ≤ C₀^(1-θ) * C₁^θ := by
  let P := exponent p (1/p₀) (1/p₁) θ
  let Q := exponent q (1/q₀) (1/q₁) θ
  let Φ : ℂ → ℂ := fun z =>
    pairing M (fun i => power (P z) (x i)) (fun j => power (Q z) (y j))
  have hdiff : Differentiable ℂ Φ := by
    dsimp only [Φ, pairing, P, Q, exponent, power]
    fun_prop
  have hbdd : BddAbove ((norm ∘ Φ) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ i, ∑ j, ‖M i j‖ *
      Real.exp ((1+|p*((1/p₁)-(1/p₀))|)*|Real.log ‖x i‖|) *
      Real.exp ((1+|q*((1/q₁)-(1/q₀))|)*|Real.log ‖y j‖|), ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    change ‖Φ z‖ ≤ _
    have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
    dsimp only [Φ, pairing]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ =>
      (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_))
    rw [norm_mul, norm_mul]
    gcongr
    · exact norm_power_exponent_le p (1/p₀) (1/p₁) θ hθ hz' (x i)
    · exact norm_power_exponent_le q (1/q₀) (1/q₁) θ hθ hz' (y j)
  have hb₀ : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖Φ z‖ ≤ C₀ := by
    intro z hz
    change z.re=0 at hz
    apply pairing_le_of_unit_bounds M p₀ q₀ C₀ hC₀ h₀
    · apply vectorNorm_power_le_one x p p₀ hp₀ (P z) _ hx
      dsimp only [P]
      rw [exponent_re_left p (1/p₀) (1/p₁) θ hp z hz]
      field_simp
    · apply vectorNorm_power_le_one y q q₀ hq₀ (Q z) _ hy
      dsimp only [Q]
      rw [exponent_re_left q (1/q₀) (1/q₁) θ hq z hz]
      field_simp
  have hb₁ : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖Φ z‖ ≤ C₁ := by
    intro z hz
    change z.re=1 at hz
    apply pairing_le_of_unit_bounds M p₁ q₁ C₁ hC₁ h₁
    · apply vectorNorm_power_le_one x p p₁ hp₁ (P z) _ hx
      dsimp only [P]
      rw [exponent_re_right p (1/p₀) (1/p₁) θ hp z hz]
      field_simp
    · apply vectorNorm_power_le_one y q q₁ hq₁ (Q z) _ hy
      dsimp only [Q]
      rw [exponent_re_right q (1/q₀) (1/q₁) θ hq z hz]
      field_simp
  have key := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := Φ) (z := (θ : ℂ)) zero_lt_one
    (by simpa only [HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Complex.ofReal_re, Set.mem_Icc] using ⟨hθ.1.le,hθ.2.le⟩)
    hdiff.diffContOnCl hbdd hb₀ hb₁
  simpa only [Φ, P, Q, exponent_self, power_one, Complex.ofReal_re,
    sub_zero, div_one] using key

theorem vectorNorm_power_sum {ι : Type*} [Fintype ι]
    (p : ℝ) (hp : 0 < p) (x : ι → ℂ) :
    vectorNorm p x ^ p = ∑ i, ‖x i‖^p := by
  have hs : 0 ≤ ∑ i, ‖x i‖^p :=
    sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p)
  simpa only [vectorNorm, one_div] using Real.rpow_inv_rpow hs hp.ne'

theorem vectorNorm_mul {ι : Type*} [Fintype ι]
    (p : ℝ) (hp : 0 < p) (c : ℂ) (x : ι → ℂ) :
    vectorNorm p (fun i => c*x i) = ‖c‖*vectorNorm p x := by
  have hs : (∑ i, ‖c*x i‖^p) = ‖c‖^p * ∑ i, ‖x i‖^p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [norm_mul, Real.mul_rpow (norm_nonneg c) (norm_nonneg (x i))]
  unfold vectorNorm
  rw [hs, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p)
    (sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p))]
  congr 1
  simpa only [one_div] using Real.rpow_rpow_inv (norm_nonneg c) hp.ne'

theorem vectorNorm_eq_zero_iff {ι : Type*} [Fintype ι]
    (p : ℝ) (hp : 0 < p) (x : ι → ℂ) :
    vectorNorm p x=0 ↔ x=0 := by
  constructor
  · intro h
    have hs : ∑ i, ‖x i‖^p=0 := by
      rw [← vectorNorm_power_sum p hp x, h, Real.zero_rpow hp.ne']
    funext i
    by_contra hi
    have ht : ‖x i‖^p ≤ ∑ j, ‖x j‖^p :=
      single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg (x j)) p) (mem_univ i)
    have hp' := Real.rpow_pos_of_pos (norm_pos_iff.mpr hi) p
    linarith
  · rintro rfl
    simp only [vectorNorm, Pi.zero_apply, norm_zero, Real.zero_rpow hp.ne',
      sum_const_zero, Real.zero_rpow (one_div_ne_zero hp.ne')]

theorem normalized_power_sum {ι : Type*} [Fintype ι]
    (p : ℝ) (hp : 0 < p) (x : ι → ℂ) (hx : vectorNorm p x ≠ 0) :
    ∑ i, ‖(vectorNorm p x : ℂ)⁻¹*x i‖^p=1 := by
  rw [← vectorNorm_power_sum p hp, vectorNorm_mul p hp]
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (vectorNorm_nonneg p x),
    inv_mul_cancel₀ hx, Real.one_rpow]

theorem pairing_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (a b : ℂ) (x : ι → ℂ) (y : κ → ℂ) :
    pairing M (fun i => a*x i) (fun j => b*y j) = a*b*pairing M x y := by
  simp only [pairing, mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- Finite-coordinate bilinear interpolation for arbitrary vectors, with the sharp endpoint mean. -/
theorem bilinear_interpolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (p₀ p₁ q₀ q₁ p q θ C₀ C₁ : ℝ)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hp : 0 < p) (hq : 0 < q) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hpmean : p*((1-θ)*(1/p₀)+θ*(1/p₁))=1)
    (hqmean : q*((1-θ)*(1/q₀)+θ*(1/q₁))=1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (h₀ : ∀ x y, ‖pairing M x y‖ ≤ C₀ * vectorNorm p₀ x * vectorNorm q₀ y)
    (h₁ : ∀ x y, ‖pairing M x y‖ ≤ C₁ * vectorNorm p₁ x * vectorNorm q₁ y)
    (x : ι → ℂ) (y : κ → ℂ) :
    ‖pairing M x y‖ ≤ C₀^(1-θ)*C₁^θ*vectorNorm p x*vectorNorm q y := by
  by_cases hx : vectorNorm p x=0
  · have hx' := (vectorNorm_eq_zero_iff p hp x).mp hx
    rw [hx, hx']
    simp only [pairing, Pi.zero_apply, mul_zero, zero_mul, sum_const_zero, norm_zero, le_refl]
  by_cases hy : vectorNorm q y=0
  · have hy' := (vectorNorm_eq_zero_iff q hq y).mp hy
    rw [hy, hy']
    simp only [pairing, Pi.zero_apply, mul_zero, sum_const_zero, norm_zero, le_refl]
  have hnx : 0 < vectorNorm p x := lt_of_le_of_ne (vectorNorm_nonneg p x) (Ne.symm hx)
  have hny : 0 < vectorNorm q y := lt_of_le_of_ne (vectorNorm_nonneg q y) (Ne.symm hy)
  let x' : ι → ℂ := fun i => (vectorNorm p x : ℂ)⁻¹*x i
  let y' : κ → ℂ := fun j => (vectorNorm q y : ℂ)⁻¹*y j
  have key := normalized_bilinear_interpolation M p₀ p₁ q₀ q₁ p q θ C₀ C₁
    hp₀ hp₁ hq₀ hq₁ hθ hpmean hqmean hC₀ hC₁ h₀ h₁ x' y'
    (normalized_power_sum p hp x hx).le (normalized_power_sum q hq y hy).le
  have he : ‖pairing M x' y'‖ = ‖pairing M x y‖/(vectorNorm p x*vectorNorm q y) := by
    dsimp only [x',y']
    rw [pairing_mul,norm_mul,norm_mul,norm_inv,norm_inv,
      Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hnx.le,Real.norm_of_nonneg hny.le]
    ring
  rw [he] at key
  have hk := (div_le_iff₀ (mul_pos hnx hny)).mp key
  simpa only [mul_assoc] using hk

end FiniteThorin
section BesselPair
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The finite Ky Fan bound also accepts contractive Bessel families, retaining zero columns.
This proof is the existing native finite_kyFan_upper proof with its actual Bessel uses explicit. -/
theorem finite_kyFan_bessel_upper {ι : Type*} [Fintype ι] (A : E →L[ℂ] F)
    (u : ι → F) (v : ι → E)
    (huB : ∀ x : F, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2)
    (hvB : ∀ x : E, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2)
    (huN : ∀ i, ‖u i‖ ≤ 1) (hvN : ∀ i, ‖v i‖ ≤ 1) :
    ‖∑ i, inner ℂ (u i) (A (v i))‖ ≤
      ∑ n ∈ Finset.range (Fintype.card ι), (approximationNumber A n : ℝ) := by
  classical
  let a : Fin (Module.finrank ℂ E) → ℝ := fun j => ∑ i, ‖inner ℂ (gramBasis A j) (v i)‖^2
  let b : Fin (Module.finrank ℂ E) → ℝ := fun j =>
    ∑ i, ‖inner ℂ (NormedSpace.normalize (A (gramBasis A j))) (u i)‖^2
  have ha1 (j) : a j ≤ 1 := by
    have h := hvB (gramBasis A j)
    simpa [a,norm_inner_symm,(gramBasis A).norm_eq_one] using h
  have hb1 (j) : b j ≤ 1 := by
    have h := huB (NormedSpace.normalize (A (gramBasis A j)))
    have hn : ‖NormedSpace.normalize (A (gramBasis A j))‖ ≤ 1 := by
      by_cases hz : A (gramBasis A j) = 0
      · simp [hz]
      · rw [NormedSpace.norm_normalize hz]
    have hb : b j ≤ ‖NormedSpace.normalize (A (gramBasis A j))‖^2 := by
      simpa [b,norm_inner_symm] using h
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hn)
  have hasum : ∑ j, a j ≤ Fintype.card ι := by
    simp only [a]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ‖v i‖^2 := Finset.sum_congr rfl (fun i _ =>
        (gramBasis A).sum_sq_norm_inner_right (v i))
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ =>
        pow_le_one₀ (norm_nonneg (v i)) (hvN i))
      _ = _ := by simp
  have hbsum : ∑ j, b j ≤ Fintype.card ι := by
    simp only [b]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        exact (normalizedFamily_bessel (fun j => A (gramBasis A j))
          (gramBasis_images_orthogonal A) (u i)).trans
            (pow_le_one₀ (norm_nonneg (u i)) (huN i)))
      _ = _ := by simp
  apply le_trans ?_ (approximation_weight_bound A (Fintype.card ι) (fun j => (a j+b j)/2)
    (fun j => by dsimp [a,b]; positivity) (fun j => by linarith [ha1 j,hb1 j])
    (by rw [← Finset.sum_div,Finset.sum_add_distrib]; linarith))
  calc
    _ = ‖∑ j : Fin (Module.finrank ℂ E), (‖A (gramBasis A j)‖ : ℂ)*
        ∑ i, inner ℂ (gramBasis A j) (v i)*inner ℂ (u i) (NormedSpace.normalize (A (gramBasis A j)))‖ := by
      congr 1
      have he (i : ι) : inner ℂ (u i) (A (v i)) =
          ∑ j : Fin (Module.finrank ℂ E),
            (inner ℂ (gramBasis A j) (v i)*(‖A (gramBasis A j)‖ : ℂ))*
              inner ℂ (u i) (NormedSpace.normalize (A (gramBasis A j))) := by
        rw [gramBasis_expansion A (v i),inner_sum]
        exact Finset.sum_congr rfl (fun j _ => inner_smul_right _ _ _)
      simp_rw [he,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j : Fin (Module.finrank ℂ E), (approximationNumber A j : ℝ)*((a j+b j)/2) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Complex.norm_real,norm_norm,approximationNumber_gramBasis]
      apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
      simp only [a,b,← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_inner_symm (u i)]
      nlinarith [two_mul_le_add_sq ‖inner ℂ (gramBasis A j) (v i)‖
        ‖inner ℂ (NormedSpace.normalize (A (gramBasis A j))) (u i)‖]


theorem finite_weighted_besselPair_bound (A : E →L[ℂ] F) {N : ℕ}
    (u : Fin N → F) (v : Fin N → E)
    (huB : ∀ x : F, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2)
    (hvB : ∀ x : E, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2)
    (huN : ∀ i, ‖u i‖ ≤ 1) (hvN : ∀ i, ‖v i‖ ≤ 1) (w : ℕ → ℝ)
    (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) (hw0 : 0 ≤ w (N-1)) :
    ‖∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))‖ ≤
      ∑ n ∈ range N, w n * (approximationNumber A n : ℝ) := by
  let z : ℕ → ℂ := fun n =>
    if hn : n < N then inner ℂ (u ⟨n,hn⟩) (A (v ⟨n,hn⟩)) else 0
  have hprefix (k : ℕ) (hk : k ≤ N) :
      ‖∑ n ∈ range k, z n‖ ≤ ∑ n ∈ range k, (approximationNumber A n : ℝ) := by
    let e : Fin k → Fin N := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin N => x.val) hij
    have huB' (x : F) : ∑ i : Fin k, ‖inner ℂ (u (e i)) x‖^2 ≤ ‖x‖^2 := by
      apply le_trans (sum_le_sum_of_injOn (s := univ) (t := univ)
        (f := fun i : Fin k => ‖inner ℂ (u (e i)) x‖^2)
        (g := fun i : Fin N => ‖inner ℂ (u i) x‖^2) e he.injOn
        (subset_univ _) (fun i hi => le_rfl) (fun i hi _ => sq_nonneg _)) (huB x)
    have hvB' (x : E) : ∑ i : Fin k, ‖inner ℂ (v (e i)) x‖^2 ≤ ‖x‖^2 := by
      apply le_trans (sum_le_sum_of_injOn (s := univ) (t := univ)
        (f := fun i : Fin k => ‖inner ℂ (v (e i)) x‖^2)
        (g := fun i : Fin N => ‖inner ℂ (v i) x‖^2) e he.injOn
        (subset_univ _) (fun i hi => le_rfl) (fun i hi _ => sq_nonneg _)) (hvB x)
    have h := finite_kyFan_bessel_upper A (u ∘ e) (v ∘ e) huB' hvB'
      (fun i => huN (e i)) (fun i => hvN (e i))
    have hsum : (∑ n ∈ range k, z n) =
        ∑ i : Fin k, inner ℂ (u (e i)) (A (v (e i))) := by
      rw [← Fin.sum_univ_eq_sum_range z k]
      apply sum_congr rfl
      intro i hi
      simp only [z, dite_eq_left (lt_of_lt_of_le i.isLt hk), e]
    simpa only [hsum, Fintype.card_fin, Function.comp_apply] using h
  have hsum : (∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))) =
      ∑ n ∈ range N, (w n : ℂ) * z n := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => (w n : ℂ) * z n) N]
    apply sum_congr rfl
    intro i hi
    simp only [z, dite_eq_left i.isLt]
  rw [hsum]
  exact complex_weighted_prefix_bound z (fun n => (approximationNumber A n : ℝ))
    w N hprefix hw hw0

/-- Finite weighted orthonormal-pair Hölder estimate, without any trace-ideal hypothesis.
Weights need only be nonnegative and decreasing on their actual finite range. -/
theorem finite_weighted_besselPair_holder (A : E →L[ℂ] F) {N : ℕ}
    (u : Fin N → F) (v : Fin N → E)
    (huB : ∀ x : F, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2)
    (hvB : ∀ x : E, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2)
    (huN : ∀ i, ‖u i‖ ≤ 1) (hvN : ∀ i, ‖v i‖ ≤ 1)
    (p q : ℝ) (hpq : p.HolderConjugate q) (w : ℕ → ℝ)
    (hw0 : ∀ i < N, 0 ≤ w i) (hw : ∀ i, i+1 < N → w (i+1) ≤ w i) :
    ‖∑ i : Fin N, (w i : ℂ) * inner ℂ (u i) (A (v i))‖ ≤
      (∑ n ∈ range N, w n^q)^(1/q) * schattenNorm p A := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.univ_eq_empty, sum_empty, norm_zero, range_zero]
    rw [Real.zero_rpow (one_div_ne_zero hpq.symm.pos.ne'), zero_mul]
  have hlast : 0 ≤ w (N-1) := hw0 _ (by omega)
  have hweighted := finite_weighted_besselPair_bound A u v huB hvB huN hvN w hw hlast
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := range N)
    (f := w) (g := fun n => (approximationNumber A n : ℝ)) hpq.symm
    (fun i hi => hw0 i (mem_range.mp hi)) (fun i hi => (approximationNumber A i).coe_nonneg)
  have hpart : (∑ n ∈ range N, (approximationNumber A n : ℝ)^p)^(1/p) ≤ schattenNorm p A := by
    apply Real.rpow_le_rpow (sum_nonneg (fun i hi =>
      Real.rpow_nonneg (approximationNumber A i).coe_nonneg p)) _ (one_div_nonneg.mpr hpq.pos.le)
    exact Summable.sum_le_tsum _ (fun i hi =>
      Real.rpow_nonneg (approximationNumber A i).coe_nonneg p) (finiteDim_schatten A p hpq.pos).2.2
  exact (hweighted.trans hh).trans
    (mul_le_mul_of_nonneg_left hpart (Real.rpow_nonneg
      (sum_nonneg (fun i hi => Real.rpow_nonneg (hw0 i (mem_range.mp hi)) q)) _))

/-- The first-slot phase that turns a complex coefficient into its nonnegative modulus. -/
def coefficientAntiPhase (c : ℂ) : ℂ := conj c / (‖c‖ : ℂ)

theorem norm_coefficientAntiPhase_le (c : ℂ) : ‖coefficientAntiPhase c‖ ≤ 1 := by
  by_cases hc : c=0
  · simp only [coefficientAntiPhase, hc, map_zero, norm_zero, Complex.ofReal_zero, zero_div]
    norm_num
  · have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    simp only [coefficientAntiPhase, norm_div, Complex.norm_conj, Complex.norm_real,
      norm_norm, div_self hn]
    exact le_rfl

theorem coefficientAntiPhase_identity (c : ℂ) :
    (‖c‖ : ℂ)*conj (coefficientAntiPhase c)=c := by
  by_cases hc : c=0
  · simp only [coefficientAntiPhase,hc,map_zero,norm_zero,Complex.ofReal_zero,zero_div,zero_mul]
  · have hn : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
    simp only [coefficientAntiPhase, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp

/-- The full complex-coefficient finite Hölder bound for contractive Bessel test families.
Sorting only finitely many scalar moduli preserves all zero columns and empty cases. -/
theorem finite_besselPair_complex_holder (A : E →L[ℂ] F) {N : ℕ}
    (u : Fin N → F) (v : Fin N → E)
    (huB : ∀ x : F, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2)
    (hvB : ∀ x : E, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2)
    (huN : ∀ i, ‖u i‖ ≤ 1) (hvN : ∀ i, ‖v i‖ ≤ 1)
    (p q : ℝ) (hpq : p.HolderConjugate q) (c : Fin N → ℂ) :
    ‖∑ i, c i * inner ℂ (u i) (A (v i))‖ ≤
      FiniteThorin.vectorNorm q c * schattenNorm p A := by
  classical
  let σ := Tuple.sort (α := OrderDual ℝ) (fun i : Fin N => ‖c i‖)
  let u' : Fin N → F := fun i => coefficientAntiPhase (c (σ i)) • u (σ i)
  let v' : Fin N → E := v ∘ σ
  let w : ℕ → ℝ := fun n => if hn : n<N then ‖c (σ ⟨n,hn⟩)‖ else 0
  have hwAt (i : Fin N) : w i=‖c (σ i)‖ := by simp only [w,dite_eq_left i.isLt]
  have huN' (i : Fin N) : ‖u' i‖ ≤ 1 := by
    dsimp only [u']
    rw [norm_smul]
    calc
      _ ≤ 1*1 := mul_le_mul (norm_coefficientAntiPhase_le _) (huN (σ i))
        (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have huB' (x : F) : ∑ i, ‖inner ℂ (u' i) x‖^2 ≤ ‖x‖^2 := by
    calc
      _ ≤ ∑ i, ‖inner ℂ (u (σ i)) x‖^2 := by
        apply sum_le_sum
        intro i hi
        have hn : ‖inner ℂ (u' i) x‖ ≤ ‖inner ℂ (u (σ i)) x‖ := by
          dsimp only [u']
          rw [inner_smul_left,norm_mul,Complex.norm_conj]
          exact mul_le_of_le_one_left (norm_nonneg _) (norm_coefficientAntiPhase_le _)
        exact pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = ∑ i, ‖inner ℂ (u i) x‖^2 := Equiv.sum_comp σ (fun i : Fin N => ‖inner ℂ (u i) x‖^2)
      _ ≤ ‖x‖^2 := huB x
  have hvB' (x : E) : ∑ i, ‖inner ℂ (v' i) x‖^2 ≤ ‖x‖^2 := by
    change (∑ i, ‖inner ℂ (v (σ i)) x‖^2) ≤ ‖x‖^2
    rw [Equiv.sum_comp σ (fun i : Fin N => ‖inner ℂ (v i) x‖^2)]
    exact hvB x
  have hvN' (i : Fin N) : ‖v' i‖ ≤ 1 := hvN (σ i)
  have hw0 (i : ℕ) (hi : i<N) : 0 ≤ w i := by
    simp only [w,dite_eq_left hi]; exact norm_nonneg _
  have hanti : Antitone (fun i : Fin N => ‖c (σ i)‖) :=
    Tuple.monotone_sort (α := OrderDual ℝ) (fun i : Fin N => ‖c i‖)
  have hw (i : ℕ) (hi : i+1<N) : w (i+1) ≤ w i := by
    have hi' : i<N := by omega
    simp only [w,dite_eq_left hi,dite_eq_left hi']
    exact hanti (show (⟨i,hi'⟩ : Fin N) ≤ ⟨i+1,hi⟩ by exact Nat.le_succ i)
  have he : (∑ i, c i*inner ℂ (u i) (A (v i))) =
      ∑ i : Fin N, (w i : ℂ)*inner ℂ (u' i) (A (v' i)) := by
    rw [← Equiv.sum_comp σ (fun i => c i*inner ℂ (u i) (A (v i)))]
    apply sum_congr rfl
    intro i hi
    simp only [u',v',Function.comp_apply,hwAt,inner_smul_left]
    rw [← mul_assoc,coefficientAntiPhase_identity]
  have hs : (∑ n ∈ range N, w n^q) = ∑ i, ‖c i‖^q := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => w n^q) N]
    simp only [hwAt]
    exact Equiv.sum_comp σ (fun i : Fin N => ‖c i‖^q)
  rw [he]
  have h := finite_weighted_besselPair_holder A u' v' huB' hvB' huN' hvN' p q hpq w hw0 hw
  simpa only [hs,FiniteThorin.vectorNorm] using h

end BesselPair
section FiniteCoefficientOperators
open Reduction
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

def finiteSequenceWeights {N : ℕ} (c : Fin N → ℂ) (n : ℕ) : ℂ :=
  if hn : n<N then c ⟨n,hn⟩ else 0

def finiteSequenceDiagonal {N : ℕ} (c : Fin N → ℂ) : SequenceOperator :=
  diagonalTruncation (finiteSequenceWeights c) (range N)

@[simp] theorem finiteSequenceDiagonal_single {N : ℕ} (c : Fin N → ℂ) (i : Fin N) :
    finiteSequenceDiagonal c (lp.single 2 i.val (1 : ℂ)) =
      c i • (lp.single 2 i.val (1 : ℂ) : SequenceL2) := by
  have h := diagonalTruncation_isDiagonal (finiteSequenceWeights c) (range N) i.val
  simpa [finiteSequenceDiagonal,finiteSequenceWeights,i.isLt] using h

theorem finiteSequenceDiagonal_schatten {N : ℕ} (c : Fin N → ℂ)
    (p : ℝ) (hp : 0 < p) : Schatten p (finiteSequenceDiagonal c) := by
  apply finiteRankSchatten _ ⟨N,?_⟩ p hp
  simpa only [finiteSequenceDiagonal,card_range] using
    rank_diagonalTruncation_le (finiteSequenceWeights c) (range N)

theorem schattenNorm_finiteSequenceDiagonal {N : ℕ} (c : Fin N → ℂ)
    (p : ℝ) (hp : 0 < p) :
    schattenNorm p (finiteSequenceDiagonal c) = FiniteThorin.vectorNorm p c := by
  unfold schattenNorm finiteSequenceDiagonal FiniteThorin.vectorNorm
  rw [diagonalTruncation_power_sum _ N p hp]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun n => ‖finiteSequenceWeights c n‖^p) N]
  apply sum_congr rfl
  intro i hi
  simp only [finiteSequenceWeights,dite_eq_left i.isLt]

/-- Replace only the singular coefficients of A, using its actual finite Gram contractions. -/
def gramCoefficientOperator (A : E →L[ℂ] F)
    (c : Fin (Module.finrank ℂ E) → ℂ) : E →L[ℂ] F :=
  (finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint ∘L
    finiteSequenceDiagonal c ∘L finiteAnalysis (fun i => gramBasis A i)

@[simp] theorem gramCoefficientOperator_column (A : E →L[ℂ] F)
    (c : Fin (Module.finrank ℂ E) → ℂ) (i : Fin (Module.finrank ℂ E)) :
    gramCoefficientOperator A c (gramBasis A i) =
      c i • NormedSpace.normalize (A (gramBasis A i)) := by
  simp only [gramCoefficientOperator, ContinuousLinearMap.comp_apply,
    finiteAnalysis_orthonormal_column _ (gramBasis A).orthonormal,
    finiteSequenceDiagonal_single,map_smul,finiteAnalysis_adjoint_single]

theorem gramCoefficientOperator_actual (A : E →L[ℂ] F) :
    gramCoefficientOperator A (fun i => (‖A (gramBasis A i)‖ : ℂ)) = A := by
  apply ContinuousLinearMap.coe_injective
  apply (gramBasis A).toBasis.ext
  intro i
  exact (gramCoefficientOperator_column A _ i).trans (complex_norm_smul_normalize _)

/-- The coefficient replacement is an actual complex-linear map. -/
def gramCoefficientLinear (A : E →L[ℂ] F) :
    (Fin (Module.finrank ℂ E) → ℂ) →ₗ[ℂ] (E →L[ℂ] F) where
  toFun := gramCoefficientOperator A
  map_add' c d := by
    apply ContinuousLinearMap.coe_injective
    apply (gramBasis A).toBasis.ext
    intro i
    change gramCoefficientOperator A (c+d) (gramBasis A i) =
      gramCoefficientOperator A c (gramBasis A i)+gramCoefficientOperator A d (gramBasis A i)
    simp only [gramCoefficientOperator_column,Pi.add_apply,add_smul]
  map_smul' a c := by
    apply ContinuousLinearMap.coe_injective
    apply (gramBasis A).toBasis.ext
    intro i
    change gramCoefficientOperator A (a • c) (gramBasis A i) =
      a • gramCoefficientOperator A c (gramBasis A i)
    simp only [gramCoefficientOperator_column,Pi.smul_apply,smul_eq_mul,mul_smul]

theorem schattenNorm_gramCoefficient_le (A : E →L[ℂ] F)
    (c : Fin (Module.finrank ℂ E) → ℂ) (p : ℝ) (hp : 0 < p) :
    schattenNorm p (gramCoefficientOperator A c) ≤ FiniteThorin.vectorNorm p c := by
  have hD := finiteSequenceDiagonal_schatten c p hp
  have hC := (gramBasis_analysis_contractions A).2
  have hR := (gramBasis_analysis_contractions A).1
  have hC' : ‖(finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint‖ ≤ 1 :=
    (ContinuousLinearMap.adjoint.norm_map _).trans_le hC
  have hprod : ‖(finiteAnalysis (fun i => NormedSpace.normalize (A (gramBasis A i)))).adjoint‖ *
      ‖finiteAnalysis (fun i => gramBasis A i)‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hC' hR (norm_nonneg _) zero_le_one
  calc
    _ ≤ _ := schattenNorm_comp_le hD _ _
    _ ≤ 1*schattenNorm p (finiteSequenceDiagonal c) :=
      mul_le_mul_of_nonneg_right hprod (Reduction.schattenNorm_nonneg p _)
    _ = _ := by rw [one_mul,schattenNorm_finiteSequenceDiagonal c p hp]

/-- Finite Bessel-pair tests recover the actual Schatten norm, by explicit singular-power weights. -/
theorem schattenNorm_le_of_besselPair_bounds (A : E →L[ℂ] F) (p q C : ℝ)
    (hpq : p.HolderConjugate q) (hC : 0 ≤ C)
    (h : ∀ (N : ℕ) (u : Fin N → F) (v : Fin N → E),
      (∀ x : F, ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2) →
      (∀ x : E, ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2) →
      (∀ i, ‖u i‖ ≤ 1) → (∀ i, ‖v i‖ ≤ 1) → ∀ c : Fin N → ℂ,
      ‖∑ i, c i*inner ℂ (u i) (A (v i))‖ ≤ C*FiniteThorin.vectorNorm q c) :
    schattenNorm p A ≤ C := by
  let σ : Fin (Module.finrank ℂ E) → ℝ := fun i => ‖A (gramBasis A i)‖
  let S : ℝ := ∑ i, σ i^p
  have hS : 0 ≤ S := sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) p)
  let u : Fin (Module.finrank ℂ E) → F := fun i => NormedSpace.normalize (A (gramBasis A i))
  let v : Fin (Module.finrank ℂ E) → E := fun i => gramBasis A i
  have huB (x : F) : ∑ i, ‖inner ℂ (u i) x‖^2 ≤ ‖x‖^2 :=
    normalizedFamily_bessel _ (gramBasis_images_orthogonal A) x
  have hvB (x : E) : ∑ i, ‖inner ℂ (v i) x‖^2 ≤ ‖x‖^2 :=
    ((gramBasis A).sum_sq_norm_inner_right x).le
  have huN (i) : ‖u i‖ ≤ 1 := by
    dsimp only [u]
    by_cases hi : A (gramBasis A i)=0
    · simp [hi,NormedSpace.normalize]
    · rw [NormedSpace.norm_normalize hi]
  have hvN (i) : ‖v i‖ ≤ 1 := (gramBasis A).norm_eq_one i |>.le
  let c : Fin (Module.finrank ℂ E) → ℂ := fun i => (σ i^(p-1) : ℝ)
  have hc : FiniteThorin.vectorNorm q c = S^(1/q) := by
    unfold FiniteThorin.vectorNorm
    congr 1
    apply sum_congr rfl
    intro i hi
    dsimp only [c]
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul (norm_nonneg _),hpq.sub_one_mul_conj]
  have ht (i) : σ i^(p-1)*σ i=σ i^p := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one' (norm_nonneg (A (gramBasis A i)))
        (by linarith [hpq.pos] : p-1+1 ≠ 0)).symm
  have hpairs : ‖∑ i, c i*inner ℂ (u i) (A (v i))‖ = S := by
    calc
      _ = ‖∑ i, ((σ i^p : ℝ) : ℂ)‖ := by
        congr 1
        apply sum_congr rfl
        intro i hi
        simp only [u,v,inner_normalize_self,c]
        exact_mod_cast ht i
      _ = S := by
        rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_of_nonneg hS]
  have hNorm : schattenNorm p A=S^(1/p) := by
    unfold schattenNorm
    rw [finiteGram_power_sum A p hpq.pos]
  have key := h (Module.finrank ℂ E) u v huB hvB huN hvN c
  rw [hpairs,hc] at key
  by_cases hz : S=0
  · rw [hNorm,hz,Real.zero_rpow (one_div_ne_zero hpq.pos.ne')]
    exact hC
  have hspos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have hsplit : S^(1/p)*S^(1/q)=S := by
    rw [← Real.rpow_add_of_nonneg hS (one_div_nonneg.mpr hpq.pos.le)
      (one_div_nonneg.mpr hpq.symm.pos.le)]
    simp only [one_div,hpq.inv_add_inv_eq_one,Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hspos (1/q))).mp
  rw [hNorm,hsplit]
  exact key

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- Scalar coordinates of an actual complex-linear operator-valued map expand into a finite matrix. -/
theorem finite_pairing_matrix {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (L : (ι → ℂ) →ₗ[ℂ] (E →L[ℂ] F)) (u : κ → F) (v : κ → E)
    (x : ι → ℂ) (y : κ → ℂ) :
    FiniteThorin.pairing (fun i j => inner ℂ (u j) (L (Pi.single i 1) (v j))) x y =
      ∑ j, y j*inner ℂ (u j) (L x (v j)) := by
  classical
  have hx : x=∑ i, x i • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  have hLx : L x=∑ i, x i • L (Pi.single i 1) := by
    calc
      L x=L (∑ i, x i • (Pi.single i (1 : ℂ) : ι → ℂ)) := congrArg L hx
      _ = _ := by rw [map_sum]; simp only [map_smul]
  rw [hLx]
  simp only [FiniteThorin.pairing,_root_.sum_apply,_root_.smul_apply,
    inner_sum,inner_smul_right]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

end FiniteCoefficientOperators
section FiniteSchattenInterpolation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- Finite Schatten interpolation, proved through actual singular-coordinate maps and scalar Thorin.
There is no Schatten-carrier interpolation or trace-duality assumption. -/
theorem finiteSchatten_interpolation
    (T : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (p₀ p₁ p θ C₀ C₁ : ℝ)
    (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp : 1 < p)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hpmean : p*((1-θ)*(1/p₀)+θ*(1/p₁))=1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (h₀ : ∀ A : H →L[ℂ] H, schattenNorm p₀ (T A) ≤ C₀*schattenNorm p₀ A)
    (h₁ : ∀ A : H →L[ℂ] H, schattenNorm p₁ (T A) ≤ C₁*schattenNorm p₁ A)
    (A : H →L[ℂ] H) :
    schattenNorm p (T A) ≤ C₀^(1-θ)*C₁^θ*schattenNorm p A := by
  let q₀ := Real.conjExponent p₀
  let q₁ := Real.conjExponent p₁
  let q := Real.conjExponent p
  have hp₀q₀ : p₀.HolderConjugate q₀ := Real.HolderConjugate.conjExponent hp₀
  have hp₁q₁ : p₁.HolderConjugate q₁ := Real.HolderConjugate.conjExponent hp₁
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hpi : (1-θ)*(1/p₀)+θ*(1/p₁)=p⁻¹ := by
    apply mul_left_cancel₀ hpq.pos.ne'
    simpa only [mul_inv_cancel₀ hpq.pos.ne'] using hpmean
  have hqi : (1-θ)*(1/q₀)+θ*(1/q₁)=q⁻¹ := by
    simp only [one_div] at hpi ⊢
    have h₀i : q₀⁻¹=1-p₀⁻¹ := by linarith [hp₀q₀.inv_add_inv_eq_one]
    have h₁i : q₁⁻¹=1-p₁⁻¹ := by linarith [hp₁q₁.inv_add_inv_eq_one]
    have hi : q⁻¹=1-p⁻¹ := by linarith [hpq.inv_add_inv_eq_one]
    rw [h₀i,h₁i,hi]
    nlinarith [hpi]
  have hqmean : q*((1-θ)*(1/q₀)+θ*(1/q₁))=1 := by
    rw [hqi,mul_inv_cancel₀ hpq.symm.pos.ne']
  apply schattenNorm_le_of_besselPair_bounds (T A) p q
    (C₀^(1-θ)*C₁^θ*schattenNorm p A) hpq
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hC₀ _) (Real.rpow_nonneg hC₁ _))
      (Reduction.schattenNorm_nonneg p A))
  intro N u v huB hvB huN hvN c
  let L := T.comp (gramCoefficientLinear A)
  let M : Fin (Module.finrank ℂ H) → Fin N → ℂ := fun i j =>
    inner ℂ (u j) (L (Pi.single i 1) (v j))
  have hPair (x : Fin (Module.finrank ℂ H) → ℂ) (y : Fin N → ℂ) :
      FiniteThorin.pairing M x y = ∑ j, y j*inner ℂ (u j) (L x (v j)) :=
    finite_pairing_matrix L u v x y
  have endpoint (r s C : ℝ) (hrs : r.HolderConjugate s) (hC : 0 ≤ C)
      (hT : ∀ B : H →L[ℂ] H, schattenNorm r (T B) ≤ C*schattenNorm r B)
      (x : Fin (Module.finrank ℂ H) → ℂ) (y : Fin N → ℂ) :
      ‖FiniteThorin.pairing M x y‖ ≤
        C*FiniteThorin.vectorNorm r x*FiniteThorin.vectorNorm s y := by
    rw [hPair]
    apply (finite_besselPair_complex_holder (L x) u v huB hvB huN hvN r s hrs y).trans
    have hcomp : schattenNorm r (L x) ≤ C*FiniteThorin.vectorNorm r x := by
      exact (hT (gramCoefficientOperator A x)).trans
        (mul_le_mul_of_nonneg_left (schattenNorm_gramCoefficient_le A x r hrs.pos) hC)
    have hm := mul_le_mul_of_nonneg_left hcomp (FiniteThorin.vectorNorm_nonneg s y)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
  let x : Fin (Module.finrank ℂ H) → ℂ := fun i => (‖A (gramBasis A i)‖ : ℂ)
  have hLx : L x=T A := by
    change T (gramCoefficientOperator A x)=T A
    dsimp only [x]
    rw [gramCoefficientOperator_actual]
  have hxNorm : FiniteThorin.vectorNorm p x=schattenNorm p A := by
    unfold FiniteThorin.vectorNorm schattenNorm
    rw [finiteGram_power_sum A p hpq.pos]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [x,Complex.norm_real,norm_norm]
  have key := FiniteThorin.bilinear_interpolation M p₀ p₁ q₀ q₁ p q θ C₀ C₁
    hp₀q₀.pos hp₁q₁.pos hp₀q₀.symm.pos hp₁q₁.symm.pos hpq.pos hpq.symm.pos hθ
    hpmean hqmean hC₀ hC₁ (endpoint p₀ q₀ C₀ hp₀q₀ hC₀ h₀)
    (endpoint p₁ q₁ C₁ hp₁q₁ hC₁ h₁) x c
  rw [hPair,hLx,hxNorm] at key
  exact key

/-- Endpoint estimates at two and four control every intervening finite Schatten exponent
with the maximum endpoint constant, including both endpoints. -/
theorem finiteSchatten_interpolation_two_four
    (T : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (p C₂ C₄ : ℝ) (hp₂ : 2 ≤ p) (hp₄ : p ≤ 4)
    (hC₂ : 0 ≤ C₂) (hC₄ : 0 ≤ C₄)
    (h₂ : ∀ A : H →L[ℂ] H, schattenNorm 2 (T A) ≤ C₂*schattenNorm 2 A)
    (h₄ : ∀ A : H →L[ℂ] H, schattenNorm 4 (T A) ≤ C₄*schattenNorm 4 A)
    (A : H →L[ℂ] H) :
    schattenNorm p (T A) ≤ max C₂ C₄*schattenNorm p A := by
  by_cases hp2 : p=2
  · subst p
    exact (h₂ A).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Reduction.schattenNorm_nonneg 2 A))
  by_cases hp4 : p=4
  · subst p
    exact (h₄ A).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Reduction.schattenNorm_nonneg 4 A))
  have hpgt : 2 < p := lt_of_le_of_ne hp₂ (Ne.symm hp2)
  have hplt : p < 4 := lt_of_le_of_ne hp₄ hp4
  have hp0 : 0 < p := by linarith
  let θ : ℝ := 2-4/p
  have hθ : θ ∈ Set.Ioo (0 : ℝ) 1 := by
    have hleft : 4/p<2 := (div_lt_iff₀ hp0).mpr (by linarith)
    have hright : 1<4/p := (lt_div_iff₀ hp0).mpr (by linarith)
    dsimp only [θ]
    exact ⟨by linarith,by linarith⟩
  have hmean : p*((1-θ)*(1/(2 : ℝ))+θ*(1/(4 : ℝ)))=1 := by
    dsimp only [θ]
    field_simp
    ring
  have hMain := finiteSchatten_interpolation T 2 4 p θ C₂ C₄ (by norm_num)
    (by norm_num) (by linarith) hθ hmean hC₂ hC₄ h₂ h₄ A
  have hmax : 0 ≤ max C₂ C₄ := hC₂.trans (le_max_left _ _)
  have hconst : C₂^(1-θ)*C₄^θ ≤ max C₂ C₄ := by
    calc
      _ ≤ (max C₂ C₄)^(1-θ)*(max C₂ C₄)^θ :=
        mul_le_mul (Real.rpow_le_rpow hC₂ (le_max_left _ _) (by linarith [hθ.2]))
          (Real.rpow_le_rpow hC₄ (le_max_right _ _) hθ.1.le)
          (Real.rpow_nonneg hC₄ _) (Real.rpow_nonneg hmax _)
      _ = max C₂ C₄ := by
        rw [← Real.rpow_add_of_nonneg hmax (by linarith [hθ.2]) hθ.1.le,
          sub_add_cancel,Real.rpow_one]
  exact hMain.trans (mul_le_mul_of_nonneg_right hconst (Reduction.schattenNorm_nonneg p A))

end FiniteSchattenInterpolation
end TTO.Paper.Proved
