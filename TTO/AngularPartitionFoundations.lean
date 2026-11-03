/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.PositiveBandConvolutionFoundations
public import Mathlib.Analysis.PSeries
public import TTO.ThinWideOffDiagonalFoundations

/-! Actual short-cell angular partitions and summable localization weights. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology Interval
namespace TTO.Paper.Proved

/-- Uniform endpoints partition the literal real period [-1/2,1/2]. -/
def angularGridPoint (N j : ℕ) : ℝ := -1/2+(j : ℝ)/(10*(N : ℝ))

def angularGridCenter (N j : ℕ) : ℝ := -1/2+((j : ℝ)+1/2)/(10*(N : ℝ))

def angularLatticeWeight (a : ℝ) (k : ℕ) : ℝ := (1+(k : ℝ)/10)^(-a)

theorem summable_angularLatticeWeight (a : ℝ) (ha : 1 < a) : Summable (angularLatticeWeight a) := by
  have h := (Real.summable_one_div_nat_add_rpow 10 a).mpr ha
  have hEq (k : ℕ) : angularLatticeWeight a k=10^a*(1/|(k : ℝ)+10|^a) := by
    dsimp only [angularLatticeWeight]
    rw [show (1 : ℝ)+(k : ℝ)/10=((k : ℝ)+10)/10 by ring,
      Real.rpow_neg (by positivity),Real.div_rpow (by positivity) (by norm_num),inv_div,
      abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ)+10)]
    ring
  exact (h.mul_left (10^a)).congr (fun k => (hEq k).symm)

/-- A finite universal scalar weight budget for every angular scale. -/
def angularGridWeightConstant (a : ℝ) : ℝ := 2*(1+∑' k : ℕ,angularLatticeWeight a k)

theorem angularGridWeightConstant_pos (a : ℝ) : 0 < angularGridWeightConstant a := by
  have h : 0 ≤ ∑' k : ℕ,angularLatticeWeight a k := tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  dsimp only [angularGridWeightConstant]
  linarith

theorem angularGridCenter_right (N j : ℕ) (hN : 0 < N) :
    angularGridCenter N (j+5*N)=((j : ℝ)+1/2)/(10*(N : ℝ)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [angularGridCenter]
  push_cast
  field_simp
  ring

theorem angularGridCenter_left (N j : ℕ) (hN : 0 < N) (hj : j < 5*N) :
    angularGridCenter N (5*N-1-j) = -(((j : ℝ)+1/2)/(10*(N : ℝ))) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNat : (5*N-1-j)+(j+1)=5*N := by omega
  have hReal := congrArg (fun n : ℕ => (n : ℝ)) hNat
  push_cast at hReal
  dsimp only [angularGridCenter]
  field_simp
  nlinarith [hReal]

/-- Every finite grid has the SAME p-kernel weight budget, independent of N. -/
theorem sum_angularGridWeight_le (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : 1 < a) :
    (∑ j ∈ Finset.range (10*N),(1+(N : ℝ)*|angularGridCenter N j|)^(-a)) ≤ angularGridWeightConstant a := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hRight (j : ℕ) : (1+(N : ℝ)*|angularGridCenter N (j+5*N)|)^(-a) ≤ angularLatticeWeight a j := by
    rw [angularGridCenter_right N j hN,abs_of_pos (by positivity)]
    have he : (N : ℝ)*(((j : ℝ)+1/2)/(10*(N : ℝ)))=((j : ℝ)+1/2)/10 := by field_simp
    rw [he]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hLeft (j : ℕ) (hj : j < 5*N) :
      (1+(N : ℝ)*|angularGridCenter N (5*N-1-j)|)^(-a) ≤ angularLatticeWeight a j := by
    rw [angularGridCenter_left N j hN hj,abs_neg,abs_of_pos (by positivity)]
    have he : (N : ℝ)*(((j : ℝ)+1/2)/(10*(N : ℝ)))=((j : ℝ)+1/2)/10 := by field_simp
    rw [he]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hSum := (summable_angularLatticeWeight a ha).sum_le_tsum (Finset.range (5*N))
    (fun k _ => Real.rpow_nonneg (by positivity) (-a))
  rw [show 10*N=5*N+5*N by omega,Finset.sum_range_add]
  calc
    _ = (∑ j ∈ Finset.range (5*N),(1+(N : ℝ)*|angularGridCenter N (5*N-1-j)|)^(-a))+
        ∑ j ∈ Finset.range (5*N),(1+(N : ℝ)*|angularGridCenter N (j+5*N)|)^(-a) := by
      apply congrArg₂ (·+·)
      · exact (Finset.sum_range_reflect (fun j => (1+(N : ℝ)*|angularGridCenter N j|)^(-a)) (5*N)).symm
      · apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_comm j (5*N)]
    _ ≤ (∑ j ∈ Finset.range (5*N),angularLatticeWeight a j)+∑ j ∈ Finset.range (5*N),angularLatticeWeight a j := by
      exact add_le_add (Finset.sum_le_sum (fun j hj => hLeft j (Finset.mem_range.mp hj)))
        (Finset.sum_le_sum (fun j _ => hRight j))
    _ ≤ _ := by dsimp only [angularGridWeightConstant,angularLatticeWeight]; linarith

/-- A pointwise p-power cell bound yields the correct ordinary integral bound for ANY p>0. -/
theorem interval_integral_norm_rpow_le (f : ℝ → ℂ) (a b p E : ℝ) (hab : a ≤ b) (hp : 0 < p)
    (hE : 0 ≤ E) (hBound : ∀ t ∈ Icc a b,‖f t‖^p ≤ E) :
    ‖∫ t in a..b,f t‖^p ≤ (b-a)^p*E := by
  have hNorm (t : ℝ) (ht : t ∈ Ι a b) : ‖f t‖ ≤ E^(p⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hE hp).mpr
    exact hBound t ⟨(uIoc_of_le hab ▸ ht).1.le,(uIoc_of_le hab ▸ ht).2⟩
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hNorm
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hInt
  calc
    _ ≤ (E^(p⁻¹)*(b-a))^p := Real.rpow_le_rpow (norm_nonneg _) hInt hp.le
    _ = _ := by rw [Real.mul_rpow (Real.rpow_nonneg hE _) (sub_nonneg.mpr hab),Real.rpow_inv_rpow hE hp.ne']; ring

theorem angularGridPoint_zero (N : ℕ) : angularGridPoint N 0 = -1/2 := by
  simp only [angularGridPoint,Nat.cast_zero,zero_div,add_zero]

theorem angularGridPoint_last (N : ℕ) (hN : 0 < N) : angularGridPoint N (10*N) = 1/2 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [angularGridPoint]
  push_cast
  field_simp
  ring

theorem angularGridPoint_length (N j : ℕ) :
    angularGridPoint N (j+1)-angularGridPoint N j = 1/(10*(N : ℝ)) := by
  dsimp only [angularGridPoint]
  push_cast
  ring

theorem angularGridPoint_mono (N : ℕ) : Monotone (angularGridPoint N) := by
  intro i j hij
  dsimp only [angularGridPoint]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity))

/-- Every closed short cell fits the arc neighborhood used by the actual local area estimate. -/
theorem angularGridCell_near_center (N j : ℕ) (hN : 0 < N) (t : ℝ)
    (ht : t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1))) :
    |t-angularGridCenter N j| ≤ 1/(10*(N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hPos : 0 ≤ 1/(10*(N : ℝ)) := by positivity
  have hLeft : angularGridCenter N j-angularGridPoint N j=1/(20*(N : ℝ)) := by
    dsimp only [angularGridCenter,angularGridPoint]
    ring
  have hRight : angularGridPoint N (j+1)-angularGridCenter N j=1/(20*(N : ℝ)) := by
    dsimp only [angularGridCenter,angularGridPoint]
    push_cast
    ring
  have hHalf : 1/(20*(N : ℝ))=(1/(10*(N : ℝ)))/2 := by ring
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

/-- Exact finite-cell integration with the valid sharp scalar p-power triangle.
No concave Jensen or quasi-Banach averaging is invoked. -/
theorem angular_partition_integral_rpow_le (f : ℝ → ℂ) (hf : Continuous f)
    (N : ℕ) (hN : 0 < N) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (E : ℕ → ℝ)
    (hE : ∀ j ∈ Finset.range (10*N),0 ≤ E j)
    (hBound : ∀ j ∈ Finset.range (10*N),∀ t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1)),‖f t‖^p ≤ E j) :
    ‖∫ t : ℝ in (-1/2)..(1/2),f t‖^p ≤ (1/(10*(N : ℝ)))^p*∑ j ∈ Finset.range (10*N),E j := by
  have hSum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := angularGridPoint N)
    (n := 10*N) (fun j _ => hf.intervalIntegrable _ _)
  rw [angularGridPoint_zero,angularGridPoint_last N hN] at hSum
  rw [← hSum]
  calc
    _ ≤ ∑ j ∈ Finset.range (10*N),‖∫ t in angularGridPoint N j..angularGridPoint N (j+1),f t‖^p :=
      complex_norm_finset_sum_rpow_le _ _ p hp hp1
    _ ≤ ∑ j ∈ Finset.range (10*N),(1/(10*(N : ℝ)))^p*E j := by
      apply Finset.sum_le_sum
      intro j hj
      have h := interval_integral_norm_rpow_le f _ _ p (E j) (angularGridPoint_mono N (by omega)) hp (hE j hj) (hBound j hj)
      simpa only [angularGridPoint_length] using h
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Bilinear short-cell bound uses genuine pointwise powers, including E=0. -/
theorem angular_partition_product_rpow_le (K G : ℝ → ℂ) (hK : Continuous K) (hG : Continuous G)
    (N : ℕ) (hN : 0 < N) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (M E : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.range (10*N),0 ≤ M j) (hE : ∀ j ∈ Finset.range (10*N),0 ≤ E j)
    (hKB : ∀ j ∈ Finset.range (10*N),∀ t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1)),‖K t‖ ≤ M j)
    (hGB : ∀ j ∈ Finset.range (10*N),∀ t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1)),‖G t‖^p ≤ E j) :
    ‖∫ t : ℝ in (-1/2)..(1/2),K t*G t‖^p ≤
      (1/(10*(N : ℝ)))^p*∑ j ∈ Finset.range (10*N),(M j)^p*E j := by
  apply angular_partition_integral_rpow_le _ (hK.mul hG) N hN p hp hp1 (fun j => (M j)^p*E j)
  · intro j hj
    exact mul_nonneg (Real.rpow_nonneg (hM j hj) p) (hE j hj)
  · intro j hj t ht
    change ‖K t*G t‖^p ≤ (M j)^p*E j
    rw [norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (hKB j hj t ht) hp.le) (hGB j hj t ht)
      (Real.rpow_nonneg (norm_nonneg _) p) (Real.rpow_nonneg (hM j hj) p)

/-- A cell stays inside the fixed real period, including its endpoints. -/
theorem angularGridCell_in_period (N j : ℕ) (hN : 0 < N) (hj : j < 10*N) (t : ℝ)
    (ht : t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1))) : |t| ≤ 1/2 := by
  have hLeft := angularGridPoint_mono N (show 0 ≤ j by omega)
  have hRight := angularGridPoint_mono N (show j+1 ≤ 10*N by omega)
  rw [angularGridPoint_zero] at hLeft
  rw [angularGridPoint_last N hN] at hRight
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

/-- The cellwise denominator is comparable to its actual center, uniformly in scale. -/
theorem angularGridCell_denominator_compare (N j : ℕ) (hN : 0 < N) (t : ℝ)
    (ht : t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1))) :
    1+(N : ℝ)*|angularGridCenter N j| ≤ 2*(1+(N : ℝ)*|t|) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNear := angularGridCell_near_center N j hN t ht
  have hAbs := abs_add_le (angularGridCenter N j-t) t
  rw [sub_add_cancel,abs_sub_comm] at hAbs
  have hM := mul_le_mul_of_nonneg_left (hAbs.trans (add_le_add hNear le_rfl)) hNr.le
  have hScale : (N : ℝ)*(1/(10*(N : ℝ)))=1/10 := by field_simp
  rw [mul_add,hScale] at hM
  nlinarith [abs_nonneg t]

/-- A concrete nonnegative pointwise majorant for every inverse-kernel short cell. -/
def angularInverseMajorant (m N n j : ℕ) : ℝ :=
  (positiveWideDecayConstant m*2^(m+1)*(N : ℝ)/(N : ℝ)^n)/
    (1+(N : ℝ)*|angularGridCenter N j|)^(m+1)

theorem angularInverseMajorant_nonneg (m N n j : ℕ) (hm : 1 ≤ m) :
    0 ≤ angularInverseMajorant m N n j := by
  dsimp only [angularInverseMajorant]
  positivity [positiveWideDecayConstant_pos m hm]

/-- Actual inverse-kernel pointwise control on every short cell. -/
theorem positiveWideInverseKernel_le_cell_majorant (m N N' n j : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N)
    (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N) (hn : 1 ≤ n) (hnm : n ≤ m) (hj : j < 10*N)
    (t : ℝ) (ht : t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1))) :
    ‖(positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 (t : Boundary))‖ ≤
      angularInverseMajorant m N n j := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRaw := positiveWideInverseKernel_decay m N N' n hm hN hNN' hRatio hn hnm t
    (angularGridCell_in_period N j (by omega) hj t ht)
  have hCompare := angularGridCell_denominator_compare N j (by omega) t ht
  have hPow : (1+(N : ℝ)*|angularGridCenter N j|)^(m+1) ≤
      2^(m+1)*(1+(N : ℝ)*|t|)^(m+1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hCompare (m+1)
  apply hRaw.trans
  dsimp only [angularInverseMajorant]
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = (positiveWideDecayConstant m*(N : ℝ)*(N : ℝ)^n)*
        (1+(N : ℝ)*|angularGridCenter N j|)^(m+1) := by ring
    _ ≤ (positiveWideDecayConstant m*(N : ℝ)*(N : ℝ)^n)*
        (2^(m+1)*(1+(N : ℝ)*|t|)^(m+1)) :=
      mul_le_mul_of_nonneg_left hPow (by positivity [positiveWideDecayConstant_pos m hm])
    _ = _ := by ring

/-- Actual p-powers of all cell majorants have a uniform scale budget. -/
theorem sum_angularInverseMajorant_rpow_le (m N n : ℕ) (hm : 1 ≤ m) (hN : 0 < N)
    (p : ℝ) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    (∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p) ≤
      (positiveWideDecayConstant m*2^(m+1)*(N : ℝ)/(N : ℝ)^n)^p*
        angularGridWeightConstant (((m+1 : ℕ) : ℝ)*p) := by
  have hEq (j : ℕ) : (angularInverseMajorant m N n j)^p =
      (positiveWideDecayConstant m*2^(m+1)*(N : ℝ)/(N : ℝ)^n)^p*
        (1+(N : ℝ)*|angularGridCenter N j|)^(-(((m+1 : ℕ) : ℝ)*p)) := by
    dsimp only [angularInverseMajorant]
    rw [Real.div_rpow (by positivity [positiveWideDecayConstant_pos m hm]) (by positivity),
      ← Real.rpow_natCast_mul (by positivity) (m+1) p,Real.rpow_neg (show (0 : ℝ) ≤ 1+(N : ℝ)*|angularGridCenter N j| by positivity)]
    rfl
  simp_rw [hEq]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_angularGridWeight_le N hN _ hOrder) (by positivity [positiveWideDecayConstant_pos m hm])

/-- The same genuine finite-cell estimate applies directly to normalized circle Haar integrals. -/
theorem circle_angular_partition_product_rpow_le (K G : Boundary → ℂ) (hK : Continuous K) (hG : Continuous G)
    (N : ℕ) (hN : 0 < N) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (M E : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.range (10*N),0 ≤ M j) (hE : ∀ j ∈ Finset.range (10*N),0 ≤ E j)
    (hKB : ∀ j ∈ Finset.range (10*N),∀ t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1)),‖K (t : Boundary)‖ ≤ M j)
    (hGB : ∀ j ∈ Finset.range (10*N),∀ t ∈ Icc (angularGridPoint N j) (angularGridPoint N (j+1)),‖G (t : Boundary)‖^p ≤ E j) :
    ‖∫ t : Boundary,K t*G t ∂circleMeasure‖^p ≤
      (1/(10*(N : ℝ)))^p*∑ j ∈ Finset.range (10*N),(M j)^p*E j := by
  have hKr : Continuous (fun t : ℝ => K (t : Boundary)) := by fun_prop
  have hGr : Continuous (fun t : ℝ => G (t : Boundary)) := by fun_prop
  have h := angular_partition_product_rpow_le _ _ hKr hGr N hN p hp hp1 M E hM hE hKB hGB
  have hInt : (∫ t : ℝ in (-1/2)..(1/2),K (t : Boundary)*G (t : Boundary)) =
      ∫ t : Boundary,K t*G t ∂circleMeasure := by
    have hMeasure : circleMeasure=(volume : Measure Boundary) := by
      simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
    rw [hMeasure]
    convert AddCircle.intervalIntegral_preimage 1 (-1/2) (fun t : Boundary => K t*G t) using 1
    norm_num
  rw [hInt] at h
  exact h

end TTO.Paper.Proved
