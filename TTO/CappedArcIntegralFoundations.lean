/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcBMOEstimatesFoundations

/-! Capped concentric arcs retain BMO control through the final full-circle scale. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

/-- Concentric doubling stops at one full real-period window. -/
def cappedArcLength (h : ℝ) (n : ℕ) : ℝ := min ((2 : ℝ)^n*h) 1

theorem cappedArcLength_pos (h : ℝ) (hh : 0<h) (n : ℕ) :
    0<cappedArcLength h n := by
  exact lt_min (mul_pos (pow_pos (by norm_num : (0 : ℝ)<2) n) hh) zero_lt_one

theorem cappedArcLength_le_one (h : ℝ) (n : ℕ) :
    cappedArcLength h n≤1 := min_le_right _ _

theorem cappedArcLength_mono (h : ℝ) (hh : 0≤h) (n : ℕ) :
    cappedArcLength h n≤cappedArcLength h (n+1) := by
  apply min_le_min_right
  apply mul_le_mul_of_nonneg_right _ hh
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (Nat.le_succ n)

theorem cappedArcLength_succ_le (h : ℝ) (n : ℕ) :
    cappedArcLength h (n+1)≤2*cappedArcLength h n := by
  change min ((2 : ℝ)^(n+1)*h) 1≤2*min ((2 : ℝ)^n*h) 1
  by_cases hn : (2 : ℝ)^n*h≤1
  · rw [min_eq_left hn]
    exact (min_le_left _ _).trans_eq (by rw [pow_succ]; ring)
  · rw [min_eq_right (le_of_not_ge hn)]
    exact (min_le_right _ _).trans (by norm_num)

theorem norm_arcMean_capped_doubling_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hUnit : h≤1) (N : ℕ) :
    ‖arcMean f (a-cappedArcLength h N/2) (a+cappedArcLength h N/2)-
      arcMean f (a-h/2) (a+h/2)‖≤2*(N : ℝ)*B := by
  let l : ℕ → ℝ := fun n => a-cappedArcLength h n/2
  let r : ℕ → ℝ := fun n => a+cappedArcLength h n/2
  have hDiff (n : ℕ) : r n-l n=cappedArcLength h n := by dsimp [l,r]; ring
  have hPos (n : ℕ) : l n<r n := by
    rw [← sub_pos,hDiff]
    exact cappedArcLength_pos h hh n
  have hLen (n : ℕ) : r n-l n≤1 := by
    rw [hDiff]
    exact cappedArcLength_le_one h n
  have hSub (n : ℕ) : Ioc (l n) (r n) ⊆ Ioc (l (n+1)) (r (n+1)) := by
    intro t ht
    dsimp [l,r] at ht ⊢
    constructor <;> linarith [cappedArcLength_mono h hh.le n,ht.1,ht.2]
  have hRatio (n : ℕ) : r (n+1)-l (n+1)≤2*(r n-l n) := by
    rw [hDiff,hDiff]
    exact cappedArcLength_succ_le h n
  have hZero : cappedArcLength h 0=h := by
    simp only [cappedArcLength,pow_zero,one_mul,min_eq_left hUnit]
  have hBound := norm_arcMean_chain_le f B hB l r N (fun n _ => hPos n)
    (fun n _ => hLen n) (fun n _ => hSub n) (fun n _ => hRatio n)
    (fun n _ => hMO _ _ (hPos n) (hLen n))
  simpa only [l,r,hZero] using hBound

/-- The capped arc has the same linear mean-drift cost as literal doubling. -/
theorem integral_norm_sub_small_arcMean_capped_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hUnit : h≤1) (N : ℕ) :
    (∫ t in Ioc (a-cappedArcLength h N/2) (a+cappedArcLength h N/2),
      ‖f (t : Boundary)-arcMean f (a-h/2) (a+h/2)‖)≤
        (2*(N : ℝ)+1)*B*cappedArcLength h N := by
  let l := a-cappedArcLength h N/2
  let r := a+cappedArcLength h N/2
  let c₀ := arcMean f (a-h/2) (a+h/2)
  let cN := arcMean f l r
  have hDiff : r-l=cappedArcLength h N := by dsimp [l,r]; ring
  have hPos : 0<r-l := by rw [hDiff]; exact cappedArcLength_pos h hh N
  have hLen : r-l≤1 := hDiff.trans_le (cappedArcLength_le_one h N)
  have hf := boundaryL2_integrableOn_lift_Ioc f l r hLen
  have hFin : volume (Ioc l r)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hc₀ : IntegrableOn (fun _ : ℝ => c₀) (Ioc l r) := integrableOn_const hFin
  have hcN : IntegrableOn (fun _ : ℝ => cN) (Ioc l r) := integrableOn_const hFin
  have hNorm₀ : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c₀‖) (Ioc l r) :=
    (hf.sub hc₀).norm
  have hNormN : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-cN‖) (Ioc l r) :=
    (hf.sub hcN).norm
  have hC : IntegrableOn (fun _ : ℝ => ‖cN-c₀‖) (Ioc l r) := integrableOn_const hFin
  have hMean : ‖cN-c₀‖≤2*(N : ℝ)*B :=
    norm_arcMean_capped_doubling_le f B hB hMO a h hh hUnit N
  have hMass : (∫ t in Ioc l r,‖f (t : Boundary)-cN‖)≤(r-l)*B := by
    have hm := mul_le_mul_of_nonneg_left (hMO l r (sub_pos.mp hPos) hLen) hPos.le
    change (r-l)*((r-l)⁻¹*(∫ t in Ioc l r,‖f (t : Boundary)-cN‖))≤(r-l)*B at hm
    rw [← mul_assoc,mul_inv_cancel₀ hPos.ne',one_mul] at hm
    exact hm
  have hPoint (t : ℝ) : ‖f (t : Boundary)-c₀‖≤‖f (t : Boundary)-cN‖+‖cN-c₀‖ := by
    calc
      _ = ‖(f (t : Boundary)-cN)+(cN-c₀)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  change (∫ t in Ioc l r,‖f (t : Boundary)-c₀‖)≤_
  calc
    _ ≤ ∫ t in Ioc l r,‖f (t : Boundary)-cN‖+‖cN-c₀‖ :=
      integral_mono hNorm₀ (hNormN.add hC) hPoint
    _ = (∫ t in Ioc l r,‖f (t : Boundary)-cN‖)+(r-l)*‖cN-c₀‖ := by
      rw [integral_add hNormN hC,setIntegral_const,
        Real.volume_real_Ioc_of_le (sub_nonneg.mp hPos.le),smul_eq_mul]
    _ ≤ (r-l)*B+(r-l)*(2*(N : ℝ)*B) :=
      add_le_add hMass (mul_le_mul_of_nonneg_left hMean hPos.le)
    _ = _ := by rw [hDiff]; ring


/-- A coarser mass estimate whose geometric coefficient can be summed without cap cases. -/
theorem integral_norm_sub_small_arcMean_capped_le_doubling (f : BoundaryL2)
    (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hUnit : h≤1) (N : ℕ) :
    (∫ t in Ioc (a-cappedArcLength h N/2) (a+cappedArcLength h N/2),
      ‖f (t : Boundary)-arcMean f (a-h/2) (a+h/2)‖)≤
        (2*(N : ℝ)+1)*B*((2 : ℝ)^N*h) :=
  (integral_norm_sub_small_arcMean_capped_le f B hB hMO a h hh hUnit N).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))

/-- The exact scalar coefficient needed for the far annular integral. -/
theorem hasSum_far_arc_coeff (B h : ℝ) :
    HasSum (fun n : ℕ => (8*B/h)*((2*(n : ℝ)+3)*(1/2 : ℝ)^n)) (80*B/h) := by
  have hr : ‖(1/2 : ℝ)‖<1 := by norm_num
  have h0 : HasSum (fun n : ℕ => (1/2 : ℝ)^n) 2 := by
    convert hasSum_geometric_of_norm_lt_one hr using 1
    norm_num
  have h1 : HasSum (fun n : ℕ => (n : ℝ)*(1/2 : ℝ)^n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hr using 1
    norm_num
  convert ((h1.mul_left 2).add (h0.mul_left 3)).mul_left (8*B/h) using 1
  · funext n
    ring
  · ring


/-- A scalar far-annular estimate from actual capped-arc masses. -/
theorem lintegral_far_inverse_sq_le_of_capped_mass
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (B a h : ℝ) (hB : 0≤B) (hh : 0<h)
    (hMass : ∀ n : ℕ,
      (∫⁻ x in Ioc (a-cappedArcLength h n/2) (a+cappedArcLength h n/2), F x)≤
        ENNReal.ofReal ((2*(n : ℝ)+1)*B*((2 : ℝ)^n*h))) :
    (∫⁻ x in Ioc (a-1/2) (a+1/2)∩{x : ℝ | h/2≤|x-a|},
      ENNReal.ofReal (1/|x-a|^2)*F x)≤ENNReal.ofReal (80*B/h) := by
  let J : ℕ → Set ℝ := fun n =>
    Ioc (a-cappedArcLength h n/2) (a+cappedArcLength h n/2)
  let S := Ioc (a-1/2) (a+1/2)∩{x : ℝ | h/2≤|x-a|}
  let R : ℕ → ℝ := fun n => (2 : ℝ)^n*h/2
  let A : ℕ → ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal (1/(R n)^2)*(J (n+1)).indicator F x
  have hR (n : ℕ) : 0<R n := by dsimp [R]; positivity
  have hPoint (x : ℝ) :
      S.indicator (fun x => ENNReal.ofReal (1/|x-a|^2)*F x) x≤∑' n,A n x := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx]
      have hRatio : 1≤|x-a|/(h/2) := by
        rw [le_div_iff₀ (by positivity : 0<h/2)]
        simpa only [one_mul,Set.mem_ofPred_eq] using hx.2
      obtain ⟨n,hn0,hn1⟩ := exists_nat_pow_near hRatio (by norm_num : (1 : ℝ)<2)
      have hLow : R n≤|x-a| := by
        have he := (le_div_iff₀ (by positivity : 0<h/2)).mp hn0
        dsimp [R]
        nlinarith
      have hHigh : |x-a|<(2 : ℝ)^(n+1)*h/2 := by
        have he := (div_lt_iff₀ (by positivity : 0<h/2)).mp hn1
        nlinarith
      have hMem : x∈J (n+1) := by
        by_cases hn : (2 : ℝ)^(n+1)*h≤1
        · dsimp [J,cappedArcLength]
          rw [min_eq_left hn]
          have he := abs_lt.mp hHigh
          exact ⟨by linarith [he.1],by linarith [he.2]⟩
        · dsimp [J,cappedArcLength]
          rw [min_eq_right (le_of_not_ge hn)]
          exact hx.1
      have hSq : (R n)^2≤|x-a|^2 := by
        nlinarith [hR n,abs_nonneg (x-a)]
      have hBound : ENNReal.ofReal (1/|x-a|^2)≤ENNReal.ofReal (1/(R n)^2) :=
        ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos (hR n)) hSq)
      calc
        _ ≤ ENNReal.ofReal (1/(R n)^2)*F x := mul_le_mul_left hBound (F x)
        _ = A n x := by dsimp only [A]; rw [Set.indicator_of_mem hMem]
        _ ≤ _ := ENNReal.le_tsum (f:=fun k : ℕ => A k x) n
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  have hMA (n : ℕ) : Measurable (A n) :=
    measurable_const.mul (hF.indicator measurableSet_Ioc)
  have hBoundA (n : ℕ) : (∫⁻ x,A n x)≤
      ENNReal.ofReal ((8*B/h)*((2*(n : ℝ)+3)*(1/2 : ℝ)^n)) := by
    dsimp only [A]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator measurableSet_Ioc]
    calc
      _ ≤ ENNReal.ofReal (1/(R n)^2)*
          ENNReal.ofReal ((2*((n+1 : ℕ) : ℝ)+1)*B*((2 : ℝ)^(n+1)*h)) :=
        mul_le_mul_right (hMass (n+1)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0≤1/(R n)^2)]
        congr 1
        dsimp [R]
        push_cast
        simp only [div_pow,one_pow,pow_succ]
        field_simp
        ring
  have hSum : (∑' n : ℕ,ENNReal.ofReal ((8*B/h)*((2*(n : ℝ)+3)*(1/2 : ℝ)^n)))=
      ENNReal.ofReal (80*B/h) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (hasSum_far_arc_coeff B h).summable,(hasSum_far_arc_coeff B h).tsum_eq]
  have hS : MeasurableSet S := measurableSet_Ioc.inter
    (measurableSet_le measurable_const (by fun_prop))
  rw [← lintegral_indicator hS]
  calc
    _ ≤ ∫⁻ x,∑' n,A n x := lintegral_mono hPoint
    _ = ∑' n,∫⁻ x,A n x := lintegral_tsum (fun n => (hMA n).aemeasurable)
    _ ≤ ∑' n : ℕ,ENNReal.ofReal ((8*B/h)*((2*(n : ℝ)+3)*(1/2 : ℝ)^n)) :=
      ENNReal.tsum_le_tsum hBoundA
    _ = _ := hSum


/-- Actual BMO data imply an ordinary, finite far weighted L¹ integral. -/
theorem integrable_far_arc_norm_div_sq (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (hUnit : h≤1) :
    IntegrableOn (fun x : ℝ =>
      ‖f (x : Boundary)-arcMean f (a-h/2) (a+h/2)‖/|x-a|^2)
      (Ioc (a-1/2) (a+1/2)∩{x : ℝ | h/2≤|x-a|}) ∧
    (∫ x in Ioc (a-1/2) (a+1/2)∩{x : ℝ | h/2≤|x-a|},
      ‖f (x : Boundary)-arcMean f (a-h/2) (a+h/2)‖/|x-a|^2)≤80*B/h := by
  let c := arcMean f (a-h/2) (a+h/2)
  let F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ‖f (x : Boundary)-c‖
  let G : ℝ → ℝ := fun x => ‖f (x : Boundary)-c‖/|x-a|^2
  let S := Ioc (a-1/2) (a+1/2)∩{x : ℝ | h/2≤|x-a|}
  have hNorm : Measurable (fun x : ℝ => ‖f (x : Boundary)-c‖) :=
    (((Lp.stronglyMeasurable f).measurable.comp AddCircle.measurable_mk').sub measurable_const).norm
  have hF : Measurable F := hNorm.ennreal_ofReal
  have hG : Measurable G := hNorm.div (by fun_prop)
  have hNN (x : ℝ) : 0≤G x := by dsimp [G]; positivity
  have hMass (n : ℕ) :
      (∫⁻ x in Ioc (a-cappedArcLength h n/2) (a+cappedArcLength h n/2),F x)≤
        ENNReal.ofReal ((2*(n : ℝ)+1)*B*((2 : ℝ)^n*h)) := by
    let l := a-cappedArcLength h n/2
    let r := a+cappedArcLength h n/2
    have hLen : r-l≤1 := by
      dsimp [l,r]
      linarith [cappedArcLength_le_one h n]
    have hFin : volume (Ioc l r)≠∞ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have hI : IntegrableOn (fun x : ℝ => ‖f (x : Boundary)-c‖) (Ioc l r) :=
      ((boundaryL2_integrableOn_lift_Ioc f l r hLen).sub
        (integrableOn_const hFin)).norm
    change (∫⁻ x in Ioc l r,ENNReal.ofReal ‖f (x : Boundary)-c‖)≤_
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (integral_norm_sub_small_arcMean_capped_le_doubling f B hB hMO a h hh hUnit n)
  have hLE : (∫⁻ x in S,ENNReal.ofReal (G x))≤ENNReal.ofReal (80*B/h) := by
    have he : (fun x => ENNReal.ofReal (G x))=
        fun x => ENNReal.ofReal (1/|x-a|^2)*F x := by
      funext x
      dsimp [G,F]
      rw [← ENNReal.ofReal_mul (by positivity : 0≤1/|x-a|^2)]
      congr 1
      ring
    rw [he]
    exact lintegral_far_inverse_sq_le_of_capped_mass F hF B a h hB hh hMass
  have hInt : IntegrableOn G S :=
    ⟨hG.aestronglyMeasurable.restrict,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hNN)).mpr
        (hLE.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hInt,?_⟩
  change (∫ x in S,G x)≤_
  calc
    _ = (∫⁻ x in S,ENNReal.ofReal (G x)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hNN) hG.aestronglyMeasurable.restrict
    _ ≤ (ENNReal.ofReal (80*B/h)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLE
    _ = _ := ENNReal.toReal_ofReal (by positivity)

end TTO.Paper.Proved
