/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ArcBMO2Foundations

/-! Actual nested-arc mean estimates for localized analytic kernel bounds. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved

theorem norm_arcMean_sub_arcMean_le_of_subset (f : BoundaryL2)
    (a b c d : ℝ) (hab : a<b) (hcd : c<d) (hLen : d-c≤1)
    (hSub : Ioc a b ⊆ Ioc c d) :
    ‖arcMean f a b-arcMean f c d‖≤(d-c)/(b-a)*meanOscillation f c d := by
  have hBig := boundaryL2_integrableOn_lift_Ioc f c d hLen
  have hFin : volume (Ioc c d)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hConst : IntegrableOn (fun _ : ℝ => arcMean f c d) (Ioc c d) :=
    integrableOn_const hFin
  have hNorm : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-arcMean f c d‖) (Ioc c d) :=
    (hBig.sub hConst).norm
  have hMon : (∫ t in Ioc a b,‖f (t : Boundary)-arcMean f c d‖)≤
      ∫ t in Ioc c d,‖f (t : Boundary)-arcMean f c d‖ :=
    setIntegral_mono_set hNorm (Eventually.of_forall fun t => norm_nonneg _)
      (Eventually.of_forall fun t ht => hSub ht)
  calc
    _ ≤ (b-a)⁻¹*(∫ t in Ioc a b,‖f (t : Boundary)-arcMean f c d‖) :=
      norm_arcMean_sub_const_le_centeredIntegral f a b hab (hBig.mono_set hSub) _
    _ ≤ (b-a)⁻¹*(∫ t in Ioc c d,‖f (t : Boundary)-arcMean f c d‖) :=
      mul_le_mul_of_nonneg_left hMon (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = _ := by
      unfold meanOscillation
      field_simp [(sub_pos.mpr hab).ne',(sub_pos.mpr hcd).ne']

theorem norm_arcMean_sub_arcMean_le_bound (f : BoundaryL2) (B : ℝ)
    (a b c d : ℝ) (hab : a<b) (hcd : c<d) (hLen : d-c≤1)
    (hSub : Ioc a b ⊆ Ioc c d) (hMO : meanOscillation f c d≤B) :
    ‖arcMean f a b-arcMean f c d‖≤(d-c)/(b-a)*B :=
  (norm_arcMean_sub_arcMean_le_of_subset f a b c d hab hcd hLen hSub).trans
    (mul_le_mul_of_nonneg_left hMO (div_nonneg (sub_nonneg.mpr hcd.le)
      (sub_nonneg.mpr hab.le)))


/-- Nested arcs whose lengths at most double have linearly controlled mean drift. -/
theorem norm_arcMean_chain_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (a b : ℕ → ℝ) (N : ℕ)
    (hPos : ∀ n≤N,a n<b n) (hLen : ∀ n≤N,b n-a n≤1)
    (hSub : ∀ n<N,Ioc (a n) (b n) ⊆ Ioc (a (n+1)) (b (n+1)))
    (hRatio : ∀ n<N,b (n+1)-a (n+1)≤2*(b n-a n))
    (hMO : ∀ n≤N,meanOscillation f (a n) (b n)≤B) :
    ‖arcMean f (a N) (b N)-arcMean f (a 0) (b 0)‖≤2*(N : ℝ)*B := by
  have hStep (n : ℕ) (hn : n<N) :
      ‖arcMean f (a (n+1)) (b (n+1))-arcMean f (a n) (b n)‖≤2*B := by
    have hQuot : (b (n+1)-a (n+1))/(b n-a n)≤2 :=
      (div_le_iff₀ (sub_pos.mpr (hPos n hn.le))).mpr (hRatio n hn)
    rw [norm_sub_rev]
    exact (norm_arcMean_sub_arcMean_le_bound f B _ _ _ _ (hPos n hn.le)
      (hPos (n+1) (by omega)) (hLen (n+1) (by omega)) (hSub n hn)
      (hMO (n+1) (by omega))).trans (mul_le_mul_of_nonneg_right hQuot hB)
  have hInd : ∀ n≤N,‖arcMean f (a n) (b n)-arcMean f (a 0) (b 0)‖≤2*(n : ℝ)*B := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      calc
        _ = ‖(arcMean f (a (n+1)) (b (n+1))-arcMean f (a n) (b n))+
            (arcMean f (a n) (b n)-arcMean f (a 0) (b 0))‖ := by congr 1; abel
        _ ≤ ‖arcMean f (a (n+1)) (b (n+1))-arcMean f (a n) (b n)‖+
            ‖arcMean f (a n) (b n)-arcMean f (a 0) (b 0)‖ := norm_add_le _ _
        _ ≤ 2*B+2*(n : ℝ)*B := add_le_add (hStep n (by omega)) (ih (by omega))
        _ = 2*((n+1 : ℕ) : ℝ)*B := by push_cast; ring
  exact hInd N le_rfl

/-- Literal concentric real arcs; only the final doubled length is restricted to one. -/
theorem norm_arcMean_doubling_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (N : ℕ) (hLast : (2 : ℝ)^N*h≤1) :
    ‖arcMean f (a-(2 : ℝ)^N*h/2) (a+(2 : ℝ)^N*h/2)-
      arcMean f (a-h/2) (a+h/2)‖≤2*(N : ℝ)*B := by
  let l : ℕ → ℝ := fun n => a-(2 : ℝ)^n*h/2
  let r : ℕ → ℝ := fun n => a+(2 : ℝ)^n*h/2
  have hDiff (n : ℕ) : r n-l n=(2 : ℝ)^n*h := by dsimp [l,r]; ring
  have hPos (n : ℕ) : l n<r n := by rw [← sub_pos,hDiff]; positivity
  have hLen (n : ℕ) (hn : n≤N) : r n-l n≤1 := by
    rw [hDiff]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hn)
      hh.le).trans hLast
  have hStep (n : ℕ) : (2 : ℝ)^n*h≤(2 : ℝ)^(n+1)*h := by
    apply mul_le_mul_of_nonneg_right _ hh.le
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ)≤2) n]
  have hSub (n : ℕ) : Ioc (l n) (r n) ⊆ Ioc (l (n+1)) (r (n+1)) := by
    intro t ht
    dsimp [l,r] at ht ⊢
    constructor <;> linarith [hStep n,ht.1,ht.2]
  have hRatio (n : ℕ) : r (n+1)-l (n+1)≤2*(r n-l n) := by
    rw [hDiff,hDiff,pow_succ]
    nlinarith
  have h := norm_arcMean_chain_le f B hB l r N (fun n _ => hPos n) hLen
    (fun n _ => hSub n) (fun n _ => hRatio n) (fun n hn => hMO _ _ (hPos n) (hLen n hn))
  simpa only [l,r,pow_zero,one_mul] using h


/-- The L¹ mass relative to a fixed small-arc mean grows only linearly per doubling. -/
theorem integral_norm_sub_small_arcMean_le (f : BoundaryL2) (B : ℝ) (hB : 0≤B)
    (hMO : ∀ a b : ℝ,a<b → b-a≤1 → meanOscillation f a b≤B)
    (a h : ℝ) (hh : 0<h) (N : ℕ) (hLast : (2 : ℝ)^N*h≤1) :
    (∫ t in Ioc (a-(2 : ℝ)^N*h/2) (a+(2 : ℝ)^N*h/2),
      ‖f (t : Boundary)-arcMean f (a-h/2) (a+h/2)‖)≤
        (2*(N : ℝ)+1)*B*((2 : ℝ)^N*h) := by
  let l := a-(2 : ℝ)^N*h/2
  let r := a+(2 : ℝ)^N*h/2
  let c₀ := arcMean f (a-h/2) (a+h/2)
  let cN := arcMean f l r
  have hDiff : r-l=(2 : ℝ)^N*h := by dsimp [l,r]; ring
  have hPos : 0<r-l := by rw [hDiff]; positivity
  have hLen : r-l≤1 := hDiff.trans_le hLast
  have hf := boundaryL2_integrableOn_lift_Ioc f l r hLen
  have hFin : volume (Ioc l r)≠∞ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hc₀ : IntegrableOn (fun _ : ℝ => c₀) (Ioc l r) := integrableOn_const hFin
  have hcN : IntegrableOn (fun _ : ℝ => cN) (Ioc l r) := integrableOn_const hFin
  have hNorm₀ : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-c₀‖) (Ioc l r) := (hf.sub hc₀).norm
  have hNormN : IntegrableOn (fun t : ℝ => ‖f (t : Boundary)-cN‖) (Ioc l r) := (hf.sub hcN).norm
  have hC : IntegrableOn (fun _ : ℝ => ‖cN-c₀‖) (Ioc l r) := integrableOn_const hFin
  have hMean : ‖cN-c₀‖≤2*(N : ℝ)*B := norm_arcMean_doubling_le f B hB hMO a h hh N hLast
  have hMass : (∫ t in Ioc l r,‖f (t : Boundary)-cN‖)≤(r-l)*B := by
    have h := mul_le_mul_of_nonneg_left (hMO l r (sub_pos.mp hPos) hLen) hPos.le
    change (r-l)*((r-l)⁻¹*(∫ t in Ioc l r,‖f (t : Boundary)-cN‖))≤(r-l)*B at h
    rw [← mul_assoc,mul_inv_cancel₀ hPos.ne',one_mul] at h
    exact h
  have hPoint (t : ℝ) : ‖f (t : Boundary)-c₀‖≤‖f (t : Boundary)-cN‖+‖cN-c₀‖ := by
    calc
      _ = ‖(f (t : Boundary)-cN)+(cN-c₀)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  change (∫ t in Ioc l r,‖f (t : Boundary)-c₀‖)≤_
  calc
    _ ≤ ∫ t in Ioc l r,‖f (t : Boundary)-cN‖+‖cN-c₀‖ :=
      integral_mono hNorm₀ (hNormN.add hC) hPoint
    _ = (∫ t in Ioc l r,‖f (t : Boundary)-cN‖)+(r-l)*‖cN-c₀‖ := by
      rw [integral_add hNormN hC,setIntegral_const,Real.volume_real_Ioc_of_le (sub_nonneg.mp hPos.le),smul_eq_mul]
    _ ≤ (r-l)*B+(r-l)*(2*(N : ℝ)*B) :=
      add_le_add hMass (mul_le_mul_of_nonneg_left hMean hPos.le)
    _ = _ := by rw [hDiff]; ring

end TTO.Paper.Proved
