/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.SingularBoundaryFoundations
public import TTO.CompactHankelFoundations
/-! Literal Poisson kernel mass concentrates at the identity along strict interior radii. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

theorem radialPoisson_tail_nonneg (n : ℕ) (s : Boundary) :
    0≤atomicPoissonKernel (hankelRadius n : ℂ) s := by
  have hr := hankelRadius_mem n
  unfold atomicPoissonKernel
  rw [Complex.norm_real,Real.norm_of_nonneg hr.1.le]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [hr.1,hr.2]

theorem radialPoisson_integrable (n : ℕ) :
    Integrable (atomicPoissonKernel (hankelRadius n : ℂ)) circleMeasure := by
  have hr := hankelRadius_mem n
  have he (s : Boundary) : fourier (T:=1) 1 s-(hankelRadius n : ℂ)≠0 := by
    intro h
    have hnorm := congrArg norm (sub_eq_zero.mp h)
    simp only [fourier_apply,Circle.norm_coe,Complex.norm_real,Real.norm_of_nonneg hr.1.le] at hnorm
    linarith [hr.2]
  have hc : Continuous (atomicPoissonKernel (hankelRadius n : ℂ)) := by
    unfold atomicPoissonKernel
    exact continuous_const.div
      (((fourier (T:=1) 1).continuous.sub continuous_const).norm.pow 2)
      (fun s => pow_ne_zero 2 (norm_ne_zero_iff.mpr (he s)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A single positive chord-distance cutoff controls the entire closed tail. -/
theorem exists_radialPoisson_tail_bound (K : Set Boundary) (hK : IsClosed K) (h0 : (0 : Boundary)∉K) :
    ∃ δ : ℝ,0<δ ∧ ∀ n : ℕ,1-hankelRadius n≤δ/2 →
      ∀ s∈K,atomicPoissonKernel (hankelRadius n : ℂ) s≤4*(1-hankelRadius n^2)/δ^2 := by
  by_cases hne : K.Nonempty
  · have hcomp : IsCompact K := hK.isCompact
    have hc : Continuous (fun s : Boundary => ‖fourier (T:=1) 1 s-1‖) :=
      ((fourier (T:=1) 1).continuous.sub continuous_const).norm
    obtain ⟨s0,hs0,hmin⟩ := hcomp.exists_isMinOn hne hc.continuousOn
    let δ := ‖fourier (T:=1) 1 s0-1‖
    have hδ : 0<δ := by
      apply norm_pos_iff.mpr
      intro hz
      have hz0 : s0=0 := circleCharacter_injective (by simpa using sub_eq_zero.mp hz)
      exact h0 (hz0 ▸ hs0)
    refine ⟨δ,hδ,?_⟩
    intro n hn s hs
    have hr := hankelRadius_mem n
    have htriangle : δ≤‖fourier (T:=1) 1 s-(hankelRadius n : ℂ)‖+(1-hankelRadius n) := by
      calc
        δ ≤ ‖fourier (T:=1) 1 s-1‖ := hmin hs
        _ = ‖(fourier (T:=1) 1 s-(hankelRadius n : ℂ))+((hankelRadius n : ℂ)-1)‖ := by congr 1; ring
        _ ≤ _ := by
          have hnorm : ‖(hankelRadius n : ℂ)-1‖=1-hankelRadius n := by
            rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
              abs_of_neg (sub_neg.mpr hr.2)]
            ring
          have hh := norm_add_le (fourier (T:=1) 1 s-(hankelRadius n : ℂ)) ((hankelRadius n : ℂ)-1)
          rw [hnorm] at hh
          exact hh
    have hd : δ^2/4≤‖fourier (T:=1) 1 s-(hankelRadius n : ℂ)‖^2 := by
      have hnorm := norm_nonneg (fourier (T:=1) 1 s-(hankelRadius n : ℂ))
      nlinarith
    have hnum : 0≤1-hankelRadius n^2 := by nlinarith [hr.1,hr.2]
    unfold atomicPoissonKernel
    rw [Complex.norm_real,Real.norm_of_nonneg hr.1.le]
    apply (div_le_div_of_nonneg_left hnum (by positivity : 0<δ^2/4) hd).trans_eq
    field_simp
  · refine ⟨1,by norm_num,?_⟩
    intro n hn s hs
    exact (hne ⟨s,hs⟩).elim

theorem tendsto_radialPoisson_closed_tail (K : Set Boundary) (hK : IsClosed K) (h0 : (0 : Boundary)∉K) :
    Tendsto (fun n => ∫ s in K,atomicPoissonKernel (hankelRadius n : ℂ) s ∂circleMeasure)
      atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hbound⟩ := exists_radialPoisson_tail_bound K hK h0
  have hr : Tendsto (fun n => 1-hankelRadius n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (tendsto_hankelRadius.mono_right nhdsWithin_le_nhds)
  have hev : ∀ᶠ n in atTop,1-hankelRadius n≤δ/2 :=
    (hr.eventually (gt_mem_nhds (half_pos hδ))).mono (fun _ h => h.le)
  have hlim : Tendsto (fun n => 4*(1-hankelRadius n^2)/δ^2) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_hankelRadius.mono_right nhdsWithin_le_nhds).pow 2
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub h).const_mul 4).div_const (δ^2)
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    setIntegral_nonneg hK.measurableSet (fun s _ => radialPoisson_tail_nonneg n s))) ?_ hlim
  filter_upwards [hev] with n hn
  have hrn := hankelRadius_mem n
  have hC : 0≤4*(1-hankelRadius n^2)/δ^2 := by
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [hrn.1,hrn.2]
  have hm := setIntegral_mono_on (radialPoisson_integrable n).integrableOn
    (integrable_const (4*(1-hankelRadius n^2)/δ^2)) hK.measurableSet (hbound n hn)
  have hc : (∫ s in K,4*(1-hankelRadius n^2)/δ^2 ∂circleMeasure)≤4*(1-hankelRadius n^2)/δ^2 := by
    simpa using (setIntegral_le_integral (μ:=circleMeasure) (s:=K)
      (integrable_const (4*(1-hankelRadius n^2)/δ^2))
      (Eventually.of_forall (fun _ => hC)))
  exact hm.trans hc

end TTO.Paper.Proved
