/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.HalfIntervalFourierFoundations
public import TTO.PaleyWienerKernelFoundations
public import Mathlib.Analysis.PSeries

/-! Exact approximation numbers of the actual Volterra operator. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- The literal positive singular-value sequence, indexed from n=0. -/
def volterraWeight (ℓ : ℝ) (n : ℕ) : ℂ :=
  ((ℓ / (Real.pi * ((n : ℝ) + 1 / 2)) : ℝ) : ℂ)

theorem volterraWeight_eq_inv_frequency (ℓ : ℝ) (n : ℕ) :
    volterraWeight ℓ n = (halfFrequency ℓ n : ℂ)⁻¹ := by
  simp only [volterraWeight, halfFrequency, Complex.ofReal_div, inv_div]

/-- The actual operator in the two complete normalized coordinate bases. -/
def volterraDiagonal (ℓ : ℝ) (hℓ : 0 < ℓ) : SequenceOperator :=
  (halfSineBasis ℓ hℓ).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    volterraOperator ℓ ∘L
    (halfCosineBasis ℓ hℓ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem volterraDiagonal_diagonal (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Diagonal (volterraWeight ℓ) (volterraDiagonal ℓ hℓ) := by
  intro n
  change (halfSineBasis ℓ hℓ).repr
    (volterraOperator ℓ ((halfCosineBasis ℓ hℓ).repr.symm (lp.single 2 n (1 : ℂ)))) = _
  rw [HilbertBasis.repr_symm_single, halfCosineBasis_apply, volterraOperator_halfCosineVector ℓ hℓ n,
    ← halfSineBasis_apply ℓ hℓ n, map_smul, HilbertBasis.repr_self,
    volterraWeight_eq_inv_frequency]

/-- Antitone diagonal magnitudes have their exact zero-based approximation numbers. -/
theorem approximationNumber_diagonal_of_antitone (w : ℕ → ℂ) (D : SequenceOperator)
    (hd : Diagonal w D) (ha : Antitone (fun n => ‖w n‖)) (n : ℕ) :
    (approximationNumber D n : ℝ) = ‖w n‖ := by
  apply le_antisymm
  · have hu := approximationNumber_diagonal_le w D hd n (Finset.range n)
      (by simp only [Finset.card_range, le_refl]) ‖w n‖₊ (fun i hi => by
        have hni : n ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
        simpa only [coe_nnnorm] using ha hni)
    exact_mod_cast hu
  · exact le_approximationNumber_diagonal_of_card w D hd (Finset.range (n + 1))
      (by simp only [Finset.card_range]; omega) ‖w n‖
      (fun i hi => ha (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

theorem norm_volterraWeight (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    ‖volterraWeight ℓ n‖ = ℓ / (Real.pi * ((n : ℝ) + 1 / 2)) := by
  rw [volterraWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact div_pos hℓ (mul_pos Real.pi_pos (by positivity))

theorem volterraWeight_norm_antitone (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Antitone (fun n => ‖volterraWeight ℓ n‖) := by
  intro m n hmn
  dsimp only
  rw [norm_volterraWeight ℓ hℓ, norm_volterraWeight ℓ hℓ]
  apply div_le_div_of_nonneg_left hℓ.le (mul_pos Real.pi_pos (by positivity))
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  have hreal : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  linarith

/-- Right unitary coordinate changes preserve every approximation number. -/
theorem approximationNumber_comp_unitary {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (U : E ≃ₗᵢ[ℂ] F) (n : ℕ) :
    approximationNumber (A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap) n =
      approximationNumber A n := by
  apply le_antisymm
  · exact approximationNumber_comp_right_contraction A _ (norm_isometry_clm_le_one U.toLinearIsometry) n
  · have h := approximationNumber_comp_right_contraction
      (A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap)
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      (norm_isometry_clm_le_one U.symm.toLinearIsometry) n
    have he : (A ∘L U.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap = A := by
      apply ContinuousLinearMap.ext
      intro x
      change A (U (U.symm x)) = A x
      rw [U.apply_symm_apply]
    rw [he] at h
    exact h

theorem approximationNumber_volterraDiagonal (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    approximationNumber (volterraDiagonal ℓ hℓ) n = approximationNumber (volterraOperator ℓ) n := by
  rw [volterraDiagonal, approximationNumber_unitary_comp, approximationNumber_comp_unitary]

/-- The exact zero-based singular values of the actual interval integral map. -/
theorem approximationNumber_volterraOperator (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) :
    (approximationNumber (volterraOperator ℓ) n : ℝ) =
      ℓ / (Real.pi * ((n : ℝ) + 1 / 2)) := by
  rw [← approximationNumber_volterraDiagonal ℓ hℓ n,
    approximationNumber_diagonal_of_antitone (volterraWeight ℓ) _
      (volterraDiagonal_diagonal ℓ hℓ) (volterraWeight_norm_antitone ℓ hℓ), norm_volterraWeight ℓ hℓ]

/-- The literal integral map factors through the actual complete basis diagonal. -/
theorem volterraOperator_factorization (ℓ : ℝ) (hℓ : 0 < ℓ) :
    volterraOperator ℓ =
      (halfSineBasis ℓ hℓ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        volterraDiagonal ℓ hℓ ∘L
        (halfCosineBasis ℓ hℓ).repr.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  change volterraOperator ℓ f = (halfSineBasis ℓ hℓ).repr.symm
    ((halfSineBasis ℓ hℓ).repr (volterraOperator ℓ
      ((halfCosineBasis ℓ hℓ).repr.symm ((halfCosineBasis ℓ hℓ).repr f))))
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem tendsto_volterraWeight (ℓ : ℝ) (_hℓ : 0 < ℓ) :
    Tendsto (volterraWeight ℓ) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop.mpr fun b => (hn.eventually_ge_atTop b).mono fun n h => by linarith
  have hd : Tendsto (fun n : ℕ => Real.pi * ((n : ℝ) + 1 / 2)) atTop atTop :=
    hshift.const_mul_atTop Real.pi_pos
  have hv : Tendsto (fun n : ℕ => ℓ / (Real.pi * ((n : ℝ) + 1 / 2))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have hw := (Complex.continuous_ofReal.tendsto 0).comp hv
  simp only [Complex.ofReal_zero] at hw
  exact hw.congr' (Eventually.of_forall fun n => rfl)

theorem isCompactOperator_volterraOperator (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsCompactOperator (volterraOperator ℓ) := by
  have hd := compact_diagonal_of_tendsto (volterraWeight ℓ) (volterraDiagonal ℓ hℓ)
    (volterraDiagonal_diagonal ℓ hℓ) (tendsto_volterraWeight ℓ hℓ)
  rw [volterraOperator_factorization ℓ hℓ]
  exact (hd.comp_clm (halfCosineBasis ℓ hℓ).repr.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (halfSineBasis ℓ hℓ).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The integral formula determines the bounded operator uniquely, including empty intervals. -/
theorem representsVolterra_unique (ℓ : ℝ) (V : IntervalL2 ℓ →L[ℂ] IntervalL2 ℓ)
    (hV : RepresentsVolterra ℓ V) : V = volterraOperator ℓ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hV f, volterraOperator_represents ℓ f] with t h₁ h₂
  exact h₁.trans h₂.symm

/-- Full E12 obligation: every actual Volterra representative is compact and has the exact numbers. -/
theorem volterraSpectrum : VolterraSpectrumObligation := by
  intro ℓ hℓ V hV
  rw [representsVolterra_unique ℓ V hV]
  exact ⟨isCompactOperator_volterraOperator ℓ hℓ, approximationNumber_volterraOperator ℓ hℓ⟩

/-- The shifted p-series criterion for the literal Volterra values, for every p>0. -/
theorem volterraSeries : VolterraSeriesObligation := by
  intro ℓ hℓ p _hp
  have hc : (ℓ / Real.pi) ^ p ≠ 0 :=
    (Real.rpow_pos_of_pos (div_pos hℓ Real.pi_pos) p).ne'
  have he (n : ℕ) : (ℓ / (Real.pi * ((n : ℝ) + 1 / 2))) ^ p =
      (ℓ / Real.pi) ^ p * (1 / |(n : ℝ) + 1 / 2| ^ p) := by
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 1 / 2),
      Real.div_rpow hℓ.le (by positivity) p,
      Real.mul_rpow Real.pi_pos.le (by positivity), Real.div_rpow hℓ.le Real.pi_pos.le p]
    ring
  simp_rw [he]
  exact (summable_mul_left_iff hc).trans (Real.summable_one_div_nat_add_rpow (1 / 2) p)

/-- Positive interval L² is genuinely infinite-dimensional, using the actual complete cosine basis. -/
theorem intervalDimension : IntervalDimensionObligation := by
  intro ℓ hℓ hfd
  let : FiniteDimensional ℂ (IntervalL2 ℓ) := hfd
  let N := Module.finrank ℂ (IntervalL2 ℓ) + 1
  have hi := (halfCosineBasis ℓ hℓ).orthonormal.linearIndependent.comp
    (fun i : Fin N => (i : ℕ)) Fin.val_injective
  have hh := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  dsimp only [N] at hh
  omega

/-- Exact ideal membership for the actual Volterra operator, including the below-one obstruction. -/
theorem schatten_volterraOperator_iff (ℓ : ℝ) (hℓ : 0 < ℓ) (p : ℝ) (hp : 0 < p) :
    Schatten p (volterraOperator ℓ) ↔ 1 < p := by
  constructor
  · intro h
    apply (volterraSeries ℓ hℓ p hp).mp
    simpa only [approximationNumber_volterraOperator ℓ hℓ] using h.2.2
  · intro h
    refine ⟨hp, isCompactOperator_volterraOperator ℓ hℓ, ?_⟩
    simpa only [approximationNumber_volterraOperator ℓ hℓ] using (volterraSeries ℓ hℓ p hp).mpr h

/-- Endpoint example reduced to the one-atom splitting lemma, supplied separately
by the atomic foundation modules. -/
theorem endpointObstruction_of_oneAtom (hOne : OneAtomObligation) : EndpointConclusion :=
  Reduction.endpointObstruction hOne schattenMonotonicity exists_volterraModelData
    volterraSpectrum volterraSeries intervalDimension scalarCompact idealLaws
    unitaryIdealLaws unitaryAlgebraLaws finiteRankSchatten coreLaws scalarSplit

end TTO.Paper.Proved
