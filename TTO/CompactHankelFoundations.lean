/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AtomicPolynomialFoundations
public import TTO.IntervalAverageFoundations
public import TTO.KernelRemainderFoundations

/-! Actual continuous radial-symbol approximations to compact represented Hankel operators.
This module does not assert a Nehari lift, an exact continuous representative, or VMOA equivalence. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Finset
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Pin native operator norm structures before constructing maps between operator spaces. -/
local instance hankelOperatorNormed : NormedAddCommGroup HankelOperator := inferInstance
local instance hankelOperatorNormedSpace : NormedSpace ℂ HankelOperator := inferInstance
local instance sequenceOperatorNormed : NormedAddCommGroup SequenceOperator := inferInstance
local instance sequenceOperatorNormedSpace : NormedSpace ℂ SequenceOperator := inferInstance


def hankelRadius (n : ℕ) : ℝ := 1-((n : ℝ)+2)⁻¹

theorem hankelRadius_mem (n : ℕ) : hankelRadius n∈Ioo (0 : ℝ) 1 := by
  have hn : 1<(n : ℝ)+2 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0<(n : ℝ)+2 := by linarith
  have hi := (inv_lt_one₀ hp).mpr hn
  have hi0 := inv_pos.mpr hp
  constructor <;> dsimp only [hankelRadius] <;> linarith

theorem tendsto_hankelRadius : Tendsto hankelRadius atTop (𝓝[<] (1 : ℝ)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => ((n : ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall (fun n => (hankelRadius_mem n).2)⟩
  change Tendsto (fun n : ℕ => 1-((n : ℝ)+2)⁻¹) atTop (𝓝 1)
  simpa only [sub_zero] using tendsto_const_nhds.sub hi

def hankelRadialDiagonal (n : ℕ) : SequenceOperator :=
  diagonalOperator (fun k => (hankelRadius n : ℂ)^k) 1 zero_le_one
    (fun k => by
      rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (hankelRadius_mem n).1.le]
      exact pow_le_one₀ (hankelRadius_mem n).1.le (hankelRadius_mem n).2.le)

theorem hankelRadialDiagonal_diagonal (n : ℕ) :
    Diagonal (fun k => (hankelRadius n : ℂ)^k) (hankelRadialDiagonal n) :=
  diagonalOperator_isDiagonal _ _ _ _

theorem norm_hankelRadialDiagonal_le_one (n : ℕ) : ‖hankelRadialDiagonal n‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
  intro k
  rw [diagonal_apply _ _ (hankelRadialDiagonal_diagonal n),norm_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (hankelRadius_mem n).1.le]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hankelRadius_mem n).1.le (hankelRadius_mem n).2.le)

theorem hankelRadialDiagonal_adjoint (n : ℕ) :
    (hankelRadialDiagonal n).adjoint=hankelRadialDiagonal n := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  rw [diagonal_apply _ _ (diagonal_adjoint _ _ (hankelRadialDiagonal_diagonal n)),
    diagonal_apply _ _ (hankelRadialDiagonal_diagonal n)]
  simp only [map_pow,Complex.conj_ofReal]

theorem hankelRadialDiagonal_eq_hardyRadial (n : ℕ) (x : SequenceL2) :
    hankelRadialDiagonal n x=
      hardyBasis.repr (hardyRadialBoundary (hardyBasis.repr.symm x) (hankelRadius n)) := by
  apply lp.ext
  funext k
  rw [diagonal_apply _ _ (hankelRadialDiagonal_diagonal n),
    hardyBasis_repr_hardyRadialBoundary _ _ (hankelRadius_mem n).1.le (hankelRadius_mem n).2]
  simp only [hardyRadialCoeff,←hardyBasis_repr_eq_fourierCoeff,LinearIsometryEquiv.apply_symm_apply]

theorem tendsto_hankelRadialDiagonal (x : SequenceL2) :
    Tendsto (fun n => hankelRadialDiagonal n x) atTop (𝓝 x) := by
  have h := (tendsto_hardyRadialBoundary (hardyBasis.repr.symm x)).comp tendsto_hankelRadius
  have hr := (hardyBasis.repr.continuous.tendsto (hardyBasis.repr.symm x)).comp h
  change Tendsto (fun n => hardyBasis.repr (hardyRadialBoundary (hardyBasis.repr.symm x) (hankelRadius n)))
    atTop (𝓝 (hardyBasis.repr (hardyBasis.repr.symm x))) at hr
  rw [LinearIsometryEquiv.apply_symm_apply] at hr
  exact hr.congr' (Eventually.of_forall (fun n => (hankelRadialDiagonal_eq_hardyRadial n x).symm))

/-- The radial Hardy series converges in the actual continuous boundary-function space. -/
def hankelRadialContinuous (g : Hardy) (n : ℕ) : C(Boundary,ℂ) :=
  ∑' k : ℕ, hardyRadialCoeff g (hankelRadius n) k • fourier (T:=1) (k : ℤ)

theorem summable_hankelRadialContinuous (g : Hardy) (n : ℕ) :
    Summable (fun k : ℕ => hardyRadialCoeff g (hankelRadius n) k • fourier (T:=1) (k : ℤ) :
      ℕ → C(Boundary,ℂ)) := by
  refine Summable.of_norm_bounded
    (summable_norm_hardyRadialCoeff g _ (hankelRadius_mem n).1.le (hankelRadius_mem n).2) (fun k => ?_)
  rw [norm_smul,fourier_norm,mul_one]

theorem hankelRadialContinuous_toL2 (g : Hardy) (n : ℕ) :
    ContinuousMap.toLp 2 circleMeasure ℂ (hankelRadialContinuous g n)=
      (hardyRadialBoundary g (hankelRadius n)).val := by
  rw [hankelRadialContinuous,hardyRadialBoundary,←hardy.subtypeL_apply,
    ContinuousLinearMap.map_tsum _ (summable_hardyRadialBoundary g _ (hankelRadius_mem n).1.le (hankelRadius_mem n).2),
    ContinuousLinearMap.map_tsum _ (summable_hankelRadialContinuous g n)]
  congr 1
  funext k
  simp [coe_fourierBasis,hardyMode]


/-- A uniformly contractive, strongly identity-convergent family converges in operator
norm after a compact factor. Only the ordinary operator Banach space is used. -/
theorem tendsto_contractive_compact_factor
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : ℕ → F →L[ℂ] F) (hBound : ∀ n,‖S n‖≤1)
    (hStrong : ∀ y,Tendsto (fun n => S n y) atTop (𝓝 y))
    (A : E →L[ℂ] F) (hA : IsCompactOperator A) :
    Tendsto (fun n => S n ∘L A) atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hAK⟩ := hA.image_closedBall_subset_compact 1
  obtain ⟨t,_htK,ht,hKt⟩ := hK.finite_cover_balls (show 0<ε/8 by positivity)
  have hEvent : ∀ᶠ n in atTop, ∀ y∈t, ‖S n y-y‖<ε/2 := by
    apply ht.eventually_all.mpr
    intro y _hy
    have h := (hStrong y).eventually (Metric.ball_mem_nhds y (half_pos hε))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hContract (n : ℕ) (x : F) : ‖S n x‖≤‖x‖ := by
    exact ((S n).le_opNorm x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg x))
  have hLip (n : ℕ) (x : F) : ‖S n x-x‖≤2*‖x‖ := by
    have hn := norm_sub_le (S n x) x
    have hc := hContract n x
    linarith
  filter_upwards [hEvent] with n he
  have hNorm : ‖S n ∘L A-A‖≤3*ε/4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hKt (hAK ⟨x,by simp [hx],rfl⟩))
    have hd : ‖A x-y‖<ε/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using! hxy
    change ‖S n (A x)-A x‖≤_
    have hs : S n (A x)-A x=(S n (A x-y)-(A x-y))+(S n y-y) := by
      simp only [map_sub]
      abel
    rw [hs]
    have hn := norm_add_le (S n (A x-y)-(A x-y)) (S n y-y)
    have h₁ := hLip n (A x-y)
    have h₂ := he y hy
    linarith
  rw [dist_eq_norm]
  exact hNorm.trans_lt (by linarith)

theorem tendsto_hankelRadialDiagonal_compact_left (K : SequenceOperator) (hK : IsCompactOperator K) :
    Tendsto (fun n => hankelRadialDiagonal n ∘L K) atTop (𝓝 K) :=
  tendsto_contractive_compact_factor hankelRadialDiagonal norm_hankelRadialDiagonal_le_one
    tendsto_hankelRadialDiagonal K hK

theorem tendsto_hankelRadialDiagonal_compact_right (K : SequenceOperator) (hK : IsCompactOperator K) :
    Tendsto (fun n => K ∘L hankelRadialDiagonal n) atTop (𝓝 K) := by
  have h := tendsto_hankelRadialDiagonal_compact_left K.adjoint (compact_adjoint_of_compact K hK)
  have ha := (ContinuousLinearMap.adjoint.continuous.tendsto K.adjoint).comp h
  simpa only [Function.comp_def,ContinuousLinearMap.adjoint_comp,hankelRadialDiagonal_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using ha

theorem norm_contractive_sandwich_error
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D K : H →L[ℂ] H) (hD : ‖D‖≤1) :
    ‖D ∘L K ∘L D-K‖≤‖K ∘L D-K‖+‖D ∘L K-K‖ := by
  have he : D ∘L K ∘L D-K=D ∘L (K ∘L D-K)+(D ∘L K-K) := by
    rw [ContinuousLinearMap.comp_sub]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [he]
  calc
    _ ≤ ‖D ∘L (K ∘L D-K)‖+‖D ∘L K-K‖ := ContinuousLinearMap.opNorm_add_le (𝕜:=ℂ) (𝕜₂:=ℂ) (E:=H) (F:=H) (σ₁₂:=RingHom.id ℂ) (D ∘L (K ∘L D-K)) (D ∘L K-K)
    _ ≤ ‖D‖*‖K ∘L D-K‖+‖D ∘L K-K‖ := add_le_add (ContinuousLinearMap.opNorm_comp_le D (K ∘L D-K)) le_rfl
    _ ≤ 1*‖K ∘L D-K‖+‖D ∘L K-K‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hD (norm_nonneg (K ∘L D-K))) le_rfl
    _ = _ := by rw [one_mul]

theorem tendsto_hankelRadialDiagonal_compact_sandwich (K : SequenceOperator) (hK : IsCompactOperator K) :
    Tendsto (fun n => hankelRadialDiagonal n ∘L K ∘L hankelRadialDiagonal n) atTop (𝓝 K) := by
  have hl := tendsto_hankelRadialDiagonal_compact_left K hK
  have hr := tendsto_hankelRadialDiagonal_compact_right K hK
  rw [tendsto_iff_norm_sub_tendsto_zero] at hl hr ⊢
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_contractive_sandwich_error (hankelRadialDiagonal n) K (norm_hankelRadialDiagonal_le_one n))
    (by simpa only [add_zero] using hr.add hl)


/-- Coordinate transport uses the genuine complete positive and negative Fourier bases. -/
def hankelSequenceOperator (H : HankelOperator) : SequenceOperator :=
  negativeBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L H ∘L hardyBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

def hankelFromSequence : SequenceOperator →L[ℂ] HankelOperator :=
  ContinuousLinearMap.postcomp Hardy negativeBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousLinearMap.precomp SequenceL2 hardyBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem hankelFromSequence_toSequence (H : HankelOperator) :
    hankelFromSequence (hankelSequenceOperator H)=H := by
  ext f
  simp [hankelFromSequence,hankelSequenceOperator]

def hankelRadialOperator (H : HankelOperator) (n : ℕ) : HankelOperator :=
  hankelFromSequence (hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L hankelRadialDiagonal n)

theorem tendsto_hankelRadialOperator (H : HankelOperator) (hH : IsCompactOperator H) :
    Tendsto (hankelRadialOperator H) atTop (𝓝 H) := by
  have hK : IsCompactOperator (hankelSequenceOperator H) :=
    (hH.comp_clm hardyBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp negativeBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have h := tendsto_hankelRadialDiagonal_compact_sandwich (hankelSequenceOperator H) hK
  have hm := (hankelFromSequence.continuous.tendsto (hankelSequenceOperator H)).comp h
  change Tendsto (fun n => hankelFromSequence (hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L hankelRadialDiagonal n))
    atTop (𝓝 H)
  simpa only [Function.comp_def,hankelFromSequence_toSequence] using hm

theorem hankelSequenceOperator_entry (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (i j : ℕ) :
    hankelSequenceOperator H (lp.single 2 j 1) i=conj (fourierCoeff g.val ((i+j : ℕ) : ℤ)) := by
  change negativeBasis.repr (H (hardyBasis.repr.symm (lp.single 2 j 1))) i=_
  rw [hardyBasis.repr_symm_single,HilbertBasis.repr_apply_apply,
    representsHankel_columns _ H hH,hankelColumn_coefficient]

theorem fourierCoeff_hardyRadialBoundary (g : Hardy) (r : ℝ) (hr : 0≤r) (hr1 : r<1) (k : ℕ) :
    fourierCoeff (hardyRadialBoundary g r).val (k : ℤ)=(r : ℂ)^k*fourierCoeff g.val (k : ℤ) := by
  change fourierCoeff (hardyRadialBoundary g r).val (k : ℤ)=hardyRadialCoeff g r k
  exact (hardyBasis_repr_eq_fourierCoeff (hardyRadialBoundary g r) k).symm.trans
    (hardyBasis_repr_hardyRadialBoundary g r hr hr1 k)

/-- Radial damping is exactly the two-sided diagonal sandwich, with no extra radius factor. -/
theorem hankelRadialOperator_represents (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (n : ℕ) :
    RepresentsHankel (star (multiply coordinate (hardyRadialBoundary g (hankelRadius n)).val))
      (hankelRadialOperator H n) := by
  apply representsHankel_of_columns
  intro j
  apply negativeBasis.repr.injective
  apply lp.ext
  funext i
  change negativeBasis.repr
    (negativeBasis.repr.symm ((hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L
      hankelRadialDiagonal n) (hardyBasis.repr (hardyBasis j)))) i=_
  rw [LinearIsometryEquiv.apply_symm_apply,hardyBasis.repr_self]
  change hankelRadialDiagonal n (hankelSequenceOperator H (hankelRadialDiagonal n (lp.single 2 j 1))) i=_
  rw [hankelRadialDiagonal_diagonal n j,map_smul,map_smul]
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  rw [diagonal_apply _ _ (hankelRadialDiagonal_diagonal n),hankelSequenceOperator_entry g H hH,
    HilbertBasis.repr_apply_apply,hankelColumn_coefficient]
  rw [fourierCoeff_hardyRadialBoundary g _ (hankelRadius_mem n).1.le (hankelRadius_mem n).2]
  simp only [map_mul,map_pow,Complex.conj_ofReal,pow_add]
  ring

/-- The approximating symbol is a genuine continuous circle function. -/
def hankelContinuousRadialSymbol (g : Hardy) (n : ℕ) : C(Boundary,ℂ) :=
  star ((fourier (T:=1) 1)*hankelRadialContinuous g n)

theorem hankelContinuousRadialSymbol_toL2 (g : Hardy) (n : ℕ) :
    ContinuousMap.toLp 2 circleMeasure ℂ (hankelContinuousRadialSymbol g n)=
      star (multiply coordinate (hardyRadialBoundary g (hankelRadius n)).val) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure (hankelContinuousRadialSymbol g n),
    Lp.coeFn_star (multiply coordinate (hardyRadialBoundary g (hankelRadius n)).val),
    multiply_ae coordinate (hardyRadialBoundary g (hankelRadius n)).val,coordinate_ae,
    ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) circleMeasure (hankelRadialContinuous g n)] with t hc hs hm hz hg
  rw [hankelRadialContinuous_toL2] at hg
  rw [hc,hs]
  change star ((fourier (T:=1) 1 t)*(hankelRadialContinuous g n) t)=
    star ((multiply coordinate (hardyRadialBoundary g (hankelRadius n)).val) t)
  rw [hm,hz,hg]

/-- Compact represented Hankel operators are operator-norm limits of their actual
continuous radial-symbol Hankels. This is approximation, not an exact continuous lift. -/
theorem compactHankel_continuous_radial_approximation (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hCompact : IsCompactOperator H) :
    (∀ n,RepresentsHankel (ContinuousMap.toLp 2 circleMeasure ℂ (hankelContinuousRadialSymbol g n))
      (hankelRadialOperator H n)) ∧ Tendsto (hankelRadialOperator H) atTop (𝓝 H) := by
  refine ⟨fun n => ?_,tendsto_hankelRadialOperator H hCompact⟩
  rw [hankelContinuousRadialSymbol_toL2]
  exact hankelRadialOperator_represents g H hH n


theorem compact_hankelRadialDiagonal (n : ℕ) : IsCompactOperator (hankelRadialDiagonal n) := by
  apply compact_diagonal_of_tendsto _ _ (hankelRadialDiagonal_diagonal n)
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  simpa only [Complex.norm_real,Real.norm_of_nonneg (hankelRadius_mem n).1.le]
    using (hankelRadius_mem n).2

theorem compact_hankelFromSequence (K : SequenceOperator) (hK : IsCompactOperator K) :
    IsCompactOperator (hankelFromSequence K) := by
  exact (hK.comp_clm hardyBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    negativeBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem compact_hankelRadialOperator (H : HankelOperator) (n : ℕ) :
    IsCompactOperator (hankelRadialOperator H n) :=
  compact_hankelFromSequence _ ((compact_hankelRadialDiagonal n).comp_clm
    (hankelSequenceOperator H ∘L hankelRadialDiagonal n))

theorem compact_iff_tendsto_hankelRadialOperator (H : HankelOperator) :
    IsCompactOperator H ↔ Tendsto (hankelRadialOperator H) atTop (𝓝 H) := by
  refine ⟨tendsto_hankelRadialOperator H,fun h => ?_⟩
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto h
    (Eventually.of_forall (compact_hankelRadialOperator H))

/-- Explicit operator-norm convergence, independent of inference of the CLM metric structure. -/
theorem tendsto_norm_hankelRadialOperator_sub (H : HankelOperator) (hH : IsCompactOperator H) :
    Tendsto (fun n => ‖hankelRadialOperator H n-H‖) atTop (𝓝 0) := by
  have hK : IsCompactOperator (hankelSequenceOperator H) :=
    (hH.comp_clm hardyBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      negativeBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hLim := tendsto_hankelRadialDiagonal_compact_sandwich (hankelSequenceOperator H) hK
  rw [tendsto_iff_norm_sub_tendsto_zero] at hLim
  have hB (n : ℕ) : ‖hankelRadialOperator H n-H‖ ≤ ‖hankelFromSequence‖*
      ‖hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L hankelRadialDiagonal n-hankelSequenceOperator H‖ := by
    have he : hankelRadialOperator H n-H=hankelFromSequence
        (hankelRadialDiagonal n ∘L hankelSequenceOperator H ∘L hankelRadialDiagonal n-hankelSequenceOperator H) := by
      rw [map_sub,hankelFromSequence_toSequence]
      rfl
    rw [he]
    exact hankelFromSequence.le_opNorm _
  exact squeeze_zero (fun n => norm_nonneg _) hB (by simpa only [mul_zero] using hLim.const_mul ‖hankelFromSequence‖)

/-- Every requested operator-norm accuracy is achieved by an actual continuous
radial boundary symbol and an actual compact Hankel operator. -/
theorem compactHankel_exists_continuous_approximation (g : Hardy) (H : HankelOperator)
    (hH : RepresentsHankel (star (multiply coordinate g.val)) H) (hCompact : IsCompactOperator H)
    (ε : ℝ) (hε : 0<ε) :
    ∃ a : C(Boundary,ℂ), ∃ K : HankelOperator,
      RepresentsHankel (ContinuousMap.toLp 2 circleMeasure ℂ a) K ∧ IsCompactOperator K ∧ ‖H-K‖<ε := by
  have hLim := tendsto_norm_hankelRadialOperator_sub H hCompact
  have he : ∀ᶠ n in atTop, ‖hankelRadialOperator H n-H‖<ε := hLim.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨hankelContinuousRadialSymbol g N,hankelRadialOperator H N,?_,
    compact_hankelRadialOperator H N,?_⟩
  · rw [hankelContinuousRadialSymbol_toL2]
    exact hankelRadialOperator_represents g H hH N
  · rw [norm_sub_rev]
    exact hN N le_rfl

end TTO.Paper.Proved
