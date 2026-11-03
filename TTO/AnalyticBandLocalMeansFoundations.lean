/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.AngularPartitionFoundations
public import TTO.RotatingDiskIncidenceFoundations
public import TTO.AnalyticBandConvolutionFoundations
public import TTO.WeightedAnalyticDerivativeFoundations

/-! Actual analytic finite-band local means, with infinity-preserving area bounds. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology Interval
namespace TTO.Paper.Proved

/-- Actual extended local area energy as a function of the rotating center. -/
def rotatingDiskLowerIntegral (N : ℕ) (U : ℂ → ℝ≥0∞) (θ : Boundary) : ℝ≥0∞ :=
  ∫⁻ z in ball ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ) (2/(N : ℝ)),U z ∂volume

theorem measurable_rotatingDiskLowerIntegral (N : ℕ) (U : ℂ → ℝ≥0∞) (hU : Measurable U) :
    Measurable (rotatingDiskLowerIntegral N U) := by
  classical
  let V : Boundary × ℂ → ℝ≥0∞ := fun q =>
    if ‖q.2-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 q.1‖ < 2/(N : ℝ) then U q.2 else 0
  have hSet : MeasurableSet {q : Boundary × ℂ |
      ‖q.2-(positiveKernelRadius N : ℂ)*fourier (T := 1) 1 q.1‖ < 2/(N : ℝ)} := by
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hV : Measurable V := (hU.comp measurable_snd).indicator hSet
  have hEq : rotatingDiskLowerIntegral N U = fun θ => ∫⁻ z,V (θ,z) ∂volume := by
    funext θ
    dsimp only [rotatingDiskLowerIntegral]
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro z
    simp only [V,Set.indicator,mem_ball,dist_eq_norm]
  rw [hEq]
  exact hV.lintegral_prod_right'

/-- The ordinary finite local cell energy; analytic hypotheses below establish its literal meaning. -/
def analyticCellAreaEnergy (G : ℂ → ℂ) (N : ℕ) (p : ℝ) (θ : Boundary) : ℝ :=
  ((N : ℝ)^2/Real.pi)*∫ z in ball ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ)
    (2/(N : ℝ)),‖G z‖^p

theorem analyticCellAreaEnergy_nonneg (G : ℂ → ℂ) (N : ℕ) (p : ℝ) (θ : Boundary) :
    0 ≤ analyticCellAreaEnergy G N p θ := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem deformed_closedBall_subset_disk_boundary (N : ℕ) (hN : 10 ≤ N) (θ : Boundary) :
    closedBall ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ) (2/(N : ℝ)) ⊆ disk := by
  refine QuotientAddGroup.induction_on θ ?_
  intro θr
  exact deformed_arc_closedBall_subset_disk N hN θr

/-- Honest local ordinary integrability turns the cell energy into the actual lower integral.
Only disk analyticity is used; G need not be measurable outside the disk. -/
theorem ofReal_analyticCellAreaEnergy (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk)
    (N : ℕ) (hN : 10 ≤ N) (p : ℝ) (hp : 0 < p) (θ : Boundary) :
    ENNReal.ofReal (analyticCellAreaEnergy G N p θ) =
      ENNReal.ofReal ((N : ℝ)^2/Real.pi)*rotatingDiskLowerIntegral N (analyticPowerZero G p) θ := by
  have hClosed := deformed_closedBall_subset_disk_boundary N hN θ
  have hI := (integrableOn_analytic_norm_rpow_closedBall G _ _ p (hG.mono hClosed) hp.le).mono_set
    ball_subset_closedBall
  have hUI : ENNReal.ofReal (∫ z in ball ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 θ)
      (2/(N : ℝ)),‖G z‖^p) = rotatingDiskLowerIntegral N (analyticPowerZero G p) θ := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    simp only [analyticPowerZero,ite_eq_left (hClosed (ball_subset_closedBall hz))]
  rw [analyticCellAreaEnergy,ENNReal.ofReal_mul (by positivity),hUI]

/-- Every shifted angular cell is controlled by its actual local analytic area energy. -/
theorem analytic_shifted_short_arc_rpow_le_area (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk)
    (N : ℕ) (hN : 10 ≤ N) (p : ℝ) (hp : 0 < p) (x : Boundary) (c t : ℝ)
    (ht : |t-c| ≤ 1/(10*(N : ℝ))) :
    ‖G ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (x-(t : Boundary)))‖^p ≤
      analyticCellAreaEnergy G N p (x-(c : Boundary)) := by
  refine QuotientAddGroup.induction_on x ?_
  intro xr
  have hAngle : |(xr-t)-(xr-c)| ≤ 1/(10*(N : ℝ)) := by
    simpa only [show (xr-t)-(xr-c)=c-t by ring,abs_sub_comm] using ht
  exact analytic_short_arc_rpow_le_area G hG N hN p hp (xr-c) (xr-t) hAngle

/-- The extended energy of any shifted family has the SAME actual annulus bound. -/
theorem lintegral_ofReal_analyticCellAreaEnergy_shift_le (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk)
    (N : ℕ) (hN : 10 ≤ N) (p : ℝ) (hp : 0 < p) (c : Boundary) :
    (∫⁻ x : Boundary,ENNReal.ofReal (analyticCellAreaEnergy G N p (x-c)) ∂circleMeasure) ≤
      ENNReal.ofReal ((N : ℝ)^2/Real.pi)*ENNReal.ofReal (4/(N : ℝ))*
        (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero G p z ∂volume) := by
  simp_rw [ofReal_analyticCellAreaEnergy G hG N hN p hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_sub_right_eq_self]
  simpa only [rotatingDiskLowerIntegral,mul_assoc] using mul_le_mul_right
    (lintegral_rotating_disk_le N hN (analyticPowerZero G p)
      (measurable_analyticPowerZero G hG p hp.le)) (ENNReal.ofReal ((N : ℝ)^2/Real.pi))

/-- The actual finite-band pointwise local-means estimate, with every cell energy discharged. -/
theorem analyticWideBand_pointwise_cell_sum (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (m N N' n : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N) (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N)
    (hn : 1 ≤ n) (hnm : n ≤ m) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (x : Boundary) :
    ‖(analyticWideBandPolynomial m N N' F).eval (fourier (T := 1) 1 x)‖^p ≤
      (1/(10*(N : ℝ)))^p*∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p*
        analyticCellAreaEnergy (iteratedDeriv n F) N p (x-(angularGridCenter N j : Boundary)) := by
  let G := iteratedDeriv n F
  let K : Boundary → ℂ := fun t => (positiveWideInverseKernel m N N' n).eval (fourier (T := 1) 1 t)
  let H : Boundary → ℂ := fun t => G ((positiveKernelRadius N : ℂ)*fourier (T := 1) 1 (x-t))
  have hG : AnalyticOnNhd ℂ G disk := by simpa only [G,iteratedDeriv_eq_iterate] using hF.iterated_deriv n
  have hr := positiveKernelRadius_bounds N hN
  have hK : Continuous K := by dsimp only [K]; fun_prop
  have hCircle := continuous_analytic_circle G hG (positiveKernelRadius N) (by linarith [hr.1]) hr.2
  have hH : Continuous H := hCircle.comp (continuous_const.sub continuous_id)
  rw [norm_analyticWideBand_inverse_convolution F hF m N N' n hN hNN' hnm x]
  apply circle_angular_partition_product_rpow_le K H hK hH N (by omega) p hp hp1
    (angularInverseMajorant m N n)
    (fun j => analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary)))
  · intro j _
    exact angularInverseMajorant_nonneg m N n j hm
  · intro j _
    exact analyticCellAreaEnergy_nonneg G N p _
  · intro j hj t ht
    exact positiveWideInverseKernel_le_cell_majorant m N N' n j hm hN hNN' hRatio hn hnm
      (Finset.mem_range.mp hj) t ht
  · intro j _ t ht
    exact analytic_shifted_short_arc_rpow_le_area G hG N hN p hp x (angularGridCenter N j) t
      (angularGridCell_near_center N j (by omega) t ht)

/-- The ordinary analytic cell energy has its actual measurable extended representative. -/
theorem measurable_ofReal_analyticCellAreaEnergy (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G disk)
    (N : ℕ) (hN : 10 ≤ N) (p : ℝ) (hp : 0 < p) :
    Measurable (fun θ : Boundary => ENNReal.ofReal (analyticCellAreaEnergy G N p θ)) := by
  have hEq : (fun θ : Boundary => ENNReal.ofReal (analyticCellAreaEnergy G N p θ)) =
      fun θ => ENNReal.ofReal ((N : ℝ)^2/Real.pi)*rotatingDiskLowerIntegral N (analyticPowerZero G p) θ := by
    funext θ
    exact ofReal_analyticCellAreaEnergy G hG N hN p hp θ
  rw [hEq]
  exact measurable_const.mul (measurable_rotatingDiskLowerIntegral N (analyticPowerZero G p)
    (measurable_analyticPowerZero G hG p hp.le))

/-- Averaging the actual finite cell sum uses only measurable nonnegative energies and Tonelli. -/
theorem analyticWideBand_lintegral_cell_budget (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (m N N' n : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N) (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N)
    (hn : 1 ≤ n) (hnm : n ≤ m) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m N N' F).eval
      (fourier (T := 1) 1 x)‖^p) ∂circleMeasure) ≤
      ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*(∑ j ∈ Finset.range (10*N),ENNReal.ofReal ((angularInverseMajorant m N n j)^p))*
        ENNReal.ofReal ((N : ℝ)^2/Real.pi)*ENNReal.ofReal (4/(N : ℝ))*
          (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero (iteratedDeriv n F) p z ∂volume) := by
  let G := iteratedDeriv n F
  let A : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ)^2/Real.pi)*ENNReal.ofReal (4/(N : ℝ))*
    (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero G p z ∂volume)
  have hG : AnalyticOnNhd ℂ G disk := by simpa only [G,iteratedDeriv_eq_iterate] using hF.iterated_deriv n
  have hMeas := measurable_ofReal_analyticCellAreaEnergy G hG N hN p hp
  have hTerm (j : ℕ) : Measurable (fun x : Boundary =>
      ENNReal.ofReal ((angularInverseMajorant m N n j)^p)*
        ENNReal.ofReal (analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary)))) :=
    measurable_const.mul (hMeas.comp (measurable_id.sub measurable_const))
  have hLift (x : Boundary) : ENNReal.ofReal (‖(analyticWideBandPolynomial m N N' F).eval
      (fourier (T := 1) 1 x)‖^p) ≤ ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*
      ∑ j ∈ Finset.range (10*N),ENNReal.ofReal ((angularInverseMajorant m N n j)^p)*
        ENNReal.ofReal (analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary))) := by
    calc
      _ ≤ ENNReal.ofReal ((1/(10*(N : ℝ)))^p*∑ j ∈ Finset.range (10*N),
          (angularInverseMajorant m N n j)^p*analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary))) :=
        ENNReal.ofReal_le_ofReal (analyticWideBand_pointwise_cell_sum F hF m N N' n hm hN hNN' hRatio hn hnm p hp hp1 x)
      _ = _ := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) p),
          ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg
            (Real.rpow_nonneg (angularInverseMajorant_nonneg m N n j hm) p) (analyticCellAreaEnergy_nonneg G N p _))]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact ENNReal.ofReal_mul (Real.rpow_nonneg (angularInverseMajorant_nonneg m N n j hm) p)
  calc
    _ ≤ ∫⁻ x : Boundary,ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*
        ∑ j ∈ Finset.range (10*N),ENNReal.ofReal ((angularInverseMajorant m N n j)^p)*
          ENNReal.ofReal (analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary))) ∂circleMeasure :=
      lintegral_mono hLift
    _ = ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*∑ j ∈ Finset.range (10*N),
        ENNReal.ofReal ((angularInverseMajorant m N n j)^p)*
          ∫⁻ x : Boundary,ENNReal.ofReal (analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary))) ∂circleMeasure := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_finsetSum _ (fun j _ => hTerm j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact lintegral_const_mul' (ENNReal.ofReal ((angularInverseMajorant m N n j)^p))
        (fun x : Boundary => ENNReal.ofReal (analyticCellAreaEnergy G N p (x-(angularGridCenter N j : Boundary))))
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*∑ j ∈ Finset.range (10*N),
        ENNReal.ofReal ((angularInverseMajorant m N n j)^p)*A := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_right (lintegral_ofReal_analyticCellAreaEnergy_shift_le G hG N hN p hp _)
        (ENNReal.ofReal ((angularInverseMajorant m N n j)^p))
    _ = _ := by rw [← Finset.sum_mul]; dsimp only [A,G]; ring

/-- A uniform local-means constant, depending only on smoothing order and exponent. -/
def analyticBandLocalMeanConstant (m : ℕ) (p : ℝ) : ℝ :=
  (4/Real.pi)*(positiveWideDecayConstant m*2^(m+1))^p*
    angularGridWeightConstant (((m+1 : ℕ) : ℝ)*p)

theorem analyticBandLocalMeanConstant_pos (m : ℕ) (hm : 1 ≤ m) (p : ℝ) :
    0 < analyticBandLocalMeanConstant m p := by
  exact mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos (by positivity [positiveWideDecayConstant_pos m hm]) p))
    (angularGridWeightConstant_pos _)

/-- The complete finite-cell prefactor has the correct N^(1-np) scale. -/
theorem angularLocalMean_prefactor_le (m N n : ℕ) (hm : 1 ≤ m) (hN : 0 < N)
    (p : ℝ) (hp : 0 < p) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    (1/(10*(N : ℝ)))^p*(∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p)*
      ((N : ℝ)^2/Real.pi)*(4/(N : ℝ)) ≤
      analyticBandLocalMeanConstant m p*(N : ℝ)/((N : ℝ)^n)^p := by
  let K : ℝ := positiveWideDecayConstant m*2^(m+1)
  have hK : 0 < K := by dsimp only [K]; positivity [positiveWideDecayConstant_pos m hm]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hSum := sum_angularInverseMajorant_rpow_le m N n hm hN p hOrder
  have hBase : (1/(10*(N : ℝ)))*(K*(N : ℝ)/(N : ℝ)^n) ≤ K/(N : ℝ)^n := by
    calc
      _ = (K/(N : ℝ)^n)/10 := by field_simp
      _ ≤ _ := div_le_self (by positivity) (by norm_num)
  calc
    _ ≤ (1/(10*(N : ℝ)))^p*((K*(N : ℝ)/(N : ℝ)^n)^p*
        angularGridWeightConstant (((m+1 : ℕ) : ℝ)*p))*((N : ℝ)^2/Real.pi)*(4/(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSum (by positivity)) (by positivity)) (by positivity)
    _ = (((1/(10*(N : ℝ)))*(K*(N : ℝ)/(N : ℝ)^n))^p*
        angularGridWeightConstant (((m+1 : ℕ) : ℝ)*p))*((N : ℝ)^2/Real.pi)*(4/(N : ℝ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ (K/(N : ℝ)^n)^p*angularGridWeightConstant (((m+1 : ℕ) : ℝ)*p)*
        ((N : ℝ)^2/Real.pi)*(4/(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hBase hp.le)
          (angularGridWeightConstant_pos _).le) (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hK.le (by positivity)]
      dsimp only [analyticBandLocalMeanConstant,K]
      field_simp

/-- Actual analytic finite-band local means, preserving infinite source energy.
The p≤1 step is the proved finite-cell scalar triangle, never an averaging assumption. -/
theorem analyticWideBand_lintegral_le_annulus (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F disk)
    (m N N' n : ℕ) (hm : 1 ≤ m) (hN : 10 ≤ N) (hNN' : N ≤ N') (hRatio : 5*N' ≤ 6*N)
    (hn : 1 ≤ n) (hnm : n ≤ m) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m N N' F).eval
      (fourier (T := 1) 1 x)‖^p) ∂circleMeasure) ≤
      ENNReal.ofReal (analyticBandLocalMeanConstant m p*(N : ℝ)/((N : ℝ)^n)^p)*
        (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero (iteratedDeriv n F) p z ∂volume) := by
  have hSumNonneg : 0 ≤ ∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (angularInverseMajorant_nonneg m N n j hm) p)
  have hCoeff : ENNReal.ofReal ((1/(10*(N : ℝ)))^p*
      (∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p)*
      ((N : ℝ)^2/Real.pi)*(4/(N : ℝ))) =
      ENNReal.ofReal ((1/(10*(N : ℝ)))^p)*
        (∑ j ∈ Finset.range (10*N),ENNReal.ofReal ((angularInverseMajorant m N n j)^p))*
          ENNReal.ofReal ((N : ℝ)^2/Real.pi)*ENNReal.ofReal (4/(N : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_sum_of_nonneg
        (fun j _ => Real.rpow_nonneg (angularInverseMajorant_nonneg m N n j hm) p)]
  calc
    _ ≤ _ := analyticWideBand_lintegral_cell_budget F hF m N N' n hm hN hNN' hRatio hn hnm p hp hp1
    _ = ENNReal.ofReal ((1/(10*(N : ℝ)))^p*
        (∑ j ∈ Finset.range (10*N),(angularInverseMajorant m N n j)^p)*
          ((N : ℝ)^2/Real.pi)*(4/(N : ℝ)))*
        (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero (iteratedDeriv n F) p z ∂volume) := by rw [hCoeff]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (angularLocalMean_prefactor_le m N n hm (by omega) p hp hOrder)) _

/-- The same local-means constant is fixed before every analytic function, scale, and derivative order. -/
theorem exists_analyticWideBand_localMean_bound (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    ∃ C : ℝ,0 < C ∧ ∀ F : ℂ → ℂ,AnalyticOnNhd ℂ F disk →
      ∀ N N' n : ℕ,10 ≤ N → N ≤ N' → 5*N' ≤ 6*N → 1 ≤ n → n ≤ m →
        (∫⁻ x : Boundary,ENNReal.ofReal (‖(analyticWideBandPolynomial m N N' F).eval
          (fourier (T := 1) 1 x)‖^p) ∂circleMeasure) ≤
          ENNReal.ofReal (C*(N : ℝ)/((N : ℝ)^n)^p)*
            (∫⁻ z in rotatingDiskAnnulus N,analyticPowerZero (iteratedDeriv n F) p z ∂volume) :=
  ⟨analyticBandLocalMeanConstant m p,analyticBandLocalMeanConstant_pos m hm p,
    fun F hF N N' n hN hNN' hRatio hn hnm =>
      analyticWideBand_lintegral_le_annulus F hF m N N' n hm hN hNN' hRatio hn hnm p hp hp1 hOrder⟩

end TTO.Paper.Proved
