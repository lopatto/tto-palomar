/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import TTO.ThinWideOffDiagonalFoundations
public import TTO.ThinWideSchurFoundations
public import TTO.FiniteDisjointBlockBudgetFoundations
public import Mathlib.Algebra.Order.Field.GeomSum

/-! Finite residue grids, geometric off-diagonal sums, and bounded nearby-band multiplicity.
These estimates keep actual error terms and never use a low-p pinching assertion. -/
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology
namespace TTO.Paper.Proved
open Reduction

/-- Literal residue-grid level; the first coordinate is the residue. -/
def residueGridLevel (M J : ℕ) (i : Fin M × Fin J) : ℕ := i.1.val+M*i.2.val

theorem residueGridLevel_lt (M J : ℕ) (i : Fin M × Fin J) : residueGridLevel M J i < M*J := by
  have h := Nat.mul_le_mul_left M (Nat.succ_le_of_lt i.2.isLt)
  dsimp only [residueGridLevel]
  nlinarith [i.1.isLt]

theorem residueGridLevel_injective (M J : ℕ) : Function.Injective (residueGridLevel M J) := by
  intro i j hij
  have hM : 0 < M := Nat.zero_le i.1.val |>.trans_lt i.1.isLt
  have hmod := congrArg (fun n : ℕ => n%M) hij
  have hFirst : i.1.val = j.1.val := by
    simpa only [residueGridLevel,Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,
      Nat.mod_eq_of_lt i.1.isLt,Nat.mod_eq_of_lt j.1.isLt] using hmod
  have hProd : M*i.2.val = M*j.2.val := by dsimp only [residueGridLevel] at hij; omega
  apply Prod.ext
  · exact Fin.ext hFirst
  · apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hM hProd

/-- Geometric summation over all smaller finite indices, including the empty row. -/
theorem finite_lower_geometric_sum_le (J : ℕ) (s : Fin J) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin J => t < s),q^(s.val-t.val)) ≤ q/(1-q) := by
  have hInject : Set.InjOn (fun t : Fin J => s.val-t.val)
      (↑(Finset.univ.filter (fun t : Fin J => t < s)) : Set (Fin J)) := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    change a.val < s.val at ha'
    change b.val < s.val at hb'
    change s.val-a.val = s.val-b.val at he
    omega
  have hMaps : Set.MapsTo (fun t : Fin J => s.val-t.val)
      (↑(Finset.univ.filter (fun t : Fin J => t < s)) : Set (Fin J)) (↑(Finset.Ico 1 (s.val+1)) : Set ℕ) := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    change t.val < s.val at ht'
    simp only [Finset.mem_coe,Finset.mem_Ico]
    omega
  apply (Finset.sum_le_sum_of_injOn (s := Finset.univ.filter (fun t : Fin J => t < s))
    (t := Finset.Ico 1 (s.val+1)) (f := fun t => q^(s.val-t.val)) (g := fun d => q^d)
    (fun t => s.val-t.val) hInject (by
      intro d hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact hMaps ht) (fun _ _ => le_rfl) (fun d _ _ => pow_nonneg hq0 d)).trans
  simpa only [pow_one] using (geom_sum_Ico_le_of_lt_one (m := 1) (n := s.val+1) hq0 hq1)

/-- At most two hundred distinct levels can charge one literal neighboring-band index. -/
theorem finite_neighbor_sum_le {ι : Type*} [Fintype ι] (level : ι → ℕ)
    (hLevel : Function.Injective level) (K : ℕ) (d : ℕ → ℝ)
    (hd : ∀ j,0 ≤ d j) (hZero : ∀ j,K ≤ j → d j = 0) :
    (∑ i,∑ j ∈ Finset.Ico (level i-100) (level i+100),d j) ≤
      200*(∑ j ∈ Finset.range K,d j) := by
  classical
  have hCut (n : ℕ) : (∑ j ∈ Finset.Ico (n-100) (n+100),d j) =
      ∑ j ∈ Finset.range K,if j ∈ Finset.Ico (n-100) (n+100) then d j else 0 := by
    rw [← Finset.sum_filter]
    have hSet : (Finset.range K).filter (fun j => j ∈ Finset.Ico (n-100) (n+100)) =
        (Finset.Ico (n-100) (n+100)) ∩ Finset.range K := by ext j; simp [and_comm]
    rw [hSet]
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hnot
    apply hZero j
    have hjK : j ∉ Finset.range K := by
      intro hjK
      exact hnot (Finset.mem_inter.mpr ⟨hj,hjK⟩)
    simpa only [Finset.mem_range,not_lt] using hjK
  simp_rw [hCut]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  rw [← Finset.sum_filter]
  have hMaps : Set.MapsTo level
      (↑(Finset.univ.filter (fun i : ι => j ∈ Finset.Ico (level i-100) (level i+100))) : Set ι)
      (↑(Finset.Ico (j+1-100) (j+101)) : Set ℕ) := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_Ico] at hi'
    simp only [Finset.mem_coe,Finset.mem_Ico]
    omega
  apply (Finset.sum_le_sum_of_injOn
    (s := Finset.univ.filter (fun i : ι => j ∈ Finset.Ico (level i-100) (level i+100)))
    (t := Finset.Ico (j+1-100) (j+101)) (f := fun _ => d j) (g := fun _ => d j)
    level hLevel.injOn (by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hMaps hi) (fun _ _ => le_rfl) (fun _ _ _ => hd j)).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hd j)
  have hCard : (Finset.Ico (j+1-100) (j+101)).card ≤ 200 := by rw [Nat.card_Ico]; omega
  exact_mod_cast hCard

/-- Exact enumeration of the full finite initial interval by the residue grid. -/
theorem residueGrid_sum_eq_range (M J : ℕ) (hM : 0 < M) (f : ℕ → ℝ) :
    (∑ j : Fin M,∑ s : Fin J,f (residueGridLevel M J (j,s))) =
      ∑ n ∈ Finset.range (M*J),f n := by
  rw [← Fintype.sum_prod_type (fun i : Fin M × Fin J => f (residueGridLevel M J i))]
  apply Finset.sum_bij (fun i _hi => residueGridLevel M J i)
  · intro i _hi
    exact Finset.mem_range.mpr (residueGridLevel_lt M J i)
  · intro i _hi j _hj hij
    exact residueGridLevel_injective M J hij
  · intro n hn
    have hn' := Finset.mem_range.mp hn
    let j : Fin M := ⟨n%M,Nat.mod_lt n hM⟩
    let s : Fin J := ⟨n/M,(Nat.div_lt_iff_lt_mul hM).mpr (by simpa only [mul_comm J M] using hn')⟩
    refine ⟨(j,s),Finset.mem_univ _,?_⟩
    exact Nat.mod_add_div n M
  · intro i _hi
    rfl

/-- Every ordered off-diagonal pair occurs once in exactly one lower-pair sum. -/
theorem finite_ordered_offDiagonal_eq_lower_pairs (J : ℕ) (E : Fin J → Fin J → ℝ) :
    (∑ s,∑ t ∈ Finset.univ.erase s,E s t) =
      ∑ s,∑ t ∈ Finset.univ.filter (fun t : Fin J => t < s),(E s t+E t s) := by
  classical
  have hErase (s : Fin J) : Finset.univ.erase s = Finset.univ.filter (fun t : Fin J => t ≠ s) := by
    ext t
    simp [ne_comm]
  have hPoint (s t : Fin J) : (if t ≠ s then E s t else 0) =
      (if t < s then E s t else 0)+(if s < t then E s t else 0) := by
    rcases lt_trichotomy t s with h|h|h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst t; simp
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  have hIfAdd (s t : Fin J) : (if t < s then E s t+E t s else 0) =
      (if t < s then E s t else 0)+(if t < s then E t s else 0) := by split_ifs <;> simp
  simp_rw [hErase,Finset.sum_filter,hPoint,hIfAdd,Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- Honest ordered-pair error summation with the mass charged at the LARGER index. -/
theorem finite_ordered_geometric_error_le (J : ℕ) (E : Fin J → Fin J → ℝ) (B : Fin J → ℝ)
    (hB : ∀ s,0 ≤ B s) (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hPair : ∀ s t : Fin J,t < s → E s t+E t s ≤ 2*C*q^(s.val-t.val)*B s) :
    (∑ s,∑ t ∈ Finset.univ.erase s,E s t) ≤ (2*C)*(q/(1-q))*(∑ s,B s) := by
  rw [finite_ordered_offDiagonal_eq_lower_pairs]
  calc
    _ ≤ ∑ s,∑ t ∈ Finset.univ.filter (fun t : Fin J => t < s),2*C*q^(s.val-t.val)*B s := by
      apply Finset.sum_le_sum
      intro s _hs
      apply Finset.sum_le_sum
      intro t ht
      exact hPair s t (Finset.mem_filter.mp ht).2
    _ = ∑ s,(2*C*B s)*(∑ t ∈ Finset.univ.filter (fun t : Fin J => t < s),q^(s.val-t.val)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ ≤ ∑ s,(2*C*B s)*(q/(1-q)) := by
      apply Finset.sum_le_sum
      intro s _hs
      exact mul_le_mul_of_nonneg_left (finite_lower_geometric_sum_le J s q hq0 hq1)
        (mul_nonneg (mul_nonneg (by norm_num) hC) (hB s))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

/-- The genuine geometric ratio at a residue spacing M. -/
def sparseGridRatio (p : ℝ) (M : ℕ) : ℝ := ((11/10 : ℝ)^(-p/2))^M

theorem sparseGridRatio_nonneg (p : ℝ) (M : ℕ) : 0 ≤ sparseGridRatio p M := by
  dsimp only [sparseGridRatio]
  positivity

theorem sparseGridRatio_lt_one (p : ℝ) (hp : 0 < p) (M : ℕ) (hM : 0 < M) :
    sparseGridRatio p M < 1 :=
  pow_lt_one₀ (by positivity) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)) hM.ne'

/-- The spacing is selected BEFORE any polynomial or finite grid. -/
theorem exists_sparseGridRatio_absorption (p : ℝ) (hp : 0 < p) (A : ℝ) :
    ∃ M : ℕ,100 ≤ M ∧ A*sparseGridRatio p M/(1-sparseGridRatio p M) ≤ 1/2 := by
  have ha0 : (0 : ℝ) ≤ (11/10 : ℝ)^(-p/2) := by positivity
  have ha1 : (11/10 : ℝ)^(-p/2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hPow := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hFrac : Tendsto (fun M : ℕ => A*sparseGridRatio p M/(1-sparseGridRatio p M)) atTop (𝓝 0) := by
    simpa only [sparseGridRatio,mul_zero,sub_zero,div_one] using!
      (tendsto_const_nhds.mul hPow).div (tendsto_const_nhds.sub hPow) (by norm_num : (1 : ℝ)-0 ≠ 0)
  have hSmall := hFrac.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨M,hM,hSmallM⟩ := ((eventually_ge_atTop 100).and hSmall).exists
  exact ⟨M,hM,hSmallM.le⟩

/-- The actual real-power decay becomes precisely q^(s-t) on each residue grid. -/
theorem residueGrid_decay_eq (M J : ℕ) (j : Fin M) (s t : Fin J) (p : ℝ) :
    (11/10 : ℝ)^(-((residueGridLevel M J (j,s)-residueGridLevel M J (j,t) : ℕ) : ℝ)*p/2) =
      (sparseGridRatio p M)^(s.val-t.val) := by
  have he : residueGridLevel M J (j,s)-residueGridLevel M J (j,t) = M*(s.val-t.val) := by
    dsimp only [residueGridLevel]
    rw [Nat.mul_sub]
    omega
  rw [he,sparseGridRatio,← pow_mul,← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 11/10)]
  congr 1
  push_cast
  ring

theorem residueGrid_separation (M J : ℕ) (hM : 100 ≤ M) (j : Fin M) (s t : Fin J) (hts : t < s) :
    residueGridLevel M J (j,t)+100 ≤ residueGridLevel M J (j,s) := by
  have hst : t.val+1 ≤ s.val := by exact Nat.succ_le_of_lt hts
  have h := Nat.mul_le_mul_left M hst
  dsimp only [residueGridLevel]
  nlinarith

/-- The complete positive-band budget is finite by literal polynomial degree, with the base mode separate. -/
def polynomialWideBandBudget (m : ℕ) (P : Polynomial ℂ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range P.natDegree,scheduledWideBandMass m j P p

theorem scheduledWideBandMass_nonneg (m j : ℕ) (P : Polynomial ℂ) (p : ℝ) :
    0 ≤ scheduledWideBandMass m j P p :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun τ => Real.rpow_nonneg
    (norm_nonneg ((thinWideBandPolynomial m (thinWideScale j) (thinWideScale (j+1)) P).eval
      (fourier (T := 1) 1 τ))) p)

theorem scheduledWideBandMass_zero_of_degree_le (m j : ℕ) (P : Polynomial ℂ)
    (hj : P.natDegree ≤ j) (p : ℝ) (hp : 0 < p) : scheduledWideBandMass m j P p = 0 := by
  simp only [scheduledWideBandMass,thinWideScale_polynomial_band_eventually_zero m P j hj,
    Polynomial.eval_zero,norm_zero,Real.zero_rpow hp.ne',integral_zero,mul_zero]

/-- Every finite grid charges the GLOBAL polynomial band budget with multiplicity at most 200. -/
theorem residueGrid_neighbor_mass_le (m M J : ℕ) (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) :
    (∑ j : Fin M,∑ s : Fin J,
      ∑ l ∈ Finset.Ico (residueGridLevel M J (j,s)-100) (residueGridLevel M J (j,s)+100),
        scheduledWideBandMass m l P p) ≤ 200*polynomialWideBandBudget m P p := by
  rw [← Fintype.sum_prod_type (fun i : Fin M × Fin J =>
    ∑ l ∈ Finset.Ico (residueGridLevel M J i-100) (residueGridLevel M J i+100),scheduledWideBandMass m l P p)]
  exact finite_neighbor_sum_le _ (residueGridLevel_injective M J) P.natDegree
    (fun l => scheduledWideBandMass m l P p) (fun l => scheduledWideBandMass_nonneg m l P p)
    (fun l hl => scheduledWideBandMass_zero_of_degree_le m l P hl p hp)

/-- Actual collective ordered-corner error estimate; no padded-truncation budget is assumed. -/
theorem residueGrid_offDiagonal_budget (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j : Fin M,∑ s : Fin J,∑ t ∈ Finset.univ.erase s,
      schattenNorm p (scheduledWideCorner m (residueGridLevel M J (j,s))
        (residueGridLevel M J (j,t)) P)^p) ≤
    400*wideOffDiagonalConstant m p*(sparseGridRatio p M/(1-sparseGridRatio p M))*
      polynomialWideBandBudget m P p := by
  let B : ℕ → ℝ := fun n => ∑ l ∈ Finset.Ico (n-100) (n+100),scheduledWideBandMass m l P p
  have hB (n : ℕ) : 0 ≤ B n := Finset.sum_nonneg (fun l _hl => scheduledWideBandMass_nonneg m l P p)
  have hC := wideOffDiagonalConstant_pos m hm p
  have hq0 := sparseGridRatio_nonneg p M
  have hq1 := sparseGridRatio_lt_one p hp M (by omega)
  have hEach (j : Fin M) : (∑ s : Fin J,∑ t ∈ Finset.univ.erase s,
      schattenNorm p (scheduledWideCorner m (residueGridLevel M J (j,s))
        (residueGridLevel M J (j,t)) P)^p) ≤
      (2*wideOffDiagonalConstant m p)*(sparseGridRatio p M/(1-sparseGridRatio p M))*
        (∑ s : Fin J,B (residueGridLevel M J (j,s))) := by
    apply finite_ordered_geometric_error_le J _ _ (fun s => hB _) _ _ hC.le hq0 hq1
    intro s t hts
    have hOff := scheduledWide_far_schattenNorm_budget m (residueGridLevel M J (j,s))
      (residueGridLevel M J (j,t)) hm (residueGrid_separation M J hM j s t hts) P p hp hp1
    rw [residueGrid_decay_eq M J j s t p] at hOff
    exact (add_le_add hOff.1 hOff.2).trans_eq (by dsimp only [B]; ring)
  have hNear := residueGrid_neighbor_mass_le m M J P p hp
  calc
    _ ≤ ∑ j : Fin M,(2*wideOffDiagonalConstant m p)*(sparseGridRatio p M/(1-sparseGridRatio p M))*
        (∑ s : Fin J,B (residueGridLevel M J (j,s))) := Finset.sum_le_sum (fun j _hj => hEach j)
    _ = ((2*wideOffDiagonalConstant m p)*(sparseGridRatio p M/(1-sparseGridRatio p M)))*
        (∑ j : Fin M,∑ s : Fin J,B (residueGridLevel M J (j,s))) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((2*wideOffDiagonalConstant m p)*(sparseGridRatio p M/(1-sparseGridRatio p M)))*
        (200*polynomialWideBandBudget m P p) := mul_le_mul_of_nonneg_left hNear
          (mul_nonneg (by positivity) (div_nonneg hq0 (by linarith)))
    _ = _ := by ring

/-- Distinct members of one residue have genuinely disjoint coordinate annuli. -/
theorem residueGrid_annuli_disjoint (m M J : ℕ) (hM : 100 ≤ M) (j : Fin M)
    (s t : Fin J) (hst : s ≠ t) :
    Disjoint (Set.Ico (20*m*thinWideScale (residueGridLevel M J (j,s)))
      (150*m*thinWideScale (residueGridLevel M J (j,s))))
      (Set.Ico (20*m*thinWideScale (residueGridLevel M J (j,t)))
        (150*m*thinWideScale (residueGridLevel M J (j,t)))) := by
  rcases lt_or_gt_of_ne hst with hst|hts
  · have hGap := residueGrid_separation M J hM j t s hst
    have h := thinWideScale_annuli_disjoint m (residueGridLevel M J (j,s))
      (residueGridLevel M J (j,t)-residueGridLevel M J (j,s)) (by omega)
    rw [Nat.add_sub_of_le (by omega)] at h
    exact h
  · have hGap := residueGrid_separation M J hM j s t hts
    have h := thinWideScale_annuli_disjoint m (residueGridLevel M J (j,t))
      (residueGridLevel M J (j,s)-residueGridLevel M J (j,t)) (by omega)
    rw [Nat.add_sub_of_le (by omega)] at h
    exact h.symm

/-- A complete concrete coordinate embedding from the actual disjoint interval windows. -/
def residueCoordinateEmbedding (m M J : ℕ) (hM : 100 ≤ M) (j : Fin M) (start : Fin J → ℕ)
    (hStart : ∀ s : Fin J,∀ i : Fin (scheduledWideSize m (residueGridLevel M J (j,s))),
      20*m*thinWideScale (residueGridLevel M J (j,s)) ≤ start s+i.val ∧
      start s+i.val < 150*m*thinWideScale (residueGridLevel M J (j,s))) :
    (Σ s : Fin J,Fin (scheduledWideSize m (residueGridLevel M J (j,s)))) ↪
      Fin (150*m*thinWideScale (M*J)) where
  toFun x := ⟨start x.1+x.2.val,(hStart x.1 x.2).2.trans_le
    (Nat.mul_le_mul_left (150*m) (thinWideScale_monotone (Nat.le_of_lt (residueGridLevel_lt M J (j,x.1)))))⟩
  inj' x y hxy := by
    obtain ⟨s,a⟩ := x
    obtain ⟨t,b⟩ := y
    have he : start s+a.val = start t+b.val := congrArg Fin.val hxy
    by_cases hst : s = t
    · subst t
      have hab : a = b := Fin.ext (by omega)
      cases hab
      rfl
    · have hD := residueGrid_annuli_disjoint m M J hM j s t hst
      have hA := hStart s a
      have hB := hStart t b
      have hContra := (Set.disjoint_left.mp hD) hA (by rw [he]; exact hB)
      exact hContra.elim

def residueRowEmbedding (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M) (j : Fin M) :=
  residueCoordinateEmbedding m M J hM j (fun s => scheduledWideRow m (residueGridLevel M J (j,s)))
    (fun s => (scheduledWide_coordinate_windows m (residueGridLevel M J (j,s)) hm).1)

def residueColumnEmbedding (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M) (j : Fin M) :=
  residueCoordinateEmbedding m M J hM j (fun s => scheduledWideColumn m (residueGridLevel M J (j,s)))
    (fun s => (scheduledWide_coordinate_windows m (residueGridLevel M J (j,s)) hm).2)

/-- The actual finite ambient Hankel matrix used for all residues at once. -/
def residueAmbientHankel (m M J : ℕ) (P : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (150*m*thinWideScale (M*J))) →L[ℂ]
      EuclideanSpace ℂ (Fin (150*m*thinWideScale (M*J))) :=
  polynomialHankelRectangleOffset (150*m*thinWideScale (M*J)) (150*m*thinWideScale (M*J)) 0 P

/-- Literal equality of the disjoint ambient corners with the scheduled polynomial corners. -/
theorem residueAmbientHankel_corner (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M)
    (j : Fin M) (s t : Fin J) (P : Polynomial ℂ) :
    disjointCoordinateCorner (fun s => scheduledWideSize m (residueGridLevel M J (j,s)))
      (fun s => scheduledWideSize m (residueGridLevel M J (j,s)))
      (150*m*thinWideScale (M*J)) (150*m*thinWideScale (M*J))
      (residueRowEmbedding m M J hm hM j) (residueColumnEmbedding m M J hm hM j)
      (residueAmbientHankel m M J P) s t =
    scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,t)) P := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (scheduledWideSize m (residueGridLevel M J (j,t)))) ℂ).toBasis.ext
  intro b
  rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
  ext a
  change disjointCoordinateCorner
    (fun s => scheduledWideSize m (residueGridLevel M J (j,s)))
    (fun s => scheduledWideSize m (residueGridLevel M J (j,s)))
    (150*m*thinWideScale (M*J)) (150*m*thinWideScale (M*J))
    (residueRowEmbedding m M J hm hM j) (residueColumnEmbedding m M J hm hM j)
    (residueAmbientHankel m M J P) s t (EuclideanSpace.single b (1 : ℂ)) a =
    scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,t)) P
      (EuclideanSpace.single b (1 : ℂ)) a
  rw [disjointCoordinateCorner_single_apply,scheduledWideCorner_single_apply]
  dsimp only [residueAmbientHankel]
  rw [polynomialHankelRectangleOffset_single_apply]
  change P.coeff (0+(scheduledWideRow m (residueGridLevel M J (j,s))+a.val)+
      (scheduledWideColumn m (residueGridLevel M J (j,t))+b.val)) = _
  congr 1
  omega

/-- The proved errorful finite block budget, instantiated at every actual residue family. -/
theorem residueAmbientHankel_diagonal_budget (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M)
    (j : Fin M) (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ s : Fin J,schattenNorm p (scheduledWideCorner m (residueGridLevel M J (j,s))
      (residueGridLevel M J (j,s)) P)^p) ≤ schattenNorm p (residueAmbientHankel m M J P)^p+
    (∑ s : Fin J,∑ t ∈ Finset.univ.erase s,schattenNorm p
      (scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,t)) P)^p) := by
  have h := finite_disjoint_coordinate_block_budget
    (fun s => scheduledWideSize m (residueGridLevel M J (j,s)))
    (fun s => scheduledWideSize m (residueGridLevel M J (j,s))) _ _
    (residueRowEmbedding m M J hm hM j) (residueColumnEmbedding m M J hm hM j)
    (residueAmbientHankel m M J P) p hp hp1
  simpa only [residueAmbientHankel_corner] using h

theorem polynomialWideBandBudget_nonneg (m : ℕ) (P : Polynomial ℂ) (p : ℝ) :
    0 ≤ polynomialWideBandBudget m P p :=
  Finset.sum_nonneg (fun j _hj => scheduledWideBandMass_nonneg m j P p)

/-- Exact coverage of the GLOBAL budget once the grid reaches the polynomial degree. -/
theorem residueGrid_bandBudget_eq (m M J : ℕ) (hM : 0 < M) (P : Polynomial ℂ)
    (hDegree : P.natDegree ≤ M*J) (p : ℝ) (hp : 0 < p) :
    (∑ j : Fin M,∑ s : Fin J,scheduledWideBandMass m (residueGridLevel M J (j,s)) P p) =
      polynomialWideBandBudget m P p := by
  rw [residueGrid_sum_eq_range M J hM (fun l => scheduledWideBandMass m l P p)]
  symm
  apply Finset.sum_subset (Finset.range_mono hDegree)
  intro l _hl hnot
  apply scheduledWideBandMass_zero_of_degree_le m l P _ p hp
  simpa only [Finset.mem_range,not_lt] using hnot

/-- One actual band is controlled by its original scheduled diagonal corner. -/
theorem scheduledWideBandMass_le_diagonal (m n : ℕ) (hm : 1 ≤ m) (P : Polynomial ℂ)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    scheduledWideBandMass m n P p ≤ (2*wideLocalSchurConstant m p)*
      schattenNorm p (scheduledWideCorner m n n P)^p := by
  have h := thinWideBand_lp_controlled_by_corner m (thinWideScale n) (thinWideScale (n+1)) hm
    (thinWideScale_ten_le n) (thinWideScale_monotone (Nat.le_succ n)) (thinWideScale_ratio n)
    P p hp hp1 hOrder
  simpa only [scheduledWideBandMass,scheduledWideCorner,scheduledWideSize,scheduledWideRow,
    scheduledWideColumn,thinWideBand_starts_add] using! h

/-- Summation of the actual finite errorful block budgets, one ambient cost per residue. -/
theorem residueAmbientHankel_sum_diagonal_budget (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M)
    (P : Polynomial ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j : Fin M,∑ s : Fin J,schattenNorm p (scheduledWideCorner m (residueGridLevel M J (j,s))
      (residueGridLevel M J (j,s)) P)^p) ≤ (M : ℝ)*schattenNorm p (residueAmbientHankel m M J P)^p+
    (∑ j : Fin M,∑ s : Fin J,∑ t ∈ Finset.univ.erase s,schattenNorm p
      (scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,t)) P)^p) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _hj =>
    residueAmbientHankel_diagonal_budget m M J hm hM j P p hp hp1)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

/-- The actual finite inequality before absorption. ALL off-diagonal error has been proved small up to q. -/
theorem residueAmbientHankel_preabsorption (m M J : ℕ) (hm : 1 ≤ m) (hM : 100 ≤ M)
    (P : Polynomial ℂ) (hDegree : P.natDegree ≤ M*J)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    polynomialWideBandBudget m P p ≤
      (2*wideLocalSchurConstant m p)*(M : ℝ)*schattenNorm p (residueAmbientHankel m M J P)^p+
      ((400*(2*wideLocalSchurConstant m p)*wideOffDiagonalConstant m p)*sparseGridRatio p M/
        (1-sparseGridRatio p M))*polynomialWideBandBudget m P p := by
  have hLocalPos := wideLocalSchurConstant_pos m p hOrder
  have hLocal : polynomialWideBandBudget m P p ≤ (2*wideLocalSchurConstant m p)*
      (∑ j : Fin M,∑ s : Fin J,schattenNorm p
        (scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,s)) P)^p) := by
    rw [← residueGrid_bandBudget_eq m M J (by omega) P hDegree p hp]
    calc
      _ ≤ ∑ j : Fin M,∑ s : Fin J,(2*wideLocalSchurConstant m p)*schattenNorm p
          (scheduledWideCorner m (residueGridLevel M J (j,s)) (residueGridLevel M J (j,s)) P)^p := by
        apply Finset.sum_le_sum
        intro j _hj
        apply Finset.sum_le_sum
        intro s _hs
        exact scheduledWideBandMass_le_diagonal m _ hm P p hp hp1 hOrder
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        exact (Finset.mul_sum _ _ _).symm
  have hDiag := residueAmbientHankel_sum_diagonal_budget m M J hm hM P p hp hp1
  have hError := residueGrid_offDiagonal_budget m M J hm hM P p hp hp1
  have hTotal := hDiag.trans (add_le_add le_rfl hError)
  apply hLocal.trans
  apply (mul_le_mul_of_nonneg_left hTotal (by positivity : (0 : ℝ) ≤ 2*wideLocalSchurConstant m p)).trans_eq
  ring

/-- A genuine uniform polynomial band lower estimate from actual disjoint corners and proved error absorption.
The spacing and bound are chosen BEFORE the polynomial and every sufficiently long finite grid. -/
theorem exists_polynomialWideBandBudget_bound (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    ∃ M : ℕ,100 ≤ M ∧ ∃ C : ℝ,0 < C ∧ ∀ P : Polynomial ℂ,∀ J : ℕ,P.natDegree ≤ M*J →
      polynomialWideBandBudget m P p ≤ C*schattenNorm p (residueAmbientHankel m M J P)^p := by
  obtain ⟨M,hM,hAbsorb⟩ := exists_sparseGridRatio_absorption p hp
    (400*(2*wideLocalSchurConstant m p)*wideOffDiagonalConstant m p)
  have hLocalPos := wideLocalSchurConstant_pos m p hOrder
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0<M)
  refine ⟨M,hM,2*(2*wideLocalSchurConstant m p)*(M : ℝ),by positivity,?_⟩
  intro P J hDegree
  have h := residueAmbientHankel_preabsorption m M J hm hM P hDegree p hp hp1 hOrder
  have hNonneg := polynomialWideBandBudget_nonneg m P p
  have hAbsorbD := mul_le_mul_of_nonneg_right hAbsorb hNonneg
  nlinarith

/-- A fully concrete finite grid exists for every polynomial after the uniform spacing has been fixed. -/
theorem exists_polynomialWideBandBudget_concrete_bound (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hOrder : 1 < ((m+1 : ℕ) : ℝ)*p) :
    ∃ M : ℕ,100 ≤ M ∧ ∃ C : ℝ,0 < C ∧ ∀ P : Polynomial ℂ,
      polynomialWideBandBudget m P p ≤
        C*schattenNorm p (residueAmbientHankel m M (P.natDegree+1) P)^p := by
  obtain ⟨M,hM,C,hC,hBound⟩ := exists_polynomialWideBandBudget_bound m hm p hp hp1 hOrder
  refine ⟨M,hM,C,hC,fun P => hBound P (P.natDegree+1) ?_⟩
  nlinarith

end TTO.Paper.Proved
