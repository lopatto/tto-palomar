/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import TTO.MatrixFoundations
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Full Fourier coordinates and literal boundary energy of the model tensor graph. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Topology

namespace TTO.Paper.Proved
open Reduction

abbrev TorusL2 := Lp ℂ 2 (Measure.pi (fun _ : Fin 2 => circleMeasure))

/-- The sole transport is the native measure-preserving two-coordinate equivalence. -/
def torusPullback : BidiskL2 →ₗᵢ[ℂ] TorusL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ MeasurableEquiv.finTwoArrow (measurePreserving_finTwoArrow circleMeasure)

def torusFourierBasis : HilbertBasis (Fin 2 → ℤ) ℂ TorusL2 := UnitAddTorus.mFourierBasis

theorem torusFourierBasis_ae (n : Fin 2 → ℤ) :
    torusFourierBasis n =ᵐ[Measure.pi (fun _ : Fin 2 => circleMeasure)] UnitAddTorus.mFourier n := by
  change UnitAddTorus.mFourierBasis n =ᵐ[Measure.pi (fun _ : Fin 2 => circleMeasure)] _
  convert (UnitAddTorus.coeFn_mFourierLp 2 n) using 1
  exact congrArg (fun f : TorusL2 => (f : (Fin 2 → Boundary) → ℂ))
    (congrFun (UnitAddTorus.coe_mFourierBasis (d := Fin 2)) n)

def fullFourierMode (ij : ℤ × ℤ) : BidiskL2 :=
  separatedProduct (fourierBasis (T := 1) ij.1) (fourierBasis (T := 1) ij.2)

theorem fullFourierMode_ae (ij : ℤ × ℤ) :
    fullFourierMode ij =ᵐ[circleMeasure.prod circleMeasure] fun p =>
      fourier (T := 1) ij.1 p.1*fourier (T := 1) ij.2 p.2 := by
  filter_upwards [separatedProduct_ae (fourierBasis (T := 1) ij.1) (fourierBasis (T := 1) ij.2),
    boundary_ae_fst (fourierBasis_ae ij.1),boundary_ae_snd (fourierBasis_ae ij.2)] with p hp h1 h2
  change separatedProduct (fourierBasis (T := 1) ij.1) (fourierBasis (T := 1) ij.2) p = _
  rw [hp,h1,h2]

theorem torusPullback_fullFourierMode (n : Fin 2 → ℤ) :
    torusPullback (fullFourierMode (n 0,n 1)) = torusFourierBasis n := by
  let hMP := measurePreserving_finTwoArrow circleMeasure
  have hp := hMP.quasiMeasurePreserving.ae_eq_comp (fullFourierMode_ae (n 0,n 1))
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (fullFourierMode (n 0,n 1)) hMP,hp,
    torusFourierBasis_ae n] with x hc hs hb
  simp only [Function.comp_apply] at hc hs
  change Lp.compMeasurePreserving MeasurableEquiv.finTwoArrow hMP (fullFourierMode (n 0,n 1)) x = _
  rw [hc,hs,hb]
  change fourier (T := 1) (n 0) (x 0)*fourier (T := 1) (n 1) (x 1) = _
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two]

theorem fullFourierMode_orthonormal : Orthonormal ℂ fullFourierMode := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (separatedProduct (fourierBasis (T := 1) i.1) (fourierBasis (T := 1) i.2))
    (separatedProduct (fourierBasis (T := 1) j.1) (fourierBasis (T := 1) j.2)) = _
  rw [inner_separatedProduct,orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal,
    orthonormal_iff_ite.mp (fourierBasis (T := 1)).orthonormal]
  by_cases ha : i.1 = j.1 <;> by_cases hb : i.2 = j.2 <;> simp [ha,hb,Prod.ext_iff]

theorem fullFourierModes_total : (Submodule.span ℂ (Set.range fullFourierMode)).orthogonal = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro G hG
  have hz : torusPullback G = 0 := by
    apply torusFourierBasis.repr.injective
    rw [map_zero]
    apply lp.ext
    funext n
    simp only [torusFourierBasis.repr_apply_apply,lp.coeFn_zero,Pi.zero_apply]
    have he := torusPullback.inner_map_map (fullFourierMode (n 0,n 1)) G
    rw [torusPullback_fullFourierMode] at he
    exact he.trans ((Submodule.mem_orthogonal _ _).mp hG _ (Submodule.subset_span ⟨(n 0,n 1),rfl⟩))
  apply torusPullback.injective
  rw [map_zero]
  exact hz

/-- Complete two-sided Fourier basis of the actual product L² space. -/
def fullFourierBasis : HilbertBasis (ℤ × ℤ) ℂ BidiskL2 :=
  HilbertBasis.mkOfOrthogonalEqBot fullFourierMode_orthonormal fullFourierModes_total

@[simp] theorem fullFourierBasis_apply (ij : ℤ × ℤ) : fullFourierBasis ij = fullFourierMode ij :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot fullFourierMode_orthonormal fullFourierModes_total) ij

def fullFourierCoeff (G : BidiskL2) (ij : ℤ × ℤ) : ℂ := inner ℂ (fullFourierMode ij) G

theorem fullFourierBasis_repr (G : BidiskL2) (ij : ℤ × ℤ) :
    fullFourierBasis.repr G ij = fullFourierCoeff G ij := by
  rw [HilbertBasis.repr_apply_apply,fullFourierBasis_apply]
  rfl

/-- The positive bidisk space is exactly the nonnegative-quadrant Fourier subspace. -/
theorem mem_bidiskHardy_iff (G : BidiskL2) :
    G ∈ bidiskHardy ↔ ∀ m n : ℤ, m < 0 ∨ n < 0 → fullFourierCoeff G (m,n) = 0 := by
  constructor
  · intro hG m n hneg
    let L := innerSL ℂ (fullFourierMode (m,n))
    have hle : bidiskHardy ≤ L.ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change inner ℂ (separatedProduct (fourierBasis (T := 1) m) (fourierBasis (T := 1) n))
          (ContinuousMap.toLp 2 (circleMeasure.prod circleMeasure) ℂ (bidiskMode i.1 i.2)) = 0
        rw [← separatedProduct_fourierBasis,inner_separatedProduct]
        rcases hneg with hm | hn
        · rw [(fourierBasis (T := 1)).orthonormal.inner_eq_zero (by omega : m ≠ (i.1 : ℤ)),zero_mul]
        · rw [(fourierBasis (T := 1)).orthonormal.inner_eq_zero (by omega : n ≠ (i.2 : ℤ)),mul_zero]
      · exact L.isClosed_ker
    exact hle hG
  · intro h
    have hs := fullFourierBasis.hasSum_repr G
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs
    apply Filter.Eventually.of_forall
    intro s
    apply bidiskHardy.sum_mem
    rintro ⟨m,n⟩ _
    by_cases hpos : 0 ≤ m ∧ 0 ≤ n
    · obtain ⟨i,rfl⟩ := Int.eq_ofNat_of_zero_le hpos.1
      obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le hpos.2
      apply bidiskHardy.smul_mem
      rw [fullFourierBasis_apply]
      change separatedProduct (fourierBasis (T := 1) (i : ℤ)) (fourierBasis (T := 1) (j : ℤ)) ∈ bidiskHardy
      rw [separatedProduct_fourierBasis]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i,j),rfl⟩)
    · have hz := h m n (by omega)
      rw [fullFourierBasis_repr,hz,zero_smul]
      exact bidiskHardy.zero_mem

def torusCharacter (ij : ℤ × ℤ) : C(Boundary × Boundary,ℂ) :=
  ⟨fun p => fourier (T := 1) ij.1 p.1*fourier (T := 1) ij.2 p.2,
    ((fourier (T := 1) ij.1).continuous.comp continuous_fst).mul
      ((fourier (T := 1) ij.2).continuous.comp continuous_snd)⟩

abbrev BidiskLInf := Lp ℂ ∞ (circleMeasure.prod circleMeasure)

def torusModeInf (ij : ℤ × ℤ) : BidiskLInf :=
  ContinuousMap.toLp ∞ (circleMeasure.prod circleMeasure) ℂ (torusCharacter ij)

def bidiskMultiply (a : BidiskLInf) : BidiskL2 →L[ℂ] BidiskL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL (circleMeasure.prod circleMeasure) ∞ 2 2 a

theorem bidiskMultiply_ae (a : BidiskLInf) (G : BidiskL2) :
    bidiskMultiply a G =ᵐ[circleMeasure.prod circleMeasure] fun p => a p*G p :=
  (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder a G

theorem torusModeInf_ae (ij : ℤ × ℤ) :
    torusModeInf ij =ᵐ[circleMeasure.prod circleMeasure] torusCharacter ij :=
  ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) _ _

/-- Full Fourier shifts for actual bounded coordinate multiplication. -/
theorem fullFourierCoeff_multiply (G : BidiskL2) (a b m n : ℤ) :
    fullFourierCoeff (bidiskMultiply (torusModeInf (a,b)) G) (m,n) = fullFourierCoeff G (m-a,n-b) := by
  rw [fullFourierCoeff,fullFourierCoeff,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [bidiskMultiply_ae (torusModeInf (a,b)) G,torusModeInf_ae (a,b),
    fullFourierMode_ae (m,n),fullFourierMode_ae (m-a,n-b)] with p hp ha hm hn
  simp only [RCLike.inner_apply,hp,ha,hm,hn,torusCharacter,ContinuousMap.coe_mk,map_mul,← fourier_neg]
  calc
    _ = G p*((fourier (T := 1) a p.1*fourier (T := 1) (-m) p.1)*
        (fourier (T := 1) b p.2*fourier (T := 1) (-n) p.2)) := by ring
    _ = _ := by
      rw [← fourier_add,← fourier_add]
      have he₁ : a+-m = -(m-a) := by ring
      have he₂ : b+-n = -(n-b) := by ring
      rw [he₁,he₂]

def boundaryDifference : BidiskL2 →L[ℂ] BidiskL2 :=
  bidiskMultiply (torusModeInf (1,0))-bidiskMultiply (torusModeInf (0,1))

theorem boundaryDifference_ae (G : BidiskL2) :
    boundaryDifference G =ᵐ[circleMeasure.prod circleMeasure] fun p =>
      (fourier (T := 1) 1 p.1-fourier (T := 1) 1 p.2)*G p := by
  filter_upwards [Lp.coeFn_sub (bidiskMultiply (torusModeInf (1,0)) G) (bidiskMultiply (torusModeInf (0,1)) G),
    bidiskMultiply_ae (torusModeInf (1,0)) G,bidiskMultiply_ae (torusModeInf (0,1)) G,
    torusModeInf_ae (1,0),torusModeInf_ae (0,1)] with p hs h1 h2 ha hb
  change (bidiskMultiply (torusModeInf (1,0)) G-bidiskMultiply (torusModeInf (0,1)) G) p = _
  simp only [Pi.sub_apply] at hs
  rw [hs,h1,h2,ha,hb]
  simp only [torusCharacter,ContinuousMap.coe_mk,fourier_zero,mul_one,one_mul]
  ring

theorem fullFourierCoeff_boundaryDifference (G : BidiskL2) (m n : ℤ) :
    fullFourierCoeff (boundaryDifference G) (m,n) = fullFourierCoeff G (m-1,n)-fullFourierCoeff G (m,n-1) := by
  change inner ℂ (fullFourierMode (m,n))
    (bidiskMultiply (torusModeInf (1,0)) G-bidiskMultiply (torusModeInf (0,1)) G) = _
  rw [inner_sub_right]
  change fullFourierCoeff (bidiskMultiply (torusModeInf (1,0)) G) (m,n)-
    fullFourierCoeff (bidiskMultiply (torusModeInf (0,1)) G) (m,n) = _
  rw [fullFourierCoeff_multiply,fullFourierCoeff_multiply,sub_zero,sub_zero]

/-- A constant coefficient along an injective infinite ray must vanish by Parseval decay. -/
theorem fullFourierCoeff_ray_zero (G : BidiskL2) (ray : ℕ → ℤ × ℤ) (hray : Function.Injective ray)
    (c : ℂ) (hc : ∀ k, fullFourierCoeff G (ray k) = c) : c = 0 := by
  have hs := (hasSum_basis_inner_norm_sq fullFourierBasis G).summable.tendsto_cofinite_zero
  have hl := hs.comp hray.tendsto_cofinite
  simp only [fullFourierBasis_apply] at hl
  change Tendsto (fun k : ℕ => ‖fullFourierCoeff G (ray k)‖^2) cofinite (𝓝 0) at hl
  simp_rw [hc] at hl
  have hz : ‖c‖^2 = 0 := tendsto_nhds_unique tendsto_const_nhds hl
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- Dividing a Hardy numerator by z-w introduces no negative spectrum when the quotient is L². -/
theorem mem_bidiskHardy_of_boundaryDifference (G N : BidiskL2) (hN : N ∈ bidiskHardy)
    (hD : boundaryDifference G = N) : G ∈ bidiskHardy := by
  have hr (m n : ℤ) (hneg : m < 0 ∨ n < 0) :
      fullFourierCoeff G (m-1,n) = fullFourierCoeff G (m,n-1) := by
    have he := fullFourierCoeff_boundaryDifference G m n
    rw [hD,(mem_bidiskHardy_iff N).mp hN m n hneg] at he
    exact sub_eq_zero.mp he.symm
  apply (mem_bidiskHardy_iff G).mpr
  intro m n hneg
  rcases hneg with hm | hn
  · let ray := fun k : ℕ => (m-(k : ℤ),n+(k : ℤ))
    have hi : Function.Injective ray := by
      intro a b h
      have hh := congrArg Prod.fst h
      dsimp [ray] at hh
      omega
    apply fullFourierCoeff_ray_zero G ray hi (fullFourierCoeff G (m,n))
    intro k
    induction k with
    | zero => simp only [ray,Nat.cast_zero,sub_zero,add_zero]
    | succ k ih =>
      have he := hr (m-(k : ℤ)) (n+(k : ℤ)+1) (Or.inl (by omega))
      have hidx : ray (k+1) = (m-(k : ℤ)-1,n+(k : ℤ)+1) := by dsimp [ray]; ext <;> ring
      rw [hidx]
      simp only [add_sub_cancel_right] at he
      dsimp [ray] at ih
      exact he.trans ih
  · let ray := fun k : ℕ => (m+(k : ℤ),n-(k : ℤ))
    have hi : Function.Injective ray := by
      intro a b h
      have hh := congrArg Prod.snd h
      dsimp [ray] at hh
      omega
    apply fullFourierCoeff_ray_zero G ray hi (fullFourierCoeff G (m,n))
    intro k
    induction k with
    | zero => simp only [ray,Nat.cast_zero,sub_zero,add_zero]
    | succ k ih =>
      have he := hr (m+(k : ℤ)+1) (n-(k : ℤ)) (Or.inr (by omega))
      have hidx : ray (k+1) = (m+(k : ℤ)+1,n-(k : ℤ)-1) := by dsimp [ray]; ext <;> ring
      rw [hidx]
      simp only [add_sub_cancel_right] at he
      dsimp [ray] at ih
      exact he.symm.trans ih

theorem boundaryDifference_separatedProduct (f g : BoundaryL2) :
    boundaryDifference (separatedProduct f g) =
      separatedProduct (multiply coordinate f) g-separatedProduct f (multiply coordinate g) := by
  apply Lp.ext
  filter_upwards [boundaryDifference_ae (separatedProduct f g),separatedProduct_ae f g,
    Lp.coeFn_sub (separatedProduct (multiply coordinate f) g) (separatedProduct f (multiply coordinate g)),
    separatedProduct_ae (multiply coordinate f) g,separatedProduct_ae f (multiply coordinate g),
    boundary_ae_fst (multiply_ae coordinate f),boundary_ae_snd (multiply_ae coordinate g),
    boundary_ae_fst coordinate_ae,boundary_ae_snd coordinate_ae] with p hD hp hs h1 h2 hf hg hc hd
  simp only [Pi.sub_apply] at hs
  rw [hD,hp,hs,h1,h2,hf,hg,hc,hd]
  ring

theorem boundaryDifference_mem_bidiskHardy (G : BidiskL2) (hG : G ∈ bidiskHardy) :
    boundaryDifference G ∈ bidiskHardy := by
  apply (mem_bidiskHardy_iff _).mpr
  intro m n hneg
  rw [fullFourierCoeff_boundaryDifference,
    (mem_bidiskHardy_iff G).mp hG (m-1) n (by omega),
    (mem_bidiskHardy_iff G).mp hG m (n-1) (by omega),sub_self]

def bidiskEvaluation (z w : Disk) : ↥bidiskHardy →L[ℂ] ℂ :=
  innerSL ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val) ∘L bidiskHardy.subtypeL

theorem bidiskEvaluation_apply (G : ↥bidiskHardy) (z w : Disk) :
    bidiskEvaluation z w G = analyticValue₂ G.val z.val w.val := (analyticValue₂_eq_inner G z w).symm

def hardyBoundaryDifference : ↥bidiskHardy →L[ℂ] ↥bidiskHardy :=
  (boundaryDifference ∘L bidiskHardy.subtypeL).codRestrict bidiskHardy
    (fun G => boundaryDifference_mem_bidiskHardy G.val G.property)

theorem toL2_coordinate_mem_hardy : toL2 coordinate ∈ hardy := by
  change toL2 (mode 1) ∈ hardy
  rw [toL2_mode]
  exact fourierBasis_mem_hardy 1

/-- Multiplication by the actual boundary difference gives the exact interior factor z-w. -/
theorem boundaryDifference_eval (G : BidiskL2) (hG : G ∈ bidiskHardy) (z w : Disk) :
    analyticValue₂ (boundaryDifference G) z.val w.val = (z.val-w.val)*analyticValue₂ G z.val w.val := by
  let L := bidiskEvaluation z w ∘L hardyBoundaryDifference
  let R := (z.val-w.val) • bidiskEvaluation z w
  have he : L = R := clm_eq_of_hilbertBasis bidiskHardyBasis L R (fun i => by
    change inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val)
      (boundaryDifference (bidiskHardyBasis i).val) =
        (z.val-w.val)*inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val) (bidiskHardyBasis i).val
    rw [bidiskHardyBasis_apply]
    have hmode : (bidiskHardyMode i).val =
        separatedProduct (fourierBasis (T := 1) (i.1 : ℤ)) (fourierBasis (T := 1) (i.2 : ℤ)) :=
      (separatedProduct_fourierBasis i.1 i.2).symm
    rw [hmode,boundaryDifference_separatedProduct,inner_sub_right,
      inner_separatedProduct,inner_separatedProduct,inner_separatedProduct]
    have hz : inner ℂ (szegoKernel z).val (fourierBasis (T := 1) (i.1 : ℤ)) = z.val^i.1 :=
      (inner_szegoKernel z (hardyMode i.1)).trans (analyticValue_fourierBasis i.1 z.val)
    have hw : inner ℂ (szegoKernel w).val (fourierBasis (T := 1) (i.2 : ℤ)) = w.val^i.2 :=
      (inner_szegoKernel w (hardyMode i.2)).trans (analyticValue_fourierBasis i.2 w.val)
    have hz' : inner ℂ (szegoKernel z).val (multiply coordinate (fourierBasis (T := 1) (i.1 : ℤ))) = z.val*z.val^i.1 := by
      have hi := inner_szegoKernel z (⟨multiply coordinate (hardyMode i.1).val,
        multiply_mem_hardy coordinate toL2_coordinate_mem_hardy _ (hardyMode i.1).property⟩ : Hardy)
      exact hi.trans ((analyticValue_coordinate_multiply (hardyMode i.1) z).trans
        (congrArg (fun a => z.val*a) (analyticValue_fourierBasis i.1 z.val)))
    have hw' : inner ℂ (szegoKernel w).val (multiply coordinate (fourierBasis (T := 1) (i.2 : ℤ))) = w.val*w.val^i.2 := by
      have hi := inner_szegoKernel w (⟨multiply coordinate (hardyMode i.2).val,
        multiply_mem_hardy coordinate toL2_coordinate_mem_hardy _ (hardyMode i.2).property⟩ : Hardy)
      exact hi.trans ((analyticValue_coordinate_multiply (hardyMode i.2) w).trans
        (congrArg (fun a => w.val*a) (analyticValue_fourierBasis i.2 w.val)))
    rw [hz,hw,hz',hw']
    ring)
  have hh := congrArg (fun A => A (⟨G,hG⟩ : ↥bidiskHardy)) he
  change bidiskEvaluation z w (hardyBoundaryDifference ⟨G,hG⟩) =
    (z.val-w.val)*bidiskEvaluation z w ⟨G,hG⟩ at hh
  rw [bidiskEvaluation_apply,bidiskEvaluation_apply] at hh
  exact hh

theorem energyH_mem_hardy (u : BoundaryLInf) (η : BoundaryL2) : energyH u η ∈ hardy :=
  multiply_mem_hardy coordinate toL2_coordinate_mem_hardy _ ((model u).orthogonalProjectionOnto η).property.1

theorem energyG_mem_hardy (u : BoundaryLInf) (η : BoundaryL2) : energyG u η ∈ hardy :=
  multiply_mem_hardy coordinate toL2_coordinate_mem_hardy _
    ((model u).orthogonalProjectionOnto (multiply (star u) η)).property.1

def boundaryNumerator (u : BoundaryLInf) (η : BoundaryL2) : BidiskL2 :=
  separatedProduct (energyH u η) (constL2 1)-separatedProduct (constL2 1) (energyH u η)+
    separatedProduct (toL2 u) (energyG u η)-separatedProduct (energyG u η) (toL2 u)

theorem boundaryNumerator_mem_bidiskHardy (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) :
    boundaryNumerator u η ∈ bidiskHardy :=
  bidiskHardy.sub_mem (bidiskHardy.add_mem
    (bidiskHardy.sub_mem
      (separatedProduct_mem_bidiskHardy ⟨_,energyH_mem_hardy u η⟩ ⟨_,constantCoreLaws.hardy 1⟩)
      (separatedProduct_mem_bidiskHardy ⟨_,constantCoreLaws.hardy 1⟩ ⟨_,energyH_mem_hardy u η⟩))
    (separatedProduct_mem_bidiskHardy ⟨_,hu.1⟩ ⟨_,energyG_mem_hardy u η⟩))
    (separatedProduct_mem_bidiskHardy ⟨_,energyG_mem_hardy u η⟩ ⟨_,hu.1⟩)

theorem analyticValue_constL2_disk (c : ℂ) (z : Disk) : analyticValue (constL2 c) z.val = c := by
  rw [constL2_fourier,analyticValue_smul _ _ z.property]
  change c*analyticValue (fourierBasis (T := 1) ((0 : ℕ) : ℤ)) z.val = c
  rw [analyticValue_fourierBasis,pow_zero,mul_one]

/-- The numerator is an actual positive bidisk Hardy vector with the manuscript's precise values. -/
theorem boundaryNumerator_eval (u : BoundaryLInf) (hu : IsInner u) (η : BoundaryL2) (z w : Disk) :
    analyticValue₂ (boundaryNumerator u η) z.val w.val =
      analyticValue (energyH u η) z.val-analyticValue (energyH u η) w.val+
        innerValue u z.val*analyticValue (energyG u η) w.val-
          innerValue u w.val*analyticValue (energyG u η) z.val := by
  rw [analyticValue₂_eq_inner ⟨_,boundaryNumerator_mem_bidiskHardy u hu η⟩ z w]
  change inner ℂ (separatedProduct (szegoKernel z).val (szegoKernel w).val)
    (separatedProduct (energyH u η) (constL2 1)-separatedProduct (constL2 1) (energyH u η)+
      separatedProduct (toL2 u) (energyG u η)-separatedProduct (energyG u η) (toL2 u)) = _
  rw [inner_sub_right,inner_add_right,inner_sub_right,inner_separatedProduct,inner_separatedProduct,
    inner_separatedProduct,inner_separatedProduct]
  have hpair (f : Hardy) (a : Disk) : inner ℂ (szegoKernel a).val f.val = analyticValue f.val a.val := inner_szegoKernel a f
  rw [hpair ⟨_,energyH_mem_hardy u η⟩ z,hpair ⟨_,constantCoreLaws.hardy 1⟩ w,
    hpair ⟨_,constantCoreLaws.hardy 1⟩ z,hpair ⟨_,energyH_mem_hardy u η⟩ w,
    hpair ⟨_,hu.1⟩ z,hpair ⟨_,energyG_mem_hardy u η⟩ w,
    hpair ⟨_,energyG_mem_hardy u η⟩ z,hpair ⟨_,hu.1⟩ w,
    analyticValue_constL2_disk,analyticValue_constL2_disk]
  unfold innerValue
  ring

theorem boundaryNumerator_ae (u : BoundaryLInf) (η : BoundaryL2) :
    boundaryNumerator u η =ᵐ[circleMeasure.prod circleMeasure] fun p =>
      energyH u η p.1-energyH u η p.2+u p.1*energyG u η p.2-u p.2*energyG u η p.1 := by
  let A := separatedProduct (energyH u η) (constL2 1)
  let B := separatedProduct (constL2 1) (energyH u η)
  let C := separatedProduct (toL2 u) (energyG u η)
  let E := separatedProduct (energyG u η) (toL2 u)
  have hc : constL2 1 =ᵐ[circleMeasure] fun _ => (1 : ℂ) := (memLp_const (1 : ℂ)).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (A-B+C) E,Lp.coeFn_add (A-B) C,Lp.coeFn_sub A B,
    separatedProduct_ae (energyH u η) (constL2 1),separatedProduct_ae (constL2 1) (energyH u η),
    separatedProduct_ae (toL2 u) (energyG u η),separatedProduct_ae (energyG u η) (toL2 u),
    boundary_ae_fst hc,boundary_ae_snd hc,boundary_ae_fst (toL2_ae u),boundary_ae_snd (toL2_ae u)]
    with p hs ha hb hA hB hC hE h1 h2 hu1 hu2
  simp only [Pi.sub_apply,Pi.add_apply] at hs ha hb
  change (A-B+C-E) p = _
  rw [hs,ha,hb,hA,hB,hC,hE,h1,h2,hu1,hu2]
  ring

theorem energyQuotient_measurable (u : BoundaryLInf) (η : BoundaryL2) :
    Measurable (fun p : Boundary × Boundary => energyQuotient u η p.1 p.2) := by
  have hh := (Lp.stronglyMeasurable (energyH u η)).measurable
  have hg := (Lp.stronglyMeasurable (energyG u η)).measurable
  have hu := (Lp.stronglyMeasurable u).measurable
  have he := (fourier (T := 1) 1).continuous.measurable
  exact ((((hh.comp measurable_fst).sub (hh.comp measurable_snd)).add
    ((hu.comp measurable_fst).mul (hg.comp measurable_snd))).sub
    ((hu.comp measurable_snd).mul (hg.comp measurable_fst))).div
      ((he.comp measurable_fst).sub (he.comp measurable_snd))

theorem energy_eq_product (u : BoundaryLInf) (η : BoundaryL2) :
    energy u η = ∫⁻ p, ENNReal.ofReal (‖energyQuotient u η p.1 p.2‖^2) ∂circleMeasure.prod circleMeasure :=
  (lintegral_prod _ ((energyQuotient_measurable u η).norm.pow_const 2 |>.ennreal_ofReal.aemeasurable)).symm

/-- The diagonal is product-null for actual normalized Haar measure. -/
theorem boundaryDifference_ne_zero_ae :
    ∀ᵐ p : Boundary × Boundary ∂circleMeasure.prod circleMeasure,
      fourier (T := 1) 1 p.1-fourier (T := 1) 1 p.2 ≠ 0 := by
  have hp : ∀ᵐ p : Boundary × Boundary ∂circleMeasure.prod circleMeasure, p.1 ≠ p.2 :=
    (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
      (Filter.Eventually.of_forall (fun x => (circleMeasure.ae_ne x).mono (fun y hy => hy.symm)))
  filter_upwards [hp] with p hne
  apply sub_ne_zero.mpr
  intro he
  apply hne
  apply AddCircle.injective_toCircle (T := 1) one_ne_zero
  apply Subtype.ext
  simpa only [fourier_one] using he

/-- Any honest L² representative of the raw quotient satisfies the genuine boundary equation. -/
theorem boundaryDifference_of_quotient (u : BoundaryLInf) (η : BoundaryL2) (G : BidiskL2)
    (hG : G =ᵐ[circleMeasure.prod circleMeasure] fun p => energyQuotient u η p.1 p.2) :
    boundaryDifference G = boundaryNumerator u η := by
  apply Lp.ext
  filter_upwards [boundaryDifference_ae G,hG,boundaryNumerator_ae u η,boundaryDifference_ne_zero_ae]
    with p hd hq hn hne
  rw [hd,hq,hn]
  unfold energyQuotient
  field_simp

/-- Actual interior numerator identity, including the zero diagonal. -/
theorem boundaryNumerator_eval_FKernel (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (z w : Disk) :
    analyticValue₂ (boundaryNumerator u η.val) z.val w.val = (z.val-w.val)*FKernel u η.val z.val w.val := by
  rw [boundaryNumerator_eval u hu η.val z w]
  by_cases h : z.val = w.val
  · rw [h]
    ring
  · have hf := (kernel_calculus kernelCalculus removableCalculus u hu hn η).1 z.val z.property w.val w.property
    rw [dividedDifference,ite_eq_right h] at hf
    rw [hf]
    field_simp

/-- The graph's analytic identity implies the actual L² boundary multiplication equation. -/
theorem boundaryDifference_of_QGraph (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (G : TensorModel u) (hG : QGraph u η G) :
    boundaryDifference G.val = boundaryNumerator u η.val := by
  have he := bidiskHardy_analyticValue₂_injective
    ⟨_,boundaryDifference_mem_bidiskHardy G.val (tensorModel_le_bidiskHardy u G.property)⟩
    ⟨_,boundaryNumerator_mem_bidiskHardy u hu η.val⟩ (fun z w => by
      rw [boundaryDifference_eval G.val (tensorModel_le_bidiskHardy u G.property),
        boundaryNumerator_eval_FKernel u hu hn η z w,hG z.val z.property w.val w.property])
  exact congrArg (fun f : ↥bidiskHardy => f.val) he

/-- Conversely the L² multiplication equation determines the genuine analytic tensor graph. -/
theorem tensorGraph_of_boundaryDifference (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (G : BidiskL2) (hD : boundaryDifference G = boundaryNumerator u η.val) :
    ∃ hG : G ∈ tensorModel u, QGraph u η ⟨G,hG⟩ := by
  have hG := mem_bidiskHardy_of_boundaryDifference G _ (boundaryNumerator_mem_bidiskHardy u hu η.val) hD
  have hoff (z w : Disk) (hne : z.val ≠ w.val) : analyticValue₂ G z.val w.val = FKernel u η.val z.val w.val := by
    have he := congrArg (fun f => analyticValue₂ f z.val w.val) hD
    rw [boundaryDifference_eval G hG z w,boundaryNumerator_eval_FKernel u hu hn η z w] at he
    exact mul_left_cancel₀ (sub_ne_zero.mpr hne) he
  have hval (z w : Disk) : analyticValue₂ G z.val w.val = FKernel u η.val z.val w.val := by
    by_cases he : z.val = w.val
    · have hwz : w = z := Subtype.ext he.symm
      subst w
      let f := secondSection G z
      have ho : IsOpen disk := isOpen_lt continuous_norm continuous_const
      have hv : (fun w => analyticValue₂ G z.val w) =ᶠ[𝓝 z.val] analyticValue f.val := by
        filter_upwards [ho.mem_nhds z.property] with w hw
        exact (secondSection_eval ⟨G,hG⟩ z ⟨w,hw⟩).symm
      have hc := (continuousAt_congr hv).mpr (analyticOnNhd_analyticValue f.val z.val z.property).continuousAt
      have hcf := kernelCalculus.continuous_diagonal u hu hn η z.val z.property
      have heq : (fun w => analyticValue₂ G z.val w) =ᶠ[𝓝[≠] z.val] FKernel u η.val z.val := by
        filter_upwards [(show ∀ᶠ w in 𝓝 z.val, w ∈ disk from ho.mem_nhds z.property).filter_mono nhdsWithin_le_nhds,
          (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] z.val, w ≠ z.val)] with w hw hne
        apply hoff z ⟨w,hw⟩
        simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,ne_eq,eq_comm] using hne
      exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
        ((hcf.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
    · exact hoff z w he
  obtain ⟨hfirst,hsecond⟩ := FKernel_sections u hu η.val
  have ht : G ∈ tensorModel u := tensor_section_criterion u G hG
    (fun w hw => by
      obtain ⟨f,hf⟩ := hfirst w hw
      exact ⟨f,fun z hz => (hf z hz).trans (hval ⟨z,hz⟩ ⟨w,hw⟩).symm⟩)
    (fun z hz => by
      obtain ⟨f,hf⟩ := hsecond z hz
      exact ⟨f,fun w hw => (hf w hw).trans (hval ⟨z,hz⟩ ⟨w,hw⟩).symm⟩)
  exact ⟨ht,fun z hz w hw => hval ⟨z,hz⟩ ⟨w,hw⟩⟩

/-- Native L² norm as its literal extended product integral. -/
theorem bidisk_lintegral_norm_sq (G : BidiskL2) :
    (∫⁻ p, ENNReal.ofReal (‖G p‖^2) ∂circleMeasure.prod circleMeasure) = ENNReal.ofReal (‖G‖^2) := by
  have hreal : ‖G‖^2 = ∫ p, ‖G p‖^2 ∂circleMeasure.prod circleMeasure := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def G G)
    rw [← integral_re] at h
    · simpa only [← norm_sq_eq_re_inner] using h
    · exact L2.integrable_inner G G
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp G).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Filter.Eventually.of_forall (fun p => sq_nonneg ‖G p‖))]
  exact (congrArg ENNReal.ofReal hreal).symm

/-- Finite raw energy supplies an actual L² quotient, rather than a formal boundary representative. -/
theorem memLp_energyQuotient (u : BoundaryLInf) (η : BoundaryL2) (he : energy u η < ∞) :
    MemLp (fun p : Boundary × Boundary => energyQuotient u η p.1 p.2) 2 (circleMeasure.prod circleMeasure) := by
  let f : Boundary × Boundary → ℂ := fun p => energyQuotient u η p.1 p.2
  have hm : Measurable f := energyQuotient_measurable u η
  have ht : (∫⁻ p, ENNReal.ofReal (‖f p‖^2) ∂circleMeasure.prod circleMeasure) < ∞ :=
    (energy_eq_product u η) ▸ he
  have hi : Integrable (fun p => ‖f p‖^2) (circleMeasure.prod circleMeasure) :=
    (lintegral_ofReal_ne_top_iff_integrable (hm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => sq_nonneg ‖f p‖))).mp ht.ne
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi

/-- An analytic graph vector is literally the boundary quotient almost everywhere off the null diagonal. -/
theorem QGraph_quotient_ae (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (G : TensorModel u) (hG : QGraph u η G) :
    G.val =ᵐ[circleMeasure.prod circleMeasure] fun p => energyQuotient u η.val p.1 p.2 := by
  have hD := boundaryDifference_of_QGraph u hu hn η G hG
  filter_upwards [boundaryDifference_ae G.val,boundaryNumerator_ae u η.val,boundaryDifference_ne_zero_ae]
    with p hd hn hne
  rw [hD] at hd
  have he := hd.symm.trans hn
  unfold energyQuotient
  exact (eq_div_iff hne).mpr ((mul_comm _ _).trans he)

theorem energy_of_QGraph (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (G : TensorModel u) (hG : QGraph u η G) :
    energy u η.val = ENNReal.ofReal (‖G‖^2) := by
  have he := lintegral_congr_ae ((QGraph_quotient_ae u hu hn η G hG).fun_comp
    (fun z : ℂ => ENNReal.ofReal (‖z‖^2)))
  simp only [Function.comp_apply] at he
  rw [energy_eq_product,← he,bidisk_lintegral_norm_sq]
  rfl

/-- Finite raw boundary energy gives the actual tensor graph by the full Fourier recurrence. -/
theorem exists_QGraph_of_energy (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (he : energy u η.val < ∞) : ∃ G : TensorModel u, QGraph u η G := by
  let hq := memLp_energyQuotient u η.val he
  let q : BidiskL2 := hq.toLp (fun p => energyQuotient u η.val p.1 p.2)
  have hqa : q =ᵐ[circleMeasure.prod circleMeasure] fun p => energyQuotient u η.val p.1 p.2 := hq.coeFn_toLp
  obtain ⟨ht,hG⟩ := tensorGraph_of_boundaryDifference u hu hn η q (boundaryDifference_of_quotient u η.val q hqa)
  exact ⟨⟨q,ht⟩,hG⟩

/-- Finite native coefficient energy gives the graph using its completely defined matrix data. -/
theorem exists_QGraph_of_matrixEnergy (u : BoundaryLInf) (b : MatrixData u) (η : Ambient u)
    (he : matrixEnergy b η < ∞) : ∃ G : TensorModel u, QGraph u η G := by
  let x : lp (fun _ : b.Index × b.Index => ℂ) 2 :=
    ⟨fun ij => b.coefficient ij η,(memlp_two_iff_energy _).mpr he⟩
  refine ⟨b.tensor x,(b.graph_coefficients η (b.tensor x)).mpr ?_⟩
  intro ij
  rw [b.tensor.symm_apply_apply]

/-- Exact native tensor norm and the literal coefficient energy, for every data package. -/
theorem matrixEnergy_of_QGraph (u : BoundaryLInf) (b : MatrixData u) (η : Ambient u)
    (G : TensorModel u) (hG : QGraph u η G) :
    ENNReal.ofReal (‖G‖^2) = matrixEnergy b η := by
  have hc := (b.graph_coefficients η G).mp hG
  have he := l2CoordinateLaws.norm _ (b.tensor.symm G)
  rw [b.tensor.symm.norm_map] at he
  exact he.trans (tsum_congr (fun ij => by rw [hc ij]))

/-- The extended boundary energy equals the matrix energy, with divergent cases retained. -/
theorem boundary_energy_eq_matrix (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (b : MatrixData u) (η : Ambient u) : energy u η.val = matrixEnergy b η := by
  by_cases he : energy u η.val < ∞
  · obtain ⟨G,hG⟩ := exists_QGraph_of_energy u hu hn η he
    exact (energy_of_QGraph u hu hn η G hG).trans (matrixEnergy_of_QGraph u b η G hG)
  · have heTop : energy u η.val = ∞ := not_lt_top_iff.mp he
    have hmTop : matrixEnergy b η = ∞ := by
      by_contra hm
      obtain ⟨G,hG⟩ := exists_QGraph_of_matrixEnergy u b η (lt_top_iff_ne_top.mpr hm)
      apply he
      rw [energy_of_QGraph u hu hn η G hG]
      exact ENNReal.ofReal_lt_top
    rw [heTop,hmTop]

/-- The native L² pairing is exactly the manuscript's iterated raw boundary pairing. -/
theorem energyPairing_of_QGraph (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η γ : Ambient u) (G H : TensorModel u) (hG : QGraph u η G) (hH : QGraph u γ H) :
    energyPairing u η.val γ.val = inner ℂ H G := by
  have hpair : (fun p => inner ℂ (H.val p) (G.val p)) =ᵐ[circleMeasure.prod circleMeasure]
      fun p => energyQuotient u η.val p.1 p.2*conj (energyQuotient u γ.val p.1 p.2) := by
    filter_upwards [QGraph_quotient_ae u hu hn η G hG,QGraph_quotient_ae u hu hn γ H hH] with p hg hh
    rw [RCLike.inner_apply,hg,hh]
  have hi := (L2.integrable_inner H.val G.val).congr hpair
  calc
    _ = ∫ p, energyQuotient u η.val p.1 p.2*conj (energyQuotient u γ.val p.1 p.2) ∂circleMeasure.prod circleMeasure :=
      (integral_prod _ hi).symm
    _ = _ := by
      change (∫ p, energyQuotient u η.val p.1 p.2*conj (energyQuotient u γ.val p.1 p.2)
        ∂circleMeasure.prod circleMeasure) = inner ℂ H.val G.val
      rw [L2.inner_def]
      exact integral_congr_ae hpair.symm

/-- Full boundary Parseval, including exact polarized pairing and all∞ energies. -/
theorem boundaryParseval : BoundaryParsevalObligation where
  norm := boundary_energy_eq_matrix
  pairing u hu hn b η γ hη hγ := by
    obtain ⟨G,hG⟩ := exists_QGraph_of_matrixEnergy u b η hη
    obtain ⟨H,hH⟩ := exists_QGraph_of_matrixEnergy u b γ hγ
    have hpair := coefficientPair_tensor u b η γ (b.tensor.symm G) (b.tensor.symm H)
      ((b.graph_coefficients η G).mp hG) ((b.graph_coefficients γ H).mp hH)
    rw [b.tensor.apply_symm_apply,b.tensor.apply_symm_apply] at hpair
    exact (energyPairing_of_QGraph u hu hn η γ G H hG hH).trans hpair.symm

/-- The analytic/energy/matrix/kernel work is proved; only natural unbounded graph/square-root theory remains. -/
theorem hilbertSchmidtEnergy_of_graph (hF : GraphFormObligation) : HilbertSchmidtConclusion :=
  hilbertSchmidtEnergy_of_kernels boundaryParseval hF

/-- The same unbounded graph/square-root proof remains for the full differential domain conclusion. -/
theorem differentialRealization_of_graph (hF : GraphFormObligation) : DifferentialConclusion :=
  differentialRealization_of_kernels boundaryParseval hF

/-- The full actual THO Hilbert–Schmidt energy criterion is unconditional. -/
theorem tho_hilbertSchmidt_energy (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u) (η : Ambient u) :
    HasSchattenTHO 2 u (star η.val) ↔ energy u η.val < ∞ := by
  rw [boundaryParseval.norm u hu hn (actualMatrixData u hu) η]
  exact (matrixOperator u hu hn (actualMatrixData u hu) η).1

theorem tho_hilbertSchmidt_energy_norm (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (η : Ambient u) (B : Model u →L[ℂ] ConjugateModel u)
    (hB : RepresentsTHO u (star η.val) B) (hs : Schatten 2 B) :
    ENNReal.ofReal (schattenNorm 2 B^2) = energy u η.val :=
  ((matrixOperator u hu hn (actualMatrixData u hu) η).2 B hB hs).trans
    (boundaryParseval.norm u hu hn (actualMatrixData u hu) η).symm

/-- The canonical TTO criterion and exact gauge are proved; no graph/square-root claim is included here. -/
theorem canonical_hilbertSchmidt_energy (u : BoundaryLInf) (hu : IsInner u) (hn : Nonconstant u)
    (φ ψ : Model u) (hψ : analyticValue ψ.val 0 = 0) :
    ∃ η : Ambient u,
      η.val = conjugation u φ.val+multiply u (multiply (star coordinate) ψ.val) ∧
      energyH u η.val = multiply coordinate (conjugation u φ.val) ∧ energyG u η.val = ψ.val ∧
      (HasSchattenTTO 2 u (splitSymbol φ.val ψ.val) ↔ energy u η.val < ∞) ∧
      ∀ A : Model u →L[ℂ] Model u, RepresentsTTO u (splitSymbol φ.val ψ.val) A → Schatten 2 A →
        ENNReal.ofReal (schattenNorm 2 A^2) = energy u η.val := by
  obtain ⟨η,hη,hH,hG,hiff,hcomp⟩ := canonicalTHO u hu hn φ ψ hψ
  refine ⟨η,hη,hH,hG,hiff.trans (tho_hilbertSchmidt_energy u hu hn η),?_⟩
  intro A hA hs
  obtain ⟨B,hB,hsB,hsing⟩ := hcomp A hA hs
  rw [schattenNorm_transfer (p := 2) hsing]
  exact tho_hilbertSchmidt_energy_norm u hu hn η B hB hsB

end TTO.Paper.Proved
