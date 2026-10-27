import BPFixedPoints.Incidence.ResolutionCup
import BPFixedPoints.Incidence.CechCupAugmentation
import BPFixedPoints.Incidence.ResolutionAugmentation

/-! # Compare the transferred product with multiplication in the original incidence ring -/

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

namespace BPFixedPoints.CechProduct

open Finsupp ResolutionTools

variable (R : Type*) [CommRing R] {V : Type*} [Fintype V]

theorem faceEquiv_d_left (d : V → ℕ) (x : C R V) :
    faceEquiv R ((contraction R d).d x) 0 = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]
  | single b r =>
    apply faceEquiv_eq_zero_of_degree R ((contraction_d_degree R d).apply_single b r)
    simp only [faceDegree, Pi.zero_apply]
    simp
    omega

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncTorusRing :=
  G.incTorusCoeffHom.toRingHom.toAlgebra

theorem incTotalCup_empty (x y : IncTotalModule (V := V) (E := E)) :
    (G.incTotalCup x y) ∅ = chainCup (IncCoeffRing E) 0 0 (x ∅) (y ∅) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hx']
  | single S x =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, Finsupp.add_apply, hy, hy']
    | single T y =>
      rw [G.incTotalCup_single, Koszul.wedgeSingle_apply]
      have hd : G.deg ∅ = 0 := funext G.deg_empty
      by_cases hS : S = ∅ <;> by_cases hT : T = ∅ <;>
        simp [hS, hT, incCupCoefficient, Finset.union_eq_empty, hd, apply_ite, ite_apply, eq_comm]
      intro _
      rw [Finsupp.single_eq_of_ne (show ∅ ≠ S ∪ T from fun h =>
        hS (Finset.union_eq_empty.mp h.symm).1)]

theorem incFaceRawEval_cup (x y : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval 0 (G.incTotalCup x y) = G.incFaceRawEval 0 x * G.incFaceRawEval 0 y := by
  simp only [G.incFaceRawEval_apply, G.incTotalCup_empty, polynomialFaceEquiv_apply,
    faceEquiv_chainCup, map_mul]

theorem incFaceRawEval_d (x : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval 0 (G.incTotalDifferential x) = 0 := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, G.incFaceRawEval_koszul, add_zero]
  simp only [G.incFaceRawEval_apply, G.incCechContraction_d_apply,
    polynomialFaceEquiv_apply, faceEquiv_d_left, map_zero]

theorem incFaceRawEval_inclusion_projection {x : IncTotalModule (V := V) (E := E)}
    (hx : G.incTotalDifferential x = 0) :
    G.incFaceRawEval 0 (G.incResolutionInclusion (G.incResolutionProjection x)) =
      G.incFaceRawEval 0 x := by
  have h := congrArg (G.incFaceRawEval 0)
    (LinearMap.congr_fun G.incResolutionHomotopy_identity x)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_add, hx, map_zero, G.incFaceRawEval_d, zero_add] using h

theorem incResolutionTorusAugmentation_cup (x y : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0)
    (hy : y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incResolutionTorusAugmentation (G.incResolutionCup x y) =
      G.incResolutionTorusAugmentation x * G.incResolutionTorusAugmentation y := by
  have hI (z : G.IncResolutionBasis →₀ IncCoeffRing E)
      (hz : z ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
      G.incTotalDifferential (G.incResolutionInclusion z) = 0 := by
    rw [show G.incTotalDifferential (G.incResolutionInclusion z) =
      G.incResolutionInclusion (G.incResolutionDifferential z) from
        LinearMap.congr_fun G.incResolutionInclusion_chain z,
      G.incResolutionDifferential_zero_degree z hz, map_zero]
  change G.incFaceRawEval 0 (G.incResolutionInclusion
    (G.incResolutionCup x y)) = G.incFaceRawEval 0 (G.incResolutionInclusion x) *
      G.incFaceRawEval 0 (G.incResolutionInclusion y)
  rw [G.incResolutionCup_apply, G.incFaceRawEval_inclusion_projection
    (G.incTotalCup_cycles (hI x hx) (hI y hy)), G.incFaceRawEval_cup]

/-- Augmentation of the product equals ordinary multiplication in the original incidence ring. -/
theorem incResolutionAugmentation_cup
    (x y : ↥(gradedPiece (IncCoeffRing E) G.incResolutionDegree 0)) :
    G.incResolutionAugmentation
        ⟨G.incResolutionCup x.val y.val, G.incResolutionCup_degree 0 0 x.property y.property⟩ =
      G.incResolutionAugmentation x * G.incResolutionAugmentation y := by
  apply Subtype.ext
  exact G.incResolutionTorusAugmentation_cup x.val y.val x.property y.property

end BPFixedPoints.Multigraph
