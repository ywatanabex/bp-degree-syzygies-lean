import BPFixedPoints.Incidence.VertexProjectiveTwistRowH0
import BPFixedPoints.Incidence.CechTwoRowH1Kernel
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Native row sections with zero second twist and their original coefficient restrictions -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- First-direction restrictions preserve every original second right-chart polynomial exponent. -/
theorem twoRowRightCoordinates_restrict (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : FaceRing R (![b,1] : Fin 2 → Fin 3)) :
    twoRowFaceCoordinates R c 1 (twoRowRestriction R (fun v => -(d v : ℤ)) h 1 x) =
      Finsupp.mapRange.linearMap (twoRowBaseRestriction R d h) (twoRowFaceCoordinates R b 1 x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [(twoRowRestriction R _ h 1).map_zero,(twoRowFaceCoordinates R c 1).map_zero,
      (twoRowFaceCoordinates R b 1).map_zero,LinearMap.map_zero]
  | add x y hx hy =>
    rw [(twoRowRestriction R _ h 1).map_add,(twoRowFaceCoordinates R c 1).map_add,
      (twoRowFaceCoordinates R b 1).map_add,LinearMap.map_add,hx,hy]
  | single m r =>
    change twoRowFaceCoordinates R c 1 (multiTwistFaceRestriction R _ _ _) = _
    rw [multiTwistFaceRestriction_single,twoRowFaceCoordinates_single,twoRowFaceCoordinates_single,
      Finsupp.mapRange.linearMap_apply,Finsupp.mapRange_single,twoRowBaseRestriction_single]
    have h0 : (refinementExponent (twoColumnFaceRefines h 1) m +
        twistRestrictionShift (twoColumnFaceRefines h 1) (fun v => -(d v : ℤ))) 0 =
          twoRowFirstExponent d h (m 0) := rfl
    have h1 : (refinementExponent (twoColumnFaceRefines h 1) m +
        twistRestrictionShift (twoColumnFaceRefines h 1) (fun v => -(d v : ℤ))) 1 = m 1 := by
      change m 1 + 0 = m 1
      exact add_zero _
    rw [h0,h1]

/-- Evaluation at the original unique degree-zero state when the second twist is zero. -/
noncomputable def twoRowH0BaseEquiv (d : Fin 2 → ℕ) (hd : d 1 = 0) (b : Fin 3) :
    CechLine.H0 (TwoRowBase R b) (d 1) ≃ₗ[R] TwoRowBase R b := by
  letI : Subsingleton (CechLine.H0Index (d 1)) := by
    simpa only [CechLine.H0Index,hd,ite_true] using (inferInstance : Subsingleton (Fin 1))
  exact Finsupp.uniqueLinearEquiv R (TwoRowBase R b) (⟨0,by simp [CechLine.H0Index,hd]⟩)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R]

/-- Original row sections with zero second twist equal the original first-coordinate face coefficients. -/
noncomputable def vertexTwistRowSectionBaseEquiv (d : Fin 2 → ℕ) (hd : d 1 = 0) (b : Fin 3) :
    vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b ≃ₗ[R] TwoRowBase R b :=
  (vertexTwistRowSectionStateEquiv R d b).trans (twoRowH0BaseEquiv R d hd b)

/-- Every original row base coefficient is the original constant coefficient of its native right-corner restriction. -/
theorem vertexTwistRowSectionBaseEquiv_apply (d : Fin 2 → ℕ) (hd : d 1 = 0) (b : Fin 3)
    (s : vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b) :
    vertexTwistRowSectionBaseEquiv R d hd b s =
      twoRowFaceCoordinates R b 1 (vertexTwistTwoRectangleCoordinates R (fun v => -(d v : ℤ)) b 1
        ((vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))).presheaf.map (homOfLE inf_le_left).op s)) 0 := by
  change twoRowH0BaseEquiv R d hd b (vertexTwistRowSectionStateEquiv R d b s) = _
  rw [vertexTwistRowSectionStateEquiv_apply]
  rw [CechLine.projectionZero,dite_eq_left hd]
  change (Finsupp.single _ _ : CechLine.H0 (TwoRowBase R b) (d 1)) _ = _
  rw [Finsupp.single_eq_same]
  rfl

/-- The native first-direction restriction on the original row sections. -/
noncomputable def vertexTwistRowSectionRestriction (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b →ₗ[R]
      vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) c :=
  SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (homOfLE (vertexTwoRowOpen_le R h))

/-- The original zero-second-twist row comparison preserves every native first-direction restriction. -/
theorem vertexTwistRowSectionBaseEquiv_restrict (d : Fin 2 → ℕ) (hd : d 1 = 0)
    {b c : Fin 3} (h : b = c ∨ c = 2)
    (s : vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b) :
    vertexTwistRowSectionBaseEquiv R d hd c (vertexTwistRowSectionRestriction R d h s) =
      twoRowBaseRestriction R d h (vertexTwistRowSectionBaseEquiv R d hd b s) := by
  rw [vertexTwistRowSectionBaseEquiv_apply,vertexTwistRowSectionBaseEquiv_apply]
  let M := vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))
  have he := vertexTwistFaceSectionsAt_restrict R (Fin 2) (fun v => -(d v : ℤ))
    (twoColumnFaceRefines h 1) _ _ (vertexTwoFaceOpen_eq R b 1).symm (vertexTwoFaceOpen_eq R c 1).symm
      (inf_le_inf_right (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 1)
        (vertexTwoRowOpen_le R h)) (M.presheaf.map (homOfLE inf_le_left).op s)
  have hc : M.presheaf.map (homOfLE inf_le_left).op (vertexTwistRowSectionRestriction R d h s) =
      M.presheaf.map (homOfLE (inf_le_inf_right
        (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 1) (vertexTwoRowOpen_le R h))).op
          (M.presheaf.map (homOfLE inf_le_left).op s) := by
    change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ (M.presheaf.map _ s)
    rw [← M.presheaf.map_comp_apply,← M.presheaf.map_comp_apply]
    rfl
  change vertexTwistTwoRectangleCoordinates R (fun v => -(d v : ℤ)) c 1
    (M.presheaf.map (homOfLE (inf_le_inf_right
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 1) (vertexTwoRowOpen_le R h))).op
        (M.presheaf.map (homOfLE inf_le_left).op s)) =
      twoRowRestriction R (fun v => -(d v : ℤ)) h 1
        (vertexTwistTwoRectangleCoordinates R (fun v => -(d v : ℤ)) b 1
          (M.presheaf.map (homOfLE inf_le_left).op s)) at he
  rw [hc,he,twoRowRightCoordinates_restrict]
  rfl

end BPFixedPoints.ProjectiveLine
