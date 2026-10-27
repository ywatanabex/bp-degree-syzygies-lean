import BPFixedPoints.Incidence.VertexProjectiveTwistFaceCoordinatesAt
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoRectangleCohomology
import BPFixedPoints.Incidence.CechTwoRectangleBoundary

/-! # The actual rectangular H2 quotient in the original face coordinates -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 200000
variable (R : Type) [CommRing R]

/-- Actual sections on the specified two-coordinate rectangle with the original geometric base action. -/
noncomputable def vertexTwistTwoRectangleSections (a : Fin 2 → ℤ) (b c : Fin 3) : ModuleCat R :=
  SchemeTools.schemeBaseOpenSectionModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
    (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c)

/-- The original canonical face coordinates, retaining the actual rectangular open. -/
noncomputable def vertexTwistTwoRectangleCoordinates (a : Fin 2 → ℤ) (b c : Fin 3) :
    vertexTwistTwoRectangleSections R a b c ≃ₗ[R] FaceRing R (![b,c] : Fin 2 → Fin 3) :=
  vertexTwistFaceSectionsAt R (Fin 2) a ![b,c] _ (vertexTwoFaceOpen_eq R b c).symm

/-- Original coordinates of all four native boundary section modules. -/
noncomputable def vertexTwistTwoRectangleBoundaryCoordinates (a : Fin 2 → ℤ) :
    SchemeTools.SchemeRectangleBoundarySections (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
      (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
      (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1) ≃ₗ[R]
        TwoRectangleCoefficients R :=
  ((vertexTwistTwoRectangleCoordinates R a 0 2).prodCongr
    (vertexTwistTwoRectangleCoordinates R a 1 2)).prodCongr
      ((vertexTwistTwoRectangleCoordinates R a 2 0).prodCongr
        (vertexTwistTwoRectangleCoordinates R a 2 1))

/-- Every original rectangle-to-top native restriction has its original coefficient map. -/
theorem vertexTwistTwoRectangleCoordinates_restrict (a : Fin 2 → ℤ) (b c : Fin 3)
    (s : vertexTwistTwoRectangleSections R a b c) :
    vertexTwistTwoRectangleCoordinates R a 2 2
      (SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
        (homOfLE (show
          (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) 2 ⊓
            SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 2) ≤
          (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
            SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c) from by
            rw [← vertexTwoFaceOpen_eq, ← vertexTwoFaceOpen_eq]
            exact vertexBinaryFaceOpen_refinement R (Fin 2) (twoFaceRefinesTop ![b,c]))) s) =
      multiTwistFaceRestriction R (twoFaceRefinesTop ![b,c]) a (vertexTwistTwoRectangleCoordinates R a b c s) :=
  vertexTwistFaceSectionsAt_restrict R (Fin 2) a (twoFaceRefinesTop ![b,c]) _ _
    (vertexTwoFaceOpen_eq R b c).symm (vertexTwoFaceOpen_eq R 2 2).symm _ s

/-- The actual four native signed restrictions agree with the specified original coefficient boundary. -/
theorem vertexTwistTwoRectangleCoordinates_boundary (a : Fin 2 → ℤ)
    (x : SchemeTools.SchemeRectangleBoundarySections (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
      (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
      (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1)) :
    vertexTwistTwoRectangleCoordinates R a 2 2
      (SchemeTools.schemeRectangleBoundaryLinear (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
        (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
        (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1) x) =
      twoRectangleBoundary R a (vertexTwistTwoRectangleBoundaryCoordinates R a x) := by
  change vertexTwistTwoRectangleCoordinates R a 2 2 ((_ - _) - (_ - _)) = _
  rw [map_sub,map_sub,map_sub]
  exact congrArg₂ (fun u v => u-v)
    (congrArg₂ (fun u v => u-v)
      (vertexTwistTwoRectangleCoordinates_restrict R a 0 2 x.1.1)
      (vertexTwistTwoRectangleCoordinates_restrict R a 1 2 x.1.2))
    (congrArg₂ (fun u v => u-v)
      (vertexTwistTwoRectangleCoordinates_restrict R a 2 0 x.2.1)
      (vertexTwistTwoRectangleCoordinates_restrict R a 2 1 x.2.2))

/-- The original full-overlap coordinates take precisely the native boundary image to the original coefficient boundary image. -/
theorem vertexTwistTwoRectangleCoordinates_range (a : Fin 2 → ℤ) :
    (LinearMap.range (SchemeTools.schemeRectangleBoundaryLinear (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) a)
      (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
      (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1))).map
      (vertexTwistTwoRectangleCoordinates R a 2 2).toLinearMap =
        LinearMap.range (twoRectangleBoundary R a) := by
  ext z
  constructor
  · rintro ⟨y,⟨x,rfl⟩,rfl⟩
    exact ⟨vertexTwistTwoRectangleBoundaryCoordinates R a x,
      (vertexTwistTwoRectangleCoordinates_boundary R a x).symm⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨s,rfl⟩ := (vertexTwistTwoRectangleBoundaryCoordinates R a).surjective x
    exact ⟨_,⟨s,rfl⟩,vertexTwistTwoRectangleCoordinates_boundary R a s⟩

/-- The actual rectangular quotient has its specified original coefficient presentation. -/
noncomputable def vertexTwistTwoRectangleCoefficientQuotientEquiv (a : Fin 2 → ℤ) :
    VertexTwistTwoRectangleQuotient R a ≃ₗ[R]
      (FaceRing R twoTopFace ⧸ LinearMap.range (twoRectangleBoundary R a)) :=
  Submodule.Quotient.equiv _ _ (vertexTwistTwoRectangleCoordinates R a 2 2)
    (vertexTwistTwoRectangleCoordinates_range R a)

noncomputable local instance twoRectangleCoordinatesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable [IsNoetherianRing R]

/-- The original coefficient rectangular quotient computes actual global H2 with the original geometric action. -/
noncomputable def vertexTwistTwoCoefficientH2LinearEquiv (a : Fin 2 → ℤ) :
    letI : Module R ((vertexTwistAbelianSheaf R (Fin 2) a).H.{1} 2) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a) 2
    (FaceRing R twoTopFace ⧸ LinearMap.range (twoRectangleBoundary R a)) ≃ₗ[R]
      (vertexTwistAbelianSheaf R (Fin 2) a).H.{1} 2 :=
  (vertexTwistTwoRectangleCoefficientQuotientEquiv R a).symm.trans
    (vertexTwistTwoRectangleH2LinearEquiv R a)

/-- Every coefficient representative is evaluated in the original full-overlap frame before the original connecting comparison. -/
theorem vertexTwistTwoCoefficientH2LinearEquiv_mk (a : Fin 2 → ℤ) (x : FaceRing R twoTopFace) :
    vertexTwistTwoCoefficientH2LinearEquiv R a (Submodule.Quotient.mk x) =
      vertexTwistTwoRectangleH2LinearEquiv R a
        (Submodule.Quotient.mk ((vertexTwistTwoRectangleCoordinates R a 2 2).symm x)) := rfl

end BPFixedPoints.ProjectiveLine
