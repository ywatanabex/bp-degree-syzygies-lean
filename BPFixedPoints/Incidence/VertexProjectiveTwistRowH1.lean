import BPFixedPoints.Incidence.SchemeModuleSectionH1
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoRectangleCoordinates

/-! # Actual row H1 in the original two-coordinate face coefficients -/

namespace BPFixedPoints.CechProduct
variable (R : Type) [CommRing R]

/-- The original two-coordinate row faces refine by changing only the second coordinate to overlap. -/
theorem twoRowFaceRefines (b c : Fin 3) :
    FaceRefines (![b,c] : Fin 2 → Fin 3) ![b,2] := by
  intro v
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The original row boundary retains the original left-minus-right restriction convention. -/
noncomputable def twoRowBoundary (a : Fin 2 → ℤ) (b : Fin 3) :
    (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) →ₗ[R]
      FaceRing R (![b,2] : Fin 2 → Fin 3) :=
  (multiTwistFaceRestriction R (twoRowFaceRefines b 0) a).comp (LinearMap.fst R _ _) -
    (multiTwistFaceRestriction R (twoRowFaceRefines b 1) a).comp (LinearMap.snd R _ _)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000
variable (R : Type) [CommRing R]
noncomputable local instance vertexRowH1HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original second-direction cover on a specified first-direction face. -/
noncomputable def vertexTwoRowSquare (b : Fin 3) :
    (Opens.grothendieckTopology (vertexScheme R (Fin 2))).MayerVietorisSquare :=
  SheafTools.rectangleRowSquare (vertexCoordinateOpen R (Fin 2) 1 0)
    (vertexCoordinateOpen R (Fin 2) 1 1) (vertexCoordinateOpen_cover R (Fin 2) 1)
    (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b)

/-- The original geometric action on actual row H1, packaged without transporting scalars. -/
noncomputable def vertexTwistRowH1Module (a : Fin 2 → ℤ) (b : Fin 3) : ModuleCat.{1} R :=
  SchemeTools.schemeBaseLocalCohomologyObject (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
    (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b) 1

/-- Both actual row corner coordinates retain their original canonical frames. -/
noncomputable def vertexTwistRowCornerCoordinates (a : Fin 2 → ℤ) (b : Fin 3) :
    (vertexTwistTwoRectangleSections R a b 0 × vertexTwistTwoRectangleSections R a b 1) ≃ₗ[R]
      (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :=
  (vertexTwistTwoRectangleCoordinates R a b 0).prodCongr (vertexTwistTwoRectangleCoordinates R a b 1)

/-- Original row coordinates identify every native corner restriction with its existing coefficient map. -/
theorem vertexTwistRowCoordinates_restrict (a : Fin 2 → ℤ) (b c : Fin 3)
    (s : vertexTwistTwoRectangleSections R a b c) :
    vertexTwistTwoRectangleCoordinates R a b 2
      (SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
        (homOfLE (show
          (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
            SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 2) ≤
          (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
            SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c) from by
              rw [← vertexTwoFaceOpen_eq,← vertexTwoFaceOpen_eq]
              exact vertexBinaryFaceOpen_refinement R (Fin 2) (twoRowFaceRefines b c))) s) =
      multiTwistFaceRestriction R (twoRowFaceRefines b c) a (vertexTwistTwoRectangleCoordinates R a b c s) :=
  vertexTwistFaceSectionsAt_restrict R (Fin 2) a (twoRowFaceRefines b c) _ _
    (vertexTwoFaceOpen_eq R b c).symm (vertexTwoFaceOpen_eq R b 2).symm _ s

/-- The native row section boundary has exactly the original two coefficient restrictions. -/
theorem vertexTwistRowCoordinates_boundary (a : Fin 2 → ℤ) (b : Fin 3)
    (x : vertexTwistTwoRectangleSections R a b 0 × vertexTwistTwoRectangleSections R a b 1) :
    vertexTwistTwoRectangleCoordinates R a b 2
      (SchemeTools.schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b) x) =
      twoRowBoundary R a b (vertexTwistRowCornerCoordinates R a b x) := by
  change vertexTwistTwoRectangleCoordinates R a b 2 (_ - _) = _
  rw [map_sub]
  exact congrArg₂ (fun s t => s-t)
    (vertexTwistRowCoordinates_restrict R a b 0 x.1) (vertexTwistRowCoordinates_restrict R a b 1 x.2)

/-- Original row coordinates take precisely the actual native boundary image to the original coefficient image. -/
theorem vertexTwistRowCoordinates_range (a : Fin 2 → ℤ) (b : Fin 3) :
    (LinearMap.range (SchemeTools.schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b))).map
        (vertexTwistTwoRectangleCoordinates R a b 2).toLinearMap = LinearMap.range (twoRowBoundary R a b) := by
  ext z
  constructor
  · rintro ⟨y,⟨x,rfl⟩,rfl⟩
    exact ⟨vertexTwistRowCornerCoordinates R a b x,(vertexTwistRowCoordinates_boundary R a b x).symm⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨s,rfl⟩ := (vertexTwistRowCornerCoordinates R a b).surjective x
    exact ⟨_,⟨s,rfl⟩,vertexTwistRowCoordinates_boundary R a b s⟩

variable [IsNoetherianRing R]

/-- The original coefficient row quotient computes actual row H1 using the original connecting map. -/
noncomputable def vertexTwistRowCoefficientH1LinearEquiv (a : Fin 2 → ℤ) (b : Fin 3) :
    (FaceRing R (![b,2] : Fin 2 → Fin 3) ⧸ LinearMap.range (twoRowBoundary R a b)) ≃ₗ[R]
      vertexTwistRowH1Module R a b := by
  let : Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) a)).H' 1 (vertexTwoRowSquare R b).X₂) :=
      vertexTwistTwoFace_subsingleton R a b 0 0
  let : Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) a)).H' 1 (vertexTwoRowSquare R b).X₃) :=
      vertexTwistTwoFace_subsingleton R a b 1 0
  exact (Submodule.Quotient.equiv _ _ (vertexTwistTwoRectangleCoordinates R a b 2)
    (vertexTwistRowCoordinates_range R a b)).symm.trans
      (SchemeTools.schemeBaseSquareSectionH1LinearEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b))

/-- Every coefficient representative retains the original frame and the original row connecting class. -/
theorem vertexTwistRowCoefficientH1LinearEquiv_mk (a : Fin 2 → ℤ) (b : Fin 3)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    vertexTwistRowCoefficientH1LinearEquiv R a b (Submodule.Quotient.mk x) =
      SheafTools.rectangleRowConnecting (vertexTwistAbelianSheaf R (Fin 2) a)
        (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
        (vertexCoordinateOpen_cover R (Fin 2) 1)
        (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b)
        ((vertexTwistTwoRectangleCoordinates R a b 2).symm x) := rfl

end BPFixedPoints.ProjectiveLine
