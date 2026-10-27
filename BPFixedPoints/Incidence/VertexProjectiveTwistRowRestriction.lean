import BPFixedPoints.Incidence.VertexProjectiveTwistRowH1

/-! # Original first-direction restrictions on actual row H1 -/

namespace BPFixedPoints.CechProduct
variable (R : Type) [CommRing R]

/-- Refine only the original first coordinate and retain the original second face. -/
theorem twoColumnFaceRefines {b c : Fin 3} (h : b = c ∨ c = 2) (i : Fin 3) :
    FaceRefines (![b,i] : Fin 2 → Fin 3) ![c,i] := by
  intro v
  fin_cases v
  · exact h
  · exact Or.inl rfl

/-- The original first-direction coefficient restriction on a specified second face. -/
noncomputable def twoRowRestriction (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2) (i : Fin 3) :
    FaceRing R (![b,i] : Fin 2 → Fin 3) →ₗ[R] FaceRing R (![c,i] : Fin 2 → Fin 3) :=
  multiTwistFaceRestriction R (twoColumnFaceRefines h i) a

/-- Native first-direction coefficient restrictions commute with both original row boundary terms. -/
theorem twoRowRestriction_boundary (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :
    twoRowRestriction R a h 2 (twoRowBoundary R a b x) =
      twoRowBoundary R a c (twoRowRestriction R a h 0 x.1,twoRowRestriction R a h 1 x.2) := by
  change multiTwistFaceRestriction R _ a (_ - _) = _ - _
  rw [map_sub]
  simp only [twoRowRestriction,LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,
    ProjectiveLine.multiTwistFaceRestriction_comp]

/-- The original first-direction restriction descends to the original row coefficient quotients. -/
noncomputable def twoRowQuotientRestriction (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    (FaceRing R (![b,2] : Fin 2 → Fin 3) ⧸ LinearMap.range (twoRowBoundary R a b)) →ₗ[R]
      (FaceRing R (![c,2] : Fin 2 → Fin 3) ⧸ LinearMap.range (twoRowBoundary R a c)) :=
  Submodule.mapQ _ _ (twoRowRestriction R a h 2) (by
    rintro x ⟨y,rfl⟩
    exact ⟨_,(twoRowRestriction_boundary R a h y).symm⟩)

/-- Every coefficient quotient representative keeps its original first-direction restriction. -/
theorem twoRowQuotientRestriction_mk (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    twoRowQuotientRestriction R a h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (twoRowRestriction R a h 2 x) := rfl

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]
noncomputable local instance vertexRowRestrictionHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The first-coordinate face refinement is the original inclusion of row opens. -/
theorem vertexTwoRowOpen_le {b c : Fin 3} (h : b = c ∨ c = 2) :
    SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) c ≤
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b := by
  rcases h with rfl | rfl
  · exact le_rfl
  · fin_cases b <;> simp [SheafTools.binaryCoverFaceFactor]

/-- The actual original row H1 restriction with its independently defined geometric action. -/
noncomputable def vertexTwistRowH1Restriction (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    vertexTwistRowH1Module R a b →ₗ[R] vertexTwistRowH1Module R a c :=
  SchemeTools.schemeBaseLocalRestrictionLinear (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
    (homOfLE (vertexTwoRowOpen_le R h)) 1

/-- Original row-overlap coordinates retain every actual first-direction restriction. -/
theorem vertexTwistRowOverlapCoordinates_restrict (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (s : vertexTwistTwoRectangleSections R a b 2) :
    vertexTwistTwoRectangleCoordinates R a c 2
      ((vertexTwistSheaf R (Fin 2) a).presheaf.map
        (homOfLE (inf_le_inf_right
          (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 2)
          (vertexTwoRowOpen_le R h))).op s) =
      twoRowRestriction R a h 2 (vertexTwistTwoRectangleCoordinates R a b 2 s) :=
  vertexTwistFaceSectionsAt_restrict R (Fin 2) a (twoColumnFaceRefines h 2) _ _
    (vertexTwoFaceOpen_eq R b 2).symm (vertexTwoFaceOpen_eq R c 2).symm _ s

variable [IsNoetherianRing R]

/-- The specified actual row H1 comparison commutes with every original first-direction restriction. -/
theorem vertexTwistRowCoefficientH1LinearEquiv_restrict (a : Fin 2 → ℤ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3) ⧸ LinearMap.range (twoRowBoundary R a b)) :
    vertexTwistRowCoefficientH1LinearEquiv R a c (twoRowQuotientRestriction R a h x) =
      vertexTwistRowH1Restriction R a h (vertexTwistRowCoefficientH1LinearEquiv R a b x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    rw [twoRowQuotientRestriction_mk,vertexTwistRowCoefficientH1LinearEquiv_mk,
      vertexTwistRowCoefficientH1LinearEquiv_mk]
    have he := vertexTwistRowOverlapCoordinates_restrict R a h
      ((vertexTwistTwoRectangleCoordinates R a b 2).symm z)
    rw [LinearEquiv.apply_symm_apply] at he
    have hs := (vertexTwistTwoRectangleCoordinates R a c 2).symm_apply_apply
      ((vertexTwistSheaf R (Fin 2) a).presheaf.map (homOfLE (inf_le_inf_right
        (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) 2)
        (vertexTwoRowOpen_le R h))).op ((vertexTwistTwoRectangleCoordinates R a b 2).symm z))
    rw [he] at hs
    rw [hs]
    exact SheafTools.rectangleRowConnecting_naturality (vertexTwistAbelianSheaf R (Fin 2) a)
      _ _ (vertexCoordinateOpen_cover R (Fin 2) 1) (vertexTwoRowOpen_le R h) _

end BPFixedPoints.ProjectiveLine
