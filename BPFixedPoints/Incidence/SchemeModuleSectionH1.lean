import BPFixedPoints.Incidence.SchemeModuleRectangleLinear

/-! # Native section cokernels and actual local H1 over the geometric base -/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance sectionH1HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

/-- The original native section restriction difference with the independently defined geometric action. -/
noncomputable def schemeBaseSquareSectionDifference :
    (schemeBaseOpenSectionModule f M S.X₂ × schemeBaseOpenSectionModule f M S.X₃) →ₗ[R]
      schemeBaseOpenSectionModule f M S.X₁ :=
  (schemeBaseOpenRestrictionLinear f M S.f₁₂).comp (LinearMap.fst R _ _) -
    (schemeBaseOpenRestrictionLinear f M S.f₁₃).comp (LinearMap.snd R _ _)

/-- Every actual section connecting kernel is precisely the native section restriction image. -/
theorem schemeBaseSquareSectionDifference_range :
    LinearMap.range (schemeBaseSquareSectionDifference f M S) =
      LinearMap.ker (schemeBaseSectionConnectingLinear f M S) := by
  ext x
  change (∃ y, schemeBaseSquareSectionDifference f M S y = x) ↔
    SheafTools.mayerVietorisSectionConnecting S ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) x = 0
  rw [SheafTools.mayerVietorisSectionConnecting_eq_zero_iff]
  constructor
  · rintro ⟨⟨y,z⟩,he⟩
    exact ⟨y,z,he⟩
  · rintro ⟨y,z,he⟩
    exact ⟨(y,z),he⟩

variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 S.X₂)]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 S.X₃)]

/-- Native section representatives compute actual local H1 linearly for the original geometric actions. -/
noncomputable def schemeBaseSquareSectionH1LinearEquiv :
    (schemeBaseOpenSectionModule f M S.X₁ ⧸ LinearMap.range (schemeBaseSquareSectionDifference f M S)) ≃ₗ[R]
      schemeBaseLocalCohomologyObject f M S.X₄ 1 :=
  (Submodule.quotEquivOfEq _ _ (schemeBaseSquareSectionDifference_range f M S)).trans
    ((schemeBaseSectionConnectingLinear f M S).quotKerEquivOfSurjective
      (SheafTools.mayerVietorisSectionConnecting_surjective S
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)))

/-- Each representative maps to the original native section connecting class. -/
theorem schemeBaseSquareSectionH1LinearEquiv_mk (x : schemeBaseOpenSectionModule f M S.X₁) :
    schemeBaseSquareSectionH1LinearEquiv f M S (Submodule.Quotient.mk x) =
      SheafTools.mayerVietorisSectionConnecting S ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) x := rfl

end BPFixedPoints.SchemeTools
