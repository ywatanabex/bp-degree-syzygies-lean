import BPFixedPoints.Incidence.TwoOpenTwistLocal
import BPFixedPoints.Incidence.TwoOpenTwistGlobalMatching

/-! # Canonical chart sections of pushed-forward structure modules

Restriction from the ambient top open to the original chart is invertible
for its pushed-forward structure module. Its inverse provides coordinates
in the original chart functions, compatible with actual sheaf restrictions.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

/-- Canonical restriction to the chart is invertible for its open structure module. -/
theorem openUnitTopRestriction_isIso (U : X.Opens) :
    IsIso ((openUnitModule X U).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  have : IsIso (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)) := by
    rw [U.ι_preimage_self]
    change IsIso (𝟙 _)
    infer_instance
  change IsIso ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
    ((forget₂ CommRingCat.{u} RingCat.{u}).map
      (U.toScheme.presheaf.map (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op)))
  infer_instance

/-- Original chart functions identify with actual sections of its pushed-forward module on the chart. -/
noncomputable def openUnitTopRestrictionIso (U : X.Opens) :
    Γ(openUnitModule X U, ⊤) ≅ Γ(openUnitModule X U, U) := by
  have := openUnitTopRestriction_isIso X U
  exact asIso ((openUnitModule X U).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op)

/-- A morphism into an open structure module gives its original chart-function coordinates. -/
noncomputable def openUnitChartCoordinates {M : X.Modules} (U : X.Opens)
    (φ : M ⟶ openUnitModule X U) :
    Γ(M, U) ⟶ Γ(openUnitModule X U, ⊤) :=
  φ.app U ≫ (openUnitTopRestrictionIso X U).inv

/-- The chart coordinates of a global section retain the original morphism on global sections. -/
@[reassoc] theorem openUnitChartCoordinates_global {M : X.Modules} (U : X.Opens)
    (φ : M ⟶ openUnitModule X U) :
    M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
        openUnitChartCoordinates X U φ = φ.app ⊤ := by
  have hn : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ φ.app U =
      φ.app ⊤ ≫ (openUnitTopRestrictionIso X U).hom :=
    φ.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  rw [openUnitChartCoordinates, ← Category.assoc, hn, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Canonical top restrictions commute with the original restriction of open structure modules. -/
@[reassoc] theorem openUnitTopRestriction_naturality {U V : X.Opens} (h : U ≤ V) :
    (openUnitModule X V).presheaf.map (homOfLE h).op ≫
        (openUnitRestriction X h).app U ≫ (openUnitTopRestrictionIso X U).inv =
      (openUnitTopRestrictionIso X V).inv ≫ (openUnitRestriction X h).app ⊤ := by
  apply (cancel_mono (openUnitTopRestrictionIso X U).hom).mp
  apply (cancel_epi (openUnitTopRestrictionIso X V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change (openUnitModule X V).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
      (openUnitModule X V).presheaf.map (homOfLE h).op ≫
      (openUnitRestriction X h).app U =
    (openUnitRestriction X h).app ⊤ ≫
      (openUnitModule X U).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  exact (openUnitRestriction X h).mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op

/-- Original chart-function coordinates commute with restriction to a smaller chart. -/
@[reassoc] theorem openUnitChartCoordinates_restriction {M : X.Modules}
    {U V : X.Opens} (h : U ≤ V) (φ : M ⟶ openUnitModule X V) :
    M.presheaf.map (homOfLE h).op ≫
        openUnitChartCoordinates X U (φ ≫ openUnitRestriction X h) =
      openUnitChartCoordinates X V φ ≫ (openUnitRestriction X h).app ⊤ := by
  have hn : M.presheaf.map (homOfLE h).op ≫ φ.app U =
      φ.app V ≫ (openUnitModule X V).presheaf.map (homOfLE h).op :=
    φ.mapPresheaf.naturality (homOfLE h).op
  simp only [openUnitChartCoordinates, Scheme.Modules.Hom.comp_app, ← Category.assoc]
  rw [hn]
  simp only [Category.assoc, openUnitTopRestriction_naturality]

/-- Endomorphisms of the actual open structure module preserve its original chart coordinates. -/
@[reassoc] theorem openUnitChartCoordinates_postcomp {M : X.Modules} (U : X.Opens)
    (φ : M ⟶ openUnitModule X U) (ψ : openUnitModule X U ⟶ openUnitModule X U) :
    openUnitChartCoordinates X U (φ ≫ ψ) =
      openUnitChartCoordinates X U φ ≫ ψ.app ⊤ := by
  have hn : ψ.app U ≫ (openUnitTopRestrictionIso X U).inv =
      (openUnitTopRestrictionIso X U).inv ≫ ψ.app ⊤ := by
    apply (Iso.eq_inv_comp (openUnitTopRestrictionIso X U)).2
    exact openUnitChartCoordinates_global X U ψ
  simp only [openUnitChartCoordinates, Scheme.Modules.Hom.comp_app, Category.assoc]
  rw [hn]

end BPFixedPoints.SheafTools
