import BPFixedPoints.Incidence.OpenUnitChartSections
import BPFixedPoints.Incidence.SheafTwoOpenCechComparison

/-! # The canonical Cech differential in the original twist frames

The source terms are sections of the actual twisted sheaf on the two opens,
and its differential uses that sheaf's own restriction maps. The coordinates
retain the original chart projections and the original overlap unit.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u
variable (X : Scheme.{u}) (U V : X.Opens) (t : Γ((U ⊓ V).toScheme, ⊤)ˣ)

/-- Original left chart functions are coordinates for actual left-chart twist sections. -/
noncomputable def twoOpenTwistLeftSectionsIso :
    Γ(twoOpenTwistModule X U V t, U) ≅ Γ(openUnitModule X U, ⊤) := by
  have := twoOpenTwist_left_app_isIso X U V t U le_rfl
  exact asIso ((twoOpenTwistInclusion X U V t ≫ biprod.fst).app U) ≪≫
    (openUnitTopRestrictionIso X U).symm

/-- Original right chart functions are coordinates for actual right-chart twist sections. -/
noncomputable def twoOpenTwistRightSectionsIso :
    Γ(twoOpenTwistModule X U V t, V) ≅ Γ(openUnitModule X V, ⊤) := by
  have := twoOpenTwist_right_app_isIso X U V t V le_rfl
  exact asIso ((twoOpenTwistInclusion X U V t ≫ biprod.snd).app V) ≪≫
    (openUnitTopRestrictionIso X V).symm

/-- Original overlap functions in the left frame are coordinates for actual overlap sections. -/
noncomputable def twoOpenTwistOverlapLeftSectionsIso :
    Γ(twoOpenTwistModule X U V t, U ⊓ V) ≅ Γ(openUnitModule X (U ⊓ V), ⊤) := by
  have := twoOpenTwist_left_app_isIso X U V t (U ⊓ V) inf_le_left
  have := openUnitRestriction_isIso_app X
    (show U ⊓ V ≤ U from inf_le_left) (U ⊓ V) inf_le_left
  exact asIso ((twoOpenTwistInclusion X U V t ≫ biprod.fst).app (U ⊓ V)) ≪≫
    asIso ((openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left)).app (U ⊓ V)) ≪≫
    (openUnitTopRestrictionIso X (U ⊓ V)).symm

/-- Original overlap functions in the right frame are coordinates for actual overlap sections. -/
noncomputable def twoOpenTwistOverlapRightSectionsIso :
    Γ(twoOpenTwistModule X U V t, U ⊓ V) ≅ Γ(openUnitModule X (U ⊓ V), ⊤) := by
  have := twoOpenTwist_right_app_isIso X U V t (U ⊓ V) inf_le_right
  have := openUnitRestriction_isIso_app X
    (show U ⊓ V ≤ V from inf_le_right) (U ⊓ V) inf_le_left
  exact asIso ((twoOpenTwistInclusion X U V t ≫ biprod.snd).app (U ⊓ V)) ≪≫
    asIso ((openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right)).app (U ⊓ V)) ≪≫
    (openUnitTopRestrictionIso X (U ⊓ V)).symm

/-- Actual restriction from the left chart preserves the original geometric restriction. -/
@[reassoc] theorem twoOpenTwistLeftSectionsIso_restriction :
    (twoOpenTwistModule X U V t).presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op ≫
        (twoOpenTwistOverlapLeftSectionsIso X U V t).hom =
      (twoOpenTwistLeftSectionsIso X U V t).hom ≫
        (openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left)).app ⊤ := by
  simpa only [twoOpenTwistLeftSectionsIso, twoOpenTwistOverlapLeftSectionsIso,
    openUnitChartCoordinates, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Scheme.Modules.Hom.comp_app, Category.assoc] using
      openUnitChartCoordinates_restriction X (show U ⊓ V ≤ U from inf_le_left)
        (twoOpenTwistInclusion X U V t ≫ biprod.fst)

/-- Actual restriction from the right chart preserves the original geometric restriction. -/
@[reassoc] theorem twoOpenTwistRightSectionsIso_restriction :
    (twoOpenTwistModule X U V t).presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op ≫
        (twoOpenTwistOverlapRightSectionsIso X U V t).hom =
      (twoOpenTwistRightSectionsIso X U V t).hom ≫
        (openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right)).app ⊤ := by
  simpa only [twoOpenTwistRightSectionsIso, twoOpenTwistOverlapRightSectionsIso,
    openUnitChartCoordinates, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Scheme.Modules.Hom.comp_app, Category.assoc] using
      openUnitChartCoordinates_restriction X (show U ⊓ V ≤ V from inf_le_right)
        (twoOpenTwistInclusion X U V t ≫ biprod.snd)

/-- The actual overlap section frames have the original transition multiplication. -/
theorem twoOpenTwistSectionsIso_transition :
    (twoOpenTwistOverlapLeftSectionsIso X U V t).hom =
      (twoOpenTwistOverlapRightSectionsIso X U V t).hom ≫
        (overlapMultiplication X U V (t : Γ((U ⊓ V).toScheme, ⊤))).app ⊤ := by
  have hm := congrArg (fun φ => openUnitChartCoordinates X (U ⊓ V) φ)
    (twoOpenTwist_matching X U V t)
  dsimp only [overlapUnitModule] at hm
  simp only [← Category.assoc] at hm
  rw [openUnitChartCoordinates_postcomp] at hm
  simpa only [twoOpenTwistOverlapLeftSectionsIso, twoOpenTwistOverlapRightSectionsIso,
    openUnitChartCoordinates, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Scheme.Modules.Hom.comp_app, Category.assoc] using hm

/-- The actual abelian sheaf underlying the twisted structure module. -/
noncomputable def twoOpenTwistAbelianSheaf :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (twoOpenTwistModule X U V t)

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (X : Scheme.{0}) (U V : X.Opens) (t : Γ((U ⊓ V).toScheme, ⊤)ˣ)

/-- The genuine ordinary Cech differential becomes the original twisted chart-function differential. -/
theorem twoOpenTwistSectionsIso_difference
    (s : Γ(twoOpenTwistModule X U V t, U) × Γ(twoOpenTwistModule X U V t, V)) :
    (twoOpenTwistOverlapLeftSectionsIso X U V t).hom
        (twoOpenSectionDifference (twoOpenTwistAbelianSheaf X U V t) U V s) =
      twoOpenGlobalDifference X U V t
        ((twoOpenTwistLeftSectionsIso X U V t).hom s.1,
          (twoOpenTwistRightSectionsIso X U V t).hom s.2) := by
  have hl := ConcreteCategory.congr_hom (twoOpenTwistLeftSectionsIso_restriction X U V t) s.1
  have hr := ConcreteCategory.congr_hom (twoOpenTwistRightSectionsIso_restriction X U V t) s.2
  have ht := ConcreteCategory.congr_hom (twoOpenTwistSectionsIso_transition X U V t)
    ((twoOpenTwistModule X U V t).presheaf.map (homOfLE inf_le_right).op s.2)
  simp only [ConcreteCategory.comp_apply] at hl hr ht
  let a : Γ(U.toScheme, ⊤) := (twoOpenTwistLeftSectionsIso X U V t).hom s.1
  let b : Γ(V.toScheme, ⊤) := (twoOpenTwistRightSectionsIso X U V t).hom s.2
  have hl' : (twoOpenTwistOverlapLeftSectionsIso X U V t).hom
      ((twoOpenTwistModule X U V t).presheaf.map (homOfLE inf_le_left).op s.1) =
      (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).appTop a :=
    hl.trans (openUnitRestriction_global X _ a)
  have hr' : (twoOpenTwistOverlapRightSectionsIso X U V t).hom
      ((twoOpenTwistModule X U V t).presheaf.map (homOfLE inf_le_right).op s.2) =
      (X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop b :=
    hr.trans (openUnitRestriction_global X _ b)
  have ht' := ht.trans (congrArg
    (fun z : Γ((U ⊓ V).toScheme, ⊤) =>
      (overlapMultiplication X U V (t : Γ((U ⊓ V).toScheme, ⊤))).app ⊤ z) hr')
  have hm := overlapMultiplication_global X U V (t : Γ((U ⊓ V).toScheme, ⊤))
    ((X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop b)
  have hright := ht'.trans hm
  rw [twoOpenGlobalDifference_apply]
  change (twoOpenTwistOverlapLeftSectionsIso X U V t).hom
    ((twoOpenTwistModule X U V t).presheaf.map (homOfLE inf_le_left).op s.1 -
      (twoOpenTwistModule X U V t).presheaf.map (homOfLE inf_le_right).op s.2) = _
  rw [map_sub]
  exact congrArg₂ (fun x y : Γ((U ⊓ V).toScheme, ⊤) => x - y) hl' hright

end BPFixedPoints.SheafTools
