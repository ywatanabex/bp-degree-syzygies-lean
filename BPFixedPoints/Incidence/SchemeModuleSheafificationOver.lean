import BPFixedPoints.Incidence.SchemeModuleTensor
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Native sheafification on opens where the original presheaf is a sheaf

Adjoint uniqueness preserves the original unit. Restriction to the native
over-site preserves its local bijectivity. Thus on a sheaf chart the actual
module sheafification returns the original restricted module presheaf.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The explicit native sheafification over the original structure-ring sheaf. -/
noncomputable def nativeModuleSheafification :
    PresheafOfModulesOfCommRing.{0} X.presheaf ⥤ X.Modules := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  exact PresheafOfModules.sheafification (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

/-- The explicit native adjunction for the original module forgetful functor. -/
noncomputable def nativeModuleSheafificationAdjunction :
    nativeModuleSheafification X ⊣ Scheme.Modules.toPresheafOfModules X := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  exact PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

/-- Native adjoint uniqueness compares the chosen and explicit sheafifications. -/
noncomputable def moduleSheafificationNativeIso :
    moduleSheafification X ≅ nativeModuleSheafification X :=
  (moduleSheafificationAdjunction X).leftAdjointUniq (nativeModuleSheafificationAdjunction X)

/-- The explicit native unit is the original abelian-presheaf sheafification map. -/
theorem nativeModuleSheafification_unit_presheaf (P : PresheafOfModulesOfCommRing.{0} X.presheaf) :
    (PresheafOfModules.toPresheaf _).map ((nativeModuleSheafificationAdjunction X).unit.app P) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := rfl

/-- Restriction of the original module presheaf to the native over-site. -/
noncomputable abbrev modulePresheafOverFunctor (U : X.Opens) :
    PresheafOfModulesOfCommRing.{0} X.presheaf ⥤
      PresheafOfModules.{0} (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U).obj)

/-- The original sheafification unit over an open on which the presheaf is already a sheaf. -/
noncomputable def nativeModuleSheafificationOverMap
    (P : PresheafOfModulesOfCommRing.{0} X.presheaf) (U : X.Opens)
    (hP : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((modulePresheafOverFunctor X U).obj P).presheaf) :
    (⟨(modulePresheafOverFunctor X U).obj P, hP⟩ :
      SheafOfModules.{0} (X.ringCatSheaf.over U)) ⟶
        ((nativeModuleSheafification X).obj P).over U where
  val := (modulePresheafOverFunctor X U).map ((nativeModuleSheafificationAdjunction X).unit.app P)

/-- Native local bijectivity makes this restricted original unit an actual isomorphism. -/
instance nativeModuleSheafificationOverMap_isIso
    (P : PresheafOfModulesOfCommRing.{0} X.presheaf) (U : X.Opens)
    (hP : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((modulePresheafOverFunctor X U).obj P).presheaf) :
    IsIso (nativeModuleSheafificationOverMap X P U hP) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  have hi := Presheaf.isLocallyInjective_whisker
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
    (Over.forget U) (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  have hs := Presheaf.isLocallySurjective_whisker
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
    (Over.forget U) (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  exact ⟨hi, hs⟩

/-- On such an open the actual sheafification is the original restricted presheaf. -/
noncomputable def moduleSheafificationOverIso
    (P : PresheafOfModulesOfCommRing.{0} X.presheaf) (U : X.Opens)
    (hP : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((modulePresheafOverFunctor X U).obj P).presheaf) :
    ((moduleSheafification X).obj P).over U ≅
      (⟨(modulePresheafOverFunctor X U).obj P, hP⟩ :
        SheafOfModules.{0} (X.ringCatSheaf.over U)) :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso ((moduleSheafificationNativeIso X).app P) ≪≫
    (asIso (nativeModuleSheafificationOverMap X P U hP)).symm

/-- The local comparison sends the original sheafification unit to the identity. -/
theorem moduleSheafificationOverIso_unit
    (P : PresheafOfModulesOfCommRing.{0} X.presheaf) (U : X.Opens)
    (hP : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((modulePresheafOverFunctor X U).obj P).presheaf) :
    (modulePresheafOverFunctor X U).map ((moduleSheafificationAdjunction X).unit.app P) ≫
      (moduleSheafificationOverIso X P U hP).hom.val = 𝟙 _ := by
  have h := (moduleSheafificationAdjunction X).unit_leftAdjointUniq_hom_app
    (nativeModuleSheafificationAdjunction X) P
  change (moduleSheafificationAdjunction X).unit.app P ≫
    (((moduleSheafificationNativeIso X).app P).hom.val) =
      (nativeModuleSheafificationAdjunction X).unit.app P at h
  change (modulePresheafOverFunctor X U).map ((moduleSheafificationAdjunction X).unit.app P) ≫
    (modulePresheafOverFunctor X U).map (((moduleSheafificationNativeIso X).app P).hom.val) ≫
      (inv (nativeModuleSheafificationOverMap X P U hP)).val = 𝟙 _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h]
  exact congrArg SheafOfModules.Hom.val (IsIso.hom_inv_id (nativeModuleSheafificationOverMap X P U hP))

end BPFixedPoints.SheafTools
