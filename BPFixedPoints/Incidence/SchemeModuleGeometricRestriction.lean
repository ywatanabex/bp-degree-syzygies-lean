import BPFixedPoints.Incidence.SchemeModuleLocalFrameRestriction

/-! # Native over-site and geometric restriction coherence

These adapters retain Mathlib's original restriction and comparison maps.
Explicit intermediate endpoints avoid expensive inference of dependent sites.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 4000000
variable (X : Scheme.{0})
/-- The native reindexing isomorphism with its original module endpoints. -/
noncomputable def moduleOverReindexIso {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    M.over W ≅ (SheafOfModules.overMap X.ringCatSheaf i).obj (M.over U) :=
  (SheafOfModules.overFunctorMap X.ringCatSheaf i).symm.app M
/-- The same original reindexing mapped to the actual open subscheme. -/
noncomputable def moduleOverReindexGeometricIso {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    (Scheme.Modules.overEquiv W).functor.obj (M.over W) ≅
      (Scheme.Modules.overEquiv W).functor.obj
        ((SheafOfModules.overMap X.ringCatSheaf i).obj (M.over U)) :=
  (Scheme.Modules.overEquiv W).functor.mapIso (moduleOverReindexIso X i M)
/-- The geometric reindexing retains the original section values. -/
theorem moduleOverReindexGeometricIso_apply {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (S : W.toScheme.Opens)
    (x : Γ((Scheme.Modules.overEquiv W).functor.obj (M.over W), S)) :
    (moduleOverReindexGeometricIso X i M).hom.app S x = x := rfl
/-- The native comparison between over-site restriction and geometric restriction. -/
noncomputable def moduleOverMapGeometricIso {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    (Scheme.Modules.overEquiv W).functor.obj
      ((SheafOfModules.overMap X.ringCatSheaf i).obj (M.over U)) ≅
    ((Scheme.Modules.overEquiv U).functor.obj (M.over U)).restrict
      (X.homOfLE (leOfHom i)) :=
  (Scheme.Modules.overMapCompOverEquiv i).app (M.over U)
/-- The original direct restriction compared with the composite open restriction. -/
noncomputable def moduleRestrictionCompIso {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    M.restrict W.ι ≅ (M.restrict U.ι).restrict (X.homOfLE (leOfHom i)) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (leOfHom i)).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).app M

/-- Restrict the native comparison with the actual open subscheme. -/
noncomputable def moduleRestrictionOverEquivIso {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    ((Scheme.Modules.overEquiv U).functor.obj (M.over U)).restrict
      (X.homOfLE (leOfHom i)) ≅
    (M.restrict U.ι).restrict (X.homOfLE (leOfHom i)) :=
  (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso
    ((Scheme.Modules.overFunctorEquiv U).app M)
/-- The native over-site restriction path on the original module. -/
noncomputable def moduleOverRestrictionPath {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    (Scheme.Modules.overEquiv W).functor.obj (M.over W) ≅
      (M.restrict U.ι).restrict (X.homOfLE (leOfHom i)) :=
  moduleOverReindexGeometricIso X i M ≪≫ moduleOverMapGeometricIso X i M ≪≫ moduleRestrictionOverEquivIso X i M

/-- The original images of the two open inclusions agree. -/
theorem moduleRestrictionImageEq {U W : X.Opens} (i : W ⟶ U) (S : W.toScheme.Opens) :
    U.ι ''ᵁ ((X.homOfLE (leOfHom i)) ''ᵁ S) = W.ι ''ᵁ S := by
  simp only [← Scheme.Hom.comp_image, X.homOfLE_ι]
/-- The restricted comparison retains the original section values. -/
theorem moduleRestrictionOverEquivIso_apply {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (S : W.toScheme.Opens)
    (x : Γ(((Scheme.Modules.overEquiv U).functor.obj (M.over U)).restrict
      (X.homOfLE (leOfHom i)), S)) :
    (moduleRestrictionOverEquivIso X i M).hom.app S x = x := rfl
/-- The native over-site comparison retains the original section values. -/
theorem moduleOverFunctorEquiv_apply (U : X.Opens) (M : X.Modules) (S : U.toScheme.Opens)
    (x : Γ((Scheme.Modules.overEquiv U).functor.obj (M.over U), S)) :
    ((Scheme.Modules.overFunctorEquiv U).hom.app M).app S x = x := rfl

/-- The native over-site diagram is the original geometric composite restriction. -/
theorem moduleOverRestrictionPath_eq {U W : X.Opens} (i : W ⟶ U) (M : X.Modules) :
    moduleOverRestrictionPath X i M =
    (Scheme.Modules.overFunctorEquiv W).app M ≪≫ moduleRestrictionCompIso X i M := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro S
  ext x
  simp only [moduleOverRestrictionPath, Iso.trans_hom, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.comp_apply]
  rw [moduleOverReindexGeometricIso_apply]
  erw [moduleRestrictionOverEquivIso_apply]
  simp only [Iso.app_hom]
  have hc : ((Scheme.Modules.overFunctorEquiv W).hom.app M).app S x = x := rfl
  calc
    (moduleOverMapGeometricIso X i M).hom.app S x =
        M.presheaf.map (eqToHom (moduleRestrictionImageEq X i S)).op x := by
      rfl
    _ = (moduleRestrictionCompIso X i M).hom.app S x := by
      simp only [moduleRestrictionCompIso, Iso.trans_hom, Iso.app_hom,
        Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
        Scheme.Modules.restrictFunctorComp_hom_app_app, AddCommGrpCat.comp_apply]
      rw [← AddCommGrpCat.comp_apply, ← M.presheaf.map_comp]
      congr 2
    _ = (moduleRestrictionCompIso X i M).hom.app S
        (((Scheme.Modules.overFunctorEquiv W).hom.app M).app S x) :=
      congrArg (fun q => (moduleRestrictionCompIso X i M).hom.app S q) hc.symm
end BPFixedPoints.SheafTools
