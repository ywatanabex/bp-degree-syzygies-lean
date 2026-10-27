import BPFixedPoints.Incidence.SchemeModuleGeometricRestriction

/-! # Original frame restrictions through the native geometric comparison -/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 4000000
variable (X : Scheme.{0})
/-- Compare the restricted over-site structure module to the actual open structure module. -/
noncomputable def moduleOverUnitRestrictionPath {U W : X.Opens} (i : W ⟶ U) :
    (Scheme.Modules.overEquiv W).functor.obj
      ((SheafOfModules.overMap X.ringCatSheaf i).obj
        (SheafOfModules.unit (X.ringCatSheaf.over U))) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  moduleOverMapGeometricIso X i (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))

/-- The canonical structure-module comparison commutes with the original open restriction. -/
theorem moduleOverUnitRestrictionPath_eq {U W : X.Opens} (i : W ⟶ U) :
    moduleOverUnitRestrictionPath X i =
      (Scheme.Modules.overEquiv W).functor.mapIso
        (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i) ≪≫
        W.sheafOfModulesEquivOverUnit X.ringCatSheaf := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro S
  ext x
  change ((X.homOfLE (leOfHom i)).appIso S).hom
    (X.presheaf.map (eqToHom (moduleRestrictionImageEq X i S)).op x) = x
  have hi : ((X.homOfLE (leOfHom i)).appIso S).inv x =
      X.presheaf.map (eqToHom (moduleRestrictionImageEq X i S)).op x := by
    rw [Scheme.Hom.appIso_homOfLE_inv]
    rfl
  exact (congrArg (fun q => ((X.homOfLE (leOfHom i)).appIso S).hom q) hi).symm.trans
    (ConcreteCategory.congr_hom ((X.homOfLE (leOfHom i)).appIso S).inv_hom_id x)
/-- Restrict the original geometric frame using the original composite-restriction isomorphism. -/
noncomputable def moduleGeometricFrameRestriction {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  moduleRestrictionCompIso X i M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))

/-- The original native over-site frame restriction is the original geometric frame restriction. -/
theorem moduleLocalFrameRestriction_eq_geometric {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction X i M e = moduleGeometricFrameRestriction X i M e := by
  let Q := Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))
  let F := (Scheme.Modules.overEquiv W).functor
  let G := (Scheme.Modules.overEquiv U).functor
  let P := SheafOfModules.overMap X.ringCatSheaf i
  let eO := moduleOverUnitIso X M U e
  have hu := congrArg Iso.hom (moduleOverUnitRestrictionPath_eq X i)
  change (moduleOverMapGeometricIso X i (SheafOfModules.unit X.ringCatSheaf)).hom ≫
    Q.map (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
      (Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))).hom =
    F.map (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i).hom ≫
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom at hu
  have hn := (Scheme.Modules.overMapCompOverEquiv i).hom.naturality eO.hom
  change F.map (P.map eO.hom) ≫
    (moduleOverMapGeometricIso X i (SheafOfModules.unit X.ringCatSheaf)).hom =
      (moduleOverMapGeometricIso X i M).hom ≫ Q.map (G.map eO.hom) at hn
  have he : G.map eO.hom = (Scheme.Modules.overFunctorEquiv U).hom.app M ≫ e.hom ≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv := by
    exact Functor.FullyFaithful.map_preimage (Scheme.Modules.overEquiv U).fullyFaithfulFunctor _
  have hc := congrArg Iso.hom (moduleOverRestrictionPath_eq X i M)
  change F.map (moduleOverReindexIso X i M).hom ≫ (moduleOverMapGeometricIso X i M).hom ≫
    Q.map ((Scheme.Modules.overFunctorEquiv U).hom.app M) =
      (Scheme.Modules.overFunctorEquiv W).hom.app M ≫ (moduleRestrictionCompIso X i M).hom at hc
  apply Iso.ext
  simp only [moduleLocalFrameRestriction, moduleLocalFrameOfOver, moduleOverFrameRestriction,
    moduleGeometricFrameRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change (Scheme.Modules.overFunctorEquiv W).inv.app M ≫
    F.map (moduleOverReindexIso X i M).hom ≫ F.map (P.map eO.hom) ≫
    F.map (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i).hom ≫
    (W.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
      (moduleRestrictionCompIso X i M).hom ≫ Q.map e.hom ≫
        (Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))).hom
  rw [← hu]
  have hnp := congrArg (fun k => k ≫
    Q.map (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
      (Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))).hom) hn
  simp only [Category.assoc] at hnp
  rw [hnp, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [Iso.inv_hom_id_map_assoc]
  have hcp := congrArg (fun k => k ≫ Q.map e.hom ≫
    (Scheme.Modules.restrictUnitIso (X.homOfLE (leOfHom i))).hom) hc
  simp only [Category.assoc] at hcp
  rw [hcp]
  simp only [Iso.inv_hom_id_app_assoc]

/-- The original finite tensor frames commute with the native geometric restriction. -/
theorem moduleTensorFamilyLocalUnitIso_geometric_restriction {U W : X.Opens}
    (i : W ⟶ U) (n : ℕ) (M : Fin n → X.Modules)
    (e : ∀ j, (M j).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleGeometricFrameRestriction X i (moduleTensorFamily X n M)
      (moduleTensorFamilyLocalUnitIso X U n M e) =
      moduleTensorFamilyLocalUnitIso X W n M
        (fun j => moduleGeometricFrameRestriction X i (M j) (e j)) := by
  simpa only [moduleLocalFrameRestriction_eq_geometric] using
    moduleTensorFamilyLocalUnitIso_restriction X i n M e

end BPFixedPoints.SheafTools
