import BPFixedPoints.Incidence.SchemeModuleFrameRestriction

/-! # Original geometric frame restrictions and their section coefficients

All comparisons use the original scheme modules and Mathlib functors.
The coefficient face atlas and derived-cohomology comparisons are separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (X : Scheme.{0})

/-- The native equivalence returns the specified original over-site frame to the actual open subscheme. -/
noncomputable def moduleLocalFrameOfOver (U : X.Opens) (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overFunctorEquiv U).symm.app M ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫ U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- The native local-frame comparison returns the original geometric frame. -/
theorem moduleLocalFrameOfOver_moduleOverUnitIso (U : X.Opens) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameOfOver X U M (moduleOverUnitIso X M U e) = e := by
  apply Iso.ext
  simp only [moduleLocalFrameOfOver, moduleOverUnitIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  change e.hom ≫ 𝟙 _ ≫ 𝟙 _ = e.hom
  simp only [Category.comp_id]

/-- The reverse comparison returns the original over-site frame. -/
theorem moduleOverUnitIso_moduleLocalFrameOfOver (U : X.Opens) (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    moduleOverUnitIso X M U (moduleLocalFrameOfOver X U M e) = e := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [moduleLocalFrameOfOver, moduleOverUnitIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  change (Scheme.Modules.overEquiv U).functor.map e.hom ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]

/-- Restrict the specified original geometric frame by the native over-site restriction and equivalence. -/
noncomputable def moduleLocalFrameRestriction {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  moduleLocalFrameOfOver X W M (moduleOverFrameRestriction X i M (moduleOverUnitIso X M U e))

/-- Its coefficients retain the original module-section values on every original subopen. -/
theorem moduleLocalFrameRestriction_coefficients {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (S : Over W)
    (x : Γ(M, S.left)) :
    (show Γ(X, S.left) from
      ((moduleOverUnitIso X M W (moduleLocalFrameRestriction X i M e)).hom.val.app (op S)).hom x) =
      (show Γ(X, S.left) from
        ((moduleOverUnitIso X M U e).hom.val.app (op ((Over.map i).obj S))).hom x) := by
  rw [moduleLocalFrameRestriction, moduleOverUnitIso_moduleLocalFrameOfOver]
  exact moduleOverFrameRestriction_apply X i M _ S x

/-- Geometric finite tensor frames commute with the specified native local-frame restriction. -/
theorem moduleTensorFamilyLocalUnitIso_restriction {U W : X.Opens} (i : W ⟶ U) (n : ℕ)
    (M : Fin n → X.Modules)
    (e : ∀ j, (M j).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction X i (moduleTensorFamily X n M) (moduleTensorFamilyLocalUnitIso X U n M e) =
      moduleTensorFamilyLocalUnitIso X W n M (fun j => moduleLocalFrameRestriction X i (M j) (e j)) := by
  change moduleLocalFrameOfOver X W (moduleTensorFamily X n M)
    (moduleOverFrameRestriction X i (moduleTensorFamily X n M)
      (moduleOverUnitIso X _ U (moduleLocalFrameOfOver X U _
        (moduleTensorFamilyOverUnitIso X U n M (fun j => moduleOverUnitIso X (M j) U (e j)))))) =
    moduleLocalFrameOfOver X W (moduleTensorFamily X n M)
      (moduleTensorFamilyOverUnitIso X W n M
        (fun j => moduleOverUnitIso X (M j) W (moduleLocalFrameOfOver X W (M j)
          (moduleOverFrameRestriction X i (M j) (moduleOverUnitIso X (M j) U (e j))))))
  rw [moduleOverUnitIso_moduleLocalFrameOfOver, moduleTensorFamilyOverUnitIso_restriction]
  congr 1
  congr 1
  funext j
  exact (moduleOverUnitIso_moduleLocalFrameOfOver X W (M j) _).symm



/-- Restricting along the identity returns the original geometric frame. -/
theorem moduleLocalFrameRestriction_id (U : X.Opens) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction X (𝟙 U) M e = e := by
  rw [moduleLocalFrameRestriction, moduleOverFrameRestriction_id, moduleLocalFrameOfOver_moduleOverUnitIso]

/-- The specified geometric frame restrictions preserve composition of the original inclusions. -/
theorem moduleLocalFrameRestriction_comp {U W K : X.Opens} (i : W ⟶ U) (j : K ⟶ W)
    (M : X.Modules) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction X j M (moduleLocalFrameRestriction X i M e) =
      moduleLocalFrameRestriction X (j ≫ i) M e := by
  dsimp only [moduleLocalFrameRestriction]
  rw [moduleOverUnitIso_moduleLocalFrameOfOver, moduleOverFrameRestriction_comp]

/-- The original frame coefficients commute with the original module and structure-ring presheaf restrictions. -/
theorem moduleLocalFrame_naturality (U : X.Opens) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    {S T : Over U} (i : S ⟶ T) (x : Γ(M, T.left)) :
    (show Γ(X, S.left) from ((moduleOverUnitIso X M U e).hom.val.app (op S)).hom
      (M.presheaf.map i.left.op x)) =
        X.presheaf.map i.left.op
          (show Γ(X, T.left) from ((moduleOverUnitIso X M U e).hom.val.app (op T)).hom x) := by
  have h := congrArg (fun k => k.hom x) ((moduleOverUnitIso X M U e).hom.val.naturality i.op)
  exact h

end BPFixedPoints.SheafTools
