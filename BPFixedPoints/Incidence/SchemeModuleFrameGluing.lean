import BPFixedPoints.Incidence.SchemeModuleHomGluing
import BPFixedPoints.Incidence.SchemeModuleFrameRestriction

/-! # Glue the same original rank-one frame comparisons

The local maps are the specified original frame followed by the inverse
specified target frame. Equal original transitions make these maps agree.
Both directions glue by the existing internal Hom sheaf.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (X : Scheme.{0})

/-- Two specified rank-one comparisons with the same original transition are the same original morphism. -/
theorem moduleFrameMap_eq_of_transition {U : X.Opens} {M N : X.Modules}
    (eM fM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN fN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (t : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hM : eM.hom = fM.hom ≫ t) (hN : eN.hom = fN.hom ≫ t) :
    eM.hom ≫ eN.inv = fM.hom ≫ fN.inv := by
  apply (cancel_mono eN.hom).mp
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,hN,Category.assoc,
    Iso.inv_hom_id_assoc,← hM]

/-- Restricting the original frame comparison preserves exactly the originally restricted frames. -/
theorem moduleFrameMap_section_restrict {U W : X.Opens} (i : W ⟶ U) (M N : X.Modules)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (moduleHomSheaf X M N).obj.map i.op (moduleOverHomSection X M N U (eM.hom ≫ eN.inv)) =
      moduleOverHomSection X M N W
        ((moduleOverFrameRestriction X i M eM).hom ≫ (moduleOverFrameRestriction X i N eN).inv) := by
  rw [moduleOverHomSection_restrict]
  congr 1

variable (M N : X.Modules) {ι : Type} (U : ι → X.Opens)

/-- The two compatible original local directions glue to the specified original global isomorphism. -/
noncomputable def moduleFrameGlueIso (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (hh : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X M N).obj U
      (fun i => moduleOverHomSection X M N (U i) (e i).hom))
    (hi : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X N M).obj U
      (fun i => moduleOverHomSection X N M (U i) (e i).inv)) : M ≅ N where
  hom := moduleHomGlue X M N U hcover (fun i => (e i).hom) hh
  inv := moduleHomGlue X N M U hcover (fun i => (e i).inv) hi
  hom_inv_id := by
    apply moduleHom_ext_of_cover X M M U hcover
    intro i
    rw [Functor.map_comp,moduleHomGlue_over,moduleHomGlue_over,CategoryTheory.Functor.map_id,Iso.hom_inv_id]
  inv_hom_id := by
    apply moduleHom_ext_of_cover X N N U hcover
    intro i
    rw [Functor.map_comp,moduleHomGlue_over,moduleHomGlue_over,CategoryTheory.Functor.map_id,Iso.inv_hom_id]

/-- The actual glued isomorphism retains the specified original local isomorphism itself. -/
theorem moduleFrameGlueIso_over (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (hh : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X M N).obj U
      (fun i => moduleOverHomSection X M N (U i) (e i).hom))
    (hi : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X N M).obj U
      (fun i => moduleOverHomSection X N M (U i) (e i).inv)) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso (moduleFrameGlueIso X M N U hcover e hh hi) = e i := by
  apply Iso.ext
  exact moduleHomGlue_over X M N U hcover (fun i => (e i).hom) hh i

end BPFixedPoints.SheafTools
