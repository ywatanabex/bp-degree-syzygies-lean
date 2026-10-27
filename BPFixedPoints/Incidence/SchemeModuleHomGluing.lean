import BPFixedPoints.Incidence.SchemeModuleHomSheaf

/-! # Glue the specified original module morphisms on an actual open cover

The existing internal Hom sheaf and Mathlib's actual sheaf gluing are used.
The global morphism retains every specified original over-site morphism.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (X : Scheme.{0}) (M N : X.Modules) {ι : Type} (U : ι → X.Opens)

/-- Original module morphisms which agree on an actual cover are equal globally. -/
theorem moduleHom_ext_of_cover (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i) (f g : M ⟶ N)
    (h : ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g) : f = g := by
  apply (moduleHomTopEquiv X M N).injective
  apply TopCat.Sheaf.eq_of_locally_eq' (X := TopCat.of X) (moduleHomSheaf X M N) U ⊤
    (fun _ => homOfLE le_top) hcover
  intro i
  change (moduleHomSheaf X M N).obj.map _ (moduleHomTopSection X M N f) =
    (moduleHomSheaf X M N).obj.map _ (moduleHomTopSection X M N g)
  rw [moduleHomTopSection_restrict,moduleHomTopSection_restrict,h i]

/-- Actual local original module morphisms glue to a unique original global module morphism. -/
theorem moduleHom_gluing (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hf : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X M N).obj U
      (fun i => moduleOverHomSection X M N (U i) (f i))) :
    ∃! g : M ⟶ N, ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g = f i := by
  obtain ⟨s,hs,_⟩ := TopCat.Sheaf.existsUnique_gluing' (X := TopCat.of X) (moduleHomSheaf X M N) U ⊤
    (fun _ => homOfLE le_top) hcover (fun i => moduleOverHomSection X M N (U i) (f i)) hf
  refine ⟨(moduleHomTopEquiv X M N).symm s,?_,?_⟩
  · intro i
    apply (moduleOverHomEquiv X M N (U i)).injective
    change moduleOverHomSection X M N (U i)
      ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map ((moduleHomTopEquiv X M N).symm s)) =
        moduleOverHomSection X M N (U i) (f i)
    rw [← moduleHomTopSection_restrict]
    change (moduleHomSheaf X M N).obj.map _
      (moduleHomTopEquiv X M N ((moduleHomTopEquiv X M N).symm s)) = _
    rw [Equiv.apply_symm_apply]
    exact hs i
  · intro g hg
    apply moduleHom_ext_of_cover X M N U hcover g _
    intro i
    apply (moduleOverHomEquiv X M N (U i)).injective
    change moduleOverHomSection X M N (U i)
      ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g) =
        moduleOverHomSection X M N (U i)
          ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).map ((moduleHomTopEquiv X M N).symm s))
    rw [hg i,← hs i]
    rw [← moduleHomTopSection_restrict]
    change _ = (moduleHomSheaf X M N).obj.map _
      (moduleHomTopEquiv X M N ((moduleHomTopEquiv X M N).symm s))
    rw [Equiv.apply_symm_apply]

/-- The unique actual gluing of the specified original local module morphisms. -/
noncomputable def moduleHomGlue (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hf : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X M N).obj U
      (fun i => moduleOverHomSection X M N (U i) (f i))) : M ⟶ N :=
  Classical.choose (moduleHom_gluing X M N U hcover f hf)

/-- The actual global gluing restricts to the original specified local morphism itself. -/
theorem moduleHomGlue_over (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hf : TopCat.Presheaf.IsCompatible (X := TopCat.of X) (moduleHomSheaf X M N).obj U
      (fun i => moduleOverHomSection X M N (U i) (f i))) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (moduleHomGlue X M N U hcover f hf) = f i :=
  (Classical.choose_spec (moduleHom_gluing X M N U hcover f hf)).1 i

end BPFixedPoints.SheafTools
