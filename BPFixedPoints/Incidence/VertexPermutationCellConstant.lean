import BPFixedPoints.Incidence.VertexProjectivePermutationCohomology
import BPFixedPoints.Incidence.SheafTerminalCohomology

/-!
# The constant-sheaf identification along a homeomorphism keeps the section `1`

For a homeomorphism `h : T ≅ T'`, the identification of constant sheaves
`topSheafEquivOfIsoConstant h : constantSheaf ⋙ (topSheafEquivOfIso h).functor ≅ constantSheaf`
is defined abstractly, by uniqueness of left adjoints of the global-section functors. Its sign is
computed here: it sends the global section given by the unit of the constant-sheaf adjunction at
`a` to the same section on `T'` (`topSheafEquivOfIsoConstant_unit`). In particular the constant
section `1` goes to `1`, not to `-1`.

Consequently, the comparison `freeSheafTopIso` between the free sheaf on the whole space and the
constant integer sheaf is compatible with the transport along `h`: if `topSheafEquivOfIsoFreeTop h`
denotes the map of free sheaves on the whole spaces sending the universal section to the universal
section, then `freeSheafTopIso.inv ≫ topSheafEquivOfIsoFreeTop h =
c.inv ≫ e.map freeSheafTopIso.inv` (`freeSheafTopIso_topSheafEquivOfIso`).
-/

namespace BPFixedPoints.Multigraph
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {T T' : TopCat.{0}} (h : T ≅ T')

/-- **The sign of the constant-sheaf identification.** The identification of constant sheaves along
a homeomorphism sends the global section given by the adjunction unit at `a` to the global section
given by the adjunction unit at `a`. -/
theorem topSheafEquivOfIsoConstant_unit (A : AddCommGrpCat.{0}) (a : A) :
    ((topSheafEquivOfIsoConstant h).hom.app A).hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
          (isTerminalTop (α := Opens T))).unit.app A).hom a) =
      ((constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
          (isTerminalTop (α := Opens T'))).unit.app A).hom a := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T))).comp (topSheafEquivOfIso h).toAdjunction).ofNatIsoRight
        (topSheafEquivOfIsoSections h))
    (constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T'))) A
  have k2 := congrArg (fun f => f.hom a) key
  refine Eq.trans ?_ k2
  have hu : ((((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T))).comp (topSheafEquivOfIso h).toAdjunction).ofNatIsoRight
        (topSheafEquivOfIsoSections h)).unit.app A).hom a =
      ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
          (isTerminalTop (α := Opens T))).unit.app A).hom a := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id,
      Adjunction.comp_unit_app]
    have hid : ∀ (F : TopCat.Sheaf AddCommGrpCat.{0} T) (x : F.obj.obj (op ⊤)),
        (((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat).obj (op ⊤)).map
          ((topSheafEquivOfIso h).toAdjunction.unit.app F)).hom x = x := by
      intro F x
      have hm : ∀ (m : op (⊤ : Opens T) ⟶ op ⊤), (F.obj.map m).hom x = x := fun m => by
        rw [Subsingleton.elim m (𝟙 _), F.obj.map_id]
        rfl
      exact hm _
    exact hid _ _
  change (((topSheafEquivOfIsoConstant h).hom.app A).hom.app (op ⊤)).hom _ = _
  rw [← hu]
  rfl

open SheafTools

/-- The universal global section of the constant integer sheaf is the unit of the constant-sheaf
adjunction at `1`. -/
theorem constantIntegerCorepresentsSections_id (S : TopCat.{0}) :
    (constantIntegerCorepresentsSections (T := S)).homEquiv (𝟙 _) =
      ((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
          (isTerminalTop (α := Opens S))).unit.app (AddCommGrpCat.of (ULift ℤ))).hom (ULift.up 1) := by
  rfl

/-- Sections of a composite out of a free sheaf are images of sections. -/
theorem freeSheafSectionsEquiv_comp {S : TopCat.{0}} {F G : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}}
    (U : Opens S) (k : (presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) (g : F ⟶ G) :
    freeSheafSectionsEquiv G U (k ≫ g) = g.hom.app (op U) (freeSheafSectionsEquiv F U k) := rfl

/-- The comparison of the free sheaves on the whole spaces: the universal section of the free
sheaf on `T'` goes to the universal section of the free sheaf on `T`. -/
noncomputable def topSheafEquivOfIsoFreeTop :
    (presheafToSheaf (Opens.grothendieckTopology T') AddCommGrpCat).obj
        (yoneda.obj (⊤ : Opens T') ⋙ AddCommGrpCat.free) ⟶
      (topSheafEquivOfIso h).functor.obj ((presheafToSheaf (Opens.grothendieckTopology T)
        AddCommGrpCat).obj (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free)) :=
  (freeSheafSectionsEquiv ((topSheafEquivOfIso h).functor.obj ((presheafToSheaf
    (Opens.grothendieckTopology T) AddCommGrpCat).obj (yoneda.obj (⊤ : Opens T) ⋙
      AddCommGrpCat.free))) ⊤).symm
    (freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _))

/-- **The sign of the constant-sheaf identification.** Under the identification of the constant
sheaves along a homeomorphism (from uniqueness of left adjoints), the comparison of the free sheaves
on the whole spaces corresponds to the canonical comparisons with the constant sheaves; the
identification sends the global section `1` to `1`. -/
theorem freeSheafTopIso_topSheafEquivOfIso :
    (freeSheafTopIso (T := T')).inv ≫ topSheafEquivOfIsoFreeTop h =
      ((topSheafEquivOfIsoConstant h).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (topSheafEquivOfIso h).functor.map (freeSheafTopIso (T := T)).inv := by
  have hhom : (freeSheafTopIso (T := T')).hom = topSheafEquivOfIsoFreeTop h ≫
      (topSheafEquivOfIso h).functor.map (freeSheafTopIso (T := T)).hom ≫
        ((topSheafEquivOfIsoConstant h).app (AddCommGrpCat.of (ULift ℤ))).hom := by
    apply (freeSheafSectionsEquiv _ (⊤ : Opens T')).injective
    have h1 := freeSheafTopIso_inv_sections (T := T')
      ((constantSheaf (Opens.grothendieckTopology T') AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ)))
      (freeSheafTopIso (T := T')).hom
    rw [Iso.inv_hom_id] at h1
    rw [← h1, constantIntegerCorepresentsSections_id]
    have hu : freeSheafSectionsEquiv _ ⊤ (topSheafEquivOfIsoFreeTop h) =
        freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _) := AddEquiv.apply_symm_apply _ _
    have h0 := freeSheafTopIso_inv_sections (T := T)
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ)))
      (freeSheafTopIso (T := T)).hom
    rw [Iso.inv_hom_id, constantIntegerCorepresentsSections_id] at h0
    have h2 : ((topSheafEquivOfIso h).functor.map (freeSheafTopIso (T := T)).hom).hom.app (op ⊤)
        (freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _)) =
          ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
            (isTerminalTop (α := Opens T))).unit.app (AddCommGrpCat.of (ULift ℤ))).hom (ULift.up 1) := by
      rw [h0, ← Category.id_comp (freeSheafTopIso (T := T)).hom, freeSheafSectionsEquiv_comp]
      rfl
    calc _ = ((topSheafEquivOfIsoConstant h).hom.app (AddCommGrpCat.of (ULift ℤ))).hom.app (op ⊤)
          (((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
            (isTerminalTop (α := Opens T))).unit.app (AddCommGrpCat.of (ULift ℤ))).hom (ULift.up 1)) :=
          (topSheafEquivOfIsoConstant_unit h _ _).symm
      _ = ((topSheafEquivOfIsoConstant h).hom.app (AddCommGrpCat.of (ULift ℤ))).hom.app (op ⊤)
          (((topSheafEquivOfIso h).functor.map (freeSheafTopIso (T := T)).hom).hom.app (op ⊤)
            (freeSheafSectionsEquiv _ ⊤ (topSheafEquivOfIsoFreeTop h))) := by
          rw [hu, h2]
      _ = _ := rfl
  rw [Iso.inv_comp_eq, hhom, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end BPFixedPoints.Multigraph
