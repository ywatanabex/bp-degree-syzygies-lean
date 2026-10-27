import BPFixedPoints.Incidence.StructureSheafCohomology
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Degree-zero local Ext cohomology is actual sheaf evaluation

The comparison uses the sheafification adjunction, the free abelian group
adjunction, and Yoneda. It applies to every open, not only the terminal open.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]
noncomputable local instance localCohomologyZeroHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (U : Opens T)

/-- The free abelian sheaf represented by an open represents sections on that open. -/
noncomputable def freeSheafSectionsEquiv :
    (((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)) ⟶ F) ≃+ F.obj.obj (op U) :=
  { toEquiv := ((sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F).trans
      (((AddCommGrpCat.adj.whiskerRight (Opens T)ᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans
        yonedaEquiv)
    map_add' := by intros; rfl }

/-- Actual degree-zero local cohomology identifies with sections, by the universal properties. -/
noncomputable def localSheafH0Equiv : F.H' 0 U ≃+ F.obj.obj (op U) :=
  AddEquiv.trans Ext.addEquiv₀ (freeSheafSectionsEquiv F U)

/-- The represented free-sheaf comparison is natural in the open. -/
theorem freeSheafSectionsEquiv_naturality {U W : Opens T} (f : U ⟶ W)
    (g : (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj W ⋙ AddCommGrpCat.free) ⟶ F) :
    freeSheafSectionsEquiv F U
      ((presheafToSheaf _ AddCommGrpCat).map
        (((Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free).map (yoneda.map f)) ≫ g) =
      F.obj.map f.op (freeSheafSectionsEquiv F W g) := by
  simp only [freeSheafSectionsEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  let a := (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat).homEquiv _ F g
  have he := (AddCommGrpCat.adj.whiskerRight (Opens T)ᵒᵖ).homEquiv_naturality_left (yoneda.map f) a
  exact (congrArg (fun y => yonedaEquiv y) he).trans (yonedaEquiv_naturality _ f).symm

/-- Degree-zero local Ext cohomology carries the actual sheaf restriction maps. -/
theorem localSheafH0Equiv_naturality {U W : Opens T} (f : U ⟶ W) (x : F.H' 0 W) :
    localSheafH0Equiv F U ((F.cohomologyPresheaf 0).map f.op x) =
      F.obj.map f.op (localSheafH0Equiv F W x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  let a := (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
    (((Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free).map (yoneda.map f))
  change freeSheafSectionsEquiv F U (Ext.addEquiv₀ ((Ext.mk₀ a).comp (Ext.mk₀ g) (zero_add 0))) =
    F.obj.map f.op (freeSheafSectionsEquiv F W (Ext.addEquiv₀ (Ext.mk₀ g)))
  rw [Ext.mk₀_comp_mk₀]
  have h₁ : Ext.addEquiv₀ (Ext.mk₀ (a ≫ g)) = a ≫ g := Ext.addEquiv₀.apply_symm_apply _
  have h₂ : Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply _
  calc
    _ = freeSheafSectionsEquiv F U (a ≫ g) := congrArg (freeSheafSectionsEquiv F U) h₁
    _ = F.obj.map f.op (freeSheafSectionsEquiv F W g) := freeSheafSectionsEquiv_naturality F f g
    _ = _ := congrArg (fun y => F.obj.map f.op (freeSheafSectionsEquiv F W y)) h₂.symm

end BPFixedPoints.SheafTools
