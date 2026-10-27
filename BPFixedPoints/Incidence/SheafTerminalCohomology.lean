import BPFixedPoints.Incidence.SheafLocalCohomologyZero

/-! # Local Ext at the terminal open is genuine global cohomology

The represented free abelian sheaf on the whole space and the constant integer
sheaf corepresent the same section functor. Their canonical isomorphism gives
the comparison in every degree, independently of any acyclicity hypothesis.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]
noncomputable local instance terminalCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The ordinary underlying set of sections on an open. -/
noncomputable def sectionSetFunctor (U : Opens T) :
    Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} ⥤ Type :=
  (sheafSections _ AddCommGrpCat).obj (op U) ⋙ forget AddCommGrpCat

/-- The free represented abelian sheaf corepresents actual sections. -/
noncomputable def freeSheafCorepresentsSections (U : Opens T) :
    (sectionSetFunctor U).CorepresentableBy
      ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) where
  homEquiv := (freeSheafSectionsEquiv _ U).toEquiv
  homEquiv_comp g f := by
    rfl

/-- The constant integer sheaf corepresents genuine global sections. -/
noncomputable def constantIntegerCorepresentsSections :
    (sectionSetFunctor (⊤ : Opens T)).CorepresentableBy
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ))) :=
  ((constantSheafAdj _ AddCommGrpCat (isTerminalTop (α := Opens T))).corepresentableBy
    (AddCommGrpCat.of (ULift ℤ))).ofIso
      (Functor.isoWhiskerLeft _ AddCommGrpCat.coyonedaObjIsoForget)

/-- Canonical comparison of the two independent sheaves defining local and
global cohomology at the terminal open. -/
noncomputable def freeSheafTopIso :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ≅
      (constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (freeSheafCorepresentsSections (⊤ : Opens T)).uniqueUpToIso
    constantIntegerCorepresentsSections

/-- In every degree, local Ext on the whole space is actual global sheaf
cohomology, defined independently from the constant integer sheaf. -/
noncomputable def localSheafTopEquiv
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :
    F.H' n ⊤ ≃+ F.H n :=
  (((extFunctor n).mapIso (freeSheafTopIso (T := T)).symm.op).app F).addCommGroupIsoToAddEquiv

/-- Existence form of the unconditional comparison in every degree. -/
theorem localSheafTop_comparison
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :
    Nonempty (F.H' n ⊤ ≃+ F.H n) :=
  ⟨localSheafTopEquiv F n⟩

/-- The comparison is natural in the actual sheaf, in every degree. -/
theorem localSheafTopEquiv_naturality
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (f : F ⟶ G) (n : ℕ) (x : F.H' n ⊤) :
    localSheafTopEquiv G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      Sheaf.H.map f n (localSheafTopEquiv F n x) := by
  exact ConcreteCategory.congr_hom
    (((extFunctor n).map (freeSheafTopIso (T := T)).inv.op).naturality f) x

/-- The canonical inverse identifies the two universal section evaluations. -/
theorem freeSheafTopIso_inv_sections
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (g : (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶ F) :
    constantIntegerCorepresentsSections.homEquiv ((freeSheafTopIso (T := T)).inv ≫ g) =
      freeSheafSectionsEquiv F ⊤ g := by
  change constantIntegerCorepresentsSections.homEquiv
    (constantIntegerCorepresentsSections.homEquiv.symm
      ((freeSheafCorepresentsSections (⊤ : Opens T)).homEquiv (𝟙 _)) ≫ g) = _
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
  exact ((freeSheafCorepresentsSections (⊤ : Opens T)).homEquiv_comp g (𝟙 _)).symm.trans
    (by rw [Category.id_comp]; rfl)

/-- In degree zero the all-degree comparison is the previously proved
identification with actual global sections. -/
theorem localSheafTopEquiv_zero_sections
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (x : F.H' 0 ⊤) :
    Sheaf.H.equiv₀ F (isTerminalTop (α := Opens T)) (localSheafTopEquiv F 0 x) =
      localSheafH0Equiv F ⊤ x := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  change Sheaf.H.equiv₀ F (isTerminalTop (α := Opens T))
    ((Ext.mk₀ (freeSheafTopIso (T := T)).inv).comp (Ext.mk₀ g) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  have h₁ : Ext.addEquiv₀ (Ext.mk₀ ((freeSheafTopIso (T := T)).inv ≫ g)) =
      (freeSheafTopIso (T := T)).inv ≫ g := Ext.addEquiv₀.apply_symm_apply _
  have h₂ : Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply _
  change constantIntegerCorepresentsSections.homEquiv
      (Ext.addEquiv₀ (Ext.mk₀ ((freeSheafTopIso (T := T)).inv ≫ g))) =
    freeSheafSectionsEquiv F ⊤ (Ext.addEquiv₀ (Ext.mk₀ g))
  calc
    _ = constantIntegerCorepresentsSections.homEquiv
        ((freeSheafTopIso (T := T)).inv ≫ g) :=
      congrArg (fun a => constantIntegerCorepresentsSections.homEquiv a) h₁
    _ = freeSheafSectionsEquiv F ⊤ g := freeSheafTopIso_inv_sections F g
    _ = _ := congrArg (freeSheafSectionsEquiv F ⊤) h₂.symm

end BPFixedPoints.SheafTools
