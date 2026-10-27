import BPFixedPoints.Incidence.SheafLocalCohomologyZero
import Mathlib.Topology.Sheaves.Flasque

/-! # Injective abelian sheaves are flasque

The free abelian sheaf represented by an open corepresents its sections.
The native free functor and sheafification preserve monomorphisms, so the
injective extension property makes every restriction surjective.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]

/-- The native free abelian sheaf construction on the original open category. -/
noncomputable def freeOpenAbelianSheaf :
    Opens T ⥤ Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  yoneda ⋙ (Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat

/-- Open inclusions induce monomorphisms between the native represented free sheaves. -/
instance freeOpenAbelianSheaf_map_mono {U V : Opens T} (f : U ⟶ V) :
    Mono ((freeOpenAbelianSheaf (T := T)).map f) := by
  dsimp only [freeOpenAbelianSheaf, Functor.comp_map]
  infer_instance

/-- Every native injective abelian sheaf is flasque on the original topological space. -/
theorem injectiveSheaf_isFlasque
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) [Injective F] :
    TopCat.Sheaf.IsFlasque (X := TopCat.of T) F where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    let g := (freeSheafSectionsEquiv F V.unop).symm s
    let h := Injective.factorThru g ((freeOpenAbelianSheaf (T := T)).map i.unop)
    refine ⟨freeSheafSectionsEquiv F U.unop h, ?_⟩
    have hn := freeSheafSectionsEquiv_naturality F i.unop h
    change freeSheafSectionsEquiv F V.unop
      ((freeOpenAbelianSheaf (T := T)).map i.unop ≫ h) = _ at hn
    rw [Injective.comp_factorThru] at hn
    exact hn.symm.trans ((freeSheafSectionsEquiv F V.unop).apply_symm_apply s)

end BPFixedPoints.SheafTools
