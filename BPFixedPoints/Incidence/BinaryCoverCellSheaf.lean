import BPFixedPoints.Incidence.BinaryCoverCellComplex
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian

/-! # The original abelian cubical cell sheaf complex is positively exact

Integer coefficients and the native forgetful functor put the original
available-cell complex in exactly the abelian sheaf category used by actual
sheaf Ext. Exact sheafification is applied to the original complex. The
augmentation and the identification of Hom with actual face sections are
proved in the separate augmentation and sections modules.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- Forget only the integer module structure, retaining the original abelian groups and maps. -/
noncomputable abbrev toAbelianPresheaf :
    ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ) ⥤ ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})

/-- The original cubical cell presheaf complex in the actual underlying abelian category. -/
noncomputable def abelianPresheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  ((toAbelianPresheaf (T := T)).mapHomologicalComplex _).obj (presheafComplex U ℤ)

/-- Forgetting the original integer module structure preserves actual positive exactness. -/
theorem abelianPresheafComplex_exact (n : ℕ) : (abelianPresheafComplex U).ExactAt (n+1) := by
  change (((presheafComplex U ℤ).sc (n+1)).map (toAbelianPresheaf (T := T))).Exact
  exact (presheafComplex_exact U ℤ n).map _

/-- Sheafification of the original cubical cell complex in the category used by actual sheaf cohomology. -/
noncomputable def sheafComplex : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    (abelianPresheafComplex U)

/-- Positive exactness of the actual original cubical cell sheaf complex on arbitrary binary open families. -/
theorem sheafComplex_exact (n : ℕ) : (sheafComplex U).ExactAt (n+1) := by
  change (((abelianPresheafComplex U).sc (n+1)).map
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})).Exact
  exact (abelianPresheafComplex_exact U n).map _

/-- Exact forgetting and sheafification retain the original direction-count bound on the actual complex. -/
theorem sheafComplex_isZero_above (n : ℕ) (hn : Fintype.card V < n) :
    IsZero ((sheafComplex U).X n) :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map_isZero
    ((toAbelianPresheaf (T := T)).map_isZero (presheafComplex_isZero_above U ℤ n hn))

end BPFixedPoints.SheafTools.BinaryCells
