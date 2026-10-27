import BPFixedPoints.Incidence.BinaryCoverCellDiagonal
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Mathlib's standard tensor complex of the original cell presheaves

Use the native pointwise module tensor and native homological totalization.
The original cell complex is not replaced or redefined by this construction.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T] (R : Type) [CommRing R]

/-- Native pointwise module tensor is additive in the original presheaf morphisms. -/
instance modulePresheafMonoidalPreadditive : MonoidalPreadditive ((Opens T)ᵒᵖ ⥤ ModuleCat R) where
  whiskerLeft_zero {X Y Z} := by ext W; simp
  zero_whiskerRight {X Y Z} := by ext W; simp
  whiskerLeft_add f g := by ext W; simp
  add_whiskerRight f g := by ext W; simp

variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → Opens T)

/-- The native Mathlib tensor totalization of the original two cell presheaf complexes. -/
noncomputable abbrev tensorPresheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat R) ℕ :=
  HomologicalComplex.tensorObj (presheafComplex U R) (presheafComplex U R)

/-- The native inclusion of the original bidegree summand into the standard totalization. -/
noncomputable abbrev tensorPresheafInclusion (i j n : ℕ) (h : i+j=n) :
    presheaf U R i ⊗ presheaf U R j ⟶ (tensorPresheafComplex R U).X n :=
  HomologicalComplex.ιTensorObj (presheafComplex U R) (presheafComplex U R) i j n h

end BPFixedPoints.SheafTools.BinaryCells
