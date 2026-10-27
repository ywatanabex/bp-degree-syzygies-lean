import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Topology.Sheaves.Abelian

/-! # The native tensor of actual abelian sheaves

Use Mathlib's integer-module equivalence, monoidal transport, and native
localization of the presheaf tensor. These scoped instances select the
integer tensor, independently of the cartesian monoidal structure on
abelian groups. No cohomology or state-space equivalence is used.
-/

namespace BPFixedPoints.SheafTools.AbelianTensor
open CategoryTheory CategoryTheory.Monoidal CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed.FunctorCategory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section

/-- Mathlib's original equivalence forgets precisely the integer module structure. -/
abbrev integerModuleEquivalence : ModuleCat.{0} ℤ ≌ AddCommGrpCat.{0} :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence

local instance : integerModuleEquivalence.functor.Additive :=
  inferInstanceAs (forget₂ (ModuleCat ℤ) AddCommGrpCat.{0}).Additive

/-- The native integer tensor transported along the original forgetful equivalence. -/
scoped instance groupMonoidal : MonoidalCategory AddCommGrpCat.{0} :=
  Monoidal.transport integerModuleEquivalence
scoped instance groupSymmetric : SymmetricCategory AddCommGrpCat.{0} :=
  inferInstanceAs (SymmetricCategory (Transported integerModuleEquivalence))
scoped instance groupClosed : MonoidalClosed AddCommGrpCat.{0} :=
  inferInstanceAs (MonoidalClosed (Transported integerModuleEquivalence))
scoped instance forgetMonoidal : (forget₂ (ModuleCat ℤ) AddCommGrpCat.{0}).Monoidal :=
  inferInstanceAs (equivalenceTransported integerModuleEquivalence).functor.Monoidal
scoped instance inverseMonoidal : integerModuleEquivalence.inverse.Monoidal :=
  inferInstanceAs (equivalenceTransported integerModuleEquivalence).inverse.Monoidal
scoped instance groupMonoidalPreadditive : MonoidalPreadditive AddCommGrpCat.{0} :=
  monoidalPreadditive_of_faithful integerModuleEquivalence.inverse

variable {T : Type} [TopologicalSpace T]

/-- The actual abelian-sheaf tensor is Mathlib's localization of the native integer tensor. -/
scoped instance sheafMonoidal :
    MonoidalCategory (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  Sheaf.monoidalCategory _ _
scoped instance sheafSymmetric :
    SymmetricCategory (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  Sheaf.symmetricCategory _ _
scoped instance sheafClosed :
    MonoidalClosed (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

attribute [local instance] CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Tensoring actual sheaves is additive because the native closed tensor preserves colimits. -/
scoped instance sheafMonoidalPreadditive :
    MonoidalPreadditive (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) where
  whiskerLeft_zero {X Y Z} := by
    haveI := (tensorLeft X).additive_of_preservesBinaryBiproducts
    exact (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := by
    haveI := (tensorRight X).additive_of_preservesBinaryBiproducts
    exact (tensorRight X).map_zero Y Z
  whiskerLeft_add {X Y Z} f g := by
    haveI := (tensorLeft X).additive_of_preservesBinaryBiproducts
    exact (tensorLeft X).map_add
  add_whiskerRight {X Y Z} f g := by
    haveI := (tensorRight X).additive_of_preservesBinaryBiproducts
    exact (tensorRight X).map_add

end
end BPFixedPoints.SheafTools.AbelianTensor
