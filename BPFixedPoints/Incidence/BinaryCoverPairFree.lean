import BPFixedPoints.Incidence.BinaryCoverPairExact
import BPFixedPoints.Incidence.BinaryCoverCellFree
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Category.Grp.Adjunctions

/-! # Original available cell pairs are their original free abelian presheaf

Mathlib's native free-abelian/Finsupp and supported-subtype equivalences
retain each original cell and coefficient. The resulting presheaf iso
commutes with the original cell inclusion restrictions, before sheafification.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The actual intersection open attached to the two original faces. -/
def pairedFaceOpen (q : (V → Fin 3) × (V → Fin 3)) : Opens T :=
  binaryCoverFaceOpen U q.1 ⊓ binaryCoverFaceOpen U q.2

/-- The original faces in original overlap dimension n. -/
def PairFaceIndex (n : ℕ) := {q : (V → Fin 3) × (V → Fin 3) // CechProduct.faceDegree q.1 + CechProduct.faceDegree q.2 = n}

/-- The original available-cell index presheaf, with unchanged original cell labels. -/
def pairedCellIndices (n : ℕ) : (Opens T)ᵒᵖ ⥤ Type where
  obj W := PairCellIndex U W.unop n
  map f := ↾fun q => ⟨q.val,(leOfHom f.unop).trans q.property.1,(leOfHom f.unop).trans q.property.2.1,q.property.2.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original abelian presheaf term, before taking Hom or any cohomology comparison. -/
noncomputable abbrev pairedPresheafTerm (n : ℕ) :=
  (toAbelianPresheaf (T := T)).obj (pairedPresheaf U ℤ n)

@[reducible] noncomputable local instance pairedFreeChainsAddCommGroup (W : Opens T) (n : ℕ) :
    AddCommGroup (pairedChains U ℤ W n) := (pairedChains U ℤ W n).addCommGroup
@[reducible] noncomputable local instance pairedFreeChainsModule (W : Opens T) (n : ℕ) :
    Module ℤ (pairedChains U ℤ W n) := (pairedChains U ℤ W n).module

/-- The native free abelian group on exactly the original available cells is the original chain term. -/
noncomputable def pairedChainFreeEquiv (W : Opens T) (n : ℕ) :
    FreeAbelianGroup (PairCellIndex U W n) ≃+ pairedChains U ℤ W n :=
  (FreeAbelianGroup.equivFinsupp _).trans (pairCellCoordinates U ℤ W n).symm.toAddEquiv

/-- Every original free generator is exactly its original cell with coefficient one. -/
theorem pairedChainFreeEquiv_of_val (W : Opens T) (n : ℕ) (q : PairCellIndex U W n) :
    (pairedChainFreeEquiv U W n (FreeAbelianGroup.of q)).val = single q.val 1 := by
  change ((pairCellCoordinates U ℤ W n).symm
    ((FreeAbelianGroup.equivFinsupp _) (FreeAbelianGroup.of q))).val = _
  rw [FreeAbelianGroup.equivFinsupp_apply,FreeAbelianGroup.toFinsupp_of,pairCellCoordinates_generator]
  rfl

/-- The original free-cell presheaf and original integer-cell term have the specified generator-preserving iso. -/
noncomputable def freePairPresheafIso (n : ℕ) :
    pairedCellIndices U n ⋙ AddCommGrpCat.free ≅ pairedPresheafTerm U n :=
  NatIso.ofComponents (fun W => (pairedChainFreeEquiv U W.unop n).toAddCommGrpIso) (by
    intro W Z f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro q
    change pairedChainFreeEquiv U Z.unop n
      (FreeAbelianGroup.map ((pairedCellIndices U n).map f) (FreeAbelianGroup.of q)) = _
    rw [FreeAbelianGroup.map_of_apply]
    apply Subtype.ext
    rw [pairedChainFreeEquiv_of_val]
    exact (pairedChainFreeEquiv_of_val U W.unop n q).symm)

end BPFixedPoints.SheafTools.BinaryCells
