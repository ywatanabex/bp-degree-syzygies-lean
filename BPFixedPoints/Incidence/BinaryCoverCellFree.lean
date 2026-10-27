import BPFixedPoints.Incidence.BinaryCoverCellSheaf
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Category.Grp.Adjunctions

/-! # Original available cells are their original free abelian presheaf

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

/-- The original faces in original overlap dimension n. -/
def FaceIndex (n : ℕ) := {q : V → Fin 3 // cellDegree q = -(n : ℤ)}

/-- The original degree-n cells available on the original open. -/
def CellIndex (W : Opens T) (n : ℕ) :=
  {q : V → Fin 3 // W ≤ binaryCoverFaceOpen U q ∧ cellDegree q = -(n : ℤ)}

/-- The original available-cell index presheaf, with unchanged original cell labels. -/
def cellIndices (n : ℕ) : (Opens T)ᵒᵖ ⥤ Type where
  obj W := CellIndex U W.unop n
  map f := ↾fun q => ⟨q.val,(leOfHom f.unop).trans q.property.1,q.property.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original abelian presheaf term, before taking Hom or any cohomology comparison. -/
noncomputable abbrev presheafTerm (n : ℕ) :=
  (toAbelianPresheaf (T := T)).obj (presheaf U ℤ n)

@[reducible] noncomputable local instance cellChainsAddCommGroup (W : Opens T) (n : ℕ) :
    AddCommGroup (chains U ℤ W n) := (chains U ℤ W n).addCommGroup
@[reducible] noncomputable local instance cellChainsModule (W : Opens T) (n : ℕ) :
    Module ℤ (chains U ℤ W n) := (chains U ℤ W n).module

/-- Combine the original availability and original degree support without changing coefficients. -/
noncomputable def chainsSupportedEquiv (W : Opens T) (n : ℕ) :
    chains U ℤ W n ≃ₗ[ℤ]
      supported ℤ ℤ {q | W ≤ binaryCoverFaceOpen U q ∧ cellDegree q = -(n : ℤ)} where
  toFun x := ⟨x.val,fun q hq => ⟨x.property.1 hq,x.property.2 hq⟩⟩
  invFun x := ⟨x.val,(fun q hq => (x.property hq).1),fun q hq => (x.property hq).2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The native free abelian group on exactly the original available cells is the original chain term. -/
noncomputable def chainFreeEquiv (W : Opens T) (n : ℕ) :
    FreeAbelianGroup (CellIndex U W n) ≃+ chains U ℤ W n :=
  (FreeAbelianGroup.equivFinsupp _).trans
    (((Finsupp.supportedEquivFinsupp (R := ℤ)
      {q | W ≤ binaryCoverFaceOpen U q ∧ cellDegree q = -(n : ℤ)}).symm.toAddEquiv).trans
      (chainsSupportedEquiv U W n).symm.toAddEquiv)

/-- Every original free generator is exactly its original cell with coefficient one. -/
theorem chainFreeEquiv_of_val (W : Opens T) (n : ℕ) (q : CellIndex U W n) :
    (chainFreeEquiv U W n (FreeAbelianGroup.of q)).val = single q.val 1 := by
  change (((Finsupp.supportedEquivFinsupp (R := ℤ)
    {q | W ≤ binaryCoverFaceOpen U q ∧ cellDegree q = -(n : ℤ)}).symm
      ((FreeAbelianGroup.equivFinsupp _) (FreeAbelianGroup.of q))) : (V → Fin 3) →₀ ℤ) = _
  rw [FreeAbelianGroup.equivFinsupp_apply,FreeAbelianGroup.toFinsupp_of,
    Finsupp.supportedEquivFinsupp_symm_single]

/-- The original free-cell presheaf and original integer-cell term have the specified generator-preserving iso. -/
noncomputable def freeCellPresheafIso (n : ℕ) :
    cellIndices U n ⋙ AddCommGrpCat.free ≅ presheafTerm U n :=
  NatIso.ofComponents (fun W => (chainFreeEquiv U W.unop n).toAddCommGrpIso) (by
    intro W Z f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro q
    change chainFreeEquiv U Z.unop n
      (FreeAbelianGroup.map ((cellIndices U n).map f) (FreeAbelianGroup.of q)) = _
    rw [FreeAbelianGroup.map_of_apply]
    apply Subtype.ext
    rw [chainFreeEquiv_of_val]
    exact (chainFreeEquiv_of_val U W.unop n q).symm)

end BPFixedPoints.SheafTools.BinaryCells
