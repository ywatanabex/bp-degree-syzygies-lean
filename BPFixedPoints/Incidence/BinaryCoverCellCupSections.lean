import BPFixedPoints.Incidence.BinaryCoverCellCupRepresentatives

/-! # Evaluate actual cell cochains on their original section representatives -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The original cell section is the image of its original supported integer generator. -/
def cellSheafSection (W : Opens T) (n : ℕ) (p : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hd : faceDegree p=n) (r : ℤ) :
    ((sheafComplex U).X n).obj.obj (op W) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
    (presheafTerm U n)).app (op W) (cellGenerator U ℤ W n p hp hd r)

/-- The original pair section is the image of its original supported integer pair. -/
def pairSheafSection (W : Opens T) (n : ℕ) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q=n) (r : ℤ) :
    ((pairedSheafComplex U).X n).obj.obj (op W) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
    (toAbelianPresheaf.obj (pairedPresheaf U ℤ n))).app (op W)
      (pairGenerator U ℤ W n p q hp hq hd r)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The original section equivalence evaluates the same original coefficient-one generator. -/
theorem sectionsEquiv_cellSheafSection (n : ℕ) (f : (sheafComplex U).X n ⟶ F)
    (q : FaceIndex (V := V) n) :
    sectionsEquiv U F n f q =
      f.hom.app (op (binaryCoverFaceOpen U q.val))
        (cellSheafSection U _ n q.val le_rfl (by
          have h := q.property
          change -(faceDegree q.val : ℤ) = -(n : ℤ) at h
          omega) 1) := by
  change f.hom.app _ (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
    (presheafTerm U n)).app _ (chainFreeEquiv U _ n (FreeAbelianGroup.of (canonicalCell U q)))) = _
  congr 1
  congr 1
  apply Subtype.ext
  exact chainFreeEquiv_of_val U _ n (canonicalCell U q)

/-- Evaluation on an original cell over a smaller open is its actual original section restriction. -/
theorem cellSheafSection_cochain (n : ℕ) (f : (sheafComplex U).X n ⟶ F)
    (q : FaceIndex (V := V) n) (W : Opens T) (hq : W ≤ binaryCoverFaceOpen U q.val) :
    f.hom.app (op W) (cellSheafSection U W n q.val hq (by
      have h := q.property
      change -(faceDegree q.val : ℤ) = -(n : ℤ) at h
      omega) 1) =
        F.obj.map (homOfLE hq).op (sectionsEquiv U F n f q) := by
  rw [sectionsEquiv_cellSheafSection]
  have h := NatTrans.naturality_apply
    ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).homEquiv _ F f)
      (homOfLE hq).op (cellGenerator U ℤ (binaryCoverFaceOpen U q.val) n q.val le_rfl (by
        have h := q.property
        change -(faceDegree q.val : ℤ) = -(n : ℤ) at h
        omega) 1)
  exact h

end
end BPFixedPoints.SheafTools.BinaryCells
