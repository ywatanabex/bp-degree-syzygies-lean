import BPFixedPoints.Incidence.BinaryCoverCellCupSections

/-! # Actual cubical cup evaluated on original face generators -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance faceFormulaSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- Evaluate the original cell cochain in its original degree, with zero outside that degree. -/
def cellCochainValue (i : ℕ) (f : (sheafComplex U).X i ⟶ F) (W : Opens T)
    (p : V → Fin 3) (hp : W ≤ binaryCoverFaceOpen U p) : F.obj.obj (op W) :=
  if hi : faceDegree p=i then f.hom.app (op W) (cellSheafSection U W i p hp hi 1) else 0

/-- The native pair cochain uses the independently specified original tensor comparison. -/
def actualPairCochain (b : SectionPairing F G H) (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (pairedSheafComplex U).X n ⟶ H :=
  (actualTensorPairComplexIso U).inv.f n ≫ actualTensorCochain U b n i j f g

/-- Each original pair generator evaluates by the original section product in its original bidegree. -/
theorem actualPairCochain_generator (b : SectionPairing F G H) (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G)
    (W : Opens T) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q=n) :
    (actualPairCochain U b n i j f g).hom.app (op W) (pairSheafSection U W n p q hp hq hd 1) =
      b.pairing W (cellCochainValue U i f W p hp) (cellCochainValue U j g W q hq) := by
  let z := sheafPureSection _ _ W
    (cellSheafSection U W (faceDegree p) p hp rfl 1)
    (cellSheafSection U W (faceDegree q) q hq rfl 1)
  have e := actualTensorPair_generator U W n p q hp hq hd 1
  have he : (actualPairCochain U b n i j f g).hom.app (op W)
      (pairSheafSection U W n p q hp hq hd 1) =
        (actualTensorInclusion U (faceDegree p) (faceDegree q) n hd ≫
          actualTensorCochain U b n i j f g).hom.app (op W) z := by
    refine (congrArg ((actualPairCochain U b n i j f g).hom.app (op W)) e.symm).trans ?_
    change ((actualTensorInclusion U (faceDegree p) (faceDegree q) n hd ≫
      (actualTensorPairComplexIso U).hom.f n ≫
        (actualTensorPairComplexIso U).inv.f n ≫ actualTensorCochain U b n i j f g).hom.app (op W)) z = _
    have hi : (actualTensorPairComplexIso U).hom.f n ≫ (actualTensorPairComplexIso U).inv.f n = 𝟙 _ :=
      HomologicalComplex.congr_hom (actualTensorPairComplexIso U).hom_inv_id n
    rw [← Category.assoc ((actualTensorPairComplexIso U).hom.f n), hi, Category.id_comp]
  rw [he]
  by_cases hi : faceDegree p=i
  · subst i
    by_cases hj : faceDegree q=j
    · subst j
      simpa only [cellCochainValue, dite_true] using
        actualTensorCochain_pure U b n (faceDegree p) (faceDegree q) hd f g W
          (cellSheafSection U W _ p hp rfl 1) (cellSheafSection U W _ q hq rfl 1)
    · simp only [actualTensorCochain, ← Category.assoc,
        actualTensorProjection_other U n (faceDegree p) j (faceDegree p) (faceDegree q) hd (Or.inr hj),
        zero_comp]
      simp [cellCochainValue, hj]
  · simp only [actualTensorCochain, ← Category.assoc,
      actualTensorProjection_other U n i j (faceDegree p) (faceDegree q) hd (Or.inl hi),
      zero_comp]
    simp [cellCochainValue, hi]

end
end BPFixedPoints.SheafTools.BinaryCells
