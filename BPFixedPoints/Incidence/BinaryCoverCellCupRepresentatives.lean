import BPFixedPoints.Incidence.AbelianSheafTensorPresheafSections
import BPFixedPoints.Incidence.BinaryCoverCellSheafCup
import BPFixedPoints.Incidence.BinaryCoverCellSections

/-! # Original cell representatives in the actual tensor and cup

Evaluate the original native tensor comparison on the original available
cells. Each pair is sent through its original bidegree inclusion, with its
unchanged coefficient, before taking any cohomology quotient.
-/

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
local instance representativeSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The native tensor comparison sends original pure representatives to the same original pair. -/
theorem actualTensorPair_pure (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (x : chains U ℤ W i) (y : chains U ℤ W j) :
    (actualTensorInclusion U i j n h ≫ (actualTensorPairComplexIso U).hom.f n).hom.app (op W)
      (sheafPureSection _ _ W
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (presheafTerm U i)).app (op W) x)
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (presheafTerm U j)).app (op W) y)) =
      ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
        (toAbelianPresheaf.obj (pairedPresheaf U ℤ n))).app (op W)
          (tensorPairLinear U ℤ W i j n h (x ⊗ₜ[ℤ] y)) := by
  rw [actualTensorPairComplexIso_inclusion]
  change (integerSheafification.map (tensorPairTerm U ℤ i j n h)).hom.app (op W)
    ((actualCellTensorIso U i j).hom.hom.app (op W) _) = _
  refine (congrArg (fun z => (integerSheafification.map (tensorPairTerm U ℤ i j n h)).hom.app (op W) z)
    (integerSheafification_tensor_pure (presheaf U ℤ i) (presheaf U ℤ j) W x y)).trans ?_
  have hn := (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.naturality
    ((toAbelianPresheaf (T := T)).map (tensorPairTerm U ℤ i j n h))
  have he := NatTrans.congr_app hn (op W)
  exact (ConcreteCategory.congr_hom he (x ⊗ₜ[ℤ] y)).symm

/-- The original coefficient-one pair is the actual pure cell tensor in its original bidegree. -/
theorem actualTensorPair_generator (W : Opens T) (n : ℕ) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q=n) (r : ℤ) :
    (actualTensorInclusion U (faceDegree p) (faceDegree q) n hd ≫
      (actualTensorPairComplexIso U).hom.f n).hom.app (op W)
      (sheafPureSection _ _ W
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (presheafTerm U (faceDegree p))).app (op W)
            (cellGenerator U ℤ W _ p hp rfl 1))
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (presheafTerm U (faceDegree q))).app (op W)
            (cellGenerator U ℤ W _ q hq rfl r))) =
      ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
        (toAbelianPresheaf.obj (pairedPresheaf U ℤ n))).app (op W)
          (pairGenerator U ℤ W n p q hp hq hd r) := by
  rw [actualTensorPair_pure,tensorPairLinear_generator,one_mul]

end
end BPFixedPoints.SheafTools.BinaryCells
