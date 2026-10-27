import BPFixedPoints.Incidence.BinaryCoverCellActualTensorDifferential

/-! # The original pair complex is the actual standard sheaf tensor complex

The specified native bidegree comparisons preserve the independently
specified total differential. Their composite with the original pair
comparison identifies the actual complexes and the original diagonal.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance actualComplexSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The actual comparison preserves the native standard total differential. -/
theorem actualTensorTermIso_boundary (n : ℕ) :
    (actualTensorTermIso U (n+1)).hom ≫ (tensorSheafComplex U).d (n+1) n =
      (actualTensorSheafComplex U).d (n+1) n ≫ (actualTensorTermIso U n).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  have hd : tensorPresheafInclusion ℤ U i j (n+1) h ≫ (tensorPresheafComplex ℤ U).d (n+1) n =
      tensorLeftDifferential U ℤ i j n+tensorRightDifferential U ℤ i j n := by
    rw [HomologicalComplex.mapBifunctor.d_eq,Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁,HomologicalComplex.mapBifunctor.ι_D₂]
  have ha : actualTensorInclusion U i j (n+1) h ≫ (actualTensorSheafComplex U).d (n+1) n =
      actualTensorLeftDifferential U i j n+actualTensorRightDifferential U i j n := by
    rw [HomologicalComplex.mapBifunctor.d_eq,Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁,HomologicalComplex.mapBifunctor.ι_D₂]
  change actualTensorInclusion U i j (n+1) h ≫
    ((actualTensorTermIso U (n+1)).hom ≫ (tensorSheafComplex U).d (n+1) n) = _
  rw [← Category.assoc,actualTensorInclusion_comparison,Category.assoc]
  change (actualCellTensorIso U i j).hom ≫
    (integerSheafification.map (tensorPresheafInclusion ℤ U i j (n+1) h) ≫
      integerSheafification.map ((tensorPresheafComplex ℤ U).d (n+1) n)) = _
  rw [← Functor.map_comp,hd,Functor.map_add,Preadditive.comp_add,
    ← actualTensorLeft_comparison U i j n h,← actualTensorRight_comparison U i j n h,
    ← Preadditive.add_comp,← ha,Category.assoc]

/-- Sheafification commutes with the standard tensor totalization by the specified original maps. -/
def actualTensorComplexIso : actualTensorSheafComplex U ≅ tensorSheafComplex U :=
  HomologicalComplex.Hom.isoOfComponents (actualTensorTermIso U) (by
    intro i j hij
    have hi : i=j+1 := hij.symm
    subst i
    exact actualTensorTermIso_boundary U j)

/-- The chain comparison has precisely the native strong monoidal and coproduct components. -/
theorem actualTensorComplexIso_hom (n : ℕ) :
    (actualTensorComplexIso U).hom.f n = (actualTensorTermIso U n).hom := rfl

/-- The original pair sheaf complex is the standard tensor of the original actual cell sheaf complexes. -/
def actualTensorPairComplexIso : actualTensorSheafComplex U ≅ pairedSheafComplex U :=
  actualTensorComplexIso U ≪≫ tensorPairSheafComplexIso U

/-- The original pure-cell comparison is retained on every actual bidegree inclusion. -/
@[reassoc] theorem actualTensorPairComplexIso_inclusion (i j n : ℕ) (h : i+j=n) :
    actualTensorInclusion U i j n h ≫ (actualTensorPairComplexIso U).hom.f n =
      (actualCellTensorIso U i j).hom ≫ integerSheafification.map (tensorPairTerm U ℤ i j n h) := by
  change actualTensorInclusion U i j n h ≫
    ((actualTensorTermIso U n).hom ≫ (tensorPairSheafComplexIso U).hom.f n) = _
  rw [← Category.assoc,actualTensorInclusion_comparison,Category.assoc,tensorPairSheafComplexIso_hom]
  change (actualCellTensorIso U i j).hom ≫
    (integerSheafification.map (tensorPresheafInclusion ℤ U i j n h) ≫
      integerSheafification.map (tensorToPairTerm U ℤ n)) = _
  rw [← Functor.map_comp,tensorInclusion_toPair]

/-- The specified original diagonal now targets the standard tensor of the actual sheaf resolutions. -/
def actualTensorDiagonalMap : sheafComplex U ⟶ actualTensorSheafComplex U :=
  tensorSheafDiagonalMap U ≫ (actualTensorComplexIso U).inv

/-- The actual tensor diagonal returns exactly the specified original pair diagonal. -/
theorem actualTensorDiagonal_toPair :
    actualTensorDiagonalMap U ≫ (actualTensorPairComplexIso U).hom = sheafDiagonalMap U := by
  simp [actualTensorDiagonalMap,actualTensorPairComplexIso,tensorSheafDiagonal_toPair]

end
end BPFixedPoints.SheafTools.BinaryCells
