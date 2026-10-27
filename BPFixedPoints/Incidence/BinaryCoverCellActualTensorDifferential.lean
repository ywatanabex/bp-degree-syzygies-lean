import BPFixedPoints.Incidence.BinaryCoverCellActualTensor

/-! # Native tensor-sheaf total differentials preserve the original signs

The left and right native total differentials are compared separately.
Strong monoidal naturality preserves the actual original differentials;
additivity preserves the native integer Koszul sign.
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
local instance actualDifferentialSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The actual cell term is the original integer term with only forgetting and sheafification. -/
theorem actualCellSheaf_X (i : ℕ) :
    (sheafComplex U).X i = integerSheafification.obj (presheaf U ℤ i) := rfl

/-- The actual cell differential is the same original differential after sheafification. -/
theorem actualCellSheaf_d (i : ℕ) :
    (sheafComplex U).d (i+1) i = integerSheafification.map (presheafDifferential U ℤ i) := by
  change integerSheafification.map ((presheafComplex U ℤ).d (i+1) i) = _
  rw [cellPresheafComplex_d]

/-- The independently specified actual first total differential. -/
abbrev actualTensorLeftDifferential (i j n : ℕ) :
    (sheafComplex U).X i ⊗ (sheafComplex U).X j ⟶ (actualTensorSheafComplex U).X n :=
  HomologicalComplex.mapBifunctor.d₁ (sheafComplex U) (sheafComplex U)
    (curriedTensor _) (ComplexShape.down ℕ) i j n

/-- The independently specified actual second total differential. -/
abbrev actualTensorRightDifferential (i j n : ℕ) :
    (sheafComplex U).X i ⊗ (sheafComplex U).X j ⟶ (actualTensorSheafComplex U).X n :=
  HomologicalComplex.mapBifunctor.d₂ (sheafComplex U) (sheafComplex U)
    (curriedTensor _) (ComplexShape.down ℕ) i j n

/-- Degree zero has no left native differential. -/
theorem actualTensorLeft_zero (j n : ℕ) : actualTensorLeftDifferential U 0 j n = 0 :=
  HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by decide)

/-- Degree zero has no right native differential. -/
theorem actualTensorRight_zero (i n : ℕ) : actualTensorRightDifferential U i 0 n = 0 :=
  HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by decide)

/-- The native left differential has no additional sign. -/
theorem actualTensorLeft_succ (i j n : ℕ) (h : i+j=n) :
    actualTensorLeftDifferential U (i+1) j n =
      (integerSheafification.map (presheafDifferential U ℤ i) ▷ (sheafComplex U).X j) ≫
        actualTensorInclusion U i j n h := by
  have e := HomologicalComplex.mapBifunctor.d₁_eq (sheafComplex U) (sheafComplex U)
    (curriedTensor _) (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n h
  have hs : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i+1,j) = 1 := rfl
  simpa only [actualCellSheaf_d,hs,one_smul,curriedTensor_map_app] using e

/-- The native right differential retains its original left-degree Koszul sign. -/
theorem actualTensorRight_succ (i j n : ℕ) (h : i+j=n) :
    actualTensorRightDifferential U i (j+1) n =
      ((-1 : ℤˣ)^i) • (((sheafComplex U).X i ◁
        integerSheafification.map (presheafDifferential U ℤ j)) ≫ actualTensorInclusion U i j n h) := by
  have e := HomologicalComplex.mapBifunctor.d₂_eq (sheafComplex U) (sheafComplex U)
    (curriedTensor _) (ComplexShape.down ℕ) i
    (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n h
  have hs : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i,j+1) = (-1 : ℤˣ)^i := rfl
  simpa only [actualCellSheaf_d,hs,curriedTensor_obj_map] using e

/-- Strong monoidal naturality preserves the original left differential itself. -/
theorem actualCellTensorIso_left (i j : ℕ) :
    (integerSheafification.map (presheafDifferential U ℤ i) ▷ (sheafComplex U).X j) ≫
      (actualCellTensorIso U i j).hom = (actualCellTensorIso U (i+1) j).hom ≫
        integerSheafification.map (presheafDifferential U ℤ i ▷ presheaf U ℤ j) :=
  Functor.LaxMonoidal.μ_natural_left integerSheafification _ _

/-- Strong monoidal naturality preserves the original right differential itself. -/
theorem actualCellTensorIso_right (i j : ℕ) :
    ((sheafComplex U).X i ◁ integerSheafification.map (presheafDifferential U ℤ j)) ≫
      (actualCellTensorIso U i j).hom = (actualCellTensorIso U i (j+1)).hom ≫
        integerSheafification.map (presheaf U ℤ i ◁ presheafDifferential U ℤ j) :=
  Functor.LaxMonoidal.μ_natural_right integerSheafification _ _

/-- Original integer unit signs survive the original forgetting and sheafification. -/
theorem integerSheafification_map_unit_smul
    {P Q : (Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ} (r : ℤˣ) (f : P ⟶ Q) :
    integerSheafification.map (r • f) = r • integerSheafification.map f := by
  simp only [Units.smul_def,Functor.map_zsmul]

/-- The specified comparison preserves the original left summand differential. -/
theorem actualTensorLeft_comparison (i j n : ℕ) (h : i+j=n+1) :
    actualTensorLeftDifferential U i j n ≫ (actualTensorTermIso U n).hom =
      (actualCellTensorIso U i j).hom ≫ integerSheafification.map (tensorLeftDifferential U ℤ i j n) := by
  cases i with
  | zero => simp only [actualTensorLeft_zero,tensorLeftDifferential_zero,zero_comp,Functor.map_zero,comp_zero]
  | succ i =>
    have h' : i+j=n := by omega
    rw [actualTensorLeft_succ U i j n h',tensorLeftDifferential_succ U ℤ i j n h',
      Category.assoc,actualTensorInclusion_comparison,← Category.assoc,actualCellTensorIso_left,
      Category.assoc,← Functor.map_comp]

/-- The specified comparison also preserves the right summand with its original sign. -/
theorem actualTensorRight_comparison (i j n : ℕ) (h : i+j=n+1) :
    actualTensorRightDifferential U i j n ≫ (actualTensorTermIso U n).hom =
      (actualCellTensorIso U i j).hom ≫ integerSheafification.map (tensorRightDifferential U ℤ i j n) := by
  cases j with
  | zero => simp only [actualTensorRight_zero,tensorRightDifferential_zero,zero_comp,Functor.map_zero,comp_zero]
  | succ j =>
    have h' : i+j=n := by omega
    rw [actualTensorRight_succ U i j n h',tensorRightDifferential_succ U ℤ i j n h',
      Linear.units_smul_comp,Category.assoc,actualTensorInclusion_comparison,
      ← Category.assoc,actualCellTensorIso_right,Category.assoc,← Functor.map_comp,
      integerSheafification_map_unit_smul,Linear.comp_units_smul]

end
end BPFixedPoints.SheafTools.BinaryCells
