import BPFixedPoints.Incidence.BinaryCoverCellTensorAugmentation

/-! # The original pair sheaf model is the sheafified standard tensor totalization

Only the original integer-module forgetting and native sheafification
functors are used. This does not assume a comparison between sheafification
of a presheaf tensor and a separately constructed tensor of sheaves.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The native standard integer tensor complex with only its original module structure forgotten. -/
noncomputable def tensorAbelianPresheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  ((toAbelianPresheaf (T := T)).mapHomologicalComplex _).obj (tensorPresheafComplex ℤ U)

/-- The native standard presheaf tensor complex sheafified in the actual Ext category. -/
noncomputable def tensorSheafComplex : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    (tensorAbelianPresheafComplex U)

/-- The specified original native total comparison after the original integer-module forgetting. -/
noncomputable def tensorPairAbelianComplexIso : tensorAbelianPresheafComplex U ≅ pairedAbelianPresheafComplex U :=
  ((toAbelianPresheaf (T := T)).mapHomologicalComplex _).mapIso (tensorPairComplexIso U ℤ)

/-- The original pair sheaf complex is the sheafification of Mathlib's standard presheaf tensor totalization. -/
noncomputable def tensorPairSheafComplexIso : tensorSheafComplex U ≅ pairedSheafComplex U :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).mapIso
    (tensorPairAbelianComplexIso U)

/-- Each actual sheaf comparison component retains the specified original pure-cell comparison. -/
theorem tensorPairSheafComplexIso_hom (n : ℕ) :
    (tensorPairSheafComplexIso U).hom.f n =
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
        ((toAbelianPresheaf (T := T)).map (tensorToPairTerm U ℤ n)) := rfl

/-- The native standard total augmentation after the original module forgetting. -/
noncomputable def tensorComponentAbelianAugmentation : (tensorAbelianPresheafComplex U).X 0 ⟶
    pairedComponentAbelianPresheaf (V := V) (T := T) :=
  (toAbelianPresheaf (T := T)).map (tensorComponentPresheafAugmentation U ℤ)

/-- The native standard total augmentation in the actual abelian sheaf category. -/
noncomputable def tensorSheafAugmentation : (tensorSheafComplex U).X 0 ⟶
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj
      (pairedComponentAbelianPresheaf (V := V) (T := T)) :=
  (presheafToSheaf _ AddCommGrpCat).map (tensorComponentAbelianAugmentation U)

/-- The original comparison preserves the independently specified native standard augmentation after sheafification. -/
theorem tensorPairSheafComplexIso_augmentation :
    (tensorPairSheafComplexIso U).hom.f 0 ≫
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map (pairedComponentAbelianAugmentation U) =
        tensorSheafAugmentation U := by
  rw [tensorPairSheafComplexIso_hom,tensorSheafAugmentation,← Functor.map_comp]
  change (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
    ((toAbelianPresheaf (T := T)).map (tensorToPairTerm U ℤ 0) ≫
      (toAbelianPresheaf (T := T)).map (pairedComponentPresheafAugmentation U ℤ)) = _
  rw [← Functor.map_comp,tensorToPair_augmentation]
  rfl

/-- The actual standard total augmentation kills its actual degree-one boundary. -/
theorem tensorSheafAugmentation_zero : (tensorSheafComplex U).d 1 0 ≫ tensorSheafAugmentation U = 0 := by
  change (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
    ((toAbelianPresheaf (T := T)).map ((tensorPresheafComplex ℤ U).d 1 0)) ≫
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
        ((toAbelianPresheaf (T := T)).map (tensorComponentPresheafAugmentation U ℤ)) = 0
  rw [← Functor.map_comp,← Functor.map_comp,tensorComponentPresheafAugmentation_zero,
    Functor.map_zero,Functor.map_zero]

/-- The specified original actual diagonal now targets the sheafified native standard tensor totalization. -/
noncomputable def tensorSheafDiagonalMap : sheafComplex U ⟶ tensorSheafComplex U :=
  sheafDiagonalMap U ≫ (tensorPairSheafComplexIso U).inv

/-- It retains the specified original pair diagonal itself. -/
theorem tensorSheafDiagonal_toPair : tensorSheafDiagonalMap U ≫ (tensorPairSheafComplexIso U).hom = sheafDiagonalMap U := by
  simp [tensorSheafDiagonalMap]

/-- The actual standard tensor diagonal preserves the original actual terminal augmentation. -/
theorem tensorSheafDiagonal_augmentation :
    (tensorSheafDiagonalMap U).f 0 ≫ tensorSheafAugmentation U = augmentation U ≫
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
        (terminalComponentDiagonal (V := V) (T := T)) := by
  have h := congrArg (fun f => f.f 0) (tensorSheafDiagonal_toPair U)
  change (tensorSheafDiagonalMap U).f 0 ≫ (tensorPairSheafComplexIso U).hom.f 0 = (sheafDiagonalMap U).f 0 at h
  rw [← tensorPairSheafComplexIso_augmentation,← Category.assoc,h,sheafDiagonal_augmentation]

end BPFixedPoints.SheafTools.BinaryCells
