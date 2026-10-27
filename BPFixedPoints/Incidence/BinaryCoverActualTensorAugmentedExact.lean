import BPFixedPoints.Incidence.BinaryCoverPairAugmentedExact

/-! # Augmented exactness of the independently specified actual tensor resolution -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The existing original pair augmentation after the existing native sheafification. -/
abbrev pairedSheafAugmentation :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
    (pairedComponentAbelianAugmentation U)

/-- The original pair sheaf augmentation kills the original pair boundary. -/
theorem pairedSheafAugmentation_zero :
    (pairedSheafComplex U).d 1 0 ≫ pairedSheafAugmentation U=0 := by
  change (presheafToSheaf _ AddCommGrpCat).map
    ((toAbelianPresheaf (T := T)).map ((pairedPresheafComplex U ℤ).d 1 0)) ≫
      (presheafToSheaf _ AddCommGrpCat).map
        ((toAbelianPresheaf (T := T)).map (pairedComponentPresheafAugmentation U ℤ))=0
  rw [← Functor.map_comp,← Functor.map_comp,pairedComponentPresheafAugmentation_zero,
    Functor.map_zero,Functor.map_zero]

/-- Exact forgetting and sheafification preserve the same original augmented pair kernel. -/
theorem pairedSheafAugmentation_exact :
    (ShortComplex.mk ((pairedSheafComplex U).d 1 0) (pairedSheafAugmentation U)
      (pairedSheafAugmentation_zero U)).Exact :=
  ((pairedComponentPresheafAugmentation_exact U ℤ).map (toAbelianPresheaf (T := T))).map
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The specified actual tensor comparison preserves the independently defined tensor augmentation. -/
theorem actualTensorPairComplexIso_augmentation :
    (actualTensorPairComplexIso U).hom.f 0 ≫ pairedSheafAugmentation U =
      actualTensorAugmentation U ≫ (actualComponentTensorIso (T := T) (V := V)).hom := by
  change (actualTensorTermIso U 0).hom ≫
    (tensorPairSheafComplexIso U).hom.f 0 ≫ pairedSheafAugmentation U = _
  rw [tensorPairSheafComplexIso_augmentation,actualTensorAugmentation_comparison]

/-- The original actual standard tensor complex and its independent augmentation are exact in degree zero. -/
theorem actualTensorAugmentation_exact :
    (ShortComplex.mk ((actualTensorSheafComplex U).d 1 0) (actualTensorAugmentation U)
      (actualTensorAugmentation_zero U)).Exact := by
  apply ShortComplex.exact_of_iso _ (pairedSheafAugmentation_exact U)
  apply Iso.symm
  exact ShortComplex.isoMk (HomologicalComplex.Hom.isoApp (actualTensorPairComplexIso U) 1)
    (HomologicalComplex.Hom.isoApp (actualTensorPairComplexIso U) 0) (actualComponentTensorIso (T := T) (V := V))
    ((actualTensorPairComplexIso U).hom.comm 1 0)
    (actualTensorPairComplexIso_augmentation U)

end
end BPFixedPoints.SheafTools.BinaryCells
