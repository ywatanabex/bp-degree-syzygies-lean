import BPFixedPoints.Incidence.BinaryCoverCellTensorDifferential

/-! # The original pair complex is Mathlib's standard tensor totalization

The original component isomorphisms preserve the independently specified
native total differential and original pair boundary.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

/-- The actual comparison preserves the native total differential in every original degree. -/
theorem tensorToPair_boundary (n : ℕ) :
    tensorToPairTerm U R (n+1) ≫ pairedPresheafDifferential U R n =
      (tensorPresheafComplex R U).d (n+1) n ≫ tensorToPairTerm U R n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  have hd : tensorPresheafInclusion R U i j (n+1) h ≫ (tensorPresheafComplex R U).d (n+1) n =
      tensorLeftDifferential U R i j n+tensorRightDifferential U R i j n := by
    rw [HomologicalComplex.mapBifunctor.d_eq,Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁,HomologicalComplex.mapBifunctor.ι_D₂]
  change tensorPresheafInclusion R U i j (n+1) h ≫ (tensorToPairTerm U R (n+1) ≫ pairedPresheafDifferential U R n) = _
  calc
    _ = (tensorPresheafInclusion R U i j (n+1) h ≫ tensorToPairTerm U R (n+1)) ≫ pairedPresheafDifferential U R n :=
      (Category.assoc _ _ _).symm
    _ = tensorPairTerm U R i j (n+1) h ≫ pairedPresheafDifferential U R n := by rw [tensorInclusion_toPair]
    _ = (tensorLeftDifferential U R i j n+tensorRightDifferential U R i j n) ≫ tensorToPairTerm U R n :=
      tensorPairTerm_boundary U R i j n h
    _ = (tensorPresheafInclusion R U i j (n+1) h ≫ (tensorPresheafComplex R U).d (n+1) n) ≫ tensorToPairTerm U R n := by rw [hd]
    _ = _ := Category.assoc _ _ _

/-- The standard tensor totalization is the original actual pair presheaf complex, by the specified maps. -/
noncomputable def tensorPairComplexIso : tensorPresheafComplex R U ≅ pairedPresheafComplex U R :=
  HomologicalComplex.Hom.isoOfComponents (tensorPairTermIso U R) (by
    intro i j hij
    have hi : i=j+1 := hij.symm
    subst i
    simpa only [tensorPairTermIso,pairedPresheafComplex,ChainComplex.of_d] using tensorToPair_boundary U R j)

/-- The chain isomorphism retains the already specified original tensor-to-pair component. -/
theorem tensorPairComplexIso_hom (n : ℕ) : (tensorPairComplexIso U R).hom.f n = tensorToPairTerm U R n := rfl

/-- Its inverse retains the already specified original pair-to-tensor component. -/
theorem tensorPairComplexIso_inv (n : ℕ) : (tensorPairComplexIso U R).inv.f n = pairToTensorTerm U R n := rfl

/-- The original diagonal now targets the actual standard Mathlib tensor totalization. -/
noncomputable def tensorPresheafDiagonalMap : presheafComplex U R ⟶ tensorPresheafComplex R U :=
  presheafDiagonalMap U R ≫ (tensorPairComplexIso U R).inv

/-- The native tensor diagonal retains exactly the previously specified original pair diagonal. -/
theorem tensorPresheafDiagonal_toPair :
    tensorPresheafDiagonalMap U R ≫ (tensorPairComplexIso U R).hom = presheafDiagonalMap U R := by
  simp [tensorPresheafDiagonalMap]

end BPFixedPoints.SheafTools.BinaryCells
