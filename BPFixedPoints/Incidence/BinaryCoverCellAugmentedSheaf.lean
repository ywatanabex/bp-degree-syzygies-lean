import BPFixedPoints.Incidence.BinaryCoverCellAugmentation
import BPFixedPoints.Incidence.BinaryCoverCellBoundary
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # The original cubical augmentation targets the original terminal free-open sheaf

The tensor component is identified with the terminal free-open presheaf
by its unique original generator. Exact forgetting and sheafification retain
the original augmented degree-zero exactness.
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

/-- The original constant component presheaf, forgetting only its integer module structure. -/
noncomputable abbrev componentAbelianPresheaf :=
  (toAbelianPresheaf (T := T)).obj
    ((Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of ℤ (Components ℤ V)))

/-- The unique original terminal-open generator is the unique original tensor component generator. -/
noncomputable def topComponentEquiv (W : Opens T) :
    FreeAbelianGroup (W ⟶ (⊤ : Opens T)) ≃+ Components ℤ V :=
  ((FreeAbelianGroup.equivFinsupp _).trans (Finsupp.uniqueAddEquiv (homOfLE le_top))).trans
    (Finsupp.uniqueAddEquiv (fun _ : V => (0 : Fin 1))).symm

/-- The specified component equivalence retains the coefficient-one generator. -/
theorem topComponentEquiv_of (W : Opens T) (i : W ⟶ (⊤ : Opens T)) :
    topComponentEquiv (V := V) W (FreeAbelianGroup.of i) = single (fun _ => 0) 1 := by
  have hi : i = homOfLE (show W ≤ ⊤ from le_top) := Subsingleton.elim _ _
  simp [topComponentEquiv,FreeAbelianGroup.equivFinsupp_apply,hi]

/-- The terminal free-open and the original constant component have their original generator-preserving iso. -/
noncomputable def topComponentPresheafIso :
    (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ≅ componentAbelianPresheaf (V := V) (T := T) :=
  NatIso.ofComponents (fun W => (topComponentEquiv (V := V) W.unop).toAddCommGrpIso) (by
    intro W Z f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro i
    change topComponentEquiv (V := V) Z.unop (FreeAbelianGroup.map _ (FreeAbelianGroup.of i)) =
      topComponentEquiv (V := V) W.unop (FreeAbelianGroup.of i)
    rw [FreeAbelianGroup.map_of_apply,topComponentEquiv_of,topComponentEquiv_of])

/-- The original tensor augmentation in the original abelian presheaf category. -/
noncomputable def componentAbelianAugmentation : presheafTerm U 0 ⟶
    componentAbelianPresheaf (V := V) (T := T) :=
  (toAbelianPresheaf (T := T)).map (componentPresheafAugmentation U ℤ)

/-- The original terminal augmentation before sheafification, with its original component coefficient. -/
noncomputable def presheafAugmentation : presheafTerm U 0 ⟶
    (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) :=
  componentAbelianAugmentation U ≫ (topComponentPresheafIso (V := V) (T := T)).inv

/-- The original terminal presheaf augmentation kills the original differential. -/
theorem presheafAugmentation_zero : abelianDifferential U 0 ≫ presheafAugmentation U = 0 := by
  rw [presheafAugmentation,← Category.assoc]
  change ((toAbelianPresheaf (T := T)).map
    (presheafDifferential U ℤ 0) ≫ (toAbelianPresheaf (T := T)).map
      (componentPresheafAugmentation U ℤ)) ≫ _ = 0
  rw [← Functor.map_comp,componentPresheafAugmentation_zero,Functor.map_zero,zero_comp]

/-- The original terminal augmentation is exact in degree zero before sheafification. -/
theorem presheafAugmentation_exact :
    (ShortComplex.mk (abelianDifferential U 0) (presheafAugmentation U)
      (presheafAugmentation_zero U)).Exact := by
  have hs := (componentPresheafAugmentation_exact U ℤ).map (toAbelianPresheaf (T := T))
  apply ShortComplex.exact_of_iso _ hs
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (topComponentPresheafIso (V := V) (T := T)).symm

/-- The original terminal augmentation of the actual original cubical cell sheaf complex. -/
noncomputable def augmentation : sheafTerm U 0 ⟶
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf _ AddCommGrpCat).map (presheafAugmentation U)

/-- The original actual augmentation kills exactly the original actual boundary. -/
theorem augmentation_zero : (sheafComplex U).d 1 0 ≫ augmentation U = 0 := by
  rw [← boundary_eq_d,augmentation,boundary,← Functor.map_comp,
    presheafAugmentation_zero,Functor.map_zero]

/-- Actual degree-zero augmented exactness of the original cubical cell sheaf complex. -/
theorem augmentation_exact :
    (ShortComplex.mk ((sheafComplex U).d 1 0) (augmentation U) (augmentation_zero U)).Exact := by
  have hs := (presheafAugmentation_exact U).map
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat)
  apply ShortComplex.exact_of_iso _ hs
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change (𝟙 _) ≫ (sheafComplex U).d 1 0 = boundary U 0 ≫ 𝟙 _
      simpa only [Category.id_comp,Category.comp_id] using (boundary_eq_d U 0).symm)
    (by simp [augmentation])

end BPFixedPoints.SheafTools.BinaryCells
