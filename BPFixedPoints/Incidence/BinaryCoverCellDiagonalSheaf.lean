import BPFixedPoints.Incidence.BinaryCoverCellDiagonal
import BPFixedPoints.Incidence.CechCubicalCellDiagonalAugmentation
import BPFixedPoints.Incidence.BinaryCoverCellAugmentedSheaf

/-! # The specified diagonal in the actual abelian sheaf category

The original integer module maps are forgotten and sheafified by the same
native functors as the actual cell resolution. Its specified diagonal
retains the original terminal augmentation through the original component
identification. A comparison with a derived tensor cup remains separate.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp
open CechCubicalCell GradedContraction
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- The actual pair complex uses the tensor of its original two component augmentations. -/
noncomputable def pairedComponentAugmentation (W : Opens T) :
    pairedChains U R W 0 →ₗ[R] Components R V ⊗[R] Components R V :=
  ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).p.comp
    ((pairCoordinates R V).symm.toLinearMap.comp (pairedChains U R W 0).subtype)

/-- The original tensor component augmentation kills the original actual pair boundary. -/
theorem pairedComponentAugmentation_boundary (W : Opens T) :
    (pairedComponentAugmentation U R W).comp (pairedDifferential U R W 0) = 0 := by
  apply LinearMap.ext
  intro x
  change ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).p
    ((pairCoordinates R V).symm (pairBoundary R V x.val)) = 0
  rw [pairBoundary_apply,LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun
    ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).p_d _

/-- The actual open diagonal retains the original native component augmentation. -/
theorem openDiagonal_augmentation (W : Opens T) :
    (pairedComponentAugmentation U R W).comp (openDiagonal U R W 0) =
      (componentDiagonal R).comp (componentAugmentation U R W) := by
  apply LinearMap.ext
  intro x
  change TensorProduct.map (contraction R (fun _ : V => 0)).p (contraction R (fun _ : V => 0)).p
    ((pairCoordinates R V).symm (pairCoordinates R V ((CechCubicalCell.diagonal R V).map x.val))) =
      componentDiagonal R ((contraction R (fun _ : V => 0)).p x.val)
  rw [LinearEquiv.symm_apply_apply]
  exact diagonal_augmentation R x.val x.property.2

/-- The same tensor component augmentation is natural for the original open restrictions. -/
noncomputable def pairedComponentPresheafAugmentation : pairedPresheaf U R 0 ⟶
    (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of R (Components R V ⊗[R] Components R V)) where
  app W := ModuleCat.ofHom (pairedComponentAugmentation U R W.unop)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The original presheaf augmentation diagram is the diagram of the specified original maps. -/
theorem presheafDiagonal_augmentation :
    presheafDiagonal U R 0 ≫ pairedComponentPresheafAugmentation U R =
      componentPresheafAugmentation U R ≫
        (Functor.const (Opens T)ᵒᵖ).map (ModuleCat.ofHom (componentDiagonal R (V := V))) := by
  apply NatTrans.ext
  funext W
  exact ModuleCat.hom_ext (openDiagonal_augmentation U R W.unop)

variable {R}

/-- Forget only the integer module structure in the original total pair complex. -/
noncomputable def pairedAbelianPresheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  ((toAbelianPresheaf (T := T)).mapHomologicalComplex _).obj (pairedPresheafComplex U ℤ)

/-- The original total pair complex in the same actual abelian sheaf category as actual Ext. -/
noncomputable def pairedSheafComplex : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    (pairedAbelianPresheafComplex U)

/-- The specified original diagonal is an actual chain map of the original abelian sheaf complexes. -/
noncomputable def sheafDiagonalMap : sheafComplex U ⟶ pairedSheafComplex U :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).map
    (((toAbelianPresheaf (T := T)).mapHomologicalComplex _).map (presheafDiagonalMap U ℤ))

/-- Every actual sheaf component is exactly the original forgotten and sheafified diagonal. -/
theorem sheafDiagonalMap_component (n : ℕ) :
    (sheafDiagonalMap U).f n = (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
      ((toAbelianPresheaf (T := T)).map (presheafDiagonal U ℤ n)) := rfl

/-- The original pair component target, with only the integer module structure forgotten. -/
noncomputable abbrev pairedComponentAbelianPresheaf :=
  (toAbelianPresheaf (T := T)).obj
    ((Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of ℤ (Components ℤ V ⊗[ℤ] Components ℤ V)))

/-- The original tensor component augmentation after the native forgetting functor. -/
noncomputable def pairedComponentAbelianAugmentation : (pairedAbelianPresheafComplex U).X 0 ⟶
    pairedComponentAbelianPresheaf (V := V) (T := T) :=
  (toAbelianPresheaf (T := T)).map (pairedComponentPresheafAugmentation U ℤ)

/-- The original terminal generator identification followed by the original component diagonal. -/
noncomputable def terminalComponentDiagonal : (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶
    pairedComponentAbelianPresheaf (V := V) (T := T) :=
  (topComponentPresheafIso (V := V) (T := T)).hom ≫
    (toAbelianPresheaf (T := T)).map
      ((Functor.const (Opens T)ᵒᵖ).map (ModuleCat.ofHom (componentDiagonal ℤ (V := V))))

/-- The specified original diagonal preserves the original terminal augmentation before sheafification. -/
theorem terminalDiagonal_augmentation :
    (toAbelianPresheaf (T := T)).map (presheafDiagonal U ℤ 0) ≫ pairedComponentAbelianAugmentation U =
      presheafAugmentation U ≫ terminalComponentDiagonal (V := V) (T := T) := by
  unfold presheafAugmentation terminalComponentDiagonal componentAbelianAugmentation pairedComponentAbelianAugmentation
  rw [Category.assoc,Iso.inv_hom_id_assoc,← Functor.map_comp,← Functor.map_comp,presheafDiagonal_augmentation]

/-- The actual original diagonal preserves the original actual terminal augmentation. -/
theorem sheafDiagonal_augmentation :
    (sheafDiagonalMap U).f 0 ≫ (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
      (pairedComponentAbelianAugmentation U) = augmentation U ≫
        (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
          (terminalComponentDiagonal (V := V) (T := T)) := by
  rw [sheafDiagonalMap_component,augmentation,← Functor.map_comp,← Functor.map_comp,terminalDiagonal_augmentation]

end BPFixedPoints.SheafTools.BinaryCells
