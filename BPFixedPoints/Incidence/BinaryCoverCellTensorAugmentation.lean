import BPFixedPoints.Incidence.BinaryCoverCellTensorComplexIso
import BPFixedPoints.Incidence.BinaryCoverCellDiagonalSheaf

/-! # The standard tensor totalization retains the original augmentation

The native total augmentation is defined directly from the original two
component augmentations, before comparing with the original pair model.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open CechCubicalCell
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance tensorAugmentationChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorAugmentationChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module

/-- The tensor of the original two component augmentations on the original bidegree-zero summand. -/
noncomputable def tensorComponentPairMap : presheaf U R 0 ⊗ presheaf U R 0 ⟶
    (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of R (Components R V ⊗[R] Components R V)) where
  app W := ModuleCat.ofHom (TensorProduct.map (componentAugmentation U R W.unop) (componentAugmentation U R W.unop))
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl

/-- The actual standard total augmentation is its native coproduct descent from the original augmentations. -/
noncomputable def tensorComponentPresheafAugmentation : (tensorPresheafComplex R U).X 0 ⟶
    (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of R (Components R V ⊗[R] Components R V)) :=
  HomologicalComplex.mapBifunctorDesc (fun i j h => by
    change i+j=0 at h
    have hi : i=0 := by omega
    have hj : j=0 := by omega
    subst i; subst j
    exact tensorComponentPairMap U R)

/-- The specified tensor-to-pair comparison retains the actual original total augmentation. -/
theorem tensorToPair_augmentation :
    tensorToPairTerm U R 0 ≫ pairedComponentPresheafAugmentation U R = tensorComponentPresheafAugmentation U R := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change i+j=0 at h
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  rw [← Category.assoc,tensorInclusion_toPair]
  change tensorPairTerm U R 0 0 0 h ≫ pairedComponentPresheafAugmentation U R =
    tensorPresheafInclusion R U 0 0 0 h ≫ tensorComponentPresheafAugmentation U R
  rw [tensorComponentPresheafAugmentation,HomologicalComplex.ι_mapBifunctorDesc]
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change TensorProduct.map (CechCubicalCell.contraction R (fun _ : V => 0)).p
    (CechCubicalCell.contraction R (fun _ : V => 0)).p
      ((pairCoordinates R V).symm (pairCoordinates R V (x.val ⊗ₜ[R] y.val))) =
        (CechCubicalCell.contraction R (fun _ : V => 0)).p x.val ⊗ₜ[R]
          (CechCubicalCell.contraction R (fun _ : V => 0)).p y.val
  rw [LinearEquiv.symm_apply_apply,TensorProduct.map_tmul]

/-- The original native standard augmentation kills the actual standard degree-one boundary. -/
theorem tensorComponentPresheafAugmentation_zero :
    (tensorPresheafComplex R U).d 1 0 ≫ tensorComponentPresheafAugmentation U R = 0 := by
  have hp : pairedPresheafDifferential U R 0 ≫ pairedComponentPresheafAugmentation U R = 0 := by
    apply NatTrans.ext
    funext W
    exact ModuleCat.hom_ext (pairedComponentAugmentation_boundary U R W.unop)
  rw [← tensorToPair_augmentation,← Category.assoc,← tensorToPair_boundary U R 0,Category.assoc,hp,comp_zero]

/-- The original diagonal preserves the independently specified original standard total augmentation. -/
theorem tensorPresheafDiagonal_augmentation :
    (tensorPresheafDiagonalMap U R).f 0 ≫ tensorComponentPresheafAugmentation U R =
      componentPresheafAugmentation U R ≫
        (Functor.const (Opens T)ᵒᵖ).map (ModuleCat.ofHom (componentDiagonal R (V := V))) := by
  have h := congrArg (fun f => f.f 0) (tensorPresheafDiagonal_toPair U R)
  change (tensorPresheafDiagonalMap U R).f 0 ≫ tensorToPairTerm U R 0 = presheafDiagonal U R 0 at h
  rw [← tensorToPair_augmentation,← Category.assoc,h,presheafDiagonal_augmentation]

end BPFixedPoints.SheafTools.BinaryCells
