import BPFixedPoints.Incidence.BinaryCoverCellTensorBasis

/-! # Return original face pairs to the native tensor totalization

Each original pair is inserted into its original bidegree by Mathlib's
native tensor summand inclusion. All original open restrictions are retained.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance tensorInverseChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorInverseChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance tensorInversePairedAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorInversePairedModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- Put the original pair in its original bidegree, with both original pure generators. -/
noncomputable def pairToTensorLinear (W : Opens T) (n : ℕ) :
    pairedChains U R W n →ₗ[R] (((tensorPresheafComplex R U).X n).obj (op W)) :=
  (Finsupp.llift _ R R _ fun z : PairCellIndex U W n =>
    (tensorPresheafInclusion R U (faceDegree z.val.1) (faceDegree z.val.2) n z.property.2.2).app (op W)
      (cellGenerator U R W _ z.val.1 z.property.1 rfl 1 ⊗ₜ[R]
        cellGenerator U R W _ z.val.2 z.property.2.1 rfl 1)).comp
          (pairCellCoordinates U R W n).toLinearMap

/-- Returning an original pair preserves the actual native summand and coefficient. -/
theorem pairToTensorLinear_generator (W : Opens T) (n : ℕ) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q=n) (r : R) :
    pairToTensorLinear U R W n (pairGenerator U R W n p q hp hq hd r) =
      (tensorPresheafInclusion R U (faceDegree p) (faceDegree q) n hd).app (op W)
        (cellGenerator U R W _ p hp rfl 1 ⊗ₜ[R] cellGenerator U R W _ q hq rfl r) := by
  let z : PairCellIndex U W n := ⟨(p,q),hp,hq,hd⟩
  rw [← pairCellCoordinates_generator U R W n z r]
  simp only [pairToTensorLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    Finsupp.llift_apply,Finsupp.lift_apply,Finsupp.sum_single_index,zero_smul]
  have hs : cellGenerator U R W (faceDegree q) q hq rfl r =
      r • cellGenerator U R W (faceDegree q) q hq rfl 1 := by
    apply Subtype.ext
    simp [cellGenerator]
  rw [hs,TensorProduct.tmul_smul,map_smul]

/-- The actual inverse term map is natural for every original open restriction. -/
noncomputable def pairToTensorTerm (n : ℕ) : pairedPresheaf U R n ⟶ (tensorPresheafComplex R U).X n where
  app W := ModuleCat.ofHom (pairToTensorLinear U R W.unop n)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply pairLinear_ext U R W.unop n
    intro p q hp hq hd r
    change pairToTensorLinear U R Z.unop n
      (pairGenerator U R Z.unop n p q ((leOfHom f.unop).trans hp) ((leOfHom f.unop).trans hq) hd r) =
        ((tensorPresheafComplex R U).X n).map f
          (pairToTensorLinear U R W.unop n (pairGenerator U R W.unop n p q hp hq hd r))
    rw [pairToTensorLinear_generator,pairToTensorLinear_generator]
    exact ConcreteCategory.congr_hom
      ((tensorPresheafInclusion R U (faceDegree p) (faceDegree q) n hd).naturality f)
        (cellGenerator U R W.unop _ p hp rfl 1 ⊗ₜ[R] cellGenerator U R W.unop _ q hq rfl r)

end BPFixedPoints.SheafTools.BinaryCells
