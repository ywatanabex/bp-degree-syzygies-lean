import BPFixedPoints.Incidence.BinaryCoverCellTensorInverse

/-! # The original pair terms are the native tensor totalization terms

Both inverse equations retain the actual original cell generators and
Mathlib's native bidegree summand inclusions.
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

@[reducible] noncomputable local instance tensorTermIsoChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorTermIsoChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance tensorTermIsoPairedAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorTermIsoPairedModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- Every actual native summand inclusion has its originally specified pair value. -/
theorem tensorToPair_inclusion_apply (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (x : chains U R W i) (y : chains U R W j) :
    (tensorToPairTerm U R n).app (op W)
      ((tensorPresheafInclusion R U i j n h).app (op W) (x ⊗ₜ[R] y)) =
        tensorPairLinear U R W i j n h (x ⊗ₜ[R] y) :=
  ConcreteCategory.congr_hom (congrArg (fun f => f.app (op W)) (tensorInclusion_toPair U R i j n h)) _

/-- An original pair returns through its original tensor summand to exactly itself. -/
theorem pairToTensor_toPair (n : ℕ) : pairToTensorTerm U R n ≫ tensorToPairTerm U R n = 𝟙 _ := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply pairLinear_ext_one U R W.unop n
  intro p q hp hq hd
  change (tensorToPairTerm U R n).app W
    (pairToTensorLinear U R W.unop n (pairGenerator U R W.unop n p q hp hq hd 1)) = _
  rw [pairToTensorLinear_generator,tensorToPair_inclusion_apply,tensorPairLinear_generator,one_mul]
  rfl

/-- Every original native tensor summand returns through the pair coordinates to exactly itself. -/
theorem tensorToPair_toTensor (n : ℕ) : tensorToPairTerm U R n ≫ pairToTensorTerm U R n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change tensorPresheafInclusion R U i j n h ≫ (tensorToPairTerm U R n ≫ pairToTensorTerm U R n) = _
  rw [← Category.assoc,tensorInclusion_toPair,Category.comp_id]
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  let f := TensorProduct.curry ((pairToTensorLinear U R W.unop n).comp (tensorPairLinear U R W.unop i j n h))
  let g := TensorProduct.curry ((tensorPresheafInclusion R U i j n h).app W).hom
  have he : f = g := by
    apply cellLinear_ext_one U R W.unop i
    intro p hp hi
    apply cellLinear_ext_one U R W.unop j
    intro q hq hj
    change pairToTensorLinear U R W.unop n
      (tensorPairLinear U R W.unop i j n h
        (cellGenerator U R W.unop i p hp hi 1 ⊗ₜ[R] cellGenerator U R W.unop j q hq hj 1)) = _
    rw [tensorPairLinear_generator,pairToTensorLinear_generator]
    subst i
    subst j
    simp only [one_mul]
    rfl
  apply TensorProduct.ext'
  intro x y
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

/-- The standard Mathlib tensor total term is the original actual available-pair presheaf. -/
noncomputable def tensorPairTermIso (n : ℕ) : (tensorPresheafComplex R U).X n ≅ pairedPresheaf U R n where
  hom := tensorToPairTerm U R n
  inv := pairToTensorTerm U R n
  hom_inv_id := tensorToPair_toTensor U R n
  inv_hom_id := pairToTensor_toPair U R n

end BPFixedPoints.SheafTools.BinaryCells
