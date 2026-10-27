import BPFixedPoints.Incidence.BinaryCoverCellTensor

/-! # Original pure cells in the native tensor totalization

The native bidegree tensor summand maps to its same original pair cells.
Availability and original degrees supply the actual support restriction.
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

@[reducible] noncomputable local instance tensorTermsChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorTermsChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance tensorTermsPairedAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorTermsPairedModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- The original available cell with its original coefficient, in its original degree. -/
noncomputable def cellGenerator (W : Opens T) (n : ℕ) (p : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hd : faceDegree p = n) (r : R) : chains U R W n :=
  ⟨single p r,single_mem_supported R r hp,
    single_mem_supported R r (by change -(faceDegree p : ℤ) = -(n : ℤ); rw [hd])⟩

/-- The original available pair with its original coefficient and summed degree. -/
noncomputable def pairGenerator (W : Opens T) (n : ℕ) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q = n) (r : R) : pairedChains U R W n :=
  ⟨single (p,q) r,single_mem_supported R r ⟨hp,hq,hd⟩⟩

/-- Original cell degree support reads the original overlap dimension. -/
theorem chain_support_degree {W : Opens T} {i : ℕ} (x : chains U R W i)
    (p : V → Fin 3) (hp : p ∈ x.val.support) : faceDegree p = i := by
  have h := x.property.2 hp
  change -(faceDegree p : ℤ) = -(i : ℤ) at h
  omega

private theorem tensor_pair_mem (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (x : chains U R W i) (y : chains U R W j) :
    pairCoordinates R V (x.val ⊗ₜ[R] y.val) ∈ pairedChains U R W n := by
  intro z hz
  have hc := Finsupp.mem_support_iff.mp hz
  rw [show pairCoordinates R V (x.val ⊗ₜ[R] y.val) z = x.val z.1*y.val z.2 from
    finsuppTensorFinsupp'_apply_apply R _ _ x.val y.val z.1 z.2] at hc
  have hx : z.1 ∈ x.val.support := Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hy : z.2 ∈ y.val.support := Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hc)
  exact ⟨x.property.1 hx,y.property.1 hy,(by
    rw [chain_support_degree U R x _ hx,chain_support_degree U R y _ hy,h])⟩

/-- The native tensor summand is sent to the original full pair coordinates and support. -/
noncomputable def tensorPairLinear (W : Opens T) (i j n : ℕ) (h : i+j=n) :
    (chains U R W i ⊗[R] chains U R W j) →ₗ[R] pairedChains U R W n :=
  ((pairCoordinates R V).toLinearMap.comp
    (TensorProduct.map (chains U R W i).subtype (chains U R W j).subtype)).codRestrict _ (by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
      | tmul x y => exact tensor_pair_mem U R W i j n h x y)

/-- The actual bidegree map retains precisely the original pure tensor sections. -/
theorem tensorPairLinear_tmul (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (x : chains U R W i) (y : chains U R W j) :
    (tensorPairLinear U R W i j n h (x ⊗ₜ[R] y)).val = pairCoordinates R V (x.val ⊗ₜ[R] y.val) := rfl

/-- Each original pure generator goes to the same original pair, with the product coefficient. -/
theorem tensorPairLinear_generator (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (p q : V → Fin 3) (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hi : faceDegree p=i) (hj : faceDegree q=j) (r s : R) :
    tensorPairLinear U R W i j n h
      (cellGenerator U R W i p hp hi r ⊗ₜ[R] cellGenerator U R W j q hq hj s) =
      pairGenerator U R W n p q hp hq (by rw [hi,hj,h]) (r*s) := by
  apply Subtype.ext
  change pairCoordinates R V (single p r ⊗ₜ[R] single q s) = single (p,q) (r*s)
  exact finsuppTensorFinsupp'_single_tmul_single R _ _ p q r s

/-- The original bidegree pairing is natural for every original open restriction. -/
noncomputable def tensorPairTerm (i j n : ℕ) (h : i+j=n) :
    presheaf U R i ⊗ presheaf U R j ⟶ pairedPresheaf U R n where
  app W := ModuleCat.ofHom (tensorPairLinear U R W.unop i j n h)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    apply Subtype.ext
    rfl

/-- The native tensor totalization maps to the same original pair term by its actual coproduct property. -/
noncomputable def tensorToPairTerm (n : ℕ) :
    (tensorPresheafComplex R U).X n ⟶ pairedPresheaf U R n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h => tensorPairTerm U R i j n h)

/-- The standard totalization comparison retains every original bidegree inclusion. -/
@[reassoc (attr := simp)] theorem tensorInclusion_toPair (i j n : ℕ) (h : i+j=n) :
    tensorPresheafInclusion R U i j n h ≫ tensorToPairTerm U R n = tensorPairTerm U R i j n h :=
  HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

end BPFixedPoints.SheafTools.BinaryCells
