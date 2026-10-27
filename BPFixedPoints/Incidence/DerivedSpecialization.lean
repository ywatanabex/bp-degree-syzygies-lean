import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Maps

/-!
# Computing the actual derived specialization of a minimal resolution

This file works with Mathlib's left derived functor of extension of
scalars. It does not define a Tor group by a proposed dimension formula.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

section Tensor

variable {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
  {M : Type u} [AddCommGroup M] [Module R M]

/-- Tensors with an element in the augmentation ideal times a module vanish. -/
theorem tmul_eq_zero_of_mem_augmentation {x : M}
    (hx : x ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M)) (c : k) :
    c ⊗ₜ[R] x = 0 := by
  have hle : RingHom.ker (algebraMap R k) • (⊤ : Submodule R M) ≤
      LinearMap.ker (TensorProduct.mk R k M c) := by
    refine Submodule.smul_le.mpr ?_
    intro a ha y hy
    change c ⊗ₜ[R] (a • y) = 0
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, RingHom.mem_ker.mp ha,
      zero_mul, TensorProduct.zero_tmul]
  exact hle hx

end Tensor

section Modules

variable {R k : Type u} [CommRing R] [CommRing k]

/-- Extension of scalars is additive, proved on pure tensors. -/
instance extendScalars_additive (f : R →+* k) : (ModuleCat.extendScalars f).Additive where
  map_add := by
    intros M N g h
    letI : Algebra R k := f.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : k) ⊗ₜ[R] (g x + h x) =
      (1 : k) ⊗ₜ[R] g x + (1 : k) ⊗ₜ[R] h x
    exact TensorProduct.tmul_add _ _ _

/-- Specializing a map whose image is in the coefficient kernel gives zero. -/
theorem extendScalars_map_eq_zero (f : R →+* k) {M N : ModuleCat.{u} R}
    (d : M ⟶ N)
    (hd : LinearMap.range d.hom ≤ RingHom.ker f • (⊤ : Submodule R N)) :
    (ModuleCat.extendScalars f).map d = 0 := by
  letI : Algebra R k := f.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (1 : k) ⊗ₜ[R] d x = 0
  exact tmul_eq_zero_of_mem_augmentation (hd ⟨x, rfl⟩) 1

end Modules

section Homology

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}

/-- If both differentials at a degree are zero, its actual homology is the term. -/
noncomputable def homologyIsoTermOfZeroDifferentials (K : HomologicalComplex C c)
    (hD : ∀ i j, K.d i j = 0) (n : ι) : K.homology n ≅ K.X n := by
  change (K.sc n).homology ≅ K.X n
  exact (ShortComplex.LeftHomologyData.ofZeros (K.sc n) (hD _ _) (hD _ _)).homologyIso

end Homology

section Derived

variable {R k : Type u} [CommRing R] [CommRing k]

/-- The actual derived scalar extension, computed from a projective resolution
whose differentials have image in the coefficient kernel. -/
noncomputable def derivedSpecializationIsoTerm (f : R →+* k)
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M)
    (hminimal : ∀ i j, LinearMap.range (P.complex.d i j).hom ≤
      RingHom.ker f • (⊤ : Submodule R (P.complex.X j))) (n : ℕ) :
    ((ModuleCat.extendScalars f).leftDerived n).obj M ≅
      (ModuleCat.extendScalars f).obj (P.complex.X n) := by
  let F := ModuleCat.extendScalars f
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hK : ∀ i j, K.d i j = 0 := fun i j =>
    extendScalars_map_eq_zero f (P.complex.d i j) (hminimal i j)
  exact (P.isoLeftDerivedObj F n) ≪≫ homologyIsoTermOfZeroDifferentials K hK n

end Derived

end BPFixedPoints.ResolutionTools
