import BPFixedPoints.Incidence.TensorParameterQuotient
import BPFixedPoints.Incidence.GradedBaseChangeFree
import BPFixedPoints.Incidence.HomogeneousQuotient

/-! # Natural quotient components of the module resolved after a parameter cut -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k T S U : Type*} [Field k] [CommRing T] [CommRing S] [CommRing U]
  [Algebra k S] [Algebra k U] [Algebra T S] [Algebra S U] [Algebra T U]
  [IsScalarTower T S U] [IsScalarTower k S U]

/-- The standard ground-field action on the iterated tensor ring. -/
@[instance_reducible] noncomputable def tensorParameterQuotientGroundAlgebra (I : Ideal T) :
    Algebra k ((S ⊗[T] (T ⧸ I)) ⊗[S] U) := inferInstance

/-- The standard quotient module over the ground field. -/
@[instance_reducible] noncomputable def parameterQuotientGroundModule (I : Ideal T) :
    Module k (U ⧸ I.map (algebraMap T U)) := inferInstance

/-- The existing ring comparison also preserves the original ground-field action. -/
noncomputable def tensorParameterQuotientAlgEquiv (I : Ideal T) :
    ((S ⊗[T] (T ⧸ I)) ⊗[S] U) ≃ₐ[k] (U ⧸ I.map (algebraMap T U)) :=
  { tensorParameterQuotient (S := S) (U := U) I with
    commutes' := fun c => by
      change tensorParameterQuotient (S := S) (U := U) I
        ((algebraMap k S c ⊗ₜ[T] (Ideal.Quotient.mk I 1)) ⊗ₜ[S] (1 : U)) = _
      rw [tensorParameterQuotient_tmul]
      simp only [map_one, one_mul, mul_one, ← IsScalarTower.algebraMap_apply k S U]
      rfl }

@[simp] theorem tensorParameterQuotientAlgEquiv_unit (I : Ideal T) (u : U) :
    tensorParameterQuotientAlgEquiv (k := k) (S := S) (U := U) I
      ((1 : S ⊗[T] (T ⧸ I)) ⊗ₜ[S] u) = Ideal.Quotient.mk (I.map (algebraMap T U)) u := by
  change tensorParameterQuotient (S := S) (U := U) I
    (((1 : S) ⊗ₜ[T] (Ideal.Quotient.mk I 1)) ⊗ₜ[S] u) = _
  rw [tensorParameterQuotient_tmul]
  simp

/-- Images of the old homogeneous components are exactly the actual quotient components. -/
theorem tensorParameterQuotient_piece (I : Ideal T) (𝒜 : ℕ → Submodule k U) (q : ℕ) :
    ((𝒜 q).map ((TensorProduct.mk S (S ⊗[T] (T ⧸ I)) U 1).restrictScalars k)).map
      (tensorParameterQuotientAlgEquiv (k := k) (S := S) (U := U) I).toLinearMap =
        gradedQuotientPiece 𝒜 (I.map (algebraMap T U)) q := by
  rw [← Submodule.map_comp, gradedQuotientPiece]
  congr 1
  ext u
  exact tensorParameterQuotientAlgEquiv_unit (k := k) (S := S) I u

end BPFixedPoints.ResolutionTools
