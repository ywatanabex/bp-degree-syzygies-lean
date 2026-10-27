import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Identifying a coefficient base change with the actual quotient ring -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {T S U : Type*} [CommRing T] [CommRing S] [CommRing U]
  [Algebra T S] [Algebra S U] [Algebra T U] [IsScalarTower T S U]

noncomputable def tensorParameterQuotient (I : Ideal T) :
    ((S ⊗[T] (T ⧸ I)) ⊗[S] U) ≃+* (U ⧸ I.map (algebraMap T U)) :=
  (Algebra.TensorProduct.comm S (S ⊗[T] (T ⧸ I)) U).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange T S S U (T ⧸ I)).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot U I).symm.toRingEquiv)

/-- The comparison uses the original coefficient and parameter actions on the quotient. -/
@[simp] theorem tensorParameterQuotient_tmul (I : Ideal T) (s : S) (t : T) (u : U) :
    tensorParameterQuotient (S := S) (U := U) I
      ((s ⊗ₜ[T] Ideal.Quotient.mk I t) ⊗ₜ[S] u) =
      Ideal.Quotient.mk (I.map (algebraMap T U))
        (algebraMap T U t * (algebraMap S U s * u)) := by
  simp only [tensorParameterQuotient, RingEquiv.trans_apply,
    AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, Algebra.smul_def]
  rfl

end BPFixedPoints.ResolutionTools
