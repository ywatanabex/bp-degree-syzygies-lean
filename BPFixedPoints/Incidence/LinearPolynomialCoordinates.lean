import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Polynomial coordinates extending an independent family of linear forms -/

namespace BPFixedPoints.ResolutionTools

open Module MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k σ ι : Type*} [Field k] {v : ι → (σ →₀ k)}

theorem basis_sumExtend_inl (hv : LinearIndependent k v) (i : ι) :
    Basis.sumExtend hv (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Basis.reindex_apply, Basis.extend_apply_self]
  rfl

/-- The linear form associated to its coefficient vector. -/
noncomputable def polynomialLinearForm (x : σ →₀ k) : MvPolynomial σ k :=
  Finsupp.linearCombination k X x

theorem symmetricPolynomial_coordinates (x : σ →₀ k) :
    SymmetricAlgebra.equivMvPolynomial (Finsupp.basisSingleOne : Basis σ k (σ →₀ k))
      (SymmetricAlgebra.ι k (σ →₀ k) x) = polynomialLinearForm x := by
  simp [SymmetricAlgebra.equivMvPolynomial, polynomialLinearForm, Basis.constr_apply,
    Finsupp.linearCombination_apply]

/-- Extend the selected coefficient vectors to a basis, then take symmetric algebras. -/
noncomputable def linearPolynomialSumEquiv (hv : LinearIndependent k v) :
    MvPolynomial (ι ⊕ Basis.sumExtendIndex hv) k ≃ₐ[k] MvPolynomial σ k :=
  (SymmetricAlgebra.equivMvPolynomial (Basis.sumExtend hv)).symm.trans
    (SymmetricAlgebra.equivMvPolynomial Finsupp.basisSingleOne)

@[simp] theorem linearPolynomialSumEquiv_X_inl (hv : LinearIndependent k v) (i : ι) :
    linearPolynomialSumEquiv hv (X (Sum.inl i)) = polynomialLinearForm (v i) := by
  simp only [linearPolynomialSumEquiv, AlgEquiv.trans_apply,
    SymmetricAlgebra.equivMvPolynomial_symm_X, basis_sumExtend_inl]
  exact symmetricPolynomial_coordinates _

/-- In these coordinates the selected forms are coefficient variables. -/
noncomputable def linearPolynomialIterEquiv (hv : LinearIndependent k v) :
    MvPolynomial σ k ≃ₐ[k] MvPolynomial (Basis.sumExtendIndex hv) (MvPolynomial ι k) :=
  (linearPolynomialSumEquiv hv).symm.trans
    ((renameEquiv k (Equiv.sumComm _ _)).trans (sumAlgEquiv k _ _))

@[simp] theorem linearPolynomialIterEquiv_form (hv : LinearIndependent k v) (i : ι) :
    linearPolynomialIterEquiv hv (polynomialLinearForm (v i)) = C (X i) := by
  unfold linearPolynomialIterEquiv
  simp only [AlgEquiv.trans_apply]
  rw [← linearPolynomialSumEquiv_X_inl hv i, AlgEquiv.symm_apply_apply]
  simp

/-- The actual action of the selected forms, before any coordinate change. -/
@[instance_reducible] noncomputable def linearPolynomialAlgebra (v : ι → (σ →₀ k)) :
    Algebra (MvPolynomial ι k) (MvPolynomial σ k) :=
  (aeval (polynomialLinearForm ∘ v)).toRingHom.toAlgebra

/-- The coordinate change respects the specified parameter algebra. -/
noncomputable def linearPolynomialParameterEquiv (hv : LinearIndependent k v) :
    letI := linearPolynomialAlgebra v
    MvPolynomial σ k ≃ₐ[MvPolynomial ι k]
      MvPolynomial (Basis.sumExtendIndex hv) (MvPolynomial ι k) := by
  letI := linearPolynomialAlgebra v
  let e := linearPolynomialIterEquiv hv
  have he : e.toAlgHom.comp (aeval (polynomialLinearForm ∘ v)) =
      IsScalarTower.toAlgHom k (MvPolynomial ι k)
        (MvPolynomial (Basis.sumExtendIndex hv) (MvPolynomial ι k)) := by
    ext i
    simp [e]
  exact { e.toRingEquiv with commutes' := fun t => DFunLike.congr_fun he t }

/-- A polynomial ring is free over any independent family of linear parameters. -/
theorem free_over_linear_parameters (hv : LinearIndependent k v) :
    letI := linearPolynomialAlgebra v
    Module.Free (MvPolynomial ι k) (MvPolynomial σ k) := by
  letI := linearPolynomialAlgebra v
  exact Module.Free.of_equiv (linearPolynomialParameterEquiv hv).symm.toLinearEquiv

end BPFixedPoints.ResolutionTools
