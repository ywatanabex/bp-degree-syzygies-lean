import BPFixedPoints.Incidence.KoszulTransport

/-!
# Koszul contraction for independent affine equations

Use the triangular transformation adding a polynomial in nonpivot variables
to each pivot. The coefficient ring is arbitrary and may be a Čech face's
Laurent coordinate ring.
-/

namespace BPFixedPoints.Koszul

open MvPolynomial

variable {E J R : Type*} [CommRing R]

/-- Algebra homomorphism adding nonpivot polynomials to pivots. -/
noncomputable def triangularHom (r : E → MvPolynomial J R) :
    MvPolynomial (E ⊕ J) R →ₐ[R] MvPolynomial (E ⊕ J) R :=
  aeval (Sum.elim (fun e => X (Sum.inl e) + rename Sum.inr (r e))
    (fun j => X (Sum.inr j)))

@[simp] theorem triangularHom_X_inl (r : E → MvPolynomial J R) (e : E) :
    triangularHom r (X (Sum.inl e)) = X (Sum.inl e) + rename Sum.inr (r e) := by
  simp [triangularHom]

@[simp] theorem triangularHom_X_inr (r : E → MvPolynomial J R) (j : J) :
    triangularHom r (X (Sum.inr j)) = X (Sum.inr j) := by
  simp [triangularHom]

@[simp] theorem triangularHom_rename (r : E → MvPolynomial J R) (p : MvPolynomial J R) :
    triangularHom r (rename Sum.inr p) = rename Sum.inr p := by
  have h : (triangularHom r).comp (rename Sum.inr) = rename Sum.inr := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact AlgHom.congr_fun h p

theorem triangularHom_comp_neg (r : E → MvPolynomial J R) :
    (triangularHom r).comp (triangularHom (fun e => -r e)) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with e | j <;> simp

theorem triangularHom_neg_comp (r : E → MvPolynomial J R) :
    (triangularHom (fun e => -r e)).comp (triangularHom r) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with e | j <;> simp

/-- Independent triangular changes of pivot variables. -/
noncomputable def triangularEquiv (r : E → MvPolynomial J R) :
    MvPolynomial (E ⊕ J) R ≃ₐ[R] MvPolynomial (E ⊕ J) R :=
  AlgEquiv.ofAlgHom (triangularHom r) (triangularHom (fun e => -r e))
    (triangularHom_comp_neg r) (triangularHom_neg_comp r)

@[simp] theorem triangularEquiv_X_inl (r : E → MvPolynomial J R) (e : E) :
    triangularEquiv r (X (Sum.inl e)) = X (Sum.inl e) + rename Sum.inr (r e) :=
  triangularHom_X_inl r e

@[simp] theorem triangularEquiv_X_inr (r : E → MvPolynomial J R) (j : J) :
    triangularEquiv r (X (Sum.inr j)) = X (Sum.inr j) := triangularHom_X_inr r j

section Contraction

variable [LinearOrder E] [Fintype E] [DecidableEq J]

/-- Contraction to the quotient by affine equations. -/
noncomputable def affineContraction (r : E → MvPolynomial J R) :
    IncidencePerturbation.Contraction R (Space E (MvPolynomial (E ⊕ J) R))
      (MvPolynomial (E ⊕ J) R ⧸ transportedIdeal Sum.inl (triangularEquiv r)) :=
  transportedContraction Sum.inl Sum.inl_injective (triangularEquiv r)

theorem affineContraction_d (r : E → MvPolynomial J R) :
    (affineContraction r).d =
      (differential (fun e => X (Sum.inl e) + rename Sum.inr (r e))).restrictScalars R := by
  rw [affineContraction, transportedContraction_d]
  simp

theorem affineContraction_p (r : E → MvPolynomial J R)
    (x : Space E (MvPolynomial (E ⊕ J) R)) :
    (affineContraction r).p x =
      Ideal.Quotient.mk (transportedIdeal Sum.inl (triangularEquiv r)) (x ∅) :=
  transportedContraction_p _ _ _ x

end Contraction

end BPFixedPoints.Koszul
