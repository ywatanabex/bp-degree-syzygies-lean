import BPFixedPoints.Incidence.CechFaces
import BPFixedPoints.Incidence.CechProductMaps
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Section actions and coefficient polynomials on Čech faces

Global exponent shifts become ordinary monomial multiplication on each face.
Exchange coefficient variables and the face-coordinate monoid ring to match
the local Koszul exactness presentation.
-/

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type*) [CommRing R]

theorem faceEquiv_multiply {V : Type*} [Fintype V]
    (q : V → Fin 3) (a b : V → ℕ) (x : C R V) :
    faceEquiv R (multiply R a b x) q =
      AddMonoidAlgebra.single (faceShift q a b) 1 * faceEquiv R x q := by
  have hmap :
      ((LinearMap.proj q).comp (faceEquiv R).toLinearMap).comp (multiply R a b) =
        (LinearMap.mulLeft R (AddMonoidAlgebra.single (faceShift q a b) 1)).comp
          ((LinearMap.proj q).comp (faceEquiv R).toLinearMap) := by
    apply Finsupp.lhom_ext
    intro f r
    obtain ⟨⟨q', m⟩, rfl⟩ := faceBasisEquiv.symm.surjective f
    change faceEquiv R (multiply R a b (single (embedFace q' m) r)) q =
      AddMonoidAlgebra.single (faceShift q a b) 1 *
        faceEquiv R (single (embedFace q' m) r) q
    rw [multiply_single, shift_embedFace]
    by_cases h : q = q'
    · subst q'
      rw [faceEquiv_single_same, faceEquiv_single_same,
        AddMonoidAlgebra.single_mul_single, one_mul, add_comm]
    · rw [faceEquiv_single_ne R h, faceEquiv_single_ne R h, mul_zero]
  exact LinearMap.congr_fun hmap x

/-- Exchange the order of coefficient variables and face coordinates. -/
noncomputable def facePolynomialEquiv (σ : Type*) {V : Type*} (q : V → Fin 3) :
    FaceRing (MvPolynomial σ R) q ≃ₐ[R] MvPolynomial σ (FaceRing R q) :=
  AddMonoidAlgebra.commAlgEquiv R

@[simp] theorem facePolynomialEquiv_single_X (σ : Type*) {V : Type*}
    (q : V → Fin 3) (m : FaceMonoid q) (j : σ) :
    facePolynomialEquiv R σ q (AddMonoidAlgebra.single m (MvPolynomial.X j)) =
      MvPolynomial.C (AddMonoidAlgebra.single m 1) * MvPolynomial.X j := by
  rw [MvPolynomial.C_mul_X_eq_monomial]
  exact AddMonoidAlgebra.commAlgEquiv_single_single (R := R) m (Finsupp.single j 1) (1 : R)

/-- Linear presentation of every face with coefficient polynomials outside. -/
noncomputable def polynomialFaceEquiv (σ : Type*) {V : Type*} [Fintype V] :
    C (MvPolynomial σ R) V ≃ₗ[R]
      ((q : V → Fin 3) → MvPolynomial σ (FaceRing R q)) :=
  ((faceEquiv (MvPolynomial σ R)).restrictScalars R).trans
    (LinearEquiv.piCongrRight fun q => (facePolynomialEquiv R σ q).toLinearEquiv)

@[simp] theorem polynomialFaceEquiv_apply (σ : Type*) {V : Type*} [Fintype V]
    (x : C (MvPolynomial σ R) V) (q : V → Fin 3) :
    polynomialFaceEquiv R σ x q = facePolynomialEquiv R σ q
      (faceEquiv (MvPolynomial σ R) x q) := rfl

theorem polynomialFaceEquiv_X_smul_multiply (σ : Type*) {V : Type*} [Fintype V]
    (q : V → Fin 3) (a b : V → ℕ) (j : σ) (x : C (MvPolynomial σ R) V) :
    polynomialFaceEquiv R σ ((MvPolynomial.X j : MvPolynomial σ R) •
      multiply (MvPolynomial σ R) a b x) q =
      (MvPolynomial.C (AddMonoidAlgebra.single (faceShift q a b) 1) * MvPolynomial.X j) *
        polynomialFaceEquiv R σ x q := by
  rw [polynomialFaceEquiv_apply, map_smul, Pi.smul_apply, faceEquiv_multiply]
  rw [← smul_mul_assoc, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one, map_mul,
    facePolynomialEquiv_single_X, polynomialFaceEquiv_apply]

/-- Decompose the total module with exterior states into facewise Koszul modules. -/
noncomputable def totalFaceEquiv (σ : Type*) (E : Type*) [Fintype E]
    {V : Type*} [Fintype V] :
    (Finset E →₀ C (MvPolynomial σ R) V) ≃ₗ[R]
      ((q : V → Fin 3) → (Finset E →₀ MvPolynomial σ (FaceRing R q))) := by
  classical
  refine
    { toFun := fun x q =>
        (Finsupp.linearEquivFunOnFinite R _ (Finset E)).symm
          (fun S => polynomialFaceEquiv R σ (x S) q)
      invFun := fun y =>
        (Finsupp.linearEquivFunOnFinite R _ (Finset E)).symm
          (fun S => (polynomialFaceEquiv R σ).symm (fun q => y q S))
      left_inv := by
        intro x
        apply Finsupp.ext
        intro S
        exact (polynomialFaceEquiv R σ).symm_apply_apply (x S)
      right_inv := by
        intro y
        funext q
        apply Finsupp.ext
        intro S
        exact congrFun ((polynomialFaceEquiv R σ).apply_symm_apply (fun q => y q S)) q
      map_add' := by
        intro x y
        funext q
        apply Finsupp.ext
        intro S
        exact congrFun ((polynomialFaceEquiv R σ).map_add (x S) (y S)) q
      map_smul' := by
        intro a x
        funext q
        apply Finsupp.ext
        intro S
        exact congrFun ((polynomialFaceEquiv R σ).map_smul a (x S)) q }

@[simp] theorem totalFaceEquiv_apply (σ : Type*) (E : Type*) [Fintype E]
    {V : Type*} [Fintype V] (x : Finset E →₀ C (MvPolynomial σ R) V)
    (q : V → Fin 3) (S : Finset E) :
    totalFaceEquiv R σ E x q S = polynomialFaceEquiv R σ (x S) q := rfl

@[simp] theorem totalFaceEquiv_symm_apply (σ : Type*) (E : Type*) [Fintype E]
    {V : Type*} [Fintype V]
    (y : (q : V → Fin 3) → (Finset E →₀ MvPolynomial σ (FaceRing R q))) (S : Finset E) :
    (totalFaceEquiv R σ E).symm y S = (polynomialFaceEquiv R σ).symm (fun q => y q S) := rfl

@[simp] theorem totalFaceEquiv_single (σ : Type*) (E : Type*) [Fintype E]
    {V : Type*} [Fintype V] (S : Finset E) (x : C (MvPolynomial σ R) V)
    (q : V → Fin 3) :
    totalFaceEquiv R σ E (single S x) q = single S (polynomialFaceEquiv R σ x q) := by
  classical
  ext T
  by_cases h : T = S
  · subst T; simp
  · simp [Finsupp.single_eq_of_ne h]

end BPFixedPoints.CechProduct
