import BPFixedPoints.Incidence.CechFaceMaps
import BPFixedPoints.Incidence.KoszulSigns

/-! # Parity action on each Čech face -/

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type*) [CommRing R] (σ : Type*)
  {V : Type*} [Fintype V]

theorem polynomialFaceEquiv_sign (d : V → ℕ) (q : V → Fin 3)
    (x : C (MvPolynomial σ R) V) :
    polynomialFaceEquiv R σ ((contraction (MvPolynomial σ R) d).sign x) q =
      (-1 : R) ^ faceDegree q • polynomialFaceEquiv R σ x q := by
  let F : C (MvPolynomial σ R) V →ₗ[R] MvPolynomial σ (FaceRing R q) :=
    (LinearMap.proj q).comp (polynomialFaceEquiv R σ).toLinearMap
  have hh : F.comp ((contraction (MvPolynomial σ R) d).sign.restrictScalars R) =
      (-1 : R) ^ faceDegree q • F := by
    apply Finsupp.lhom_ext
    intro b r
    change F ((contraction (MvPolynomial σ R) d).sign (single b r)) =
      (-1 : R) ^ faceDegree q • F (single b r)
    rw [contraction_sign_single]
    have he := Koszul.map_neg_one_pow_smul (R := MvPolynomial σ R) (A := R)
      F.toAddMonoidHom (cechDegree b) (single b r)
    change F ((-1 : MvPolynomial σ R) ^ cechDegree b • single b r) =
      (-1 : R) ^ cechDegree b • F (single b r) at he
    rw [he]
    obtain ⟨⟨q', m⟩, rfl⟩ := faceBasisEquiv.symm.surjective b
    change (-1 : R) ^ cechDegree (embedFace q' m) • F (single (embedFace q' m) r) =
      (-1 : R) ^ faceDegree q • F (single (embedFace q' m) r)
    by_cases h : q = q'
    · subst q'
      rw [cechDegree_embedFace]
    · have hz : F (single (embedFace q' m) r) = 0 := by
        simp [F, polynomialFaceEquiv_apply, faceEquiv_single_ne _ h]
      rw [hz, smul_zero, smul_zero]
  exact LinearMap.congr_fun hh x

end BPFixedPoints.CechProduct
