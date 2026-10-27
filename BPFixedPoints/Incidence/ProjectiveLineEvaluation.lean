import BPFixedPoints.Incidence.ProjectiveLineTransitionMorphisms

/-! # Evaluation of the original Proj charts in arbitrary coefficient algebras

These are actual scheme morphisms induced by polynomial evaluation. The
overlap identity follows from the already proved original Laurent transition.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- Evaluate an original affine Proj chart at a specified ring element. -/
noncomputable def evaluationChart (f : R →+* A) (a : A) (i : Fin 2) :
    Spec (CommRingCat.of A) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f a)) ≫ chartι R i

/-- Evaluation of a chart commutes with every actual ring map. -/
@[reassoc] theorem evaluationChart_natural (f : R →+* A) (a : A) (i : Fin 2) (g : A →+* B) :
    Spec.map (CommRingCat.ofHom g) ≫ evaluationChart f a i =
      evaluationChart (g.comp f) (g a) i := by
  dsimp only [evaluationChart]
  rw [← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- The evaluated projective point has its original coefficient map. -/
@[reassoc] theorem evaluationChart_toSpecBase (f : R →+* A) (a : A) (i : Fin 2) :
    evaluationChart f a i ≫ toSpecBase R = Spec.map (CommRingCat.ofHom f) := by
  dsimp only [evaluationChart]
  rw [Category.assoc, chartι_toSpecBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  simp

/-- The two original evaluated coordinates define the same actual Proj point on a unit overlap. -/
theorem evaluationChart_unit_transition (f : R →+* A) (u : Aˣ) :
    evaluationChart f (u : A) 0 = evaluationChart f (↑(u⁻¹) : A) 1 := by
  have hl : CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) ≫
      CommRingCat.ofHom (LaurentPolynomial.eval₂ f u) =
      CommRingCat.ofHom (Polynomial.eval₂RingHom f (u : A)) := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  have hr : CommRingCat.ofHom
      (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) :
        Polynomial R →+* LaurentPolynomial R) ≫
      CommRingCat.ofHom (LaurentPolynomial.eval₂ f u) =
      CommRingCat.ofHom (Polynomial.eval₂RingHom f (↑(u⁻¹) : A)) := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  have h := congrArg (fun k => Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫ k)
    (left_right_transition R)
  simpa only [← Spec.map_comp_assoc, hl, hr, evaluationChart] using h

end BPFixedPoints.ProjectiveLine
