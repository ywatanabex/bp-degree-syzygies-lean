import BPFixedPoints.Incidence.ProjectiveLineOverBase
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Properness of the actual projective line over its original coefficient ring

The degree-zero homogeneous ring is the original coefficient ring. The Cox
polynomial algebra is finite type over it, so Mathlib's actual Proj properness
theorem applies to the original structural morphism.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The original two-variable Cox algebra is finite type over its genuine degree-zero ring. -/
instance coxFiniteTypeOverZero : Algebra.FiniteType (grading R 0) (CoxRing R) := by
  let f : MvPolynomial (Fin 2) (grading R 0) →ₐ[grading R 0] CoxRing R := aeval X
  have he : f.toRingHom = MvPolynomial.map (constantsEquiv R).symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [f, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, map_C]
      change r.val = C ((constantsEquiv R).symm r)
      exact (congrArg Subtype.val ((constantsEquiv R).apply_symm_apply r)).symm
    · intro i
      simp [f]
  have hs : Function.Surjective f := by
    change Function.Surjective f.toRingHom
    rw [he]
    exact MvPolynomial.map_surjective (constantsEquiv R).symm.toRingHom
      (constantsEquiv R).symm.surjective
  exact Algebra.FiniteType.of_surjective f hs

/-- The actual Proj line is proper over the original coefficient scheme. -/
instance toSpecBase_isProper : IsProper (toSpecBase R) := by
  have hc : CommRingCat.ofHom (constantsToZero R) = (constantsEquiv R).toCommRingCatIso.hom := rfl
  dsimp only [toSpecBase]
  rw [hc]
  infer_instance

end BPFixedPoints.ProjectiveLine
