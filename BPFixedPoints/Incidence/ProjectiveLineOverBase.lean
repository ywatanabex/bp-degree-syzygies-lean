import BPFixedPoints.Incidence.ProjectiveLineGeometry
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Over

/-! # The actual projective line over its original coefficient scheme

The structural morphism is Mathlib's Proj-to-degree-zero morphism followed by
the original coefficient inclusion. Both polynomial charts preserve that base
map, so they are morphisms over the actual coefficient scheme.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The original coefficient ring is exactly the degree-zero homogeneous ring. -/
noncomputable def constantsEquiv : R ≃+* grading R 0 :=
  { constantsToZero R with
    invFun := fun p => p.val.coeff 0
    left_inv := by intro r; simp [constantsToZero]
    right_inv := by
      intro p
      apply Subtype.ext
      change C (p.val.coeff 0) = p.val
      simpa only [homogeneousComponent_zero] using homogeneousComponent_eq_self p.property }

/-- The actual Proj structural morphism to the original coefficient scheme. -/
noncomputable def toSpecBase : projectiveLine R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R) ≫ Spec.map (CommRingCat.ofHom (constantsToZero R))

/-- On each original chart, the structural map is the original polynomial coefficient map. -/
@[reassoc] theorem chartι_toSpecBase (i : Fin 2) :
    chartι R i ≫ toSpecBase R = Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  dsimp only [chartι, toSpecBase]
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact toPolynomial_constants R i r

/-- The genuine projective line as a scheme over the original coefficient scheme. -/
noncomputable def overBase : Over (Spec (CommRingCat.of R)) := Over.mk (toSpecBase R)

/-- The original polynomial affine chart over the same coefficient scheme. -/
noncomputable def polynomialOverBase : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))

/-- The original chart inclusion is a morphism over the original base. -/
noncomputable def chartOverBase (i : Fin 2) : polynomialOverBase R ⟶ overBase R :=
  Over.homMk (chartι R i) (chartι_toSpecBase R i)

end BPFixedPoints.ProjectiveLine
