import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Algebra.Tower

/-! # Actual base-scheme scalar actions on genuine module sections

The coefficient homomorphism comes from the given structural morphism to
Spec R and Gamma-Spec. Module scalars are restricted through this actual
homomorphism, independently of every later coordinate comparison.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- The original base action on actual global functions, induced by the structural scheme morphism. -/
noncomputable def schemeBaseCoefficientHom (f : X ⟶ Spec (CommRingCat.of R)) :
    R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom

/-- The base algebra of actual global functions is induced by the genuine structural morphism. -/
noncomputable abbrev schemeBaseSectionsAlgebra (f : X ⟶ Spec (CommRingCat.of R)) :
    Algebra R Γ(X, ⊤) := (schemeBaseCoefficientHom f).toAlgebra

/-- The base module structure on actual module sections restricts the original structure-ring action. -/
@[instance_reducible] noncomputable def schemeBaseModuleSections (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) :
    Module R Γ(M, ⊤) := Module.compHom _ (schemeBaseCoefficientHom f)

/-- Pulling back the actual structural morphism pulls back the original base coefficient homomorphism. -/
theorem schemeBaseCoefficientHom_comp {Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ X) :
    schemeBaseCoefficientHom (g ≫ f) = g.appTop.hom.comp (schemeBaseCoefficientHom f) := by
  apply RingHom.ext
  intro r
  rfl

/-- A genuine module projection to an open structure module respects its original geometric base action. -/
theorem openUnitProjection_base_smul (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (U : X.Opens)
    (φ : M ⟶ (Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : R) (s : Γ(M, ⊤)) :
    letI := schemeBaseModuleSections f M
    φ.app ⊤ (r • s) = Mul.mul (α := Γ(U.toScheme, ⊤))
      (schemeBaseCoefficientHom (U.ι ≫ f) r) (φ.app ⊤ s) := by
  letI := schemeBaseModuleSections f M
  change φ.app ⊤ (schemeBaseCoefficientHom f r • s) = _
  rw [Scheme.Modules.Hom.app_smul]
  rfl

end BPFixedPoints.SchemeTools
