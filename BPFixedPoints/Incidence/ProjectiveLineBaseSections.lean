import BPFixedPoints.Incidence.SchemeModuleBaseScalars
import BPFixedPoints.Incidence.ProjectiveLineGeometricSections

/-! # Original geometric coefficient actions in the projective-line charts

The scalar homomorphisms come from the actual structural morphism. The affine
coordinate comparisons carry them to the original polynomial and Laurent
coefficient inclusions, using the existing geometric chart-to-base formulas.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Genuine affine coordinates preserve the base action of the original geometric structural morphism. -/
theorem affineIsoSectionsIso_coefficient {R : Type} [CommRing R] {A : CommRingCat}
    {X : Scheme} (e : X ≅ Spec A) (f : X ⟶ Spec (CommRingCat.of R)) (i : R →+* A)
    (he : f = e.hom ≫ Spec.map (CommRingCat.ofHom i)) (r : R) :
    (affineIsoSectionsIso e).hom (schemeBaseCoefficientHom f r) = i r := by
  have h := affineIsoSectionsIso_naturality e (Iso.refl _) f (CommRingCat.ofHom i)
    (by simpa only [Iso.refl_hom, Category.comp_id] using he)
  change f.appTop ≫ (affineIsoSectionsIso e).hom =
    (𝟙 _) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom i at h
  simp only [Category.id_comp] at h
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) ≫
    (affineIsoSectionsIso e).hom) r = i r
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]
  rfl

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The genuine standard open structural morphism has the original polynomial coefficient map. -/
theorem standardOpen_toSpecBase (i : Fin 2) :
    (standardOpen R i).ι ≫ toSpecBase R =
      (standardOpenIso R i).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  apply (cancel_epi (standardOpenIso R i).inv).mp
  rw [← Category.assoc, standardOpenIso_inv_ι, chartι_toSpecBase, Iso.inv_hom_id_assoc]

/-- The genuine overlap structural morphism has the original Laurent coefficient map. -/
theorem standardIntersection_toSpecBase :
    (standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R =
      (standardIntersectionLaurentIso R).hom ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)) := by
  apply (cancel_epi (standardIntersectionLaurentIso R).inv).mp
  rw [← Category.assoc, standardIntersectionLaurentIso_inv_ι,
    overlapι_toSpecBase, Iso.inv_hom_id_assoc]
  rfl

/-- Actual chart global-section coordinates retain the original geometric polynomial base action. -/
theorem chartGlobalSectionsEquiv_coefficient (i : Fin 2) (r : R) :
    chartGlobalSectionsEquiv R i
      (SchemeTools.schemeBaseCoefficientHom ((standardOpen R i).ι ≫ toSpecBase R) r) =
        Polynomial.C r :=
  SchemeTools.affineIsoSectionsIso_coefficient (standardOpenIso R i) _ _
    (standardOpen_toSpecBase R i) r

/-- Actual overlap global-section coordinates retain the original geometric Laurent base action. -/
theorem standardIntersectionSectionsEquiv_coefficient (r : R) :
    standardIntersectionSectionsEquiv R
      (SchemeTools.schemeBaseCoefficientHom ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R) r) =
        LaurentPolynomial.C r :=
  SchemeTools.affineIsoSectionsIso_coefficient (standardIntersectionLaurentIso R) _ _
    (standardIntersection_toSpecBase R) r

/-- The actual chart coordinate is an algebra equivalence for its independently induced geometric base action. -/
noncomputable def chartGlobalSectionsAlgEquiv (i : Fin 2) :
    letI := SchemeTools.schemeBaseSectionsAlgebra ((standardOpen R i).ι ≫ toSpecBase R)
    Γ((standardOpen R i).toScheme, ⊤) ≃ₐ[R] Polynomial R := by
  letI := SchemeTools.schemeBaseSectionsAlgebra ((standardOpen R i).ι ≫ toSpecBase R)
  exact { chartGlobalSectionsEquiv R i with commutes' := chartGlobalSectionsEquiv_coefficient R i }

/-- The actual overlap coordinate is an algebra equivalence for its independently induced geometric base action. -/
noncomputable def standardIntersectionSectionsAlgEquiv :
    letI := SchemeTools.schemeBaseSectionsAlgebra
      ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R)
    Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) ≃ₐ[R] LaurentPolynomial R := by
  letI := SchemeTools.schemeBaseSectionsAlgebra
    ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R)
  exact { standardIntersectionSectionsEquiv R with
    commutes' := standardIntersectionSectionsEquiv_coefficient R }

end BPFixedPoints.ProjectiveLine
