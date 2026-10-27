import BPFixedPoints.Incidence.ProjectiveProductChartImages
import BPFixedPoints.Incidence.VertexProjectiveTwistLocalFrames
import BPFixedPoints.Incidence.ProjectiveLineBaseSections
import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars

/-! # Original polynomial coordinates on actual vertex-chart sections

The equivalences come from the original open immersion and Gamma--Spec.
The base coefficient map is the original structural morphism.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

/-- The original open coefficient is the original global coefficient on that open subscheme. -/
theorem schemeBaseCoefficientAt_open_top {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (r : R) :
    U.topIso.inv (schemeBaseCoefficientAt f U r) = schemeBaseCoefficientHom (U.ι ≫ f) r := by
  rw [schemeBaseCoefficientHom_comp]
  dsimp only [schemeBaseCoefficientAt, RingHom.comp_apply]
  change X.presheaf.map (eqToHom U.ι_image_top).op
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (schemeBaseCoefficientHom f r)) =
      U.ι.appTop (schemeBaseCoefficientHom f r)
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original vertex chart identifies its actual image with its original polynomial spectrum. -/
noncomputable def vertexChartOpenIso (σ : V → Fin 2) :
    (vertexChartOpen R V σ).toScheme ≅ Spec (CommRingCat.of (MvPolynomial V R)) :=
  (vertexChartι R V σ).isoOpensRange.symm

/-- The coordinate isomorphism retains the original chart inclusion. -/
@[reassoc] theorem vertexChartOpenIso_inv_ι (σ : V → Fin 2) :
    (vertexChartOpenIso R V σ).inv ≫ (vertexChartOpen R V σ).ι = vertexChartι R V σ :=
  Scheme.Hom.isoOpensRange_hom_ι _

/-- The original chart-to-base map has the original polynomial coefficient inclusion. -/
theorem vertexChartOpenIso_toBase (σ : V → Fin 2) :
    (vertexChartOpen R V σ).ι ≫ vertexToBase R V =
      (vertexChartOpenIso R V σ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial V R))) := by
  apply (cancel_epi (vertexChartOpenIso R V σ).inv).mp
  rw [← Category.assoc, vertexChartOpenIso_inv_ι, vertexChartι_toBase,
    Iso.inv_hom_id_assoc]

/-- Actual global functions on the original chart subscheme in the original polynomial coordinates. -/
noncomputable def vertexChartGlobalSectionsEquiv (σ : V → Fin 2) :
    Γ((vertexChartOpen R V σ).toScheme, ⊤) ≃+* MvPolynomial V R :=
  (SchemeTools.affineIsoSectionsIso (vertexChartOpenIso R V σ)).commRingCatIsoToRingEquiv

/-- Actual chart-global coordinates retain the original geometric base coefficients. -/
theorem vertexChartGlobalSectionsEquiv_coefficient (σ : V → Fin 2) (r : R) :
    vertexChartGlobalSectionsEquiv R V σ
      (SchemeTools.schemeBaseCoefficientHom ((vertexChartOpen R V σ).ι ≫ vertexToBase R V) r) =
        MvPolynomial.C r :=
  SchemeTools.affineIsoSectionsIso_coefficient (vertexChartOpenIso R V σ) _ _
    (vertexChartOpenIso_toBase R V σ) r

/-- Actual ambient chart sections in the original vertex-labelled polynomial coordinates. -/
noncomputable def vertexChartSectionsEquiv (σ : V → Fin 2) :
    Γ(vertexScheme R V, vertexChartOpen R V σ) ≃+* MvPolynomial V R :=
  (vertexChartOpen R V σ).topIso.symm.commRingCatIsoToRingEquiv.trans
    (vertexChartGlobalSectionsEquiv R V σ)

/-- The polynomial section coordinates preserve the independently defined original ambient base action. -/
theorem vertexChartSectionsEquiv_coefficient (σ : V → Fin 2) (r : R) :
    vertexChartSectionsEquiv R V σ
      (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ) r) =
        MvPolynomial.C r := by
  change vertexChartGlobalSectionsEquiv R V σ
    ((vertexChartOpen R V σ).topIso.inv
      (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ) r)) = _
  rw [SchemeTools.schemeBaseCoefficientAt_open_top, vertexChartGlobalSectionsEquiv_coefficient]

/-- The original vertex projection has exactly its original single-variable polynomial morphism in chart coordinates. -/
theorem vertexChartProjection_geometric (σ : V → Fin 2) (v : V) :
    vertexChartOpenProjectionLift R V σ v ≫ (standardOpenIso R (σ v)).hom =
      (vertexChartOpenIso R V σ).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (MvPolynomial.X v : MvPolynomial V R)).toRingHom) := by
  apply (cancel_epi (vertexChartOpenIso R V σ).inv).mp
  apply (cancel_mono ((standardOpenIso R (σ v)).inv ≫ (standardOpen R (σ v)).ι)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [vertexChartOpenProjectionLift_fac, ← Category.assoc, vertexChartOpenIso_inv_ι,
    standardOpenIso_inv_ι]
  exact vertexChartι_projection R V σ v

/-- Actual pullback of every factor-chart polynomial evaluates at the original vertex variable. -/
theorem vertexChartProjection_global_sections (σ : V → Fin 2) (v : V)
    (s : Γ((standardOpen R (σ v)).toScheme, ⊤)) :
    vertexChartGlobalSectionsEquiv R V σ ((vertexChartOpenProjectionLift R V σ v).appTop s) =
      Polynomial.aeval (MvPolynomial.X v : MvPolynomial V R) (chartGlobalSectionsEquiv R (σ v) s) :=
  ConcreteCategory.congr_hom (SchemeTools.affineIsoSectionsIso_naturality
    (vertexChartOpenIso R V σ) (standardOpenIso R (σ v))
    (vertexChartOpenProjectionLift R V σ v)
    (CommRingCat.ofHom (Polynomial.aeval (MvPolynomial.X v : MvPolynomial V R)).toRingHom)
    (vertexChartProjection_geometric R V σ v)) s

end BPFixedPoints.ProjectiveLine
