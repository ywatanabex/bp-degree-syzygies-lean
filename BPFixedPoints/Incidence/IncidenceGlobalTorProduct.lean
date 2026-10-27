import BPFixedPoints.Incidence.IncidenceGlobalResolutionTor
import BPFixedPoints.Incidence.ResolutionTorProduct

/-! # Standard Tor products for genuine incidence global functions

Multiplication lifts are required to preserve the actual global-section
augmentation. Their products are computed by scalar extension of the actual
chain maps and compared to the original Tor product by derived functoriality.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance globalTorProductIncidenceAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance globalTorProductSectionAlgebra : Algebra (IncCoeffRing E) Γ(G.incidenceGluedScheme, ⊤) :=
  G.incidenceGlobalCoefficientAlgebra
noncomputable local instance globalTorProductResidueAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

/-- A genuine multiplication lift for the actual global-section coefficient algebra. -/
structure IncGlobalResolutionMultiplication extends
    GradedFreePairing G.incResolutionDegree G.incResolutionDifferential where
  augmentation : ∀ x y : G.IncFreeTerm 0,
    G.incidenceGlobalAugmentation
      ⟨mul x.val y.val, homogeneous 0 0 x.property y.property⟩ =
        G.incidenceGlobalAugmentation x * G.incidenceGlobalAugmentation y

namespace IncGlobalResolutionMultiplication
variable {G} (μ : G.IncGlobalResolutionMultiplication)

/-- Comparison of actual global-function multiplication lifts with the original ring lifts. -/
noncomputable def toOriginal : G.IncResolutionMultiplication where
  toGradedFreePairing := μ.toGradedFreePairing
  augmentation x y hx hy := by
    have h := congrArg (fun z => (G.incidenceGluedGlobalSectionsAlgEquiv z).val)
      (μ.augmentation ⟨x, hx⟩ ⟨y, hy⟩)
    simp only [incidenceGlobalAugmentation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul, AlgEquiv.apply_symm_apply, Subalgebra.coe_mul] at h
    exact h

/-- Actual multiplication chain map into the resolution of genuine global sections. -/
noncomputable def chainMap :
    G.incTensorResolutionComplex ⟶ G.incidenceGlobalFreeResolution.complex :=
  μ.toOriginal.chainMap

/-- Product on actual derived Tor obtained by specializing a genuine multiplication chain map. -/
noncomputable def torProduct (p q : ℕ) :
    G.incidenceGlobalTor p →ₗ[ℂ] G.incidenceGlobalTor q →ₗ[ℂ] G.incidenceGlobalTor (p+q) :=
  ((specializedGradedPair (k := ℂ) G.incResolutionDegree p q).compl₁₂
    (G.incidenceGlobalTorIsoFreeTerm p).hom.hom (G.incidenceGlobalTorIsoFreeTerm q).hom.hom).compr₂
      ((G.incidenceGlobalTorIsoFreeTerm (p+q)).inv.hom.comp
        (((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
          (μ.chainMap.f (p+q))).hom))

/-- All lifts of the actual global-section multiplication induce the same product. -/
theorem torProduct_eq (ν : G.IncGlobalResolutionMultiplication) (p q : ℕ) :
    μ.torProduct p q = ν.torProduct p q := by
  unfold torProduct chainMap
  rw [μ.toOriginal.specialized_chainMap_eq ν.toOriginal (p+q)]

/-- The derived functor's actual global-section comparison preserves these standard products. -/
theorem torProduct_comparison (p q : ℕ) (x : G.incidenceGlobalTor p)
    (y : G.incidenceGlobalTor q) :
    (G.incidenceGlobalTorIso (p+q)).hom (μ.torProduct p q x y) =
      μ.toOriginal.torProduct p q ((G.incidenceGlobalTorIso p).hom x)
        ((G.incidenceGlobalTorIso q).hom y) := by
  apply (G.incidenceTorIsoFreeTerm (p+q)).toLinearEquiv.injective
  have hc (n : ℕ) (z : G.incidenceGlobalTor n) :
      (G.incidenceTorIsoFreeTerm n).hom ((G.incidenceGlobalTorIso n).hom z) =
        (G.incidenceGlobalTorIsoFreeTerm n).hom z :=
    congrArg (fun f => f z) (G.incidenceGlobalTorIso_freeTerm n)
  change (G.incidenceTorIsoFreeTerm (p+q)).hom
      ((G.incidenceGlobalTorIso (p+q)).hom (μ.torProduct p q x y)) =
    (G.incidenceTorIsoFreeTerm (p+q)).hom
      (μ.toOriginal.torProduct p q ((G.incidenceGlobalTorIso p).hom x)
        ((G.incidenceGlobalTorIso q).hom y))
  rw [hc]
  simp only [torProduct, chainMap, IncResolutionMultiplication.torProduct,
    LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  change (G.incidenceGlobalTorIsoFreeTerm (p+q)).toLinearEquiv
      ((G.incidenceGlobalTorIsoFreeTerm (p+q)).toLinearEquiv.symm _) =
    (G.incidenceTorIsoFreeTerm (p+q)).toLinearEquiv
      ((G.incidenceTorIsoFreeTerm (p+q)).toLinearEquiv.symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  apply congrArg (((ModuleCat.extendScalars
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
      (μ.toOriginal.chainMap.f (p+q))).hom)
  exact congrArg₂ (fun a b => specializedGradedPair (R := IncCoeffRing E) (k := ℂ)
    G.incResolutionDegree p q a b) (hc p x).symm (hc q y).symm

end IncGlobalResolutionMultiplication

/-- Every original multiplication lift also lifts multiplication of actual global functions. -/
noncomputable def incidenceGlobalMultiplicationOfOriginal (μ : G.IncResolutionMultiplication) :
    G.IncGlobalResolutionMultiplication where
  toGradedFreePairing := μ.toGradedFreePairing
  augmentation x y := by
    apply G.incidenceGluedGlobalSectionsAlgEquiv.injective
    simp only [incidenceGlobalAugmentation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul, AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    exact μ.augmentation x.val y.val x.property y.property

/-- Standard Tor multiplication of genuine global functions, from an actual multiplication lift. -/
noncomputable def incidenceGlobalTorProduct (p q : ℕ) :=
  (G.incidenceGlobalMultiplicationOfOriginal G.incidenceStandardMultiplication).torProduct p q

/-- Every lift of actual global-section multiplication gives the standard product. -/
theorem incidenceGlobalTorProduct_eq_of_lift (μ : G.IncGlobalResolutionMultiplication)
    (p q : ℕ) : G.incidenceGlobalTorProduct p q = μ.torProduct p q :=
  (G.incidenceGlobalMultiplicationOfOriginal G.incidenceStandardMultiplication).torProduct_eq μ p q

/-- The actual derived comparison identifies standard Tor products of genuine
structure-sheaf global functions and the original incidence ring. -/
theorem incidenceGlobalTorIso_mul (p q : ℕ) (x : G.incidenceGlobalTor p)
    (y : G.incidenceGlobalTor q) :
    (G.incidenceGlobalTorIso (p+q)).hom (G.incidenceGlobalTorProduct p q x y) =
      G.incidenceTorProduct p q ((G.incidenceGlobalTorIso p).hom x)
        ((G.incidenceGlobalTorIso q).hom y) := by
  rw [incidenceGlobalTorProduct, IncGlobalResolutionMultiplication.torProduct_comparison]
  rw [G.incidenceTorProduct_eq_of_lift]

/-- Total Betti number of the actual global-function module with its geometric action. -/
theorem sum_finrank_incidenceGlobalTor :
    ∑ p ∈ Finset.range (Fintype.card E + 1),
      Module.finrank ℂ (G.incidenceGlobalTor p) = G.Q := by
  simp_rw [G.finrank_incidenceGlobalTor]
  exact G.sum_finrank_incidenceTor

end BPFixedPoints.Multigraph
