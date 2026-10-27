import BPFixedPoints.Incidence.IncidenceGlobalCoefficientCompatibility
import BPFixedPoints.Incidence.ResolutionTor

/-! # The original minimal resolution computes Tor of actual global sections

Global functions carry the coefficient action from the actual scheme projection.
The global-section comparison preserves that action. Consequently the existing
free complex, augmented through the proved comparison, resolves this actual
module. Tor here is defined by Mathlib's left derived extension of scalars.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance globalResolutionIncidenceAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

noncomputable local instance globalResolutionSectionAlgebra : Algebra (IncCoeffRing E) Γ(G.incidenceGluedScheme, ⊤) :=
  G.incidenceGlobalCoefficientAlgebra

/-- The original free complex augmented to the actual structure-sheaf global functions. -/
noncomputable def incidenceGlobalAugmentation :
    G.IncFreeTerm 0 →ₗ[IncCoeffRing E] Γ(G.incidenceGluedScheme, ⊤) :=
  G.incidenceGluedGlobalSectionsAlgEquiv.symm.toLinearMap.comp G.incResolutionAugmentation

theorem incidenceGlobalAugmentation_surjective :
    Function.Surjective G.incidenceGlobalAugmentation :=
  G.incidenceGluedGlobalSectionsAlgEquiv.symm.surjective.comp G.incResolutionAugmentation_surjective

theorem incidenceGlobalAugmentation_exact :
    LinearMap.range (G.incFreeTermDifferential 0) = LinearMap.ker G.incidenceGlobalAugmentation := by
  rw [G.incFreeTermDifferential_augmentation_exact]
  ext x
  simp only [LinearMap.mem_ker, incidenceGlobalAugmentation, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply]
  exact G.incidenceGluedGlobalSectionsAlgEquiv.symm.injective.eq_iff.symm.trans
    (by rw [map_zero])

/-- A genuine projective resolution of the actual global-section coefficient module. -/
noncomputable def incidenceGlobalFreeResolution :
    ProjectiveResolution (ModuleCat.of (IncCoeffRing E) Γ(G.incidenceGluedScheme, ⊤)) :=
  projectiveResolutionOfLinearExact G.IncFreeTerm G.incFreeTermDifferential
    G.incFreeTermDifferential_exact G.incidenceGlobalAugmentation
    G.incidenceGlobalAugmentation_surjective G.incidenceGlobalAugmentation_exact

/-- The original differentials remain minimal for genuine global sections. -/
theorem incidenceGlobalFreeResolution_minimal (i j : ℕ) :
    LinearMap.range (G.incidenceGlobalFreeResolution.complex.d i j).hom ≤
      RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) •
        (⊤ : Submodule (IncCoeffRing E) (G.incidenceGlobalFreeResolution.complex.X j)) :=
  G.incFreeResolution_minimal i j

/-- Actual Tor of genuine structure-sheaf global sections with the geometric coefficient action. -/
noncomputable def incidenceGlobalTor (p : ℕ) : ModuleCat ℂ :=
  ((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).obj
    (ModuleCat.of (IncCoeffRing E) Γ(G.incidenceGluedScheme, ⊤))

/-- Derived functoriality of the proved coefficient-linear global-section comparison. -/
noncomputable def incidenceGlobalTorIso (p : ℕ) : G.incidenceGlobalTor p ≅ G.incidenceTor p :=
  ((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).mapIso
    G.incidenceGluedGlobalSectionsAlgEquiv.toLinearEquiv.toModuleIso

/-- The actual global-section Tor is computed by the original minimal free terms. -/
noncomputable def incidenceGlobalTorIsoFreeTerm (p : ℕ) :
    G.incidenceGlobalTor p ≅
      (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).obj
        (ModuleCat.of (IncCoeffRing E) (G.IncFreeTerm p)) :=
  derivedSpecializationIsoTerm
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) G.incidenceGlobalFreeResolution
    G.incidenceGlobalFreeResolution_minimal p

/-- The derived comparison is the same identity-on-free-terms comparison as
that supplied by the actual minimal resolutions. -/
theorem incidenceGlobalTorIso_freeTerm (p : ℕ) :
    (G.incidenceGlobalTorIso p).hom ≫ (G.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceGlobalTorIsoFreeTerm p).hom := by
  let e := G.incidenceGluedGlobalSectionsAlgEquiv.toLinearEquiv.toModuleIso
  have hP : (G.incidenceGlobalFreeResolution.π.f 0).hom = G.incidenceGlobalAugmentation := by
    dsimp only [incidenceGlobalFreeResolution, projectiveResolutionOfLinearExact,
      projectiveResolutionOfExact]
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have hQ : (G.incFreeResolution.π.f 0).hom = G.incResolutionAugmentation := by
    dsimp only [incFreeResolution, projectiveResolutionOfLinearExact, projectiveResolutionOfExact]
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  let φ : G.incidenceGlobalFreeResolution.complex ⟶ G.incFreeResolution.complex := 𝟙 _
  have hc : φ.f 0 ≫ G.incFreeResolution.π.f 0 =
      G.incidenceGlobalFreeResolution.π.f 0 ≫ e.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (G.incFreeResolution.π.f 0).hom x =
      e.hom.hom ((G.incidenceGlobalFreeResolution.π.f 0).hom x)
    rw [hP, hQ]
    exact (G.incidenceGluedGlobalSectionsAlgEquiv.apply_symm_apply _).symm
  have hn := ProjectiveResolution.isoLeftDerivedObj_hom_naturality e.hom
    G.incidenceGlobalFreeResolution G.incFreeResolution φ hc
    (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)) p
  dsimp only [incidenceGlobalTorIso, incidenceTorIsoFreeTerm, incidenceGlobalTorIsoFreeTerm,
    derivedSpecializationIsoTerm, Functor.mapIso_hom, id_eq, Iso.trans_hom]
  simp only [φ, CategoryTheory.Functor.map_id] at hn
  have hn' : ((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).map e.hom ≫
      (G.incFreeResolution.isoLeftDerivedObj
        (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)) p).hom =
      (G.incidenceGlobalFreeResolution.isoLeftDerivedObj
        (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)) p).hom :=
    hn.trans (CategoryTheory.Category.comp_id _)
  rw [← Category.assoc, hn']
  rfl

/-- State coordinates for actual derived Tor of actual global sections. -/
noncomputable def incidenceGlobalTorEquivState (p : ℕ) :
    G.incidenceGlobalTor p ≃ₗ[ℂ]
      ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) :=
  (G.incidenceGlobalTorIsoFreeTerm p).toLinearEquiv.trans
    (G.incSpecializedFreeTermEquiv p)

/-- Geometric global sections have exactly the original actual Tor dimensions. -/
theorem finrank_incidenceGlobalTor (p : ℕ) :
    Module.finrank ℂ (G.incidenceGlobalTor p) = Module.finrank ℂ (G.incidenceTor p) :=
  (G.incidenceGlobalTorIso p).toLinearEquiv.finrank_eq

end BPFixedPoints.Multigraph
