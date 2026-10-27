import BPFixedPoints.Incidence.IncidenceCoefficientMorphism

/-! # The actual global-section equivalence preserves the geometric coefficient action

The coefficient action is induced by the scheme projection built on each
original incidence face. Compatibility is proved through the actual torus
restriction, the naturality of `ΓSpecIso`, and the original coefficient map.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

/-- Global restriction to a realized affine open is its actual map on global sections. -/
theorem affineOpenSectionsIso_global {Y : Scheme.{0}} (A : CommRingCat.{0})
    (f : Spec A ⟶ Y) [IsOpenImmersion f] :
    Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op ≫
        (affineOpenSectionsIso A f).hom = f.appTop ≫ (Scheme.ΓSpecIso A).hom := by
  simp only [affineOpenSectionsIso, Iso.trans_hom, openImageSectionsIso_hom]
  rw [Scheme.Hom.map_appLE_assoc]
  congr 1

end BPFixedPoints.SheafTools

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory Opposite SheafTools
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Actual restriction of global functions to the original common torus coordinates. -/
noncomputable def incidenceGlobalTorusHom :
    Γ(G.incidenceGluedScheme, ⊤) →+* G.IncTorusRing :=
  G.incidenceTorusSectionsEquiv.toRingHom.comp
    (sectionRestrict G.incidenceGluedScheme.sheaf (show G.incidenceTorusOpen ≤ ⊤ from le_top))

@[simp] theorem incidenceGluedGlobalSectionsEquiv_val
    (s : Γ(G.incidenceGluedScheme, ⊤)) :
    (G.incidenceGluedGlobalSectionsEquiv s).val = G.incidenceGlobalTorusHom s := rfl

/-- The section-to-torus map is computed by the actual torus embedding. -/
theorem incidenceGlobalTorusHom_eq :
    CommRingCat.ofHom G.incidenceGlobalTorusHom =
      G.incidenceTorusι.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of G.IncTorusRing)).hom := by
  exact affineOpenSectionsIso_global (CommRingCat.of G.IncTorusRing) G.incidenceTorusι

/-- The actual geometric coefficient action restricts to the original torus coefficient map. -/
theorem incidenceGlobalCoefficientHom_torus :
    G.incidenceGlobalTorusHom.comp G.incidenceGlobalCoefficientHom = G.incTorusCoeffHom.toRingHom := by
  have he : CommRingCat.ofHom G.incidenceGlobalCoefficientHom ≫
      CommRingCat.ofHom G.incidenceGlobalTorusHom =
        CommRingCat.ofHom G.incTorusCoeffHom.toRingHom := by
    rw [G.incidenceGlobalTorusHom_eq]
    change ((Scheme.ΓSpecIso (CommRingCat.of (IncCoeffRing E))).inv ≫
      G.incidenceCoefficientMorphism.appTop) ≫ G.incidenceTorusι.appTop ≫ _ = _
    rw [Category.assoc, ← Scheme.Hom.comp_appTop_assoc, G.incidenceTorusι_coefficient,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom he

/-- The global-section comparison respects the original coefficient map, with
the source action obtained independently from the scheme projection. -/
theorem incidenceGluedGlobalSectionsEquiv_coeff (r : IncCoeffRing E) :
    G.incidenceGluedGlobalSectionsEquiv (G.incidenceGlobalCoefficientHom r) = G.coeffHom r := by
  apply Subtype.ext
  rw [G.incidenceGluedGlobalSectionsEquiv_val]
  exact RingHom.congr_fun G.incidenceGlobalCoefficientHom_torus r

/-- The coefficient algebra structure on genuine global sections is induced by
its geometric projection, not by the comparison equivalence. -/
noncomputable abbrev incidenceGlobalCoefficientAlgebra :
    Algebra (IncCoeffRing E) Γ(G.incidenceGluedScheme, ⊤) :=
  G.incidenceGlobalCoefficientHom.toAlgebra

/-- The geometric global-section comparison is an equivalence over the original
coefficient ring, with both coefficient actions independently specified. -/
noncomputable def incidenceGluedGlobalSectionsAlgEquiv :
    letI := G.incidenceGlobalCoefficientAlgebra
    letI := G.coeffHom.toRingHom.toAlgebra
    Γ(G.incidenceGluedScheme, ⊤) ≃ₐ[IncCoeffRing E] G.IncidenceRing := by
  letI := G.incidenceGlobalCoefficientAlgebra
  letI := G.coeffHom.toRingHom.toAlgebra
  exact { G.incidenceGluedGlobalSectionsEquiv with
    commutes' := G.incidenceGluedGlobalSectionsEquiv_coeff }

end BPFixedPoints.Multigraph
