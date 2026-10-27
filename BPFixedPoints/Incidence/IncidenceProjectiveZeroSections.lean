import BPFixedPoints.Incidence.IncidenceProjectiveZeroScheme
import BPFixedPoints.Incidence.IncidenceGlobalCoefficientCompatibility

/-! # Actual global functions of the independent projective incidence zero scheme

The global-section map is induced by the actual geometric scheme isomorphism.
Both coefficient actions are defined from their actual scheme projections.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory

/-- The existing global-section functor applied to an actual geometric isomorphism. -/
@[irreducible] noncomputable def globalSectionsRingEquiv {X Y : Scheme} (e : X ≅ Y) :
    Γ(Y, ⊤) ≃+* Γ(X, ⊤) :=
  (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv

/-- The comparison is the actual pullback of sections, rather than an abstract ring identification. -/
theorem globalSectionsRingEquiv_apply {X Y : Scheme} (e : X ≅ Y) (s : Γ(Y, ⊤)) :
    globalSectionsRingEquiv e s = e.hom.appTop s := by
  unfold globalSectionsRingEquiv
  rfl

/-- Global pullback along an actual isomorphism preserves the coefficient action from the base. -/
theorem globalSectionsRingEquiv_coefficient {X Y : Scheme} (e : X ≅ Y)
    (R : Type) [CommRing R] (sx : X ⟶ Spec (CommRingCat.of R))
    (sy : Y ⟶ Spec (CommRingCat.of R)) (h : e.hom ≫ sy = sx) (r : R) :
    globalSectionsRingEquiv e (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sy.appTop).hom r) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sx.appTop).hom r := by
  rw [globalSectionsRingEquiv_apply]
  have ha : sy.appTop ≫ e.hom.appTop = sx.appTop := by
    rw [← Scheme.Hom.comp_appTop]
    exact congrArg (fun f => f.appTop) h
  have hc := congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f) ha
  exact congrArg (fun f => CommRingCat.Hom.hom f r) hc

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The independent zero scheme's actual coefficient-space structural morphism. -/
noncomputable def incidenceProjectiveZeroToBase :
    G.incidenceProjectiveZeroScheme ⟶ Spec (CommRingCat.of (IncCoeffRing E)) :=
  G.incidenceProjectiveZeroι ≫ ProjectiveLine.vertexToBase (IncCoeffRing E) V

/-- The coefficient action on the actual structure-sheaf global sections. -/
noncomputable def incidenceProjectiveZeroCoefficientHom :
    IncCoeffRing E →+* Γ(G.incidenceProjectiveZeroScheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (IncCoeffRing E))).inv ≫
    G.incidenceProjectiveZeroToBase.appTop).hom

/-- Actual pullback of global functions along the geometric scheme comparison. -/
@[irreducible] noncomputable def incidenceProjectiveZeroSectionsToGlued :
    Γ(G.incidenceProjectiveZeroScheme, ⊤) ≃+* Γ(G.incidenceGluedScheme, ⊤) :=
  SchemeTools.globalSectionsRingEquiv G.incidenceProjectiveZeroIso

/-- The geometric global-section comparison preserves the independent actual coefficient actions. -/
theorem incidenceProjectiveZeroSectionsToGlued_coeff (p : IncCoeffRing E) :
    G.incidenceProjectiveZeroSectionsToGlued (G.incidenceProjectiveZeroCoefficientHom p) =
      G.incidenceGlobalCoefficientHom p := by
  unfold incidenceProjectiveZeroSectionsToGlued
  exact SchemeTools.globalSectionsRingEquiv_coefficient G.incidenceProjectiveZeroIso
    (IncCoeffRing E) G.incidenceCoefficientMorphism G.incidenceProjectiveZeroToBase
    G.incidenceProjectiveZeroIso_hom_toBase p

/-- The independent projective zero scheme has exactly the original incidence ring as global functions. -/
noncomputable def incidenceProjectiveZeroGlobalSectionsEquiv :
    Γ(G.incidenceProjectiveZeroScheme, ⊤) ≃+* G.IncidenceRing :=
  G.incidenceProjectiveZeroSectionsToGlued.trans G.incidenceGluedGlobalSectionsEquiv

theorem incidenceProjectiveZeroGlobalSectionsEquiv_coeff (p : IncCoeffRing E) :
    G.incidenceProjectiveZeroGlobalSectionsEquiv (G.incidenceProjectiveZeroCoefficientHom p) =
      G.coeffHom p := by
  change G.incidenceGluedGlobalSectionsEquiv
    (G.incidenceProjectiveZeroSectionsToGlued (G.incidenceProjectiveZeroCoefficientHom p)) = _
  rw [G.incidenceProjectiveZeroSectionsToGlued_coeff, G.incidenceGluedGlobalSectionsEquiv_coeff]

/-- The zero scheme's coefficient algebra is induced by its geometric structural morphism. -/
noncomputable abbrev incidenceProjectiveZeroCoefficientAlgebra :
    Algebra (IncCoeffRing E) Γ(G.incidenceProjectiveZeroScheme, ⊤) :=
  G.incidenceProjectiveZeroCoefficientHom.toAlgebra

/-- The actual projective-zero global-section comparison over the original coefficient ring. -/
noncomputable def incidenceProjectiveZeroGlobalSectionsAlgEquiv :
    letI := G.incidenceProjectiveZeroCoefficientAlgebra
    letI := G.coeffHom.toRingHom.toAlgebra
    Γ(G.incidenceProjectiveZeroScheme, ⊤) ≃ₐ[IncCoeffRing E] G.IncidenceRing := by
  letI := G.incidenceProjectiveZeroCoefficientAlgebra
  letI := G.coeffHom.toRingHom.toAlgebra
  exact { G.incidenceProjectiveZeroGlobalSectionsEquiv with
    commutes' := G.incidenceProjectiveZeroGlobalSectionsEquiv_coeff }

theorem incidenceProjectiveZeroGlobalSections_comparison :
    Nonempty (Γ(G.incidenceProjectiveZeroScheme, ⊤) ≃+* G.IncidenceRing) :=
  ⟨G.incidenceProjectiveZeroGlobalSectionsEquiv⟩

end BPFixedPoints.Multigraph
