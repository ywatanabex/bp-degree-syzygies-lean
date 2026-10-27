import BPFixedPoints.Incidence.IncidenceGluedTorus
import BPFixedPoints.Incidence.AffineOpenSections

/-! # Actual global regular functions of the glued incidence scheme

All atlas hypotheses are discharged by the original quotient-face construction:
actual open cover, integral structure sheaf, common torus, and naturality of
restriction to the torus. The conclusion is an isomorphism with the independently
defined incidence intersection ring. A comparison with a separately constructed
projective zero scheme and higher sheaf cohomology is a further result.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory SheafTools
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The actual original chart coordinates identify sections of its realized open. -/
noncomputable def incidenceChartSectionsEquiv (σ : V → Bool) :
    Γ(G.incidenceGluedScheme, G.incidenceChartOpen σ) ≃+* G.IncChartRing σ :=
  (affineOpenSectionsIso (CommRingCat.of (G.IncChartRing σ))
    (G.incidenceChartι σ)).commRingCatIsoToRingEquiv

/-- The actual original torus coordinates identify sections of its realized open. -/
noncomputable def incidenceTorusSectionsEquiv :
    Γ(G.incidenceGluedScheme, G.incidenceTorusOpen) ≃+* G.IncTorusRing :=
  (affineOpenSectionsIso (CommRingCat.of G.IncTorusRing)
    G.incidenceTorusι).commRingCatIsoToRingEquiv

/-- The sheaf restriction is the original chart-to-torus coefficient homomorphism. -/
theorem incidenceChartSections_restrict (σ : V → Bool)
    (s : Γ(G.incidenceGluedScheme, G.incidenceChartOpen σ)) :
    G.incidenceTorusSectionsEquiv
      (sectionRestrict G.incidenceGluedScheme.sheaf (G.incidenceTorusOpen_le_chart σ) s) =
        G.incChartMap σ (G.incidenceChartSectionsEquiv σ s) := by
  have hn := affineOpenSectionsIso_naturality
    (CommRingCat.ofHom (G.incChartMap σ).toRingHom)
    (G.incidenceChartι σ) G.incidenceTorusι
    (G.incidenceTorusι_factor σ) (G.incidenceTorusOpen_le_chart σ)
  exact congrArg (fun f => CommRingCat.Hom.hom f s) hn

/-- Unconditional global-section comparison for the incidence scheme constructed
from its original quotient charts and full higher intersections. -/
noncomputable def incidenceGluedGlobalSectionsEquiv :
    Γ(G.incidenceGluedScheme, ⊤) ≃+* G.IncidenceRing :=
  G.incidenceGlobalSectionsEquivOfAtlas G.incidenceGluedScheme
    G.incidenceChartOpen G.incidenceTorusOpen G.incidenceTorusOpen_le_chart
    G.incidenceChartOpen_cover G.incidenceTorusSectionsEquiv G.incidenceChartSectionsEquiv
    G.incidenceChartSections_restrict

/-- The constructed scheme has exactly the original incidence ring as its
regular functions, without any atlas or section-identification assumption. -/
theorem incidenceGluedGlobalSections :
    Nonempty (Γ(G.incidenceGluedScheme, ⊤) ≃+* G.IncidenceRing) :=
  ⟨G.incidenceGluedGlobalSectionsEquiv⟩

end BPFixedPoints.Multigraph
