import BPFixedPoints.Incidence.IntegralSchemeChartIntersection
import BPFixedPoints.Incidence.ChartSections

/-! # Global-section comparison from a realized incidence atlas

This theorem uses the structure sheaf of an actual integral scheme. A realization
of the polynomial incidence charts as an open cover, and its compatible torus
chart, are explicit inputs. Constructing that scheme and atlas is still required
before applying this theorem to the paper's projective incidence zero scheme.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens
open SheafTools
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E) (X : Scheme.{0}) [IsIntegral X]
  (U : (V → Bool) → X.Opens) (W : X.Opens) [Nonempty W]
  (hW : ∀ σ, W ≤ U σ) (hcover : (⊤ : X.Opens) ≤ iSup U)
  (eW : Γ(X, W) ≃+* G.IncTorusRing)
  (eU : ∀ σ, Γ(X, U σ) ≃+* G.IncChartRing σ)
  (hres : ∀ σ (s : Γ(X, U σ)),
    eW (sectionRestrict X.sheaf (hW σ) s) = G.incChartMap σ (eU σ s))

/-- Identify the intersection of actual sheaf chart images with the existing,
independently defined incidence ring. -/
noncomputable def incidenceChartIntersectionMap :
    chartImageIntersection X.sheaf U W hW →+* G.IncidenceRing where
  toFun x := ⟨eW x.val, by
    rw [IncidenceRing, Algebra.mem_iInf]
    intro σ
    obtain ⟨s, hs⟩ := (Subring.mem_iInf.mp x.property) σ
    exact ⟨eU σ s, (hres σ s).symm.trans (congrArg eW hs)⟩⟩
  map_zero' := Subtype.ext (map_zero eW)
  map_one' := Subtype.ext (map_one eW)
  map_add' x y := Subtype.ext (map_add eW x.val y.val)
  map_mul' x y := Subtype.ext (map_mul eW x.val y.val)

/-- Surjectivity uses chart representatives of the original intersection ring;
no equality with global sections is assumed in the atlas data. -/
theorem incidenceChartIntersectionMap_bijective :
    Function.Bijective (G.incidenceChartIntersectionMap X U W hW eW eU hres) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact eW.injective (congrArg Subtype.val h)
  · intro x
    have hx : eW.symm x.val ∈ chartImageIntersection X.sheaf U W hW := by
      apply Subring.mem_iInf.mpr
      intro σ
      obtain ⟨s, hs⟩ := (Algebra.mem_iInf.mp x.property) σ
      refine ⟨(eU σ).symm s, ?_⟩
      apply eW.injective
      rw [hres, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact hs
    refine ⟨⟨eW.symm x.val, hx⟩, Subtype.ext ?_⟩
    exact eW.apply_symm_apply x.val

/-- Actual global regular functions agree with the original incidence ring once
its affine charts and torus have been realized as the specified scheme atlas. -/
noncomputable def incidenceGlobalSectionsEquivOfAtlas :
    Γ(X, ⊤) ≃+* G.IncidenceRing :=
  (integralGlobalSectionsEquivChartIntersection X U W hW hcover).trans
    (RingEquiv.ofBijective (G.incidenceChartIntersectionMap X U W hW eW eU hres)
      (G.incidenceChartIntersectionMap_bijective X U W hW eW eU hres))

include hW hcover eW eU hres in
/-- Existence form of the comparison, with every atlas realization hypothesis explicit. -/
theorem incidenceGlobalSectionsOfAtlas :
    Nonempty (Γ(X, ⊤) ≃+* G.IncidenceRing) :=
  ⟨G.incidenceGlobalSectionsEquivOfAtlas X U W hW hcover eW eU hres⟩

end BPFixedPoints.Multigraph
