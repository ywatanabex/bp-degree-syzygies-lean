import BPFixedPoints.Incidence.IncidenceKernelBundleTransitions
import BPFixedPoints.Incidence.VertexProjectiveFaceTwistUnits
import BPFixedPoints.Incidence.EdgeExteriorBundle

/-! # The diagonal transitions are those of the actual edge line sheaves

`IncidenceKernelBundleTransitions.lean` shows that on a face `r` refined by chart `σ`, the
chart-`σ` evaluation map is the face's own evaluation map followed by the diagonal action of
the units `incOverlapEdgeUnit hσ e`. This file identifies these units with the transition
coefficients of the actual edge line sheaf `edgeLineSheaf ℂ e = O(endCount e)` on the scheme
`vertexScheme ℂ V`, read in the face coordinates `vertexFaceSectionsEquiv`:

* `edgeLineSheaf_pairTransition`: the transition coefficient of `edgeLineSheaf ℂ e` between the
  frame of chart `σ` and the frame of the chart of the face `r` (`vertexFaceBaseChoice V r`, the
  orientation used by `incFaceEvaluation r`) is `incOverlapEdgeUnit hσ e`;
* `edgeLineSheaf_chartCoefficient_overlap`: for every actual section of `edgeLineSheaf ℂ e` over
  the face open, its chart-`σ` frame coefficient is `incOverlapEdgeUnit hσ e` times its face-frame
  coefficient. This is the sheaf-level form of the diagonal action `D_σ` on the summand `L_e`.

Not constructed here: the evaluation `O^{4m} → edgeBundle` as a morphism of sheaves of modules,
its kernel sheaf, or the local freeness of that kernel sheaf.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory MvPolynomial CechProduct ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)
variable {σ : V → Bool} {r : V → Fin 3}

/-- The frame of a face is the frame of the chart `faceOrientation r` used by
`incFaceEvaluation r`. -/
theorem vertexFaceBaseChoice_eq_faceOrientation (r : V → Fin 3) :
    vertexFaceBaseChoice V r = faceOrientation r :=
  rfl

/-- The frame chosen for a chart face is the frame of the chart itself. -/
theorem vertexFaceBaseChoice_chartFace (σ : V → Bool) :
    vertexFaceBaseChoice V (chartFace σ) = σ := by
  funext v
  exact chartFace_orientation σ v

/-- **The edge units are actual sheaf transitions.** The transition coefficient of the edge line
sheaf `edgeLineSheaf ℂ e` from the frame of chart `σ` to the frame of the face `r`, on the face
open and in face coordinates, is the edge unit `incOverlapEdgeUnit hσ e`. -/
theorem edgeLineSheaf_pairTransition (hσ : FaceRefines (chartFace σ) r) (e : E) :
    vertexFaceSectionsEquiv ℂ V r
      (vertexTwistSheafPairTransitionCoefficient ℂ V (fun v => (G.endCount e v : ℤ))
        (vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r))
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen ℂ V) r)
        (vertexFaceRefinement_le_pair ℂ V hσ)) =
      (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) := by
  rw [vertexFaceRefinement_pair_unit, incOverlapEdgeUnit_eq_multiTwistTransition]

/-- **Frame coefficients of edge-sheaf sections on an overlap.** For an actual section `x` of
`edgeLineSheaf ℂ e` over the face open of `r`, its coefficient in the frame of chart `σ` is the
edge unit `incOverlapEdgeUnit hσ e` times its coefficient in the frame of the face `r`, both read
in the face coordinates. -/
theorem edgeLineSheaf_chartCoefficient_overlap (hσ : FaceRefines (chartFace σ) r) (e : E)
    (x : Γ(G.edgeLineSheaf ℂ e, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen ℂ V) r)) :
    vertexFaceSectionsEquiv ℂ V r
      (vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ))
        (vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)))
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen ℂ V) r)
        ((vertexFaceRefinement_le_pair ℂ V hσ).trans inf_le_left) x) =
      (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) *
        vertexFaceSectionsEquiv ℂ V r
          (vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ))
            (vertexBooleanPivot V (vertexFaceBaseChoice V r))
            (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen ℂ V) r)
            ((vertexFaceRefinement_le_pair ℂ V hσ).trans inf_le_right) x) := by
  rw [vertexTwistSheafChartCoefficient_pair_transition (hW := vertexFaceRefinement_le_pair ℂ V hσ),
    map_mul, edgeLineSheaf_pairTransition, mul_comm]

end BPFixedPoints.Multigraph
