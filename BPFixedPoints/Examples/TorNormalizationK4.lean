import BPFixedPoints.Examples.Graphs
import BPFixedPoints.Incidence.IncidenceTorNormalization

/-! # Normalization acceptance test on `K₄` in positive Tor degree

The normalization of the Tor-to-exterior isomorphism `Φ = incidenceTorExteriorEquiv` is not
determined by naturality, products and the unit (`λ^p Φ` has the same properties); it is fixed by
the coefficient formula. This file checks it on one specified representative of `K₄` in
bidegree `(p, q) = (1, 5)`, in cohomological degree `q - p = 4`.

* The edge set `S = {1, 2, 3, 4, 5}` (all edges except edge `0 = {0, 1}`) has `|S| = 5`,
  degrees `d_S = (2, 2, 3, 3)` (`K4_deg_fiveEdges`) and `v(S) = 4` (`K4_support_fiveEdges`).
  Its state `κ₀ = (0, 0, 0, 0)` (`K4FiveState`) has homological degree `1`
  (`K4_incResolutionDegree_fiveState`) and cohomological degree `4`.
* The Tor class `K4FiveClass ∈ Tor_1` is the specialization of the free generator of this state;
  it lies in the internal piece of degree `5` (`K4FiveClass_mem`), its full state vector is the
  single basis vector `e_{(S, κ₀)}` with coefficient `1` (`K4_incidenceTorFullState_fiveClass`),
  and it is nonzero (`K4FiveClass_ne_zero`).
* **The test** (`K4_torNormalization_fiveClass`): `Φ` sends it to the exterior class with the same
  state vector, with coefficient `+1` (`K4_torNormalization_state`,
  `K4_torNormalization_components`).
* **The representative, with its sign** (`K4_torNormalization_representative`,
  `K4_torNormalization_cocycle`): this exterior class is the image, under the biproduct inclusion
  of the summand `O(-2,-2,-3,-3)` of `S`, of the actual class in `H⁴` of the specified cell
  cocycle whose signed tensor coefficient vector (`vertexTwistCellCoefficientEquiv`) is the single
  overlap Laurent monomial `t₀⁻¹ t₁⁻¹ t₂⁻¹ t₃⁻¹` with coefficient `+1`.
* **Rescaling is detected** (`K4_torNormalization_pins_scalar`): for `λ ∈ ℂ`, the rescaled map
  `λ^1 Φ` passes this test iff `λ = 1`.

The unit test and the sign tests of edge signs, edge reversals and vertex swaps are referenced in
`BPFixedPoints.Incidence.IncidenceTorNormalization`. Not proved here: tests on other states of `K₄`
(they follow from `incidenceTorExteriorEquiv_stateClass` in the same way).
-/

namespace BPFixedPoints.Examples
open CategoryTheory TopologicalSpace AlgebraicGeometry CechProduct ProjectiveLine Multigraph
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section

local instance torNormalizationK4HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ (Fin 4))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The five edges of `K₄` other than edge `0 = {0, 1}`. -/
def K4FiveEdges : Set.powersetCard (Fin 6) 5 :=
  ⟨{1, 2, 3, 4, 5}, (by decide : ({1, 2, 3, 4, 5} : Finset (Fin 6)).card = 5)⟩

/-- The degrees of the five-edge set are `(2, 2, 3, 3)`. -/
theorem K4_deg_fiveEdges : K4.deg (K4FiveEdges : Finset (Fin 6)) = ![2, 2, 3, 3] := by
  decide

/-- The five-edge set covers all four vertices: `v(S) = 4`. -/
theorem K4_support_fiveEdges : K4.support (K4FiveEdges : Finset (Fin 6)) = Finset.univ := by
  decide

/-- The state `κ₀ = (0, 0, 0, 0)` of the twist `(2, 2, 3, 3)`: at every vertex the first basis
state of `H¹(O(-d_v))`, the Laurent monomial `t_v⁻¹`. -/
def K4FiveState : HBasis (K4.deg (K4FiveEdges : Finset (Fin 6))) :=
  fun v => ⟨0, by rw [K4_deg_fiveEdges]; fin_cases v <;> decide⟩

/-- The state `(S, κ₀)` has homological degree `p = |S| - v(S) = 1`. -/
theorem K4_incResolutionDegree_fiveState :
    K4.incResolutionDegree ⟨(K4FiveEdges : Finset (Fin 6)), K4FiveState⟩ = 1 := by
  change (K4FiveEdges : Finset (Fin 6)).card - (K4.support (K4FiveEdges : Finset (Fin 6))).card = 1
  rw [K4_support_fiveEdges]
  decide

/-- The twist of the five-edge set has cohomological degree `4`. -/
theorem K4_cohomologyDegree_fiveEdges :
    cohomologyDegree (K4.deg (K4FiveEdges : Finset (Fin 6))) = 4 :=
  K4.cohomologyDegree_deg_of_incResolutionDegree K4FiveEdges K4FiveState
    K4_incResolutionDegree_fiveState

/-- The Tor class in `Tor_1` of the state `(S, κ₀)`: the specialization of its free generator. -/
def K4FiveClass : K4.incidenceTor 1 :=
  K4.incidenceTorStateClass ⟨(K4FiveEdges : Finset (Fin 6)), K4FiveState⟩
    K4_incResolutionDegree_fiveState

/-- The class lies in the internal piece of bidegree `(1, 5)`. -/
theorem K4FiveClass_mem : K4FiveClass ∈ K4.incidenceTorInternalPiece 1 5 :=
  K4.incidenceTorStateClass_mem _ _ (Set.powersetCard.card_eq K4FiveEdges)

/-- The full state vector of the class is the single basis vector of `(S, κ₀)`. -/
theorem K4_incidenceTorFullState_fiveClass :
    K4.incidenceTorFullState 1 K4FiveClass =
      Finsupp.single ⟨(K4FiveEdges : Finset (Fin 6)), K4FiveState⟩ 1 :=
  K4.incidenceTorFullState_stateClass _ _

/-- The class is nonzero. -/
theorem K4FiveClass_ne_zero : K4FiveClass ≠ 0 :=
  K4.incidenceTorStateClass_ne_zero _ _

/-- **Acceptance test on `K₄` in bidegree `(1, 5)`.** The Tor-to-exterior isomorphism sends the
Tor class of `(S, κ₀)` to the exterior class of the same state in `H⁴`. -/
theorem K4_torNormalization_fiveClass :
    K4.incidenceTorExteriorEquiv (by decide : 1 ≤ 5) ⟨K4FiveClass, K4FiveClass_mem⟩ =
      K4.exteriorStateClass ℂ K4FiveEdges K4FiveState K4_cohomologyDegree_fiveEdges :=
  K4.incidenceTorExteriorEquiv_stateClass _ K4FiveEdges K4FiveState K4_incResolutionDegree_fiveState

/-- The image has the same state vector as the Tor class, with coefficient `+1`. -/
theorem K4_torNormalization_state :
    K4.exteriorCohomologyState ℂ 5 4
        (K4.incidenceTorExteriorEquiv (by decide : 1 ≤ 5) ⟨K4FiveClass, K4FiveClass_mem⟩) =
      Finsupp.single ⟨(K4FiveEdges : Finset (Fin 6)), K4FiveState⟩ 1 := by
  rw [K4_torNormalization_fiveClass, exteriorCohomologyState_stateClass]

/-- The state components of the image: `single κ₀ 1` in the summand of `S`, zero in the other
five summands of the fifth exterior bundle. -/
theorem K4_torNormalization_components :
    K4.exteriorBundleStateLinearEquiv ℂ 5 4
        (K4.incidenceTorExteriorEquiv (by decide : 1 ≤ 5) ⟨K4FiveClass, K4FiveClass_mem⟩) =
      Pi.single K4FiveEdges ⟨Finsupp.single K4FiveState 1,
        single_mem_stateDegreePiece ℂ K4FiveState K4_cohomologyDegree_fiveEdges⟩ := by
  rw [K4_torNormalization_fiveClass, exteriorBundleStateLinearEquiv_stateClass]

/-- **The explicit image.** The Tor class of `(S, κ₀)` goes to the image, under the biproduct
inclusion of the summand of `S`, of the actual class in `H⁴(O(-2,-2,-3,-3))` of the specified cell
cocycle `vertexTwistCellStateInclusion (single κ₀ 1)`. -/
theorem K4_torNormalization_representative :
    letI := vertexTwistCellModule ℂ (Fin 4)
      (fun v => -(K4.deg (K4FiveEdges : Finset (Fin 6)) v : ℤ)) 3
    K4.incidenceTorExteriorEquiv (by decide : 1 ≤ 5) ⟨K4FiveClass, K4FiveClass_mem⟩ =
      Sheaf.H.map (K4.exteriorIncl ℂ 5 K4FiveEdges) 4
        (vertexTwistCellActualLinearEquiv ℂ (Fin 4) _ 3
          (QuotientAddGroup.mk (vertexTwistCellStateInclusion ℂ (Fin 4)
            (K4.deg (K4FiveEdges : Finset (Fin 6))) 4
            ⟨Finsupp.single K4FiveState 1,
              single_mem_stateDegreePiece ℂ K4FiveState K4_cohomologyDegree_fiveEdges⟩))) := by
  rw [K4_torNormalization_fiveClass, exteriorStateClass_succ]

/-- At every vertex the state `κ₀` is included as the single overlap Laurent monomial `t⁻¹`. -/
theorem K4_lineInclusionMonomials_fiveState (v : Fin 4) :
    lineInclusionMonomials (K4.deg (K4FiveEdges : Finset (Fin 6)) v) (K4FiveState v) =
      {Sum.inr (Sum.inr (-1))} := by
  fin_cases v <;> rfl

/-- The contraction inclusion of `single κ₀ 1` is the single overlap Laurent monomial
`t₀⁻¹ t₁⁻¹ t₂⁻¹ t₃⁻¹` with coefficient `+1`. -/
theorem K4_contraction_i_fiveState :
    (contraction ℂ (K4.deg (K4FiveEdges : Finset (Fin 6)))).i (Finsupp.single K4FiveState 1) =
      Finsupp.single (fun _ => Sum.inr (Sum.inr (-1))) 1 := by
  ext b
  rw [contraction_i_single_apply]
  simp only [K4_lineInclusionMonomials_fiveState, Finset.mem_singleton]
  by_cases hb : b = fun _ => Sum.inr (Sum.inr (-1))
  · subst hb
    simp
  · rw [Finsupp.single_eq_of_ne hb]
    exact ite_eq_right_iff.mpr fun h => absurd (funext h) hb

/-- **The sign convention of the representative.** The signed tensor coefficient vector of the
cell cocycle representing the image is the overlap Laurent monomial `t₀⁻¹ t₁⁻¹ t₂⁻¹ t₃⁻¹` with
coefficient `+1`. -/
theorem K4_torNormalization_cocycle :
    (vertexTwistCellCoefficientEquiv ℂ (Fin 4) (K4.deg (K4FiveEdges : Finset (Fin 6))) 4
        (vertexTwistCellStateInclusion ℂ (Fin 4) (K4.deg (K4FiveEdges : Finset (Fin 6))) 4
          ⟨Finsupp.single K4FiveState 1,
            single_mem_stateDegreePiece ℂ K4FiveState K4_cohomologyDegree_fiveEdges⟩).val).val =
      Finsupp.single (fun _ => Sum.inr (Sum.inr (-1))) 1 := by
  rw [vertexTwistCellStateInclusion_coefficient]
  exact K4_contraction_i_fiveState

/-- **Rescaling is detected.** For `λ ∈ ℂ`, the rescaled isomorphism `λ^p Φ` with `p = 1` passes
the `K₄` test iff `λ = 1`. -/
theorem K4_torNormalization_pins_scalar (c : ℂ) :
    letI := K4.exteriorBundleCohomologyModule ℂ 5 (5 - 1)
    c ^ 1 • K4.incidenceTorExteriorEquiv (by decide : 1 ≤ 5) ⟨K4FiveClass, K4FiveClass_mem⟩ =
      K4.exteriorStateClass ℂ K4FiveEdges K4FiveState K4_cohomologyDegree_fiveEdges ↔ c = 1 := by
  rw [pow_one]
  exact K4.smul_incidenceTorExteriorEquiv_stateClass_eq_iff _ K4FiveEdges K4FiveState
    K4_incResolutionDegree_fiveState c

end
end BPFixedPoints.Examples
