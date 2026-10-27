import BPFixedPoints.Incidence.IncidenceEdgeMapRings
import BPFixedPoints.Incidence.IncidenceEdgeSignRings

/-!
# Signed edge maps act on the coefficient ring and on the incidence ring

A signed edge map `φ : SignedEdgeMap G H` is an edge map `G → H` (vertices fixed, an arbitrary
function of edges, reversal flags) together with an edge sign `ε = φ.edgeSign` on the source
edges: the orientation-line signs `ε_φ(e)` of the functoriality proposition of the supplement,
which uses `e ↦ ε_φ(e) e_{φ(e)}` and `a_φ^* b_e = ε_φ(e) b_{φ(e)}` for general maps.

**Order convention.** Every map of a signed edge map is the sign change on the source graph `G`
followed by the unsigned edge map `G → H`, as for signed edge relabelings.

* The coefficient ring homomorphism (`signedCoeffRingHom`, `signedCoeffAlgHom`) is
  `c_{e,α,β} ↦ ε_e c_{φ e,α,β}`, with the endpoint indices exchanged when `e` is reversed
  (`signedCoeffAlgHom_X`): the coefficient sign change `edgeSignCoeff ε` followed by the coefficient
  renaming `EdgeMap.coeffAlgHom`. It preserves the coefficient origin
  (`constantCoeff_signedCoeffRingHom`).
* The sign change followed by the renaming of chart variables carries the chart equation of `e`
  to `ε_e` times the chart equation of `φ e` (`rename_varSignHom_incChartEq`), the Lean
  counterpart of `a_φ^* b_e = ε_φ(e) b_{φ(e)}`; the same holds for the torus relations.
* The incidence ring homomorphism (`signedIncidenceHom`) is the incidence sign change of `G`
  followed by the incidence homomorphism of the edge map; it intertwines the coefficient maps
  (`signedIncidenceHom_coeffHom`).

Identity (`refl`, trivial sign) and composition (`trans`, signs `e ↦ ε_φ(e) · ε_ψ(φ e)`) of signed
edge maps are defined here; unsigned edge maps (`ofEdgeMap`) and pure sign changes (`ofEdgeSign`) are
special cases. Signed relabelings are compared with signed edge maps in
`IncidenceSignedEdgeMapTor.lean`.

None of these ring maps is an isomorphism in general, and the coefficient ring homomorphism is not
flat in general. Functoriality of the ring maps themselves is not stated; the functoriality laws are
proved on Tor and on exterior cohomology in `IncidenceSignedEdgeMapTor.lean` and
`IncidenceSignedEdgeMapExterior.lean`.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- A signed edge map: an edge map together with the orientation-line sign `ε_φ(e) ∈ {±1}` of
every source edge. -/
structure SignedEdgeMap {V E E' : Type} (G : Multigraph V E) (H : Multigraph V E') extends
    EdgeMap G H where
  /-- The orientation-line sign of each source edge. -/
  edgeSign : EdgeSign E

namespace SignedEdgeMap

/-! ## Identity, composition and special cases -/

/-- The identity signed edge map: the identity edge map with trivial signs. -/
def refl {V E : Type} (G : Multigraph V E) : SignedEdgeMap G G where
  toEdgeMap := EdgeMap.refl G
  edgeSign := 1

/-- The composite of signed edge maps: the composite edge map with signs
`e ↦ ε_φ(e) · ε_ψ(φ e)`. -/
def trans {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'} {K : Multigraph V E''}
    (φ : SignedEdgeMap G H) (ψ : SignedEdgeMap H K) : SignedEdgeMap G K where
  toEdgeMap := φ.toEdgeMap.trans ψ.toEdgeMap
  edgeSign e := φ.edgeSign e * ψ.edgeSign (φ.edge e)

@[simp] theorem refl_toEdgeMap {V E : Type} (G : Multigraph V E) :
    (refl G).toEdgeMap = EdgeMap.refl G := rfl

@[simp] theorem refl_edgeSign {V E : Type} (G : Multigraph V E) : (refl G).edgeSign = 1 := rfl

@[simp] theorem trans_toEdgeMap {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : SignedEdgeMap G H) (ψ : SignedEdgeMap H K) :
    (φ.trans ψ).toEdgeMap = φ.toEdgeMap.trans ψ.toEdgeMap := rfl

theorem trans_edgeSign_apply {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : SignedEdgeMap G H) (ψ : SignedEdgeMap H K) (e : E) :
    (φ.trans ψ).edgeSign e = φ.edgeSign e * ψ.edgeSign (φ.edge e) := rfl

/-- An unsigned edge map, as a signed edge map with trivial signs. -/
def ofEdgeMap {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H) :
    SignedEdgeMap G H where
  toEdgeMap := φ
  edgeSign := 1

/-- A pure sign change, as a signed edge map with the identity edge map. -/
def ofEdgeSign {V E : Type} (G : Multigraph V E) (ε : EdgeSign E) : SignedEdgeMap G G where
  toEdgeMap := EdgeMap.refl G
  edgeSign := ε

end SignedEdgeMap

namespace SignedEdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)

/-! ## The coefficient ring homomorphism -/

/-- The coefficient ring homomorphism of a signed edge map: the coefficient sign change of `G`
followed by the coefficient renaming of the edge map,
`c_{e,α,β} ↦ ε_e c_{φ e,α,β}` (endpoint indices exchanged for a reversed edge). -/
noncomputable def signedCoeffRingHom : IncCoeffRing E →+* IncCoeffRing E' :=
  φ.toEdgeMap.coeffRingHom.comp (edgeSignCoeff φ.edgeSign).toRingEquiv.toRingHom

/-- The coefficient ring homomorphism of a signed edge map, as an algebra homomorphism. -/
noncomputable def signedCoeffAlgHom : IncCoeffRing E →ₐ[ℂ] IncCoeffRing E' :=
  φ.toEdgeMap.coeffAlgHom.comp (edgeSignCoeff φ.edgeSign).toAlgHom

/-- The coefficient ring homomorphism is the sign change followed by the renaming. -/
theorem signedCoeffRingHom_apply (r : IncCoeffRing E) :
    φ.signedCoeffRingHom r = φ.toEdgeMap.coeffAlgHom (edgeSignCoeff φ.edgeSign r) := rfl

theorem signedCoeffAlgHom_apply (r : IncCoeffRing E) :
    φ.signedCoeffAlgHom r = φ.toEdgeMap.coeffAlgHom (edgeSignCoeff φ.edgeSign r) := rfl

/-- The ring homomorphism underlying the algebra homomorphism. -/
theorem signedCoeffAlgHom_toRingHom :
    (φ.signedCoeffAlgHom : IncCoeffRing E →+* IncCoeffRing E') = φ.signedCoeffRingHom := rfl

/-- The coefficient ring homomorphism on a variable:
`c_{e,ab} ↦ ε_e c_{φ e, endpointIndex e ab}`. -/
@[simp] theorem signedCoeffAlgHom_X (e : E) (ab : Fin 2 × Fin 2) :
    φ.signedCoeffAlgHom (X (e, ab)) =
      ((φ.edgeSign e : ℤ) : IncCoeffRing E') * X (φ.edge e, φ.toEdgeMap.endpointIndex e ab) := by
  rw [signedCoeffAlgHom_apply, edgeSignCoeff_X, map_mul, map_intCast, EdgeMap.coeffAlgHom_X,
    EdgeMap.coeffIdxMap_apply]

@[simp] theorem signedCoeffRingHom_X (e : E) (ab : Fin 2 × Fin 2) :
    φ.signedCoeffRingHom (X (e, ab)) =
      ((φ.edgeSign e : ℤ) : IncCoeffRing E') * X (φ.edge e, φ.toEdgeMap.endpointIndex e ab) :=
  φ.signedCoeffAlgHom_X e ab

/-- The coefficient ring homomorphism preserves the coefficient origin. -/
@[simp] theorem constantCoeff_signedCoeffRingHom (r : IncCoeffRing E) :
    constantCoeff (φ.signedCoeffRingHom r) = constantCoeff r := by
  rw [signedCoeffRingHom_apply, ← EdgeMap.coeffRingHom_apply, EdgeMap.constantCoeff_coeffRingHom,
    constantCoeff_edgeSignCoeff]

/-- The coefficient ring homomorphism is compatible with the coefficient origins. -/
theorem constantCoeff_comp_signedCoeffRingHom :
    (constantCoeff : IncCoeffRing E' →+* ℂ).comp φ.signedCoeffRingHom = constantCoeff :=
  RingHom.ext φ.constantCoeff_signedCoeffRingHom

/-! ## Chart equations and torus relations -/

/-- **The pullback of chart equations.** The sign change followed by the renaming of chart
variables carries the chart equation of `e` to `ε_e` times the chart equation of the image edge,
the counterpart of `a_φ^* b_e = ε_φ(e) b_{φ(e)}`. -/
theorem rename_varSignHom_incChartEq (σ : V → Bool) (e : E) :
    rename φ.toEdgeMap.chartVarMap (varSignHom φ.edgeSign.chartVarSign (G.incChartEq σ e)) =
      ((φ.edgeSign e : ℤ) : MvPolynomial (IncChartVar V E') ℂ) * H.incChartEq σ (φ.edge e) := by
  rw [G.varSignHom_incChartEq φ.edgeSign σ e, map_mul, map_intCast, EdgeMap.rename_incChartEq]

/-- The sign change followed by the renaming of torus variables carries a torus relation to its
sign times the torus relation of the mapped index. -/
theorem rename_varSignHom_incTorusRel (i : V ⊕ E) :
    rename φ.toEdgeMap.torusVarMap (varSignHom φ.edgeSign.torusVarSign (G.incTorusRel i)) =
      ((φ.edgeSign.relSign i : ℤ) : MvPolynomial (IncTorusVar V E') ℂ) *
        H.incTorusRel (φ.toEdgeMap.relIdxMap i) := by
  rw [G.varSignHom_incTorusRel φ.edgeSign i, map_mul, map_intCast, EdgeMap.rename_incTorusRel]

/-! ## The incidence ring homomorphism -/

/-- The algebra homomorphism of common torus rings of a signed edge map: the torus sign change of
`G` followed by the torus homomorphism of the edge map. -/
noncomputable def signedTorusHom : G.IncTorusRing →ₐ[ℂ] H.IncTorusRing :=
  φ.toEdgeMap.torusHom.comp (G.edgeSignTorus φ.edgeSign).toAlgHom

/-- The torus homomorphism is the torus sign change followed by the torus homomorphism of the
edge map. -/
theorem signedTorusHom_apply (x : G.IncTorusRing) :
    φ.signedTorusHom x = φ.toEdgeMap.torusHom (G.edgeSignTorus φ.edgeSign x) := rfl

/-- The algebra homomorphism of chart rings of a signed edge map. -/
noncomputable def signedChartHom (σ : V → Bool) : G.IncChartRing σ →ₐ[ℂ] H.IncChartRing σ :=
  (φ.toEdgeMap.chartHom σ).comp (G.edgeSignChart φ.edgeSign σ).toAlgHom

/-- The torus homomorphism intertwines the chart restrictions. -/
theorem signedTorusHom_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    φ.signedTorusHom (G.incChartMap σ y) = H.incChartMap σ (φ.signedChartHom σ y) := by
  rw [signedTorusHom_apply, edgeSignTorus_incChartMap, EdgeMap.torusHom_incChartMap]
  rfl

/-- The incidence ring homomorphism of a signed edge map: the incidence sign change of `G`
followed by the incidence homomorphism of the edge map. -/
noncomputable def signedIncidenceHom : G.IncidenceRing →ₐ[ℂ] H.IncidenceRing :=
  φ.toEdgeMap.incidenceHom.comp (G.edgeSignIncidence φ.edgeSign).toAlgHom

/-- The incidence homomorphism is the incidence sign change followed by the incidence homomorphism
of the edge map. -/
theorem signedIncidenceHom_apply (x : G.IncidenceRing) :
    φ.signedIncidenceHom x = φ.toEdgeMap.incidenceHom (G.edgeSignIncidence φ.edgeSign x) := rfl

/-- In the common torus ring the incidence homomorphism is the torus homomorphism. -/
@[simp] theorem signedIncidenceHom_val (x : G.IncidenceRing) :
    (φ.signedIncidenceHom x : H.IncTorusRing) = φ.signedTorusHom x.val := rfl

/-- The incidence ring homomorphism intertwines the coefficient maps through the signed
coefficient homomorphism. -/
theorem signedIncidenceHom_coeffHom (r : IncCoeffRing E) :
    φ.signedIncidenceHom (G.coeffHom r) = H.coeffHom (φ.signedCoeffAlgHom r) := by
  rw [signedIncidenceHom_apply, edgeSignIncidence_coeffHom, EdgeMap.incidenceHom_coeffHom]
  rfl

/-- The incidence ring homomorphism intertwines the coefficient actions. -/
theorem signedIncidenceHom_coeff_mul (r : IncCoeffRing E) (x : G.IncidenceRing) :
    φ.signedIncidenceHom (G.coeffHom r * x) =
      H.coeffHom (φ.signedCoeffRingHom r) * φ.signedIncidenceHom x := by
  rw [map_mul, signedIncidenceHom_coeffHom]
  rfl

/-! ## Special cases -/

/-- For trivial signs the coefficient homomorphism is that of the edge map. -/
theorem ofEdgeMap_signedCoeffAlgHom (ψ : EdgeMap G H) (r : IncCoeffRing E) :
    (ofEdgeMap ψ).signedCoeffAlgHom r = ψ.coeffAlgHom r := by
  rw [signedCoeffAlgHom_apply]
  exact congrArg ψ.coeffAlgHom (edgeSignCoeff_one r)

end SignedEdgeMap

end BPFixedPoints.Multigraph
