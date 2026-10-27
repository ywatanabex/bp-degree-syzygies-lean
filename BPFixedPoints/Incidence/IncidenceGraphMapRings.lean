import BPFixedPoints.Incidence.IncidenceSignedEdgeMapRings
import BPFixedPoints.Incidence.IncidenceVertexMapRings

/-!
# General graph maps act on the coefficient ring and on the incidence ring

A graph map `φ : GraphMap G H` from `G : Multigraph V E` to `H : Multigraph W E'` consists of a
vertex function `vertex : V → W`, an edge function `edge : E → E'`, reversal flags and edge signs
`ε = φ.edgeSign`, such that the endpoints of the image edge `φ e` are the images of the endpoints of
`e`, in the same order or exchanged according to the reversal flag. These are the graph maps of the
functoriality proposition of the paper, with the orientation-line signs `ε_φ(e)`. Vertices and edges
may be identified. The noncontracting condition (`IsNoncontracting`: the two distinct endpoints of
an edge keep distinct images) is recorded separately and is not used by any ring map.

**Factorization.** Every graph map factors as `G → G_v → H`, where `G_v = G.pushVertices vertex`
has the vertices of `H` and the edges of `G`:
* the vertex factor `vertexFactor : VertexMap G G_v` identifies vertices and keeps the edges;
* the edge factor `edgeFactor : SignedEdgeMap G_v H` keeps the vertices and maps the edges with the
  reversal flags and signs of `φ`.
Conversely vertex maps and signed edge maps are graph maps (`VertexMap.toGraphMap`,
`SignedEdgeMap.toGraphMap`), and `φ` is the composite of its two factors
(`toGraphMap_vertexFactor_trans_edgeFactor`).

**Intrinsic ring maps.** Defined directly from `φ`, not from the factorization:
* the coefficient ring map (`coeffAlgHom`, `coeffRingHom`) copies a coefficient with its sign,
  `c_{e,α,β} ↦ ε_e c_{φ e,α,β}`, with the endpoint indices exchanged for a reversed edge;
* the torus ring map (`torusHom`) is the substitution `t_v ↦ t_{φ v}`, `s_v ↦ s_{φ v}`,
  `c ↦ ε c'` on the common tori (`torusPolyHom`), i.e. pullback of functions along
  `(a_φ, β_φ)`; it carries the torus relation of an edge `e` to `ε_e` times the relation of `φ e`
  (`torusPolyHom_incTorusRel`, the counterpart of `a_φ^* b_e = ε_φ(e) b_{φ(e)}`);
* the incidence ring map (`incidenceHom`) is the restriction of the torus ring map.

The intrinsic maps are the composites of the maps of the two factors (`coeffAlgHom_eq_edgeFactor`,
`torusHom_eq_comp`, `incidenceHom_eq_comp`); that the torus ring map preserves the incidence rings
is proved through this factorization. They intertwine the coefficient maps
(`incidenceHom_coeffHom`), preserve the coefficient origin, and satisfy the functor laws for the
identity graph map (`refl`) and composition (`trans`, with reversal flags combined by `xor` and
signs `e ↦ ε_φ(e) · ε_ψ(φ e)`): `coeffAlgHom_refl`, `coeffAlgHom_trans`, `torusHom_refl`,
`torusHom_trans`, `incidenceHom_refl`, `incidenceHom_trans`. For vertex maps and signed edge maps,
regarded as graph maps, they are the maps of those (`VertexMap.toGraphMap_incidenceHom`,
`SignedEdgeMap.toGraphMap_incidenceHom` and the coefficient versions).

Not covered here: chart ring maps of general graph maps, gradings, and the disjoint union formula.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- A graph map `G → H`: a vertex function, an edge function, reversal flags and orientation-line
signs `ε_φ(e) ∈ {±1}`, such that the endpoints of the image of an edge are the images of its
endpoints, exchanged when the edge is reversed. Vertices and edges may be identified. -/
structure GraphMap {V W E E' : Type} (G : Multigraph V E) (H : Multigraph W E') where
  /-- The vertex function. -/
  vertex : V → W
  /-- The edge function. -/
  edge : E → E'
  /-- Whether the endpoint order of an edge is reversed by the map. -/
  reversed : E → Bool
  /-- The orientation-line sign of each source edge. -/
  edgeSign : EdgeSign E
  /-- The first endpoint of the image edge. -/
  fst_edge : ∀ e, H.fst (edge e) = if reversed e then vertex (G.snd e) else vertex (G.fst e)
  /-- The second endpoint of the image edge. -/
  snd_edge : ∀ e, H.snd (edge e) = if reversed e then vertex (G.fst e) else vertex (G.snd e)

namespace GraphMap

/-! ## Identity, composition and the noncontracting condition -/

section Basic

variable {V W X E E' E'' : Type} {G : Multigraph V E} {H : Multigraph W E'}
  {K : Multigraph X E''}

/-- Graph maps with the same data are equal. -/
theorem ext' {φ ψ : GraphMap G H} (hv : φ.vertex = ψ.vertex) (he : φ.edge = ψ.edge)
    (hr : φ.reversed = ψ.reversed) (hs : φ.edgeSign = ψ.edgeSign) : φ = ψ := by
  cases φ
  cases ψ
  cases hv
  cases he
  cases hr
  cases hs
  rfl

/-- The identity graph map: identity on vertices and edges, no reversal, trivial signs. -/
def refl (G : Multigraph V E) : GraphMap G G where
  vertex := id
  edge := id
  reversed _ := false
  edgeSign := 1
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The composite of two graph maps: composite vertex and edge functions, an edge is reversed when
exactly one of the two maps reverses it, and the signs multiply, `e ↦ ε_φ(e) · ε_ψ(φ e)`. -/
def trans (φ : GraphMap G H) (ψ : GraphMap H K) : GraphMap G K where
  vertex := ψ.vertex ∘ φ.vertex
  edge := ψ.edge ∘ φ.edge
  reversed e := xor (φ.reversed e) (ψ.reversed (φ.edge e))
  edgeSign e := φ.edgeSign e * ψ.edgeSign (φ.edge e)
  fst_edge e := by
    simp only [Function.comp_apply]
    rw [ψ.fst_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl
  snd_edge e := by
    simp only [Function.comp_apply]
    rw [ψ.snd_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl

@[simp] theorem refl_vertex (G : Multigraph V E) : (refl G).vertex = id := rfl

@[simp] theorem refl_edge (G : Multigraph V E) : (refl G).edge = id := rfl

@[simp] theorem refl_reversed (G : Multigraph V E) (e : E) : (refl G).reversed e = false := rfl

@[simp] theorem refl_edgeSign (G : Multigraph V E) : (refl G).edgeSign = 1 := rfl

@[simp] theorem trans_vertex (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).vertex = ψ.vertex ∘ φ.vertex := rfl

@[simp] theorem trans_edge (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).edge = ψ.edge ∘ φ.edge := rfl

theorem trans_reversed (φ : GraphMap G H) (ψ : GraphMap H K) (e : E) :
    (φ.trans ψ).reversed e = xor (φ.reversed e) (ψ.reversed (φ.edge e)) := rfl

theorem trans_edgeSign_apply (φ : GraphMap G H) (ψ : GraphMap H K) (e : E) :
    (φ.trans ψ).edgeSign e = φ.edgeSign e * ψ.edgeSign (φ.edge e) := rfl

/-- The identity is a left unit for composition. -/
theorem refl_trans (φ : GraphMap G H) : (refl G).trans φ = φ := by
  refine ext' rfl rfl ?_ ?_
  · funext e
    exact Bool.false_xor _
  · funext e
    exact one_mul _

/-- The identity is a right unit for composition. -/
theorem trans_refl (φ : GraphMap G H) : φ.trans (refl H) = φ := by
  refine ext' rfl rfl ?_ ?_
  · funext e
    exact Bool.xor_false _
  · funext e
    exact mul_one _

/-- Composition of graph maps is associative. -/
theorem trans_assoc {Y E''' : Type} {L : Multigraph Y E'''} (φ : GraphMap G H) (χ : GraphMap H K)
    (ψ : GraphMap K L) : (φ.trans χ).trans ψ = φ.trans (χ.trans ψ) := by
  refine ext' rfl rfl ?_ ?_
  · funext e
    exact Bool.xor_assoc _ _ _
  · funext e
    exact mul_assoc _ _ _

/-- The paper's noncontracting condition: the two distinct endpoints of an edge keep distinct
images. It is not used by the ring maps. -/
def IsNoncontracting (φ : GraphMap G H) : Prop :=
  ∀ e, G.fst e ≠ G.snd e → φ.vertex (G.fst e) ≠ φ.vertex (G.snd e)

/-- A noncontracting graph map sends a non-loop edge to a non-loop edge. -/
theorem fst_edge_ne_snd_edge (φ : GraphMap G H) (hφ : φ.IsNoncontracting) {e : E}
    (he : G.fst e ≠ G.snd e) : H.fst (φ.edge e) ≠ H.snd (φ.edge e) := by
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · exact hφ e he
  · exact fun h => hφ e he h.symm

end Basic

/-! ## The factorization through the intermediate graph -/

section Factorization

variable {V W E E' : Type} {G : Multigraph V E} {H : Multigraph W E'} (φ : GraphMap G H)

/-- The vertex factor `G → G_v` of a graph map, with `G_v = G.pushVertices φ.vertex`: the vertex
function of `φ`, edges unchanged. -/
def vertexFactor : VertexMap G (G.pushVertices φ.vertex) := VertexMap.ofFun G φ.vertex

/-- The edge factor `G_v → H` of a graph map: vertices fixed, the edge function, reversal flags
and signs of `φ`. -/
def edgeFactor : SignedEdgeMap (G.pushVertices φ.vertex) H where
  edge := φ.edge
  reversed := φ.reversed
  fst_edge := φ.fst_edge
  snd_edge := φ.snd_edge
  edgeSign := φ.edgeSign

@[simp] theorem vertexFactor_vertex : φ.vertexFactor.vertex = φ.vertex := rfl

@[simp] theorem edgeFactor_edge : φ.edgeFactor.edge = φ.edge := rfl

@[simp] theorem edgeFactor_reversed : φ.edgeFactor.reversed = φ.reversed := rfl

@[simp] theorem edgeFactor_edgeSign : φ.edgeFactor.edgeSign = φ.edgeSign := rfl

end Factorization

end GraphMap

/-- A vertex map, as a graph map: edges unchanged, no reversal, trivial signs. -/
def VertexMap.toGraphMap {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : GraphMap G H where
  vertex := φ.vertex
  edge := id
  reversed _ := false
  edgeSign := 1
  fst_edge := φ.fst_edge
  snd_edge := φ.snd_edge

/-- A signed edge map, as a graph map: vertices fixed. -/
def SignedEdgeMap.toGraphMap {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeMap G H) : GraphMap G H where
  vertex := id
  edge := φ.edge
  reversed := φ.reversed
  edgeSign := φ.edgeSign
  fst_edge := φ.fst_edge
  snd_edge := φ.snd_edge

namespace GraphMap

variable {V W E E' : Type} {G : Multigraph V E} {H : Multigraph W E'}

/-- **The factorization.** A graph map is the composite of its vertex factor and its edge
factor. -/
theorem toGraphMap_vertexFactor_trans_edgeFactor (φ : GraphMap G H) :
    φ.vertexFactor.toGraphMap.trans φ.edgeFactor.toGraphMap = φ := by
  refine ext' rfl rfl ?_ ?_
  · funext e
    exact Bool.false_xor _
  · funext e
    exact one_mul _

/-! ## The coefficient ring map -/

section Coefficients

variable (φ : GraphMap G H)

/-- The endpoint-index pair of the image coefficient: exchanged when the edge is reversed. -/
def endpointIndex (e : E) (ab : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  if φ.reversed e then ab.swap else ab

/-- The map of coefficient indices: an index of an edge goes to the corresponding index of its
image edge. -/
def coeffIdxMap (c : IncCoeffIdx E) : IncCoeffIdx E' := (φ.edge c.1, φ.endpointIndex c.1 c.2)

@[simp] theorem coeffIdxMap_apply (e : E) (ab : Fin 2 × Fin 2) :
    φ.coeffIdxMap (e, ab) = (φ.edge e, φ.endpointIndex e ab) := rfl

/-- **The coefficient ring map** of a graph map, as an algebra homomorphism: a coefficient of an
image edge is copied with its sign to every edge above it,
`c_{e,α,β} ↦ ε_e c_{φ e,α,β}` (endpoint indices exchanged for a reversed edge). -/
noncomputable def coeffAlgHom : IncCoeffRing E →ₐ[ℂ] IncCoeffRing E' :=
  aeval fun c => ((φ.edgeSign c.1 : ℤ) : IncCoeffRing E') * X (φ.coeffIdxMap c)

/-- **The coefficient ring map** of a graph map. -/
noncomputable def coeffRingHom : IncCoeffRing E →+* IncCoeffRing E' :=
  φ.coeffAlgHom.toRingHom

theorem coeffRingHom_apply (r : IncCoeffRing E) : φ.coeffRingHom r = φ.coeffAlgHom r := rfl

/-- The coefficient ring map on a variable. -/
@[simp] theorem coeffAlgHom_X (c : IncCoeffIdx E) :
    φ.coeffAlgHom (X c) = ((φ.edgeSign c.1 : ℤ) : IncCoeffRing E') * X (φ.coeffIdxMap c) :=
  aeval_X _ _

/-- The coefficient ring map is compatible with the coefficient origins. -/
theorem constantCoeff_comp_coeffRingHom :
    (constantCoeff : IncCoeffRing E' →+* ℂ).comp φ.coeffRingHom = constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [coeffRingHom]
  · intro c
    simp [coeffRingHom]

/-- The coefficient ring map preserves the coefficient origin. -/
@[simp] theorem constantCoeff_coeffRingHom (r : IncCoeffRing E) :
    constantCoeff (φ.coeffRingHom r) = constantCoeff r :=
  RingHom.congr_fun φ.constantCoeff_comp_coeffRingHom r

end Coefficients

/-! ## The torus ring map -/

section Torus

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] (φ : GraphMap G H)

/-- The images of the torus variables: `t_v ↦ t_{φ v}`, `s_v ↦ s_{φ v}`, and a coefficient goes to
the signed coefficient of the image edge. -/
noncomputable def torusVal : IncTorusVar V E → MvPolynomial (IncTorusVar W E') ℂ
  | Sum.inl v => X (Sum.inl (φ.vertex v))
  | Sum.inr (Sum.inl v) => X (Sum.inr (Sum.inl (φ.vertex v)))
  | Sum.inr (Sum.inr c) =>
      ((φ.edgeSign c.1 : ℤ) : MvPolynomial (IncTorusVar W E') ℂ) *
        X (Sum.inr (Sum.inr (φ.coeffIdxMap c)))

/-- The substitution of torus variables of a graph map, on polynomials: pullback of functions along
`(a_φ, β_φ)`. -/
noncomputable def torusPolyHom :
    MvPolynomial (IncTorusVar V E) ℂ →ₐ[ℂ] MvPolynomial (IncTorusVar W E') ℂ :=
  aeval φ.torusVal

@[simp] theorem torusPolyHom_X (w : IncTorusVar V E) : φ.torusPolyHom (X w) = φ.torusVal w :=
  aeval_X _ _

/-- The substitution is the renaming of vertex variables of the vertex factor, followed by the sign
change and the renaming of coefficient variables of the edge factor. -/
theorem torusPolyHom_eq_comp :
    φ.torusPolyHom = (rename φ.edgeFactor.toEdgeMap.torusVarMap).comp
      ((varSignHom (φ.edgeSign.torusVarSign (V := W))).comp
        (rename φ.vertexFactor.torusVarMap)) := by
  apply MvPolynomial.algHom_ext
  intro w
  rcases w with v | v | c
  · simp [torusVal, EdgeMap.torusVarMap]
  · simp [torusVal, EdgeMap.torusVarMap]
  · simp only [torusPolyHom_X, torusVal, AlgHom.comp_apply, rename_X,
      VertexMap.torusVarMap_inr_inr, varSignHom_X, EdgeSign.torusVarSign_inr_inr, map_mul,
      map_intCast, EdgeMap.torusVarMap, Sum.map_inr]
    rfl

/-- The map of torus relation indices. -/
def relIdxMap : V ⊕ E → W ⊕ E' := Sum.map φ.vertex φ.edge

/-- **Pullback of the edge equations.** The substitution carries the torus relation of an index
to its sign times the torus relation of the image index; for an edge `e` this is
`a_φ^* b_e = ε_φ(e) b_{φ(e)}`. -/
theorem torusPolyHom_incTorusRel (i : V ⊕ E) :
    φ.torusPolyHom (G.incTorusRel i) =
      ((φ.edgeSign.relSign i : ℤ) : MvPolynomial (IncTorusVar W E') ℂ) *
        H.incTorusRel (φ.relIdxMap i) := by
  rw [torusPolyHom_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply,
    VertexMap.rename_incTorusRel]
  have h := φ.edgeFactor.rename_varSignHom_incTorusRel (φ.vertexFactor.relIdxMap i)
  rw [edgeFactor_edgeSign] at h
  rw [h]
  rcases i with v | e <;> rfl

/-- The torus relations of `G` map into the torus ideal of `H`. -/
theorem torusIdeal_le_comap :
    Ideal.span (Set.range G.incTorusRel) ≤
      (Ideal.span (Set.range H.incTorusRel)).comap φ.torusPolyHom := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, torusPolyHom_incTorusRel]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- **The torus ring map** of a graph map: the substitution of torus variables on the common
torus rings. -/
noncomputable def torusHom : G.IncTorusRing →ₐ[ℂ] H.IncTorusRing :=
  Ideal.quotientMapₐ _ φ.torusPolyHom φ.torusIdeal_le_comap

theorem torusHom_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    φ.torusHom (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (φ.torusPolyHom p) := rfl

/-- **The torus ring map is the composite of the factors**, elementwise: the torus map of the
vertex factor followed by the signed torus map of the edge factor. -/
theorem torusHom_eq_comp_apply (x : G.IncTorusRing) :
    φ.torusHom x = φ.edgeFactor.signedTorusHom (φ.vertexFactor.torusHom x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [torusHom_mk, VertexMap.torusHom_mk, SignedEdgeMap.signedTorusHom_apply, edgeSignTorus_mk,
    EdgeMap.torusHom_mk, torusPolyHom_eq_comp]
  rfl

/-- **The torus ring map is the composite of the factors.** -/
theorem torusHom_eq_comp :
    φ.torusHom = φ.edgeFactor.signedTorusHom.comp φ.vertexFactor.torusHom :=
  AlgHom.ext φ.torusHom_eq_comp_apply

/-- The torus ring map sends the incidence ring of `G` into the incidence ring of `H`. -/
theorem torusHom_mem_incidenceRing {x : G.IncTorusRing} (hx : x ∈ G.IncidenceRing) :
    φ.torusHom x ∈ H.IncidenceRing := by
  rw [torusHom_eq_comp_apply]
  exact (φ.edgeFactor.signedIncidenceHom (φ.vertexFactor.incidenceHom ⟨x, hx⟩)).property

end Torus

/-! ## The incidence ring map -/

section Incidence

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] (φ : GraphMap G H)

/-- **The incidence ring map** `𝒰_φ : 𝒰_G → 𝒰_H` of a graph map: the restriction of the torus ring
map, i.e. pullback of regular functions along `(a_φ, β_φ)`. -/
noncomputable def incidenceHom : G.IncidenceRing →ₐ[ℂ] H.IncidenceRing :=
  (φ.torusHom.comp G.IncidenceRing.val).codRestrict H.IncidenceRing
    fun x => φ.torusHom_mem_incidenceRing x.property

@[simp] theorem incidenceHom_val (x : G.IncidenceRing) :
    (φ.incidenceHom x : H.IncTorusRing) = φ.torusHom x.val := rfl

/-- **The incidence ring map is the composite of the factors**, elementwise. -/
theorem incidenceHom_eq_comp_apply (x : G.IncidenceRing) :
    φ.incidenceHom x = φ.edgeFactor.signedIncidenceHom (φ.vertexFactor.incidenceHom x) :=
  Subtype.ext (φ.torusHom_eq_comp_apply x.val)

/-- **The incidence ring map is the composite of the factors.** -/
theorem incidenceHom_eq_comp :
    φ.incidenceHom = φ.edgeFactor.signedIncidenceHom.comp φ.vertexFactor.incidenceHom :=
  AlgHom.ext φ.incidenceHom_eq_comp_apply

/-- **The coefficient ring map is that of the edge factor**; the vertex factor does not change the
coefficients. -/
theorem coeffAlgHom_eq_edgeFactor : φ.coeffAlgHom = φ.edgeFactor.signedCoeffAlgHom := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [coeffAlgHom_X, SignedEdgeMap.signedCoeffAlgHom_X]
  rfl

/-- The coefficient ring map is that of the edge factor, as ring homomorphisms. -/
theorem coeffRingHom_eq_edgeFactor : φ.coeffRingHom = φ.edgeFactor.signedCoeffRingHom := by
  rw [← SignedEdgeMap.signedCoeffAlgHom_toRingHom, ← coeffAlgHom_eq_edgeFactor]
  rfl

/-- The incidence ring map intertwines the coefficient maps through the coefficient ring map. -/
theorem incidenceHom_coeffHom (r : IncCoeffRing E) :
    φ.incidenceHom (G.coeffHom r) = H.coeffHom (φ.coeffAlgHom r) := by
  rw [incidenceHom_eq_comp_apply, VertexMap.incidenceHom_coeffHom,
    SignedEdgeMap.signedIncidenceHom_coeffHom, coeffAlgHom_eq_edgeFactor]

/-- The incidence ring map intertwines the coefficient actions. -/
theorem incidenceHom_coeff_mul (r : IncCoeffRing E) (x : G.IncidenceRing) :
    φ.incidenceHom (G.coeffHom r * x) = H.coeffHom (φ.coeffRingHom r) * φ.incidenceHom x := by
  rw [map_mul, incidenceHom_coeffHom]
  rfl

end Incidence

/-! ## Identity and composition laws -/

section Laws

variable {X E'' : Type} {K : Multigraph X E''}

/-- The endpoint index of a composite is the composite of the endpoint indices. -/
theorem trans_endpointIndex (φ : GraphMap G H) (ψ : GraphMap H K) (e : E)
    (ab : Fin 2 × Fin 2) :
    (φ.trans ψ).endpointIndex e ab = ψ.endpointIndex (φ.edge e) (φ.endpointIndex e ab) := by
  unfold endpointIndex
  rw [trans_reversed]
  cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> simp

/-- The coefficient index map of a composite is the composite of the coefficient index maps. -/
theorem trans_coeffIdxMap (φ : GraphMap G H) (ψ : GraphMap H K) (c : IncCoeffIdx E) :
    (φ.trans ψ).coeffIdxMap c = ψ.coeffIdxMap (φ.coeffIdxMap c) := by
  rcases c with ⟨e, ab⟩
  rw [coeffIdxMap_apply, coeffIdxMap_apply, coeffIdxMap_apply, trans_endpointIndex]
  rfl

/-- The coefficient index map of the identity is the identity. -/
@[simp] theorem refl_coeffIdxMap (G : Multigraph V E) (c : IncCoeffIdx E) :
    (refl G).coeffIdxMap c = c := by
  rcases c with ⟨e, ab⟩
  rfl

/-- **Identity law** for the coefficient ring map. -/
theorem coeffAlgHom_refl (G : Multigraph V E) :
    (refl G).coeffAlgHom = AlgHom.id ℂ (IncCoeffRing E) := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [coeffAlgHom_X, refl_coeffIdxMap]
  simp

/-- **Identity law** for the coefficient ring map, as ring homomorphisms. -/
theorem coeffRingHom_refl (G : Multigraph V E) :
    (refl G).coeffRingHom = RingHom.id (IncCoeffRing E) := by
  rw [coeffRingHom, coeffAlgHom_refl]
  rfl

/-- **Composition law** for the coefficient ring map. -/
theorem coeffAlgHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).coeffAlgHom = ψ.coeffAlgHom.comp φ.coeffAlgHom := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [AlgHom.comp_apply, coeffAlgHom_X, coeffAlgHom_X, map_mul, map_intCast, coeffAlgHom_X,
    trans_coeffIdxMap, trans_edgeSign_apply, Units.val_mul, Int.cast_mul, mul_assoc]
  rfl

/-- **Composition law** for the coefficient ring map, as ring homomorphisms. -/
theorem coeffRingHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).coeffRingHom = ψ.coeffRingHom.comp φ.coeffRingHom := by
  rw [coeffRingHom, coeffAlgHom_trans]
  rfl

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq X] [Fintype X]
  [DecidableEq E] [Fintype E] [DecidableEq E'] [Fintype E'] [DecidableEq E''] [Fintype E'']

/-- The substitution of the identity graph map is the identity. -/
theorem torusPolyHom_refl (G : Multigraph V E) :
    (refl G).torusPolyHom = AlgHom.id ℂ (MvPolynomial (IncTorusVar V E) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro w
  rcases w with v | v | c
  · rw [torusPolyHom_X]
    rfl
  · rw [torusPolyHom_X]
    rfl
  · rw [torusPolyHom_X, torusVal, refl_coeffIdxMap]
    simp

/-- The substitution of a composite is the composite of the substitutions. -/
theorem torusPolyHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).torusPolyHom = ψ.torusPolyHom.comp φ.torusPolyHom := by
  apply MvPolynomial.algHom_ext
  intro w
  rcases w with v | v | c
  · simp [torusVal]
  · simp [torusVal]
  · rw [AlgHom.comp_apply, torusPolyHom_X, torusPolyHom_X, torusVal, torusVal, map_mul,
      map_intCast, torusPolyHom_X, torusVal, trans_coeffIdxMap, trans_edgeSign_apply,
      Units.val_mul, Int.cast_mul, mul_assoc]
    rfl

/-- **Identity law** for the torus ring map. -/
theorem torusHom_refl (G : Multigraph V E) :
    (refl G).torusHom = AlgHom.id ℂ G.IncTorusRing := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [torusHom_mk, torusPolyHom_refl]
  rfl

/-- **Composition law** for the torus ring map. -/
theorem torusHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).torusHom = ψ.torusHom.comp φ.torusHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AlgHom.comp_apply, torusHom_mk, torusHom_mk, torusHom_mk, torusPolyHom_trans]
  rfl

/-- **Identity law** for the incidence ring map. -/
theorem incidenceHom_refl (G : Multigraph V E) :
    (refl G).incidenceHom = AlgHom.id ℂ G.IncidenceRing := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [incidenceHom_val, torusHom_refl]
  rfl

/-- **Composition law** for the incidence ring map. -/
theorem incidenceHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).incidenceHom = ψ.incidenceHom.comp φ.incidenceHom := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [incidenceHom_val, torusHom_trans]
  rfl

/-- Elementwise identity law for the incidence ring map. -/
theorem incidenceHom_refl_apply (G : Multigraph V E) (x : G.IncidenceRing) :
    (refl G).incidenceHom x = x := by
  rw [incidenceHom_refl, AlgHom.id_apply]

/-- Elementwise composition law for the incidence ring map. -/
theorem incidenceHom_trans_apply (φ : GraphMap G H) (ψ : GraphMap H K) (x : G.IncidenceRing) :
    (φ.trans ψ).incidenceHom x = ψ.incidenceHom (φ.incidenceHom x) := by
  rw [incidenceHom_trans, AlgHom.comp_apply]

end Laws

end GraphMap

/-! ## Vertex maps and signed edge maps as graph maps -/

section SpecialCases

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E]
  [Fintype E] [DecidableEq E'] [Fintype E']

/-- For a vertex map, regarded as a graph map, the coefficient ring map is the identity. -/
theorem VertexMap.toGraphMap_coeffAlgHom {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : φ.toGraphMap.coeffAlgHom = AlgHom.id ℂ (IncCoeffRing E) := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [GraphMap.coeffAlgHom_X]
  simp only [toGraphMap, Pi.one_apply, Units.val_one, Int.cast_one, one_mul, AlgHom.id_apply]
  rfl

/-- For a vertex map, regarded as a graph map, the coefficient ring map is the identity, as ring
homomorphisms. -/
theorem VertexMap.toGraphMap_coeffRingHom {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : φ.toGraphMap.coeffRingHom = RingHom.id (IncCoeffRing E) := by
  rw [GraphMap.coeffRingHom, VertexMap.toGraphMap_coeffAlgHom]
  rfl

/-- For a vertex map, regarded as a graph map, the torus ring map is that of the vertex map. -/
theorem VertexMap.toGraphMap_torusHom {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : φ.toGraphMap.torusHom = φ.torusHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GraphMap.torusHom_mk, VertexMap.torusHom_mk]
  congr 1
  have h : φ.toGraphMap.torusPolyHom = rename φ.torusVarMap := by
    apply MvPolynomial.algHom_ext
    intro w
    rcases w with v | v | c
    · rw [GraphMap.torusPolyHom_X, rename_X]
      rfl
    · rw [GraphMap.torusPolyHom_X, rename_X]
      rfl
    · rw [GraphMap.torusPolyHom_X, GraphMap.torusVal, rename_X]
      simp only [toGraphMap, Pi.one_apply, Units.val_one, Int.cast_one, one_mul]
      rfl
  rw [h]

/-- For a vertex map, regarded as a graph map, the incidence ring map is that of the vertex map. -/
theorem VertexMap.toGraphMap_incidenceHom {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : φ.toGraphMap.incidenceHom = φ.incidenceHom := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [GraphMap.incidenceHom_val, VertexMap.toGraphMap_torusHom]
  rfl

/-- For a signed edge map, regarded as a graph map, the coefficient ring map is the signed
coefficient ring map. -/
theorem SignedEdgeMap.toGraphMap_coeffAlgHom {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeMap G H) : φ.toGraphMap.coeffAlgHom = φ.signedCoeffAlgHom := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [GraphMap.coeffAlgHom_X, SignedEdgeMap.signedCoeffAlgHom_X]
  rfl

/-- For a signed edge map, regarded as a graph map, the coefficient ring map is the signed
coefficient ring map, as ring homomorphisms. -/
theorem SignedEdgeMap.toGraphMap_coeffRingHom {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeMap G H) : φ.toGraphMap.coeffRingHom = φ.signedCoeffRingHom := by
  rw [← SignedEdgeMap.signedCoeffAlgHom_toRingHom, ← SignedEdgeMap.toGraphMap_coeffAlgHom]
  rfl

/-- For a signed edge map, regarded as a graph map, the torus ring map is the signed torus ring
map. -/
theorem SignedEdgeMap.toGraphMap_torusHom {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeMap G H) : φ.toGraphMap.torusHom = φ.signedTorusHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GraphMap.torusHom_mk, SignedEdgeMap.signedTorusHom_apply, edgeSignTorus_mk,
    EdgeMap.torusHom_mk]
  congr 1
  have h : φ.toGraphMap.torusPolyHom =
      (rename φ.toEdgeMap.torusVarMap).comp (varSignHom (φ.edgeSign.torusVarSign (V := V))) := by
    apply MvPolynomial.algHom_ext
    intro w
    rcases w with v | v | c
    · simp [GraphMap.torusVal, EdgeMap.torusVarMap, toGraphMap]
    · simp [GraphMap.torusVal, EdgeMap.torusVarMap, toGraphMap]
    · simp only [GraphMap.torusPolyHom_X, GraphMap.torusVal, AlgHom.comp_apply, varSignHom_X,
        EdgeSign.torusVarSign_inr_inr, map_mul, map_intCast, rename_X, EdgeMap.torusVarMap,
        Sum.map_inr]
      rfl
  rw [h]
  rfl

/-- For a signed edge map, regarded as a graph map, the incidence ring map is the signed incidence
ring map. -/
theorem SignedEdgeMap.toGraphMap_incidenceHom {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeMap G H) : φ.toGraphMap.incidenceHom = φ.signedIncidenceHom := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [GraphMap.incidenceHom_val, SignedEdgeMap.toGraphMap_torusHom]
  rfl

end SpecialCases

end BPFixedPoints.Multigraph
