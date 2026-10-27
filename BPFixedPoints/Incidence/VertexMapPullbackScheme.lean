import BPFixedPoints.Incidence.VertexProjectivePermutation
import BPFixedPoints.Incidence.IncidenceVertexMapRings

/-!
# The coordinate map of a vertex function between vertex projective products

For an arbitrary function `f : V → W` of finite vertex sets (vertices may be identified, and
vertices of `W` may be missed), the contravariant coordinate map
`a_f : (P¹)^W → (P¹)^V`, `(x_w) ↦ (x_{f v})_v`, is the morphism over the coefficient scheme given by
the universal property of the actual indexed product `vertexIsProduct`: its composite with the
projection of the vertex `v` is the projection of the vertex `f v` (`vertexOverBaseMap`,
`vertexOverBaseMap_projection`). On schemes it is `vertexSchemeMap R f`.

Proved here: identity and composition laws (`vertexSchemeMap_id`, `vertexSchemeMap_comp`), agreement
with the permutation isomorphism for bijections (`vertexSchemeMap_equiv`), the preimages of the
coordinate opens (`vertexSchemeMap_preimage_coordinateOpen`) and of the polynomial charts, which
contain the charts of `W` (`vertexChartOpen_le_preimage`). For a vertex map `φ : VertexMap G H` the
map `a_φ = vertexSchemeMap R φ.vertex` is contravariantly functorial in `φ`
(`VertexMap.schemeMap_trans`).

For a vertex function that identifies two vertices, `a_f` is not an isomorphism: it is the
composite of a diagonal and a coordinate projection. Nothing about sheaves is proved here; see
`VertexMapPullbackCohomology` for the induced map of sheaf cohomology.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ProjectiveLine

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] {V W X : Type} [Fintype V] [Fintype W] [Fintype X]

/-- **The contravariant coordinate map of a vertex function** `f : V → W`,
`(x_w) ↦ (x_{f v})_v`, over the coefficient scheme. -/
noncomputable def vertexOverBaseMap (f : V → W) : vertexOverBase R W ⟶ vertexOverBase R V :=
  (vertexIsProduct R V).lift (Fan.mk (vertexOverBase R W) fun v => vertexProjectionOver R W (f v))

/-- The vertex `v` coordinate of the coordinate map is the vertex `f v` coordinate. -/
@[reassoc (attr := simp)] theorem vertexOverBaseMap_projection (f : V → W) (v : V) :
    vertexOverBaseMap R f ≫ vertexProjectionOver R V v = vertexProjectionOver R W (f v) :=
  (vertexIsProduct R V).fac _ ⟨v⟩

/-- The coordinate map of the identity is the identity. -/
theorem vertexOverBaseMap_id : vertexOverBaseMap R (id : V → V) = 𝟙 _ :=
  vertexOverBase_hom_ext R fun v => by simp

/-- The coordinate map is contravariantly functorial. -/
theorem vertexOverBaseMap_comp (f : V → W) (g : W → X) :
    vertexOverBaseMap R (g ∘ f) = vertexOverBaseMap R g ≫ vertexOverBaseMap R f :=
  vertexOverBase_hom_ext R fun v => by simp

/-- For a bijection the coordinate map is the permutation map. -/
theorem vertexOverBaseMap_equiv (ψ : V ≃ W) : vertexOverBaseMap R ψ = vertexOverBasePerm R ψ :=
  rfl

/-- **The coordinate map of a vertex function on the vertex projective products.** -/
noncomputable def vertexSchemeMap (f : V → W) : vertexScheme R W ⟶ vertexScheme R V :=
  (vertexOverBaseMap R f).left

/-- The coordinate map lies over the coefficient scheme. -/
@[reassoc (attr := simp)] theorem vertexSchemeMap_toBase (f : V → W) :
    vertexSchemeMap R f ≫ vertexToBase R V = vertexToBase R W :=
  Over.w (vertexOverBaseMap R f)

/-- On schemes, the vertex `v` coordinate of the coordinate map is the vertex `f v` coordinate. -/
@[reassoc (attr := simp)] theorem vertexSchemeMap_projection (f : V → W) (v : V) :
    vertexSchemeMap R f ≫ (vertexProjectionOver R V v).left =
      (vertexProjectionOver R W (f v)).left := by
  rw [vertexSchemeMap, ← Over.comp_left, vertexOverBaseMap_projection]

theorem vertexSchemeMap_id : vertexSchemeMap R (id : V → V) = 𝟙 _ := by
  rw [vertexSchemeMap, vertexOverBaseMap_id]
  rfl

theorem vertexSchemeMap_comp (f : V → W) (g : W → X) :
    vertexSchemeMap R (g ∘ f) = vertexSchemeMap R g ≫ vertexSchemeMap R f := by
  rw [vertexSchemeMap, vertexOverBaseMap_comp, Over.comp_left]
  rfl

/-- For a bijection the coordinate map is the permutation isomorphism. -/
theorem vertexSchemeMap_equiv (ψ : V ≃ W) : vertexSchemeMap R ψ = vertexSchemePerm R ψ := rfl

/-- The coordinate map is determined by its vertex coordinates. -/
theorem vertexSchemeMap_ext {T : Scheme} {g g' : T ⟶ vertexScheme R V}
    (hg : g ≫ vertexToBase R V = g' ≫ vertexToBase R V)
    (h : ∀ v, g ≫ (vertexProjectionOver R V v).left = g' ≫ (vertexProjectionOver R V v).left) :
    g = g' := by
  have h' := vertexOverBase_hom_ext R (T := Over.mk (g ≫ vertexToBase R V))
    (f := Over.homMk g rfl) (g := Over.homMk g' hg.symm) fun v => by
      ext1
      exact h v
  exact congrArg CommaMorphism.left h'

/-- The coordinate map pulls back the coordinate opens of `v` to those of `f v`. -/
theorem vertexSchemeMap_preimage_coordinateOpen (f : V → W) (v : V) (i : Fin 2) :
    vertexSchemeMap R f ⁻¹ᵁ vertexCoordinateOpen R V v i = vertexCoordinateOpen R W (f v) i := by
  rw [vertexCoordinateOpen, vertexCoordinateOpen, ← Scheme.Hom.comp_preimage,
    vertexSchemeMap_projection]

/-- A point lies in the preimage of the chart of `σ` exactly when its coordinate at every `f v`
lies in the standard open of `σ v`. -/
theorem mem_preimage_vertexChartOpen (f : V → W) (σ : V → Fin 2) (x : vertexScheme R W) :
    x ∈ vertexSchemeMap R f ⁻¹ᵁ vertexChartOpen R V σ ↔
      ∀ v, (vertexProjectionOver R W (f v)).left x ∈ standardOpen R (σ v) := by
  have hp : ∀ v, (vertexProjectionOver R V v).left (vertexSchemeMap R f x) =
      (vertexProjectionOver R W (f v)).left x := fun v =>
    congrArg (fun g => g x) (vertexSchemeMap_projection R f v)
  change vertexSchemeMap R f x ∈ vertexChartOpen R V σ ↔ _
  rw [mem_vertexChartOpen]
  simp only [hp]

/-- **Charts pull back to unions of charts**: the chart of `τ : W → Fin 2` lies in the preimage of
the chart of `τ ∘ f`. -/
theorem vertexChartOpen_le_preimage (f : V → W) (τ : W → Fin 2) :
    vertexChartOpen R W τ ≤ vertexSchemeMap R f ⁻¹ᵁ vertexChartOpen R V (fun v => τ (f v)) := by
  intro x hx
  rw [mem_preimage_vertexChartOpen]
  intro v
  exact (mem_vertexChartOpen R W τ x).1 hx (f v)

/-! ## Vertex maps -/

namespace VertexMap

variable {E : Type} {G : Multigraph V E} {H : Multigraph W E} {K : Multigraph X E}

/-- **The coordinate map `a_φ : (P¹)^W → (P¹)^V` of a vertex map**, `(x_w) ↦ (x_{φ v})_v`. -/
noncomputable def schemeMap (φ : VertexMap G H) : vertexScheme R W ⟶ vertexScheme R V :=
  vertexSchemeMap R φ.vertex

@[reassoc (attr := simp)] theorem schemeMap_projection (φ : VertexMap G H) (v : V) :
    φ.schemeMap R ≫ (vertexProjectionOver R V v).left =
      (vertexProjectionOver R W (φ.vertex v)).left :=
  vertexSchemeMap_projection R φ.vertex v

/-- The coordinate map of the identity vertex map is the identity. -/
theorem schemeMap_refl (G : Multigraph V E) : (refl G).schemeMap R = 𝟙 _ :=
  vertexSchemeMap_id R

/-- The coordinate map of a composite is the reversed composite of the coordinate maps. -/
theorem schemeMap_trans (φ : VertexMap G H) (χ : VertexMap H K) :
    (φ.trans χ).schemeMap R = χ.schemeMap R ≫ φ.schemeMap R :=
  vertexSchemeMap_comp R φ.vertex χ.vertex

/-- For a vertex bijection the coordinate map of the underlying vertex map is the permutation
isomorphism. -/
theorem _root_.BPFixedPoints.Multigraph.VertexRelabel.toVertexMap_schemeMap
    (φ : VertexRelabel G H) : φ.toVertexMap.schemeMap R = vertexSchemePerm R φ.vertex := rfl

end VertexMap

end BPFixedPoints.Multigraph
