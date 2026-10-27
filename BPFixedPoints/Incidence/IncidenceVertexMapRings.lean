import BPFixedPoints.Incidence.IncidenceVertexRelabelRings
import BPFixedPoints.Incidence.Generators

/-!
# Vertex maps act on the incidence ring

A `VertexMap G H` is a graph map with the same edge type which may identify vertices: an
arbitrary function `vertex : V → W` such that every edge of `H` has the endpoints
`vertex ∘ G.fst` and `vertex ∘ G.snd`. The coefficient indices `IncCoeffIdx E` and the
coefficient ring `IncCoeffRing E` are unchanged.

The coordinate map `a_φ : X_H → X_G`, `(x_w) ↦ (x_{φ v})`, is contravariant; pulling back
functions gives the ring maps defined here, in the covariant direction `G → H`:
* a chart `τ` of `H` pulls back to the chart `τ ∘ vertex` of `G` (`chartPull`), and renaming the
  chart variables `t_v ↦ t_{vertex v}`, `c ↦ c` maps the chart ring of `G` at `τ ∘ vertex` to the
  chart ring of `H` at `τ` (`chartHom`, `rename_incChartEq`);
* the same renaming `t_v ↦ t_{vertex v}`, `s_v ↦ s_{vertex v}`, `c ↦ c` gives the map of common
  torus rings (`torusHom`, `rename_incTorusRel`), compatible with the chart restrictions
  (`torusHom_comp_incChartMap`);
* an element of the intersection of the chart images of `G` lies in the image of the chart
  `τ ∘ vertex` for every chart `τ` of `H`, so its image lies in every chart image of `H`
  (`torusHom_mem_incidenceRing`). This gives the incidence ring map
  `incidenceHom : G.IncidenceRing →ₐ[ℂ] H.IncidenceRing`.

The incidence ring map is the identity on coefficients (`incidenceHom_coeffHom`), it is the
identity for the identity map and is compatible with composition (`incidenceHom_refl`,
`incidenceHom_trans`), and for a vertex bijection it is the isomorphism
`VertexRelabel.incidenceEquiv` (`VertexRelabel.toVertexMap_incidenceHom`).

Loops are allowed throughout: if `vertex` identifies the two endpoints of an edge, that edge is a
loop of `H`, and the incidence ring of `H` is still defined. The paper's noncontracting assumption
(distinct endpoints stay distinct, `IsNoncontracting`) is only needed to stay among loopless
graphs (`loopless_of_isNoncontracting`); nothing in the ring maps uses it.

Degrees of `H` are sums of degrees of `G` over the fibres of `vertex` (`deg_eq_sum_fiber`). For a
cycle union `S` of `G`, the edge set `S` is a cycle union of `H` exactly when `vertex` is injective
on the vertex support of `S` (`isCycleUnion_iff_injOn`), and a simple cycle of `G` on whose
vertices `vertex` is injective is a simple cycle of `H` (`isSimpleCycle_of_injOn`).

Not covered here: maps that change the edge type (see `IncidenceEdgeMap*.lean`), orientation
signs, and the sheaf-theoretic description of the map.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- A graph map with the same edge type which may identify vertices: an arbitrary vertex function
carrying the endpoints of every edge of `G` to the endpoints of the same edge of `H`, in the same
order. -/
structure VertexMap {V W E : Type} (G : Multigraph V E) (H : Multigraph W E) where
  /-- The vertex function. -/
  vertex : V → W
  /-- The first endpoint of an edge of `H` is the image of the first endpoint in `G`. -/
  fst_edge : ∀ e, H.fst e = vertex (G.fst e)
  /-- The second endpoint of an edge of `H` is the image of the second endpoint in `G`. -/
  snd_edge : ∀ e, H.snd e = vertex (G.snd e)

/-- The multigraph obtained by pushing the endpoints forward along a vertex function. -/
def pushVertices {V W E : Type} (G : Multigraph V E) (f : V → W) : Multigraph W E where
  fst e := f (G.fst e)
  snd e := f (G.snd e)

namespace VertexMap

/-- The vertex map of a graph onto the graph obtained by pushing the endpoints forward. -/
def ofFun {V W E : Type} (G : Multigraph V E) (f : V → W) : VertexMap G (G.pushVertices f) where
  vertex := f
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The identity vertex map. -/
def refl {V E : Type} (G : Multigraph V E) : VertexMap G G where
  vertex := id
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The composite of two vertex maps. -/
def trans {V W X E : Type} {G : Multigraph V E} {H : Multigraph W E} {K : Multigraph X E}
    (φ : VertexMap G H) (χ : VertexMap H K) : VertexMap G K where
  vertex := χ.vertex ∘ φ.vertex
  fst_edge e := by rw [χ.fst_edge, φ.fst_edge]; rfl
  snd_edge e := by rw [χ.snd_edge, φ.snd_edge]; rfl

@[simp] theorem ofFun_vertex {V W E : Type} (G : Multigraph V E) (f : V → W) :
    (ofFun G f).vertex = f := rfl

@[simp] theorem refl_vertex {V E : Type} (G : Multigraph V E) : (refl G).vertex = id := rfl

@[simp] theorem trans_vertex {V W X E : Type} {G : Multigraph V E} {H : Multigraph W E}
    {K : Multigraph X E} (φ : VertexMap G H) (χ : VertexMap H K) :
    (φ.trans χ).vertex = χ.vertex ∘ φ.vertex := rfl

/-- Vertex maps are determined by their vertex functions. -/
theorem ext' {V W E : Type} {G : Multigraph V E} {H : Multigraph W E} {φ φ' : VertexMap G H}
    (h : φ.vertex = φ'.vertex) : φ = φ' := by
  cases φ
  cases φ'
  cases h
  rfl

/-- The identity is a left unit for composition. -/
theorem refl_trans {V W E : Type} {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H) :
    (refl G).trans φ = φ :=
  ext' rfl

/-- The identity is a right unit for composition. -/
theorem trans_refl {V W E : Type} {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H) :
    φ.trans (refl H) = φ :=
  ext' rfl

/-- Composition of vertex maps is associative. -/
theorem trans_assoc {V W X Y E : Type} {G : Multigraph V E} {H : Multigraph W E}
    {K : Multigraph X E} {L : Multigraph Y E} (φ : VertexMap G H) (χ : VertexMap H K)
    (ψ : VertexMap K L) : (φ.trans χ).trans ψ = φ.trans (χ.trans ψ) :=
  ext' rfl

/-! ## The noncontracting condition -/

/-- The paper's noncontracting condition: the two distinct endpoints of an edge keep distinct
images. -/
def IsNoncontracting {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : Prop :=
  ∀ e, G.fst e ≠ G.snd e → φ.vertex (G.fst e) ≠ φ.vertex (G.snd e)

/-- A noncontracting vertex map from a loopless graph has a loopless target. This is the only
place where the noncontracting condition enters: the ring maps below are defined for every vertex
map, loops included. -/
theorem loopless_of_isNoncontracting {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) (hφ : φ.IsNoncontracting) (hG : G.Loopless) : H.Loopless := by
  intro e h
  rw [φ.fst_edge, φ.snd_edge] at h
  exact hφ e (hG e) h

/-- An edge whose endpoints are identified becomes a loop. -/
theorem isLoop_of_vertex_eq {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) {e : E} (h : φ.vertex (G.fst e) = φ.vertex (G.snd e)) : H.IsLoop e := by
  unfold IsLoop
  rw [φ.fst_edge, φ.snd_edge, h]

end VertexMap

/-- A vertex bijection, regarded as a vertex map. -/
def VertexRelabel.toVertexMap {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexRelabel G H) : VertexMap G H where
  vertex := φ.vertex
  fst_edge := φ.fst_edge
  snd_edge := φ.snd_edge

@[simp] theorem VertexRelabel.toVertexMap_vertex {V W E : Type} {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) : (φ.toVertexMap.vertex : V → W) = φ.vertex :=
  rfl

/-- A vertex bijection is noncontracting. -/
theorem VertexRelabel.toVertexMap_isNoncontracting {V W E : Type} {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) : φ.toVertexMap.IsNoncontracting :=
  fun _ h hφ => h (φ.vertex.injective hφ)

namespace VertexMap

/-! ## Degrees -/

section Degrees

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- The fibre of a vertex of `H`. -/
def fiber (w : W) : Finset V := Finset.univ.filter fun v => φ.vertex v = w

@[simp] theorem mem_fiber {w : W} {v : V} : v ∈ φ.fiber w ↔ φ.vertex v = w := by
  simp [fiber]

/-- Endpoint counts of `H` are sums of endpoint counts of `G` over the fibre. -/
theorem endCount_eq_sum_fiber (e : E) (w : W) :
    H.endCount e w = ∑ v ∈ φ.fiber w, G.endCount e v := by
  unfold endCount
  rw [Finset.sum_add_distrib, φ.fst_edge, φ.snd_edge]
  congr 1
  · rw [Finset.sum_ite_eq]
    simp only [mem_fiber]
  · rw [Finset.sum_ite_eq]
    simp only [mem_fiber]

/-- Degrees of `H` are sums of degrees of `G` over the fibre. -/
theorem deg_eq_sum_fiber (S : Finset E) (w : W) :
    H.deg S w = ∑ v ∈ φ.fiber w, G.deg S v := by
  unfold deg
  simp only [φ.endCount_eq_sum_fiber]
  exact Finset.sum_comm

/-- The degree of an image vertex is at least the degree of the original vertex. -/
theorem deg_le_deg_vertex (S : Finset E) (v : V) : G.deg S v ≤ H.deg S (φ.vertex v) := by
  rw [φ.deg_eq_sum_fiber]
  exact Finset.single_le_sum (f := fun v => G.deg S v) (fun _ _ => Nat.zero_le _)
    ((φ.mem_fiber).2 rfl)

/-- Two distinct vertices with the same image contribute both degrees. -/
theorem deg_add_le_deg_vertex (S : Finset E) {v v' : V} (hne : v ≠ v')
    (h : φ.vertex v = φ.vertex v') : G.deg S v + G.deg S v' ≤ H.deg S (φ.vertex v) := by
  rw [φ.deg_eq_sum_fiber, ← Finset.sum_pair hne]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (φ.mem_fiber).2 rfl
  · exact (φ.mem_fiber).2 h.symm

/-- The image of a support vertex lies in the support. -/
theorem vertex_mem_support {S : Finset E} {v : V} (hv : v ∈ G.support S) :
    φ.vertex v ∈ H.support S := by
  rw [mem_support_iff] at hv ⊢
  exact lt_of_lt_of_le hv (φ.deg_le_deg_vertex S v)

/-- Every support vertex of `H` is the image of a support vertex of `G`. -/
theorem exists_mem_support_of_mem_support {S : Finset E} {w : W} (hw : w ∈ H.support S) :
    ∃ v ∈ G.support S, φ.vertex v = w := by
  rw [mem_support_iff, φ.deg_eq_sum_fiber] at hw
  obtain ⟨v, hv, hpos⟩ := Finset.exists_lt_of_sum_lt (s := φ.fiber w) (f := fun _ => 0)
    (g := fun v => G.deg S v) (by simpa using hw)
  exact ⟨v, (G.mem_support_iff).2 hpos, (φ.mem_fiber).1 hv⟩

/-- The vertex support of an edge set of `H` is the image of its vertex support in `G`. -/
theorem support_eq_image (S : Finset E) : H.support S = (G.support S).image φ.vertex := by
  ext w
  rw [Finset.mem_image]
  constructor
  · exact φ.exists_mem_support_of_mem_support
  · rintro ⟨v, hv, rfl⟩
    exact φ.vertex_mem_support hv

/-- If the vertex function is injective on the vertex support of `S`, the degree of `S` at the
image of a support vertex is its degree in `G`. -/
theorem deg_vertex_of_injOn {S : Finset E} (h : Set.InjOn φ.vertex (G.support S)) {v : V}
    (hv : v ∈ G.support S) : H.deg S (φ.vertex v) = G.deg S v := by
  rw [φ.deg_eq_sum_fiber]
  refine Finset.sum_eq_single_of_mem v ((φ.mem_fiber).2 rfl) fun v' hv' hne => ?_
  by_contra h0
  exact hne (h ((G.mem_support_iff).2 (Nat.pos_of_ne_zero h0)) hv ((φ.mem_fiber).1 hv'))

/-- A cycle union of `G` is a cycle union of `H` exactly when the vertex function is injective on
its vertex support. -/
theorem isCycleUnion_iff_injOn {S : Finset E} (hS : G.IsCycleUnion S) :
    H.IsCycleUnion S ↔ Set.InjOn φ.vertex (G.support S) := by
  constructor
  · intro hH v hv v' hv' h
    by_contra hne
    rw [Finset.mem_coe, mem_support_iff] at hv hv'
    have hle := φ.deg_add_le_deg_vertex S hne h
    rcases hS v with h2 | h2 <;> rcases hS v' with h2' | h2' <;>
      rcases hH (φ.vertex v) with h0 | h0 <;> omega
  · intro h w
    by_cases hw : w ∈ H.support S
    · obtain ⟨v, hv, rfl⟩ := φ.exists_mem_support_of_mem_support hw
      rw [φ.deg_vertex_of_injOn h hv]
      exact hS v
    · left
      rw [mem_support_iff] at hw
      omega

/-- A simple cycle of `G` on whose vertices the vertex function is injective is a simple cycle of
`H`. -/
theorem isSimpleCycle_of_injOn {C : Finset E} (hC : G.IsSimpleCycle C)
    (h : Set.InjOn φ.vertex (G.support C)) : H.IsSimpleCycle C := by
  have hdeg : ∀ D ⊆ C, ∀ v ∈ G.support C, H.deg D (φ.vertex v) = G.deg D v := by
    intro D hD v hv
    rw [φ.deg_eq_sum_fiber]
    refine Finset.sum_eq_single_of_mem v ((φ.mem_fiber).2 rfl) fun v' hv' hne => ?_
    by_contra h0
    have hv'C : v' ∈ G.support C :=
      (G.mem_support_iff).2 (lt_of_lt_of_le (Nat.pos_of_ne_zero h0) (G.deg_mono hD v'))
    exact hne (h hv'C hv ((φ.mem_fiber).1 hv'))
  refine ⟨hC.1, ((φ.isCycleUnion_iff_injOn hC.isCycleUnion).2 h).isEvenSet, ?_⟩
  intro D hD hne hev
  apply hC.2.2 D hD hne
  intro v
  by_cases hv : v ∈ G.support C
  · rw [← hdeg D hD v hv]
    exact hev _
  · have h0 : G.deg C v = 0 := by rw [mem_support_iff] at hv; omega
    have : G.deg D v = 0 := by have := G.deg_mono hD v; omega
    rw [this]
    exact ⟨0, rfl⟩

/-- If two vertices of a cycle union are identified, it is not a cycle union of `H`. -/
theorem not_isCycleUnion_of_identify {S : Finset E} (hS : G.IsCycleUnion S) {v v' : V}
    (hv : v ∈ G.support S) (hv' : v' ∈ G.support S) (hne : v ≠ v')
    (h : φ.vertex v = φ.vertex v') : ¬ H.IsCycleUnion S := by
  rw [φ.isCycleUnion_iff_injOn hS]
  exact fun hinj => hne (hinj hv hv' h)

end Degrees

/-! ## Chart and torus rings -/

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- The chart of `G` obtained by pulling back a chart of `H` along the vertex function. -/
def chartPull (τ : W → Bool) : V → Bool := fun v => τ (φ.vertex v)

/-- Renaming of chart variables: `t_v ↦ t_{vertex v}`, coefficients are fixed. -/
def chartVarMap : IncChartVar V E → IncChartVar W E := Sum.map φ.vertex id

/-- Renaming of torus variables: `t_v ↦ t_{vertex v}`, `s_v ↦ s_{vertex v}`, coefficients are
fixed. -/
def torusVarMap : IncTorusVar V E → IncTorusVar W E := Sum.map φ.vertex (Sum.map φ.vertex id)

/-- Renaming of the torus relation indices. -/
def relIdxMap : V ⊕ E → W ⊕ E := Sum.map φ.vertex id

@[simp] theorem chartVarMap_inl (v : V) : φ.chartVarMap (Sum.inl v) = Sum.inl (φ.vertex v) := rfl

@[simp] theorem chartVarMap_inr (c : IncCoeffIdx E) : φ.chartVarMap (Sum.inr c) = Sum.inr c := rfl

@[simp] theorem torusVarMap_inl (v : V) :
    φ.torusVarMap (E := E) (Sum.inl v) = Sum.inl (φ.vertex v) := rfl

@[simp] theorem torusVarMap_inr_inl (v : V) :
    φ.torusVarMap (E := E) (Sum.inr (Sum.inl v)) = Sum.inr (Sum.inl (φ.vertex v)) := rfl

@[simp] theorem torusVarMap_inr_inr (c : IncCoeffIdx E) :
    φ.torusVarMap (V := V) (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inr c) := rfl

/-- A renamed chart edge equation of the pulled-back chart is the edge equation of `H`. -/
theorem rename_incChartEq (τ : W → Bool) (e : E) :
    rename φ.chartVarMap (G.incChartEq (φ.chartPull τ) e) = H.incChartEq τ e := by
  unfold incChartEq
  simp only [map_sum, map_mul, rename_X, map_incCoord, chartVarMap_inl, chartVarMap_inr,
    chartPull, φ.fst_edge, φ.snd_edge]

/-- A renamed torus relation is the torus relation of the renamed index. -/
theorem rename_incTorusRel (i : V ⊕ E) :
    rename φ.torusVarMap (G.incTorusRel i) = H.incTorusRel (φ.relIdxMap i) := by
  rcases i with v | e
  · simp [incTorusRel, relIdxMap]
  · simp only [incTorusRel, relIdxMap, Sum.map_inr, id, rename_rename]
    have h := φ.rename_incChartEq (fun _ => false) e
    rw [show φ.chartPull (fun _ : W => false) = fun _ : V => false from rfl] at h
    rw [← h, rename_rename]
    have hf : (φ.torusVarMap ∘ Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) =
        ((Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) ∘ φ.chartVarMap) := by
      funext w
      rcases w with v | c <;> rfl
    rw [hf]

/-- Renaming carries the torus relations of `G` into the torus ideal of `H`. -/
theorem torusIdeal_le_comap :
    Ideal.span (Set.range G.incTorusRel) ≤
      (Ideal.span (Set.range H.incTorusRel)).comap (rename φ.torusVarMap) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rw [rename_incTorusRel]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- Renaming carries the chart equations of the pulled-back chart of `G` into the chart ideal
of `H`. -/
theorem chartIdeal_le_comap (τ : W → Bool) :
    Ideal.span (Set.range (G.incChartEq (φ.chartPull τ))) ≤
      (Ideal.span (Set.range (H.incChartEq τ))).comap (rename φ.chartVarMap) := by
  rw [Ideal.span_le]
  rintro _ ⟨e, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rw [rename_incChartEq]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- **The torus ring map** of a vertex map: `t_v ↦ t_{vertex v}`, `s_v ↦ s_{vertex v}`,
`c ↦ c`. -/
noncomputable def torusHom : G.IncTorusRing →ₐ[ℂ] H.IncTorusRing :=
  Ideal.quotientMapₐ _ (rename φ.torusVarMap) φ.torusIdeal_le_comap

/-- The torus map on the class of a polynomial. -/
theorem torusHom_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    φ.torusHom (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.torusVarMap p) := rfl

/-- **The chart ring map** of a vertex map: from the chart of `G` pulled back from the chart `τ`
of `H` to the chart `τ` of `H`. -/
noncomputable def chartHom (τ : W → Bool) :
    G.IncChartRing (φ.chartPull τ) →ₐ[ℂ] H.IncChartRing τ :=
  Ideal.quotientMapₐ _ (rename φ.chartVarMap) (φ.chartIdeal_le_comap τ)

/-- The chart map on the class of a polynomial. -/
theorem chartHom_mk (τ : W → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    φ.chartHom τ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.chartVarMap p) := rfl

/-- The torus map on the torus values of chart variables of a pulled-back chart. -/
theorem torusHom_incChartVal (τ : W → Bool) (w : IncChartVar V E) :
    φ.torusHom (G.incChartVal (φ.chartPull τ) w) = H.incChartVal τ (φ.chartVarMap w) := by
  rcases w with v | c
  · simp only [incChartVal, chartVarMap_inl]
    by_cases h : τ (φ.vertex v) <;> simp [chartPull, h, torusHom_mk]
  · simp [incChartVal, torusHom_mk]

/-- The torus map intertwines the restriction of the pulled-back chart of `G` with the restriction
of the chart of `H`. -/
theorem torusHom_comp_incChartMap (τ : W → Bool) :
    φ.torusHom.comp (G.incChartMap (φ.chartPull τ)) = (H.incChartMap τ).comp (φ.chartHom τ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change φ.torusHom (G.incChartMap (φ.chartPull τ) (Ideal.Quotient.mk _ (X w))) =
    H.incChartMap τ (Ideal.Quotient.mk _ (rename φ.chartVarMap (X w)))
  rw [incChartMap_mk, aeval_X, torusHom_incChartVal, rename_X, incChartMap_mk, aeval_X]

/-- Elementwise form of `torusHom_comp_incChartMap`. -/
theorem torusHom_incChartMap (τ : W → Bool) (y : G.IncChartRing (φ.chartPull τ)) :
    φ.torusHom (G.incChartMap (φ.chartPull τ) y) = H.incChartMap τ (φ.chartHom τ y) :=
  AlgHom.congr_fun (φ.torusHom_comp_incChartMap τ) y

/-- **Sections extend.** An element of the intersection of the chart images of `G` maps into every
chart image of `H`: on the chart `τ` of `H` it comes from the pulled-back chart `τ ∘ vertex`. -/
theorem torusHom_mem_incidenceRing {x : G.IncTorusRing} (hx : x ∈ G.IncidenceRing) :
    φ.torusHom x ∈ H.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range] at hx ⊢
  intro τ
  obtain ⟨y, hy⟩ := hx (φ.chartPull τ)
  exact ⟨φ.chartHom τ y, by rw [← torusHom_incChartMap, hy]⟩

/-- **The incidence ring map** of a vertex map: pullback of regular functions along the coordinate
map `a_φ : X_H → X_G`. -/
noncomputable def incidenceHom : G.IncidenceRing →ₐ[ℂ] H.IncidenceRing :=
  (φ.torusHom.comp G.IncidenceRing.val).codRestrict H.IncidenceRing
    fun x => φ.torusHom_mem_incidenceRing x.property

@[simp] theorem incidenceHom_val (x : G.IncidenceRing) :
    (φ.incidenceHom x : H.IncTorusRing) = φ.torusHom x.val := rfl

/-- The incidence ring map is the identity on coefficients. -/
theorem incidenceHom_coeffHom (r : IncCoeffRing E) :
    φ.incidenceHom (G.coeffHom r) = H.coeffHom r := by
  have h : φ.incidenceHom.comp G.coeffHom = H.coeffHom := by
    apply MvPolynomial.algHom_ext
    intro c
    apply Subtype.ext
    change φ.torusHom (G.coeffHom (X c)).val = (H.coeffHom (X c)).val
    simp only [coeffHom, aeval_X]
    rw [torusHom_mk, rename_X]
    rfl
  exact AlgHom.congr_fun h r

/-- The torus map is the identity on the coefficient actions of the common tori. -/
theorem torusHom_incTorusCoeffHom (r : IncCoeffRing E) :
    φ.torusHom (G.incTorusCoeffHom r) = H.incTorusCoeffHom r := by
  rw [G.incTorusCoeffHom_apply, H.incTorusCoeffHom_apply, ← φ.incidenceHom_coeffHom r]
  rfl

/-- The incidence ring map commutes with the coefficient actions. -/
theorem incidenceHom_coeff_mul (r : IncCoeffRing E) (x : G.IncidenceRing) :
    φ.incidenceHom (G.coeffHom r * x) = H.coeffHom r * φ.incidenceHom x := by
  rw [map_mul, incidenceHom_coeffHom]

/-! ## Identity, composition and vertex bijections -/

/-- The torus map of the identity vertex map is the identity. -/
theorem torusHom_refl (G : Multigraph V E) : (refl G).torusHom = AlgHom.id ℂ G.IncTorusRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change Ideal.Quotient.mk _ (rename (refl G).torusVarMap (X w)) = Ideal.Quotient.mk _ (X w)
  rw [rename_X]
  rcases w with v | v | c <;> rfl

/-- The torus map of a composite is the composite of the torus maps. -/
theorem torusHom_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) : (φ.trans χ).torusHom = χ.torusHom.comp φ.torusHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change Ideal.Quotient.mk _ (rename (φ.trans χ).torusVarMap (X w)) =
    χ.torusHom (φ.torusHom (Ideal.Quotient.mk _ (X w)))
  rw [torusHom_mk, torusHom_mk, rename_X, rename_X, rename_X]
  rcases w with v | v | c <;> rfl

/-- **Identity law.** The incidence ring map of the identity vertex map is the identity. -/
theorem incidenceHom_refl (G : Multigraph V E) :
    (refl G).incidenceHom = AlgHom.id ℂ G.IncidenceRing := by
  ext x
  change (refl G).torusHom x.val = x.val
  rw [torusHom_refl, AlgHom.id_apply]

/-- **Composition law.** The incidence ring map of a composite is the composite of the incidence
ring maps. -/
theorem incidenceHom_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) : (φ.trans χ).incidenceHom = χ.incidenceHom.comp φ.incidenceHom := by
  ext x
  change (φ.trans χ).torusHom x.val = χ.torusHom (φ.torusHom x.val)
  rw [torusHom_trans, AlgHom.comp_apply]

/-- Elementwise identity law. -/
theorem incidenceHom_refl_apply (G : Multigraph V E) (x : G.IncidenceRing) :
    (refl G).incidenceHom x = x := by
  rw [incidenceHom_refl, AlgHom.id_apply]

/-- Elementwise composition law. -/
theorem incidenceHom_trans_apply {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) (x : G.IncidenceRing) :
    (φ.trans χ).incidenceHom x = χ.incidenceHom (φ.incidenceHom x) := by
  rw [incidenceHom_trans, AlgHom.comp_apply]

end VertexMap

/-- **Agreement with vertex bijections.** For a vertex bijection the torus map of the underlying
vertex map is the torus isomorphism of the relabeling. -/
theorem VertexRelabel.toVertexMap_torusHom {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [DecidableEq E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) (x : G.IncTorusRing) :
    φ.toVertexMap.torusHom x = φ.torusEquiv x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [VertexMap.torusHom_mk, torusEquiv_mk]
  rfl

/-- **Agreement with vertex bijections.** For a vertex bijection the incidence ring map of the
underlying vertex map is the incidence ring isomorphism of the relabeling. -/
theorem VertexRelabel.toVertexMap_incidenceHom {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [DecidableEq E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) (x : G.IncidenceRing) :
    φ.toVertexMap.incidenceHom x = φ.incidenceEquiv x :=
  Subtype.ext (φ.toVertexMap_torusHom x.val)

end BPFixedPoints.Multigraph
