import BPFixedPoints.Incidence.CoefficientModule

/-!
# Vertex bijections act on the incidence ring

A `VertexRelabel G H` is an isomorphism of multigraphs with the same edge type: a bijection
`vertex : V ≃ W` such that every edge of `H` has the endpoints `vertex ∘ G.fst` and
`vertex ∘ G.snd`. The coefficient indices `IncCoeffIdx E` and the coefficient ring
`IncCoeffRing E` are unchanged, and the coefficient map is the identity.

Renaming the vertex variables gives isomorphisms of the chart rings (the chart `σ` of `G` goes to
the chart `σ ∘ vertex.symm` of `H`), of the common torus rings, compatible with the chart
restrictions, and hence of the actual incidence rings (`incidenceEquiv`). This isomorphism is the
identity on coefficients: `incidenceEquiv (G.coeffHom r) = H.coeffHom r`. Vertex degrees of edge
sets are transported along the bijection (`deg_eq`).
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- An isomorphism of multigraphs with the same edge type: a vertex bijection carrying the
endpoints of every edge of `G` to the endpoints of the same edge of `H`, in the same order. -/
structure VertexRelabel {V W E : Type} (G : Multigraph V E) (H : Multigraph W E) where
  /-- The bijection of vertices. -/
  vertex : V ≃ W
  /-- The first endpoint of an edge of `H` is the image of the first endpoint in `G`. -/
  fst_edge : ∀ e, H.fst e = vertex (G.fst e)
  /-- The second endpoint of an edge of `H` is the image of the second endpoint in `G`. -/
  snd_edge : ∀ e, H.snd e = vertex (G.snd e)

/-- The multigraph obtained by renaming the vertices along a bijection. -/
def mapVertices {V W E : Type} (G : Multigraph V E) (ψ : V ≃ W) : Multigraph W E where
  fst e := ψ (G.fst e)
  snd e := ψ (G.snd e)

namespace VertexRelabel

/-- The vertex relabeling of a graph onto its renamed graph. -/
def ofEquiv {V W E : Type} (G : Multigraph V E) (ψ : V ≃ W) : VertexRelabel G (G.mapVertices ψ) where
  vertex := ψ
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The identity vertex relabeling. -/
def refl {V E : Type} (G : Multigraph V E) : VertexRelabel G G where
  vertex := Equiv.refl V
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The composite of two vertex relabelings. -/
def trans {V W X E : Type} {G : Multigraph V E} {H : Multigraph W E} {K : Multigraph X E}
    (φ : VertexRelabel G H) (χ : VertexRelabel H K) : VertexRelabel G K where
  vertex := φ.vertex.trans χ.vertex
  fst_edge e := by rw [χ.fst_edge, φ.fst_edge]; rfl
  snd_edge e := by rw [χ.snd_edge, φ.snd_edge]; rfl

/-- The inverse vertex relabeling. -/
def symm {V W E : Type} {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H) :
    VertexRelabel H G where
  vertex := φ.vertex.symm
  fst_edge e := by rw [φ.fst_edge, Equiv.symm_apply_apply]
  snd_edge e := by rw [φ.snd_edge, Equiv.symm_apply_apply]

@[simp] theorem refl_vertex {V E : Type} (G : Multigraph V E) :
    (refl G).vertex = Equiv.refl V := rfl

@[simp] theorem trans_vertex {V W X E : Type} {G : Multigraph V E} {H : Multigraph W E}
    {K : Multigraph X E} (φ : VertexRelabel G H) (χ : VertexRelabel H K) :
    (φ.trans χ).vertex = φ.vertex.trans χ.vertex := rfl

@[simp] theorem symm_vertex {V W E : Type} {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexRelabel G H) : φ.symm.vertex = φ.vertex.symm := rfl

/-! ## Degrees -/

section Degrees

variable {V W E : Type} [DecidableEq V] [DecidableEq W] {G : Multigraph V E} {H : Multigraph W E}
  (φ : VertexRelabel G H)

/-- Endpoint counts at image vertices are the original endpoint counts. -/
@[simp] theorem endCount_vertex (e : E) (v : V) : H.endCount e (φ.vertex v) = G.endCount e v := by
  unfold endCount
  rw [φ.fst_edge, φ.snd_edge]
  simp only [φ.vertex.injective.eq_iff]

/-- Degrees at image vertices are the original degrees. -/
@[simp] theorem deg_vertex (S : Finset E) (v : V) : H.deg S (φ.vertex v) = G.deg S v := by
  simp [deg]

/-- The degree vector of an edge set of `H` is the transported degree vector of `G`. -/
theorem deg_eq (S : Finset E) : H.deg S = fun w => G.deg S (φ.vertex.symm w) := by
  funext w
  rw [← φ.deg_vertex S (φ.vertex.symm w), Equiv.apply_symm_apply]

/-- Endpoint counts of `H`, through the inverse bijection. -/
theorem endCount_eq (e : E) (w : W) : H.endCount e w = G.endCount e (φ.vertex.symm w) := by
  rw [← φ.endCount_vertex e (φ.vertex.symm w), Equiv.apply_symm_apply]

end Degrees

/-! ## The incidence ring -/

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)

/-- The chart of `H` corresponding to a chart of `G`. -/
def chartIndex (σ : V → Bool) : W → Bool := fun w => σ (φ.vertex.symm w)

/-- Renaming of chart variables: vertex coordinates are renamed, coefficients are fixed. -/
def chartVarEquiv : IncChartVar V E ≃ IncChartVar W E :=
  Equiv.sumCongr φ.vertex (Equiv.refl _)

/-- Renaming of torus variables. -/
def torusVarEquiv : IncTorusVar V E ≃ IncTorusVar W E :=
  Equiv.sumCongr φ.vertex (Equiv.sumCongr φ.vertex (Equiv.refl _))

/-- A renamed chart edge equation is the edge equation of the corresponding chart of `H`. -/
theorem rename_incChartEq (σ : V → Bool) (e : E) :
    rename φ.chartVarEquiv (G.incChartEq σ e) = H.incChartEq (φ.chartIndex σ) e := by
  unfold incChartEq
  simp only [map_sum, map_mul, rename_X, map_incCoord, chartVarEquiv, Equiv.sumCongr_apply,
    Sum.map_inr, Sum.map_inl, Equiv.refl_apply, chartIndex, φ.fst_edge, φ.snd_edge,
    Equiv.symm_apply_apply]

/-- Renaming of the torus relation indices. -/
def relIdxEquiv : V ⊕ E ≃ W ⊕ E := Equiv.sumCongr φ.vertex (Equiv.refl E)

/-- A renamed torus relation is the torus relation of the renamed index. -/
theorem rename_incTorusRel (i : V ⊕ E) :
    rename φ.torusVarEquiv (G.incTorusRel i) = H.incTorusRel (φ.relIdxEquiv i) := by
  rcases i with v | e
  · simp [incTorusRel, relIdxEquiv, torusVarEquiv]
  · simp only [incTorusRel, relIdxEquiv, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
      rename_rename]
    have h := φ.rename_incChartEq (fun _ => false) e
    rw [show φ.chartIndex (fun _ : V => false) = fun _ : W => false from rfl] at h
    rw [← h, rename_rename]
    have hf : (φ.torusVarEquiv ∘ Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) =
        ((Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) ∘ φ.chartVarEquiv) := by
      funext w
      rcases w with v | c <;> rfl
    rw [hf]

/-- The renaming of torus polynomials. -/
noncomputable def torusPolyEquiv :
    MvPolynomial (IncTorusVar V E) ℂ ≃ₐ[ℂ] MvPolynomial (IncTorusVar W E) ℂ :=
  renameEquiv ℂ φ.torusVarEquiv

theorem map_torusIdeal :
    Ideal.span (Set.range H.incTorusRel) =
      (Ideal.span (Set.range G.incTorusRel)).map (φ.torusPolyEquiv : _ →+* _) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨G.incTorusRel (φ.relIdxEquiv.symm i), ⟨_, rfl⟩, ?_⟩
    change rename φ.torusVarEquiv (G.incTorusRel (φ.relIdxEquiv.symm i)) = _
    rw [rename_incTorusRel, Equiv.apply_symm_apply]
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨φ.relIdxEquiv i, (φ.rename_incTorusRel i).symm⟩

/-- The isomorphism of common torus rings. -/
noncomputable def torusEquiv : G.IncTorusRing ≃ₐ[ℂ] H.IncTorusRing :=
  Ideal.quotientEquivAlg _ _ φ.torusPolyEquiv φ.map_torusIdeal

theorem torusEquiv_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    φ.torusEquiv (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.torusVarEquiv p) := rfl

theorem map_chartIdeal (σ : V → Bool) :
    Ideal.span (Set.range (H.incChartEq (φ.chartIndex σ))) =
      (Ideal.span (Set.range (G.incChartEq σ))).map
        ((renameEquiv ℂ φ.chartVarEquiv : _ ≃ₐ[ℂ] _) : _ →+* _) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨G.incChartEq σ e, ⟨_, rfl⟩, ?_⟩
    change rename φ.chartVarEquiv (G.incChartEq σ e) = _
    rw [rename_incChartEq]
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, (φ.rename_incChartEq σ e).symm⟩

/-- The isomorphism of chart rings. -/
noncomputable def chartEquiv (σ : V → Bool) :
    G.IncChartRing σ ≃ₐ[ℂ] H.IncChartRing (φ.chartIndex σ) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ φ.chartVarEquiv) (φ.map_chartIdeal σ)

theorem torusEquiv_incChartVal (σ : V → Bool) (w : IncChartVar V E) :
    φ.torusEquiv (G.incChartVal σ w) = H.incChartVal (φ.chartIndex σ) (φ.chartVarEquiv w) := by
  rcases w with v | c
  · simp only [incChartVal, chartVarEquiv, chartIndex, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.symm_apply_apply]
    split_ifs <;> simp [torusEquiv_mk, torusVarEquiv]
  · simp [incChartVal, torusEquiv_mk, torusVarEquiv, chartVarEquiv]

/-- The torus isomorphism intertwines the chart restrictions. -/
theorem torusEquiv_comp_incChartMap (σ : V → Bool) :
    φ.torusEquiv.toAlgHom.comp (G.incChartMap σ) =
      (H.incChartMap (φ.chartIndex σ)).comp (φ.chartEquiv σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change φ.torusEquiv (G.incChartMap σ (Ideal.Quotient.mk _ (X w))) =
    H.incChartMap (φ.chartIndex σ) (Ideal.Quotient.mk _ (rename φ.chartVarEquiv (X w)))
  rw [incChartMap_mk, aeval_X, torusEquiv_incChartVal, rename_X, incChartMap_mk, aeval_X]

theorem torusEquiv_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    φ.torusEquiv (G.incChartMap σ y) = H.incChartMap (φ.chartIndex σ) (φ.chartEquiv σ y) :=
  AlgHom.congr_fun (φ.torusEquiv_comp_incChartMap σ) y

/-- Every chart of `H` corresponds to a chart of `G`. -/
theorem chartIndex_surjective (τ : W → Bool) : φ.chartIndex (fun v => τ (φ.vertex v)) = τ := by
  funext w
  simp [chartIndex]

/-- The torus isomorphism preserves the incidence rings. -/
theorem torusEquiv_mem_incidenceRing_iff (x : G.IncTorusRing) :
    φ.torusEquiv x ∈ H.IncidenceRing ↔ x ∈ G.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range]
  constructor
  · intro h σ
    obtain ⟨y, hy⟩ := h (φ.chartIndex σ)
    refine ⟨(φ.chartEquiv σ).symm y, φ.torusEquiv.injective ?_⟩
    rw [torusEquiv_incChartMap, AlgEquiv.apply_symm_apply, hy]
  · intro h τ
    obtain ⟨y, hy⟩ := h (fun v => τ (φ.vertex v))
    have hmem : ∃ z, H.incChartMap (φ.chartIndex (fun v => τ (φ.vertex v))) z = φ.torusEquiv x :=
      ⟨φ.chartEquiv _ y, by rw [← torusEquiv_incChartMap, hy]⟩
    rwa [φ.chartIndex_surjective τ] at hmem

/-- The isomorphism of actual incidence rings induced by a vertex relabeling. -/
noncomputable def incidenceEquiv : G.IncidenceRing ≃ₐ[ℂ] H.IncidenceRing where
  toFun x := ⟨φ.torusEquiv x.val, (φ.torusEquiv_mem_incidenceRing_iff x.val).mpr x.property⟩
  invFun y := ⟨φ.torusEquiv.symm y.val, (φ.torusEquiv_mem_incidenceRing_iff _).mp
    (by rw [AlgEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (φ.torusEquiv.symm_apply_apply x.val)
  right_inv y := Subtype.ext (φ.torusEquiv.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul φ.torusEquiv x.val y.val)
  map_add' x y := Subtype.ext (map_add φ.torusEquiv x.val y.val)
  commutes' r := Subtype.ext (φ.torusEquiv.commutes r)

@[simp] theorem incidenceEquiv_val (x : G.IncidenceRing) :
    (φ.incidenceEquiv x : H.IncTorusRing) = φ.torusEquiv x.val := rfl

@[simp] theorem incidenceEquiv_symm_val (y : H.IncidenceRing) :
    (φ.incidenceEquiv.symm y : G.IncTorusRing) = φ.torusEquiv.symm y.val := rfl

/-- The incidence ring isomorphism of a vertex relabeling is the identity on coefficients. -/
theorem incidenceEquiv_coeffHom (r : IncCoeffRing E) :
    φ.incidenceEquiv (G.coeffHom r) = H.coeffHom r := by
  have h : φ.incidenceEquiv.toAlgHom.comp G.coeffHom = H.coeffHom := by
    apply MvPolynomial.algHom_ext
    intro c
    apply Subtype.ext
    change φ.torusEquiv (G.coeffHom (X c)).val = (H.coeffHom (X c)).val
    simp only [coeffHom, aeval_X]
    rw [torusEquiv_mk, rename_X]
    rfl
  exact AlgHom.congr_fun h r

/-- The torus isomorphism is the identity on the coefficient actions of the common tori. -/
theorem torusEquiv_incTorusCoeffHom (r : IncCoeffRing E) :
    φ.torusEquiv (G.incTorusCoeffHom r) = H.incTorusCoeffHom r := by
  rw [G.incTorusCoeffHom_apply, H.incTorusCoeffHom_apply, ← φ.incidenceEquiv_coeffHom r]
  rfl

/-- The inverse incidence ring isomorphism is the identity on coefficients. -/
theorem incidenceEquiv_symm_coeffHom (r : IncCoeffRing E) :
    φ.incidenceEquiv.symm (H.coeffHom r) = G.coeffHom r := by
  rw [← φ.incidenceEquiv_coeffHom r, AlgEquiv.symm_apply_apply]

end VertexRelabel

end BPFixedPoints.Multigraph
