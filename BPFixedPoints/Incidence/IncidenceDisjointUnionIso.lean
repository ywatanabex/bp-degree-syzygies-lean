import BPFixedPoints.Incidence.IncidenceDisjointUnionRings

/-!
# Oriented isomorphisms of multigraphs act on incidence rings

An oriented isomorphism `φ : OrientedIso G G'` is a pair of bijections on vertices and on edges
that carries the ordered endpoint pair of every edge to the ordered endpoint pair of its image.
Renaming vertex coordinates and coefficients gives isomorphisms of the coefficient rings
(`coeffEquiv`), of the chart rings (`chartEquiv σ`, from the chart `σ` to the chart
`σ ∘ φ.vertex.symm`) and of the common tori (`torusEquiv`), compatible with the chart restrictions.
Since `σ ↦ σ ∘ φ.vertex.symm` is a bijection of charts, the torus isomorphism restricts to an
isomorphism of the incidence rings (`incidenceEquiv`), compatible with the coefficient maps.

Unlike `EdgeRelabel`, vertices may be renamed and the vertex type may change, but no edge is
reversed. The disjoint-union isomorphisms `sumComm`, `sumAssoc` and `sumEmpty` are recorded here;
their compatibility with the tensor formula is proved in `IncidenceDisjointUnionCoherence.lean`.
General noncontracting graph maps (non-bijective) are not treated.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- An isomorphism of multigraphs preserving the ordered endpoint pair of every edge. -/
structure OrientedIso {V E V' E' : Type*} (G : Multigraph V E) (G' : Multigraph V' E') where
  /-- The bijection of vertices. -/
  vertex : V ≃ V'
  /-- The bijection of edges. -/
  edge : E ≃ E'
  /-- The first endpoint of an image edge is the image of the first endpoint. -/
  fst_edge : ∀ e, G'.fst (edge e) = vertex (G.fst e)
  /-- The second endpoint of an image edge is the image of the second endpoint. -/
  snd_edge : ∀ e, G'.snd (edge e) = vertex (G.snd e)

namespace OrientedIso

/-! ### The disjoint-union isomorphisms -/

section Graphs

variable {V W U E F D : Type*} (G : Multigraph V E) (H : Multigraph W F) (K : Multigraph U D)

/-- The symmetry `G ⊔ H ≅ H ⊔ G`. -/
def sumComm : OrientedIso (G.disjointSum H) (H.disjointSum G) where
  vertex := Equiv.sumComm V W
  edge := Equiv.sumComm E F
  fst_edge := by rintro (e | f) <;> rfl
  snd_edge := by rintro (e | f) <;> rfl

/-- The associativity `(G ⊔ H) ⊔ K ≅ G ⊔ (H ⊔ K)`. -/
def sumAssoc : OrientedIso ((G.disjointSum H).disjointSum K) (G.disjointSum (H.disjointSum K)) where
  vertex := Equiv.sumAssoc V W U
  edge := Equiv.sumAssoc E F D
  fst_edge := by rintro ((e | f) | d) <;> rfl
  snd_edge := by rintro ((e | f) | d) <;> rfl

/-- The right unit `G ⊔ G₀ ≅ G` for a graph `G₀` with no vertices and no edges. -/
def sumEmpty {V₀ E₀ : Type*} [IsEmpty V₀] [IsEmpty E₀] (G₀ : Multigraph V₀ E₀) :
    OrientedIso (G.disjointSum G₀) G where
  vertex := Equiv.sumEmpty V V₀
  edge := Equiv.sumEmpty E E₀
  fst_edge := by
    rintro (e | e)
    · rfl
    · exact isEmptyElim e
  snd_edge := by
    rintro (e | e)
    · rfl
    · exact isEmptyElim e

end Graphs

/-! ### The induced isomorphisms of rings -/

variable {V E V' E' : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq V'] [Fintype V'] [DecidableEq E'] [Fintype E']
  {G : Multigraph V E} {G' : Multigraph V' E'} (φ : OrientedIso G G')

/-- Renaming of coefficient indices. -/
def coeffIdxEquiv : IncCoeffIdx E ≃ IncCoeffIdx E' := Equiv.prodCongr φ.edge (Equiv.refl _)

@[simp] theorem coeffIdxEquiv_apply (e : E) (ab : Fin 2 × Fin 2) :
    φ.coeffIdxEquiv (e, ab) = (φ.edge e, ab) := rfl

/-- The coefficient ring isomorphism of an oriented isomorphism. -/
noncomputable def coeffEquiv : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E' :=
  renameEquiv ℂ φ.coeffIdxEquiv

/-- Renaming of chart variables. -/
def chartVarEquiv : IncChartVar V E ≃ IncChartVar V' E' :=
  Equiv.sumCongr φ.vertex φ.coeffIdxEquiv

/-- Renaming of torus variables. -/
def torusVarEquiv : IncTorusVar V E ≃ IncTorusVar V' E' :=
  Equiv.sumCongr φ.vertex (Equiv.sumCongr φ.vertex φ.coeffIdxEquiv)

/-- Renaming of torus relation indices. -/
def relIdxEquiv : V ⊕ E ≃ V' ⊕ E' := Equiv.sumCongr φ.vertex φ.edge

/-- A renamed chart equation is the chart equation of the image edge on the image chart. -/
theorem rename_incChartEq (σ : V → Bool) (e : E) :
    rename φ.chartVarEquiv (G.incChartEq σ e) = G'.incChartEq (σ ∘ φ.vertex.symm) (φ.edge e) := by
  unfold incChartEq
  rw [φ.fst_edge e, φ.snd_edge e]
  simp [map_mul, rename_X, map_incCoord, chartVarEquiv]

/-- A renamed torus relation is the torus relation of the renamed index. -/
theorem rename_incTorusRel (i : V ⊕ E) :
    rename φ.torusVarEquiv (G.incTorusRel i) = G'.incTorusRel (φ.relIdxEquiv i) := by
  rcases i with v | e
  · simp [incTorusRel, relIdxEquiv, torusVarEquiv]
  · simp only [incTorusRel, relIdxEquiv, Equiv.sumCongr_apply, Sum.map_inr, rename_rename]
    rw [show G'.incChartEq (fun _ => false) (φ.edge e) =
      G'.incChartEq ((fun _ => false) ∘ φ.vertex.symm) (φ.edge e) from rfl,
      ← φ.rename_incChartEq, rename_rename]
    congr 2
    funext w
    rcases w with v | c <;> rfl

theorem map_torusIdeal :
    Ideal.span (Set.range G'.incTorusRel) =
      (Ideal.span (Set.range G.incTorusRel)).map
        ((renameEquiv ℂ φ.torusVarEquiv : _ ≃ₐ[ℂ] _) : _ →+* _) := by
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
noncomputable def torusEquiv : G.IncTorusRing ≃ₐ[ℂ] G'.IncTorusRing :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ φ.torusVarEquiv) φ.map_torusIdeal

theorem torusEquiv_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    φ.torusEquiv (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.torusVarEquiv p) := rfl

@[simp] theorem torusEquiv_mk_X (w : IncTorusVar V E) :
    φ.torusEquiv (Ideal.Quotient.mk _ (X w)) = Ideal.Quotient.mk _ (X (φ.torusVarEquiv w)) := by
  rw [torusEquiv_mk, rename_X]

theorem map_chartIdeal (σ : V → Bool) :
    Ideal.span (Set.range (G'.incChartEq (σ ∘ φ.vertex.symm))) =
      (Ideal.span (Set.range (G.incChartEq σ))).map
        ((renameEquiv ℂ φ.chartVarEquiv : _ ≃ₐ[ℂ] _) : _ →+* _) := by
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨e', rfl⟩
    refine ⟨G.incChartEq σ (φ.edge.symm e'), ⟨_, rfl⟩, ?_⟩
    change rename φ.chartVarEquiv (G.incChartEq σ (φ.edge.symm e')) = _
    rw [rename_incChartEq, Equiv.apply_symm_apply]
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨φ.edge e, (φ.rename_incChartEq σ e).symm⟩

/-- The isomorphism from the chart `σ` of `G` to the chart `σ ∘ φ.vertex.symm` of `G'`. -/
noncomputable def chartEquiv (σ : V → Bool) :
    G.IncChartRing σ ≃ₐ[ℂ] G'.IncChartRing (σ ∘ φ.vertex.symm) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ φ.chartVarEquiv) (φ.map_chartIdeal σ)

theorem torusEquiv_incChartVal (σ : V → Bool) (w : IncChartVar V E) :
    φ.torusEquiv (G.incChartVal σ w) =
      G'.incChartVal (σ ∘ φ.vertex.symm) (φ.chartVarEquiv w) := by
  rcases w with v | c
  · simp only [incChartVal, chartVarEquiv, Equiv.sumCongr_apply, Sum.map_inl, Function.comp_apply,
      Equiv.symm_apply_apply]
    split_ifs <;> simp [torusVarEquiv]
  · simp [incChartVal, torusVarEquiv, chartVarEquiv]

/-- The torus isomorphism intertwines the chart restrictions. -/
theorem torusEquiv_comp_incChartMap (σ : V → Bool) :
    φ.torusEquiv.toAlgHom.comp (G.incChartMap σ) =
      (G'.incChartMap (σ ∘ φ.vertex.symm)).comp (φ.chartEquiv σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change φ.torusEquiv (G.incChartMap σ (Ideal.Quotient.mk _ (X w))) =
    G'.incChartMap (σ ∘ φ.vertex.symm) (Ideal.Quotient.mk _ (rename φ.chartVarEquiv (X w)))
  rw [incChartMap_mk, aeval_X, torusEquiv_incChartVal, rename_X, incChartMap_mk, aeval_X]

theorem torusEquiv_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    φ.torusEquiv (G.incChartMap σ y) = G'.incChartMap (σ ∘ φ.vertex.symm) (φ.chartEquiv σ y) :=
  AlgHom.congr_fun (φ.torusEquiv_comp_incChartMap σ) y

/-- The torus isomorphism preserves the incidence rings. -/
theorem torusEquiv_mem_incidenceRing_iff (x : G.IncTorusRing) :
    φ.torusEquiv x ∈ G'.IncidenceRing ↔ x ∈ G.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range]
  constructor
  · intro h σ
    obtain ⟨y, hy⟩ := h (σ ∘ φ.vertex.symm)
    refine ⟨(φ.chartEquiv σ).symm y, φ.torusEquiv.injective ?_⟩
    rw [torusEquiv_incChartMap, AlgEquiv.apply_symm_apply, hy]
  · intro h σ'
    obtain ⟨σ, rfl⟩ : ∃ σ : V → Bool, σ' = σ ∘ φ.vertex.symm :=
      ⟨σ' ∘ φ.vertex, by funext v; simp⟩
    obtain ⟨y, rfl⟩ := h σ
    exact ⟨φ.chartEquiv σ y, (φ.torusEquiv_incChartMap σ y).symm⟩

/-- **Oriented isomorphisms act on incidence rings.** -/
noncomputable def incidenceEquiv : G.IncidenceRing ≃ₐ[ℂ] G'.IncidenceRing where
  toFun x := ⟨φ.torusEquiv x.val, (φ.torusEquiv_mem_incidenceRing_iff x.val).mpr x.property⟩
  invFun y := ⟨φ.torusEquiv.symm y.val, (φ.torusEquiv_mem_incidenceRing_iff _).mp
    (by rw [AlgEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (φ.torusEquiv.symm_apply_apply x.val)
  right_inv y := Subtype.ext (φ.torusEquiv.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul φ.torusEquiv x.val y.val)
  map_add' x y := Subtype.ext (map_add φ.torusEquiv x.val y.val)
  commutes' r := Subtype.ext (φ.torusEquiv.commutes r)

@[simp] theorem incidenceEquiv_val (x : G.IncidenceRing) :
    (φ.incidenceEquiv x : G'.IncTorusRing) = φ.torusEquiv x.val := rfl

@[simp] theorem incidenceEquiv_symm_val (y : G'.IncidenceRing) :
    (φ.incidenceEquiv.symm y : G.IncTorusRing) = φ.torusEquiv.symm y.val := rfl

/-- The incidence ring isomorphism intertwines the coefficient maps. -/
theorem incidenceEquiv_coeffHom (r : IncCoeffRing E) :
    φ.incidenceEquiv (G.coeffHom r) = G'.coeffHom (φ.coeffEquiv r) := by
  have h : φ.incidenceEquiv.toAlgHom.comp G.coeffHom =
      G'.coeffHom.comp φ.coeffEquiv.toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨e, ab⟩
    apply Subtype.ext
    change φ.torusEquiv (G.coeffHom (X (e, ab))).val =
      (G'.coeffHom (rename φ.coeffIdxEquiv (X (e, ab)))).val
    simp [coeffHom, torusVarEquiv]
  exact AlgHom.congr_fun h r

end OrientedIso

end BPFixedPoints.Multigraph
