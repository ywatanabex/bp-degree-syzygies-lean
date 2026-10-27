import BPFixedPoints.Incidence.IncidenceRelabelRings
import BPFixedPoints.Incidence.IncidenceEdgeMapStates

/-!
# Edge maps act on the coefficient ring and on the incidence ring

An edge map `φ : EdgeMap G H` copies the coefficient of an image edge to every edge above it: the
coefficient ring homomorphism (`coeffAlgHom`, `coeffRingHom`) renames
`c_{e,α,β} ↦ c_{φ e,α,β}`, or `c_{φ e,β,α}` when the endpoint order of `e` is reversed. It
preserves the coefficient origin (`constantCoeff_coeffRingHom`). Renaming carries every chart edge
equation of `G` exactly to the chart edge equation of the image edge in `H`
(`rename_incChartEq`), with no sign, so renaming the vertex and coefficient variables induces
algebra homomorphisms of the chart rings (`chartHom`) and of the common torus rings (`torusHom`),
compatible with the chart restrictions. Since the incidence ring is the intersection of the chart
images in the torus ring, the torus homomorphism restricts to an algebra homomorphism of the actual
incidence rings (`incidenceHom`), which intertwines the coefficient maps (`incidenceHom_coeffHom`).

None of these maps is an isomorphism in general, and the coefficient ring homomorphism is not flat
in general.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- The endpoint-index pair of the image coefficient: exchanged when the edge is reversed. -/
def endpointIndex (e : E) (ab : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  if φ.reversed e then ab.swap else ab

@[simp] theorem endpointIndex_endpointIndex (e : E) (ab : Fin 2 × Fin 2) :
    φ.endpointIndex e (φ.endpointIndex e ab) = ab := by
  unfold endpointIndex
  split_ifs <;> simp

/-- Exchanging endpoint indices of a reversed edge, as a permutation. -/
def endpointIndexEquiv (e : E) : Fin 2 × Fin 2 ≃ Fin 2 × Fin 2 where
  toFun := φ.endpointIndex e
  invFun := φ.endpointIndex e
  left_inv := φ.endpointIndex_endpointIndex e
  right_inv := φ.endpointIndex_endpointIndex e

/-- The map of coefficient indices: an index of an edge goes to the corresponding index of its
image edge. -/
def coeffIdxMap (c : IncCoeffIdx E) : IncCoeffIdx E' := (φ.edge c.1, φ.endpointIndex c.1 c.2)

@[simp] theorem coeffIdxMap_apply (e : E) (ab : Fin 2 × Fin 2) :
    φ.coeffIdxMap (e, ab) = (φ.edge e, φ.endpointIndex e ab) := rfl

/-- The coefficient ring homomorphism of an edge map, as an algebra homomorphism. -/
noncomputable def coeffAlgHom : IncCoeffRing E →ₐ[ℂ] IncCoeffRing E' :=
  rename φ.coeffIdxMap

/-- The coefficient ring homomorphism of an edge map. -/
noncomputable def coeffRingHom : IncCoeffRing E →+* IncCoeffRing E' :=
  φ.coeffAlgHom.toRingHom

@[simp] theorem coeffRingHom_apply (p : IncCoeffRing E) : φ.coeffRingHom p = φ.coeffAlgHom p := rfl

theorem coeffAlgHom_apply (p : IncCoeffRing E) : φ.coeffAlgHom p = rename φ.coeffIdxMap p := rfl

@[simp] theorem coeffAlgHom_X (c : IncCoeffIdx E) : φ.coeffAlgHom (X c) = X (φ.coeffIdxMap c) := by
  simp [coeffAlgHom]

/-- The coefficient ring homomorphism preserves the coefficient origin. -/
@[simp] theorem constantCoeff_coeffRingHom (p : IncCoeffRing E) :
    constantCoeff (φ.coeffRingHom p) = constantCoeff p :=
  constantCoeff_rename _ p

/-- The coefficient ring homomorphism is compatible with the coefficient origins. -/
theorem constantCoeff_comp_coeffRingHom :
    (constantCoeff : IncCoeffRing E' →+* ℂ).comp φ.coeffRingHom = constantCoeff :=
  RingHom.ext φ.constantCoeff_coeffRingHom

/-- Renaming of chart variables: vertex coordinates are fixed, coefficients are mapped. -/
def chartVarMap : IncChartVar V E → IncChartVar V E' := Sum.map id φ.coeffIdxMap

/-- Renaming of torus variables. -/
def torusVarMap : IncTorusVar V E → IncTorusVar V E' := Sum.map id (Sum.map id φ.coeffIdxMap)

/-- A renamed edge equation on every chart is the chart equation of the image edge. -/
theorem rename_incChartEq (σ : V → Bool) (e : E) :
    rename φ.chartVarMap (G.incChartEq σ e) = H.incChartEq σ (φ.edge e) := by
  unfold incChartEq
  rw [φ.fst_edge e, φ.snd_edge e]
  simp only [map_sum, map_mul, rename_X, map_incCoord, chartVarMap, Sum.map_inr, Sum.map_inl,
    id_eq, coeffIdxMap_apply, endpointIndex]
  cases φ.reversed e
  · simp
  · simp only [ite_true, Prod.swap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring

/-- The map of torus relation indices. -/
def relIdxMap : V ⊕ E → V ⊕ E' := Sum.map id φ.edge

/-- A renamed torus relation is the torus relation of the mapped index. -/
theorem rename_incTorusRel (i : V ⊕ E) :
    rename φ.torusVarMap (G.incTorusRel i) = H.incTorusRel (φ.relIdxMap i) := by
  rcases i with v | e
  · simp [incTorusRel, relIdxMap, torusVarMap]
  · simp only [incTorusRel, relIdxMap, Sum.map_inr, rename_rename]
    rw [← φ.rename_incChartEq, rename_rename]
    have hf : (φ.torusVarMap ∘ Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) =
        ((Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) ∘ φ.chartVarMap) := by
      funext w
      rcases w with v | c <;> rfl
    rw [hf]

/-- The torus relations of `G` map into the torus ideal of `H`. -/
theorem torusIdeal_le_comap :
    Ideal.span (Set.range G.incTorusRel) ≤
      (Ideal.span (Set.range H.incTorusRel)).comap (rename φ.torusVarMap : _ →ₐ[ℂ] _) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change rename φ.torusVarMap (G.incTorusRel i) ∈ Ideal.span (Set.range H.incTorusRel)
  rw [rename_incTorusRel]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- The chart equations of `G` map into the chart ideal of `H`. -/
theorem chartIdeal_le_comap (σ : V → Bool) :
    Ideal.span (Set.range (G.incChartEq σ)) ≤
      (Ideal.span (Set.range (H.incChartEq σ))).comap (rename φ.chartVarMap : _ →ₐ[ℂ] _) := by
  rw [Ideal.span_le]
  rintro _ ⟨e, rfl⟩
  change rename φ.chartVarMap (G.incChartEq σ e) ∈ Ideal.span (Set.range (H.incChartEq σ))
  rw [rename_incChartEq]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- The algebra homomorphism of common torus rings induced by an edge map. -/
noncomputable def torusHom : G.IncTorusRing →ₐ[ℂ] H.IncTorusRing :=
  Ideal.quotientMapₐ _ (rename φ.torusVarMap) φ.torusIdeal_le_comap

theorem torusHom_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    φ.torusHom (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.torusVarMap p) := rfl

/-- The algebra homomorphism of chart rings induced by an edge map. -/
noncomputable def chartHom (σ : V → Bool) : G.IncChartRing σ →ₐ[ℂ] H.IncChartRing σ :=
  Ideal.quotientMapₐ _ (rename φ.chartVarMap) (φ.chartIdeal_le_comap σ)

theorem chartHom_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    φ.chartHom σ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename φ.chartVarMap p) := rfl

/-- The torus homomorphism on the torus values of chart variables. -/
theorem torusHom_incChartVal (σ : V → Bool) (w : IncChartVar V E) :
    φ.torusHom (G.incChartVal σ w) = H.incChartVal σ (φ.chartVarMap w) := by
  rcases w with v | c
  · simp only [incChartVal, chartVarMap, Sum.map_inl, id_eq]
    split_ifs <;> simp [torusHom_mk, torusVarMap]
  · simp [incChartVal, torusHom_mk, torusVarMap, chartVarMap]

/-- The torus homomorphism intertwines the chart restrictions. -/
theorem torusHom_comp_incChartMap (σ : V → Bool) :
    φ.torusHom.comp (G.incChartMap σ) = (H.incChartMap σ).comp (φ.chartHom σ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change φ.torusHom (G.incChartMap σ (Ideal.Quotient.mk _ (X w))) =
    H.incChartMap σ (Ideal.Quotient.mk _ (rename φ.chartVarMap (X w)))
  rw [incChartMap_mk, aeval_X, torusHom_incChartVal, rename_X, incChartMap_mk, aeval_X]

/-- The torus homomorphism on chart restrictions. -/
theorem torusHom_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    φ.torusHom (G.incChartMap σ y) = H.incChartMap σ (φ.chartHom σ y) :=
  AlgHom.congr_fun (φ.torusHom_comp_incChartMap σ) y

/-- The torus homomorphism maps the incidence ring of `G` into the incidence ring of `H`. -/
theorem torusHom_mem_incidenceRing {x : G.IncTorusRing} (hx : x ∈ G.IncidenceRing) :
    φ.torusHom x ∈ H.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range] at hx ⊢
  intro σ
  obtain ⟨y, rfl⟩ := hx σ
  exact ⟨φ.chartHom σ y, (φ.torusHom_incChartMap σ y).symm⟩

/-- The algebra homomorphism of actual incidence rings induced by an edge map. -/
noncomputable def incidenceHom : G.IncidenceRing →ₐ[ℂ] H.IncidenceRing where
  toFun x := ⟨φ.torusHom x.val, φ.torusHom_mem_incidenceRing x.property⟩
  map_one' := Subtype.ext (map_one φ.torusHom)
  map_mul' x y := Subtype.ext (map_mul φ.torusHom x.val y.val)
  map_zero' := Subtype.ext (map_zero φ.torusHom)
  map_add' x y := Subtype.ext (map_add φ.torusHom x.val y.val)
  commutes' r := Subtype.ext (φ.torusHom.commutes r)

@[simp] theorem incidenceHom_val (x : G.IncidenceRing) :
    (φ.incidenceHom x : H.IncTorusRing) = φ.torusHom x.val := rfl

/-- The incidence ring homomorphism intertwines the coefficient maps. -/
theorem incidenceHom_coeffHom (r : IncCoeffRing E) :
    φ.incidenceHom (G.coeffHom r) = H.coeffHom (φ.coeffAlgHom r) := by
  have h : φ.incidenceHom.comp G.coeffHom = H.coeffHom.comp φ.coeffAlgHom := by
    apply MvPolynomial.algHom_ext
    intro c
    apply Subtype.ext
    change φ.torusHom (G.coeffHom (X c)).val = (H.coeffHom (φ.coeffAlgHom (X c))).val
    rw [coeffAlgHom_X]
    simp only [coeffHom, aeval_X]
    rw [torusHom_mk, rename_X]
    rfl
  exact AlgHom.congr_fun h r

/-- The torus homomorphism intertwines the coefficient actions on the common tori. -/
theorem torusHom_incTorusCoeffHom (r : IncCoeffRing E) :
    φ.torusHom (G.incTorusCoeffHom r) = H.incTorusCoeffHom (φ.coeffAlgHom r) := by
  rw [incTorusCoeffHom_apply, incTorusCoeffHom_apply, ← incidenceHom_coeffHom]
  rfl

end EdgeMap

end BPFixedPoints.Multigraph
