import BPFixedPoints.Incidence.CoefficientModule
import BPFixedPoints.Incidence.IncidenceRelabelStates

/-!
# Edge relabelings act on the coefficient ring and on the incidence ring

An edge relabeling `φ : EdgeRelabel G H` renames the coefficient variables:
`c_{e,α,β} ↦ c_{φ e,α,β}`, or `c_{φ e,β,α}` when the endpoint order of `e` is reversed
(`coeffIdxEquiv`). Since the coefficients are indexed by ordered endpoint pairs, this carries every
chart edge equation of `G` exactly to the chart edge equation of the image edge in `H`
(`rename_incChartEq`), with no sign. Renaming the vertex and coefficient variables gives
isomorphisms of the coefficient rings (`coeffEquiv`, which preserves the constant coefficient), of
the chart rings and of the common torus rings, compatible with the chart restrictions. Hence it
restricts to an isomorphism of the actual incidence rings (`incidenceEquiv`), intertwining the
coefficient maps.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

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

/-- Relabeling of coefficient indices. -/
def coeffIdxEquiv : IncCoeffIdx E ≃ IncCoeffIdx E' where
  toFun c := (φ.edge c.1, φ.endpointIndex c.1 c.2)
  invFun c := (φ.edge.symm c.1, φ.endpointIndex (φ.edge.symm c.1) c.2)
  left_inv c := by
    obtain ⟨e, ab⟩ := c
    simp
  right_inv c := by
    obtain ⟨e, ab⟩ := c
    simp

@[simp] theorem coeffIdxEquiv_apply (e : E) (ab : Fin 2 × Fin 2) :
    φ.coeffIdxEquiv (e, ab) = (φ.edge e, φ.endpointIndex e ab) := rfl

/-- The coefficient ring isomorphism of an edge relabeling. -/
noncomputable def coeffEquiv : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E' :=
  renameEquiv ℂ φ.coeffIdxEquiv

@[simp] theorem coeffEquiv_X (c : IncCoeffIdx E) :
    φ.coeffEquiv (X c) = X (φ.coeffIdxEquiv c) := by
  simp [coeffEquiv]

theorem coeffEquiv_apply (p : IncCoeffRing E) : φ.coeffEquiv p = rename φ.coeffIdxEquiv p := rfl

/-- The coefficient ring isomorphism preserves the coefficient origin. -/
@[simp] theorem constantCoeff_coeffEquiv (p : IncCoeffRing E) :
    constantCoeff (φ.coeffEquiv p) = constantCoeff p :=
  constantCoeff_rename _ p

/-- The coefficient ring isomorphism is compatible with the coefficient origins. -/
theorem constantCoeff_comp_coeffEquiv :
    (constantCoeff : IncCoeffRing E' →+* ℂ).comp φ.coeffEquiv.toRingEquiv.toRingHom =
      constantCoeff := by
  ext p
  · exact φ.constantCoeff_coeffEquiv (C p)
  · exact φ.constantCoeff_coeffEquiv (X _)

/-- Renaming of chart variables: vertex coordinates are fixed, coefficients are relabeled. -/
def chartVarEquiv : IncChartVar V E ≃ IncChartVar V E' :=
  Equiv.sumCongr (Equiv.refl V) φ.coeffIdxEquiv

/-- Renaming of torus variables. -/
def torusVarEquiv : IncTorusVar V E ≃ IncTorusVar V E' :=
  Equiv.sumCongr (Equiv.refl V) (Equiv.sumCongr (Equiv.refl V) φ.coeffIdxEquiv)

/-- A relabeled edge equation on every chart is the chart equation of the image edge. -/
theorem rename_incChartEq (σ : V → Bool) (e : E) :
    rename φ.chartVarEquiv (G.incChartEq σ e) = H.incChartEq σ (φ.edge e) := by
  unfold incChartEq
  rw [φ.fst_edge e, φ.snd_edge e]
  simp only [map_sum, map_mul, rename_X, map_incCoord, chartVarEquiv, Equiv.sumCongr_apply,
    Sum.map_inr, Sum.map_inl, Equiv.refl_apply, coeffIdxEquiv_apply, endpointIndex]
  cases φ.reversed e
  · simp
  · simp only [ite_true, Prod.swap]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring

/-- Relabeling of the torus relation indices. -/
def relIdxEquiv : V ⊕ E ≃ V ⊕ E' := Equiv.sumCongr (Equiv.refl V) φ.edge

/-- A relabeled torus relation is the torus relation of the relabeled index. -/
theorem rename_incTorusRel (i : V ⊕ E) :
    rename φ.torusVarEquiv (G.incTorusRel i) = H.incTorusRel (φ.relIdxEquiv i) := by
  rcases i with v | e
  · simp [incTorusRel, relIdxEquiv, torusVarEquiv]
  · simp only [incTorusRel, relIdxEquiv, Equiv.sumCongr_apply, Sum.map_inr, rename_rename]
    rw [← φ.rename_incChartEq, rename_rename]
    have hf : (φ.torusVarEquiv ∘ Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) =
        ((Sum.elim Sum.inl fun c => Sum.inr (Sum.inr c)) ∘ φ.chartVarEquiv) := by
      funext w
      rcases w with v | c <;> rfl
    rw [hf]

/-- The renaming of torus polynomials. -/
noncomputable def torusPolyEquiv :
    MvPolynomial (IncTorusVar V E) ℂ ≃ₐ[ℂ] MvPolynomial (IncTorusVar V E') ℂ :=
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
    Ideal.span (Set.range (H.incChartEq σ)) =
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

/-- The isomorphism of chart rings. -/
noncomputable def chartEquiv (σ : V → Bool) : G.IncChartRing σ ≃ₐ[ℂ] H.IncChartRing σ :=
  Ideal.quotientEquivAlg _ _ (renameEquiv ℂ φ.chartVarEquiv) (φ.map_chartIdeal σ)

theorem torusEquiv_incChartVal (σ : V → Bool) (w : IncChartVar V E) :
    φ.torusEquiv (G.incChartVal σ w) = H.incChartVal σ (φ.chartVarEquiv w) := by
  rcases w with v | c
  · simp only [incChartVal, chartVarEquiv, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
    split_ifs <;> simp [torusEquiv_mk, torusVarEquiv]
  · simp [incChartVal, torusEquiv_mk, torusVarEquiv, chartVarEquiv]

/-- The torus isomorphism intertwines the chart restrictions. -/
theorem torusEquiv_comp_incChartMap (σ : V → Bool) :
    φ.torusEquiv.toAlgHom.comp (G.incChartMap σ) =
      (H.incChartMap σ).comp (φ.chartEquiv σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change φ.torusEquiv (G.incChartMap σ (Ideal.Quotient.mk _ (X w))) =
    H.incChartMap σ (Ideal.Quotient.mk _ (rename φ.chartVarEquiv (X w)))
  rw [incChartMap_mk, aeval_X, torusEquiv_incChartVal, rename_X, incChartMap_mk, aeval_X]

theorem torusEquiv_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    φ.torusEquiv (G.incChartMap σ y) = H.incChartMap σ (φ.chartEquiv σ y) :=
  AlgHom.congr_fun (φ.torusEquiv_comp_incChartMap σ) y

/-- The torus isomorphism preserves the incidence rings. -/
theorem torusEquiv_mem_incidenceRing_iff (x : G.IncTorusRing) :
    φ.torusEquiv x ∈ H.IncidenceRing ↔ x ∈ G.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range]
  constructor
  · intro h σ
    obtain ⟨y, hy⟩ := h σ
    refine ⟨(φ.chartEquiv σ).symm y, φ.torusEquiv.injective ?_⟩
    rw [torusEquiv_incChartMap, AlgEquiv.apply_symm_apply, hy]
  · rintro h σ
    obtain ⟨y, rfl⟩ := h σ
    exact ⟨φ.chartEquiv σ y, (φ.torusEquiv_incChartMap σ y).symm⟩

/-- The isomorphism of actual incidence rings induced by an edge relabeling. -/
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

/-- The incidence ring isomorphism intertwines the coefficient maps. -/
theorem incidenceEquiv_coeffHom (r : IncCoeffRing E) :
    φ.incidenceEquiv (G.coeffHom r) = H.coeffHom (φ.coeffEquiv r) := by
  have h : φ.incidenceEquiv.toAlgHom.comp G.coeffHom = H.coeffHom.comp φ.coeffEquiv.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro c
    apply Subtype.ext
    change φ.torusEquiv (G.coeffHom (X c)).val = (H.coeffHom (φ.coeffEquiv (X c))).val
    rw [coeffEquiv_X]
    simp only [coeffHom, aeval_X]
    rw [torusEquiv_mk, rename_X]
    rfl
  exact AlgHom.congr_fun h r

/-- The torus isomorphism intertwines the coefficient actions on the common tori. -/
theorem torusEquiv_incTorusCoeffHom (r : IncCoeffRing E) :
    φ.torusEquiv (G.incTorusCoeffHom r) = H.incTorusCoeffHom (φ.coeffEquiv r) := by
  rw [incTorusCoeffHom_apply, incTorusCoeffHom_apply, ← incidenceEquiv_coeffHom]
  rfl

end EdgeRelabel

end BPFixedPoints.Multigraph
