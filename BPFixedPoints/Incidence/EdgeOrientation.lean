import BPFixedPoints.Graph.Basic
import BPFixedPoints.Incidence.ExteriorAlgebraBridge

/-!
# Orientation lines of edges and of edge states

For an edge `e` with endpoints `u = G.fst e` and `v = G.snd e`, the orientation line is
`or(e) = ⋀² R^{u,v}`, the second exterior power of the functions on the endpoint set.
The ordered endpoint pair gives the generator `e_u ∧ e_v`, and reversing the pair negates
it. For a non-loop the generator is a basis, so the line is free of rank one; for a loop
the endpoint set is a singleton, the generator vanishes and the line has rank zero.

For a finite edge state `S`, the state orientation line is the span of the increasingly
ordered wedge of the edge generators of `S`, inside the exterior algebra of
`⨁ e, or(e)`. The product of the generators of disjoint states is the project's shuffle
sign times the generator of the union, and choosing the edge generators identifies the
state generators with the standard basis of `Koszul.Space E R`.
-/

namespace BPFixedPoints.Multigraph

open Set Set.powersetCard

variable {V E : Type*} [DecidableEq V] (G : Multigraph V E)

/-! ### The endpoint set -/

/-- The endpoint set of an edge: two vertices, or one vertex for a loop. -/
def endpoints (e : E) : Finset V := {G.fst e, G.snd e}

/-- The first endpoint lies in the endpoint set. -/
theorem fst_mem_endpoints (e : E) : G.fst e ∈ G.endpoints e :=
  Finset.mem_insert_self _ _

/-- The second endpoint lies in the endpoint set. -/
theorem snd_mem_endpoints (e : E) : G.snd e ∈ G.endpoints e :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The first endpoint as an element of the endpoint set. -/
def fstEndpoint (e : E) : G.endpoints e := ⟨G.fst e, G.fst_mem_endpoints e⟩

/-- The second endpoint as an element of the endpoint set. -/
def sndEndpoint (e : E) : G.endpoints e := ⟨G.snd e, G.snd_mem_endpoints e⟩

/-- Every element of the endpoint set is one of the two endpoints. -/
theorem eq_fstEndpoint_or_eq_sndEndpoint {e : E} (x : G.endpoints e) :
    x = G.fstEndpoint e ∨ x = G.sndEndpoint e := by
  obtain ⟨x, hx⟩ := x
  rcases Finset.mem_insert.mp hx with hx | hx
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp hx))

/-- A non-loop has two endpoints. -/
theorem card_endpoints_of_ne {e : E} (h : G.fst e ≠ G.snd e) : (G.endpoints e).card = 2 :=
  Finset.card_pair h

/-- A loop has one endpoint. -/
theorem card_endpoints_of_isLoop {e : E} (h : G.IsLoop e) : (G.endpoints e).card = 1 := by
  simp [endpoints, show G.fst e = G.snd e from h]

/-- For a non-loop, the endpoint set is identified with `Fin 2`, the first endpoint going
to `0` and the second to `1`. -/
def endpointsEquivFin {e : E} (h : G.fst e ≠ G.snd e) : G.endpoints e ≃ Fin 2 where
  toFun x := if x.1 = G.fst e then 0 else 1
  invFun i := ![G.fstEndpoint e, G.sndEndpoint e] i
  left_inv x := by
    rcases G.eq_fstEndpoint_or_eq_sndEndpoint x with rfl | rfl
    · simp [fstEndpoint]
    · simp [sndEndpoint, Ne.symm h]
  right_inv i := by
    fin_cases i
    · simp [fstEndpoint]
    · simp [sndEndpoint, Ne.symm h]

/-- The inverse of `endpointsEquivFin` lists the first and then the second endpoint. -/
theorem endpointsEquivFin_symm_apply {e : E} (h : G.fst e ≠ G.snd e) (i : Fin 2) :
    (G.endpointsEquivFin h).symm i = ![G.fstEndpoint e, G.sndEndpoint e] i := rfl

/-! ### Orientation lines of edges -/

variable (R : Type*) [CommRing R]

/-- The orientation line `or(e) = ⋀² R^{endpoints e}` of an edge. -/
abbrev orientationLine (e : E) : Type _ := ⋀[R]^2 (G.endpoints e → R)

/-- The generator `e_{fst e} ∧ e_{snd e}` of the orientation line, determined by the
ordered endpoint pair of the edge. -/
noncomputable def orientationGenerator (e : E) : G.orientationLine R e :=
  exteriorPower.ιMulti R 2 ![Pi.single (G.fstEndpoint e) 1, Pi.single (G.sndEndpoint e) 1]

/-- Reversing the endpoint pair negates the orientation generator. -/
theorem orientationGenerator_reverse (e : E) :
    exteriorPower.ιMulti R 2
        ![Pi.single (G.sndEndpoint e) (1 : R), Pi.single (G.fstEndpoint e) 1] =
      -G.orientationGenerator R e := by
  have hv : (![Pi.single (G.sndEndpoint e) (1 : R), Pi.single (G.fstEndpoint e) 1] :
      Fin 2 → G.endpoints e → R) =
      ![Pi.single (G.fstEndpoint e) 1, Pi.single (G.sndEndpoint e) 1] ∘ Equiv.swap 0 1 := by
    funext i
    fin_cases i <;> rfl
  rw [hv, AlternatingMap.map_swap _ _ (by decide : (0 : Fin 2) ≠ 1), orientationGenerator]

/-- The orientation generator of a loop vanishes. -/
theorem orientationGenerator_eq_zero_of_isLoop {e : E} (h : G.IsLoop e) :
    G.orientationGenerator R e = 0 := by
  have hx : G.fstEndpoint e = G.sndEndpoint e := Subtype.ext h
  rw [orientationGenerator, hx]
  exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)

/-- For a non-loop, the standard basis of the functions on the endpoint set, indexed by the
first and second endpoints. -/
noncomputable def endpointBasis {e : E} (h : G.fst e ≠ G.snd e) :
    Module.Basis (Fin 2) R (G.endpoints e → R) :=
  (Pi.basisFun R (G.endpoints e)).reindex (G.endpointsEquivFin h)

/-- The endpoint basis consists of the indicator functions of the first and second
endpoints. -/
theorem endpointBasis_apply {e : E} (h : G.fst e ≠ G.snd e) (i : Fin 2) :
    G.endpointBasis R h i =
      ![Pi.single (G.fstEndpoint e) (1 : R), Pi.single (G.sndEndpoint e) 1] i := by
  rw [endpointBasis, Module.Basis.reindex_apply, Pi.basisFun_apply,
    endpointsEquivFin_symm_apply]
  fin_cases i <;> rfl

/-- The increasing enumeration of `Fin 2` is the identity. -/
private theorem orderEmbOfFin_univ_two (h : (Finset.univ : Finset (Fin 2)).card = 2)
    (i : Fin 2) : Finset.orderEmbOfFin Finset.univ h i = i := by
  set f := Finset.orderEmbOfFin (Finset.univ : Finset (Fin 2)) h
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  rw [Fin.lt_def] at h01
  fin_cases i <;> apply Fin.ext <;> simp <;> omega

/-- The only two-element subset of `Fin 2` is `Fin 2` itself. -/
private def powersetCardFinTwoEquiv : powersetCard (Fin 2) 2 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Finset.univ, by simp⟩
  left_inv s := Subtype.ext (Finset.eq_univ_of_card _ (by simp)).symm
  right_inv _ := rfl

/-- For a non-loop, the orientation generator is a basis of the orientation line. -/
noncomputable def orientationBasis {e : E} (h : G.fst e ≠ G.snd e) :
    Module.Basis Unit R (G.orientationLine R e) :=
  ((G.endpointBasis R h).exteriorPower 2).reindex powersetCardFinTwoEquiv

/-- The unique vector of `orientationBasis` is the orientation generator. -/
@[simp] theorem orientationBasis_apply {e : E} (h : G.fst e ≠ G.snd e) (u : Unit) :
    G.orientationBasis R h u = G.orientationGenerator R e := by
  rw [orientationBasis, Module.Basis.reindex_apply, exteriorPower.basis_apply,
    orientationGenerator]
  simp only [exteriorPower.ιMulti_family]
  congr 1
  funext i
  show G.endpointBasis R h (Finset.orderEmbOfFin Finset.univ (by simp) i) = _
  rw [orderEmbOfFin_univ_two, endpointBasis_apply]

/-- For a non-loop, the orientation line is free of rank one. -/
theorem finrank_orientationLine [Nontrivial R] {e : E} (h : G.fst e ≠ G.snd e) :
    Module.finrank R (G.orientationLine R e) = 1 := by
  rw [Module.finrank_eq_card_basis (G.orientationBasis R h), Fintype.card_unit]

/-- For a loop, the orientation line has rank zero. -/
theorem finrank_orientationLine_of_isLoop [Nontrivial R] {e : E} (h : G.IsLoop e) :
    Module.finrank R (G.orientationLine R e) = 0 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    G.card_endpoints_of_isLoop h]
  rfl

/-- The coordinate of the orientation line along its generator; it is zero on loops,
whose orientation line has rank zero. -/
noncomputable def orientationCoord (e : E) : G.orientationLine R e →ₗ[R] R :=
  if h : G.fst e ≠ G.snd e then (G.orientationBasis R h).coord () else 0

/-- The coordinate of the generator of a non-loop is one. -/
theorem orientationCoord_generator {e : E} (h : G.fst e ≠ G.snd e) :
    G.orientationCoord R e (G.orientationGenerator R e) = 1 := by
  simp only [orientationCoord, ne_eq, h, not_false_eq_true, ↓reduceDIte]
  rw [← G.orientationBasis_apply R h (), Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

/-! ### Orientation lines of edge states -/

variable [LinearOrder E]

/-- The direct sum of the orientation lines of all edges. -/
abbrev orientationSpace : Type _ := DirectSum E fun e => G.orientationLine R e

/-- The generator of `or(e)`, placed in the summand of `e`. -/
noncomputable def edgeOrientationVector (e : E) : G.orientationSpace R :=
  DirectSum.lof R E (fun e => G.orientationLine R e) e (G.orientationGenerator R e)

/-- The orientation generator of a state: the wedge, in increasing edge order, of the
orientation generators of its edges. -/
noncomputable def stateOrientationGenerator (S : Finset E) :
    ExteriorAlgebra R (G.orientationSpace R) :=
  Koszul.orderedWedge R (G.edgeOrientationVector R) S

/-- The orientation line of a state: the span of its orientation generator. It does not
depend on the edge order or the edge orientations, which only change the generator by a
sign. -/
def stateOrientationLine (S : Finset E) : Submodule R (ExteriorAlgebra R (G.orientationSpace R)) :=
  R ∙ G.stateOrientationGenerator R S

/-- The generator lies in the state orientation line. -/
theorem stateOrientationGenerator_mem (S : Finset E) :
    G.stateOrientationGenerator R S ∈ G.stateOrientationLine R S :=
  Submodule.mem_span_singleton_self _

/-- The empty state has generator `1`. -/
@[simp] theorem stateOrientationGenerator_empty :
    G.stateOrientationGenerator R (∅ : Finset E) = 1 :=
  Koszul.orderedWedge_empty _

/-- A one-edge state has as generator the image of the edge generator. -/
@[simp] theorem stateOrientationGenerator_singleton (e : E) :
    G.stateOrientationGenerator R {e} = ExteriorAlgebra.ι R (G.edgeOrientationVector R e) :=
  Koszul.orderedWedge_singleton _ e

/-- The state orientation generator has exterior degree `S.card`. -/
theorem stateOrientationGenerator_mem_exteriorPower (S : Finset E) :
    G.stateOrientationGenerator R S ∈ ⋀[R]^S.card (G.orientationSpace R) :=
  Koszul.orderedWedge_mem_exteriorPower _ S

/-- The state orientation line lies in the exterior power of degree `S.card`. -/
theorem stateOrientationLine_le_exteriorPower (S : Finset E) :
    G.stateOrientationLine R S ≤ ⋀[R]^S.card (G.orientationSpace R) :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr (G.stateOrientationGenerator_mem_exteriorPower R S)

/-- The generators of disjoint states multiply to the shuffle sign times the generator of
the union. -/
theorem stateOrientationGenerator_mul_of_disjoint {S T : Finset E} (h : Disjoint S T) :
    G.stateOrientationGenerator R S * G.stateOrientationGenerator R T =
      Koszul.shuffleSign (R := R) S T • G.stateOrientationGenerator R (S ∪ T) :=
  Koszul.orderedWedge_mul_of_disjoint _ h

/-- The generators of overlapping states multiply to zero. -/
theorem stateOrientationGenerator_mul_of_not_disjoint {S T : Finset E} (h : ¬Disjoint S T) :
    G.stateOrientationGenerator R S * G.stateOrientationGenerator R T = 0 :=
  Koszul.orderedWedge_mul_of_not_disjoint _ h

/-- The product of two state orientation lines lies in the orientation line of the union. -/
theorem stateOrientationLine_mul_le (S T : Finset E) :
    G.stateOrientationLine R S * G.stateOrientationLine R T ≤
      G.stateOrientationLine R (S ∪ T) := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [smul_mul_smul_comm]
  by_cases h : Disjoint S T
  · rw [G.stateOrientationGenerator_mul_of_disjoint R h, smul_smul]
    exact Submodule.smul_mem _ _ (G.stateOrientationGenerator_mem R _)
  · rw [G.stateOrientationGenerator_mul_of_not_disjoint R h, smul_zero]
    exact Submodule.zero_mem _

/-! ### Trivialization by the edge generators -/

/-- The map sending each orientation line to the coordinate line of its edge, by the
coordinate along the edge generator. -/
noncomputable def orientationTrivialization : G.orientationSpace R →ₗ[R] (E →₀ R) :=
  DirectSum.toModule R E (E →₀ R) fun e => (Finsupp.lsingle e).comp (G.orientationCoord R e)

/-- The trivialization sends the generator of a non-loop to the generator of its edge. -/
theorem orientationTrivialization_edgeOrientationVector {e : E} (h : G.fst e ≠ G.snd e) :
    G.orientationTrivialization R (G.edgeOrientationVector R e) = Finsupp.single e 1 := by
  rw [orientationTrivialization, edgeOrientationVector, DirectSum.toModule_lof,
    LinearMap.comp_apply, G.orientationCoord_generator R h, Finsupp.lsingle_apply]

/-- On a state without loops, the trivialization sends the state orientation generator to
the standard basis state of `Koszul.Space E R`. -/
theorem map_orientationTrivialization_stateOrientationGenerator {S : Finset E}
    (hS : ∀ e ∈ S, G.fst e ≠ G.snd e) :
    ExteriorAlgebra.map (G.orientationTrivialization R) (G.stateOrientationGenerator R S) =
      Koszul.exteriorAlgebraEquiv E R (Finsupp.single S 1) := by
  rw [stateOrientationGenerator, Koszul.map_orderedWedge,
    Koszul.exteriorAlgebraEquiv_single_one]
  exact Koszul.orderedWedge_congr fun e he =>
    G.orientationTrivialization_edgeOrientationVector R (hS e he)

/-- On a state without loops, the orientation generator is linearly independent. -/
theorem linearIndependent_stateOrientationGenerator {S : Finset E}
    (hS : ∀ e ∈ S, G.fst e ≠ G.snd e) :
    LinearIndependent R fun _ : Unit => G.stateOrientationGenerator R S := by
  refine LinearIndependent.of_comp
    ((Koszul.exteriorAlgebraEquiv E R).symm.toLinearMap.comp
      (ExteriorAlgebra.map (G.orientationTrivialization R)).toLinearMap) ?_
  have hv : ((Koszul.exteriorAlgebraEquiv E R).symm.toLinearMap.comp
      (ExteriorAlgebra.map (G.orientationTrivialization R)).toLinearMap ∘
        fun _ : Unit => G.stateOrientationGenerator R S) =
      (Finsupp.basisSingleOne : Module.Basis (Finset E) R (Finset E →₀ R)) ∘
        fun _ : Unit => S := by
    funext u
    simp [G.map_orientationTrivialization_stateOrientationGenerator R hS]
  rw [hv]
  exact Finsupp.basisSingleOne.linearIndependent.comp _ (Function.injective_of_subsingleton _)

/-- On a state without loops, the orientation generator is a basis of the state
orientation line. -/
noncomputable def stateOrientationBasis {S : Finset E} (hS : ∀ e ∈ S, G.fst e ≠ G.snd e) :
    Module.Basis Unit R (G.stateOrientationLine R S) :=
  (Module.Basis.span (G.linearIndependent_stateOrientationGenerator R hS)).map
    (LinearEquiv.ofEq _ _ (by rw [stateOrientationLine, Set.range_const]))

/-- The unique vector of `stateOrientationBasis` is the state orientation generator. -/
@[simp] theorem stateOrientationBasis_apply {S : Finset E} (hS : ∀ e ∈ S, G.fst e ≠ G.snd e)
    (u : Unit) :
    (G.stateOrientationBasis R hS u : ExteriorAlgebra R (G.orientationSpace R)) =
      G.stateOrientationGenerator R S := by
  simp [stateOrientationBasis]

/-- On a state without loops, the state orientation line is free of rank one. -/
theorem finrank_stateOrientationLine [Nontrivial R] {S : Finset E}
    (hS : ∀ e ∈ S, G.fst e ≠ G.snd e) :
    Module.finrank R (G.stateOrientationLine R S) = 1 := by
  rw [Module.finrank_eq_card_basis (G.stateOrientationBasis R hS), Fintype.card_unit]

end BPFixedPoints.Multigraph
