import BPFixedPoints.Incidence.IncidenceSignedEdgeMapRings
import BPFixedPoints.Incidence.IncidenceEdgeSignStates

/-!
# The exterior map and the state map of a signed edge map

For a signed edge map `φ : SignedEdgeMap G H` with edge sign `ε`, the linear map of free modules
`e ↦ ε_e e_{φ e}` (`signedEdgeLinearMap`) induces, through Mathlib's exterior algebra, the signed
exterior map of exterior state modules (`signedExteriorMap`). It sends left exterior multiplication
by `e` to `ε_e` times that by `φ e`, preserves the exterior product, composes functorially with the
composite signs, and sends the basis vector of an edge set `S` to `wedgeSign S · ∏_{e ∈ S} ε_e`
times the basis vector of `φ S` (`signedExteriorMap_single`), which is zero when the edge function
is not injective on `S`.

For a signed edge map `φ : SignedEdgeMap G H` with edge sign `ε`, the signed state map
(`signedStateMap`) is the edge-sign scaling of `G` followed by the state map of the edge map: the
basis state of an edge set `S` goes to `wedgeSign S · ∏_{e ∈ S} ε_e` times the same state of the
image edge set `φ S` when the edge function is injective on `S`, and to zero otherwise
(`signedStateMap_single`).

Edge signs of the target pull back along the edge function (`EdgeMap.pullSign`,
`e ↦ ε'_{φ e}`); on an edge set where the edge function is injective, the sign of the image edge
set is the pulled-back sign of the edge set (`EdgeMap.setSign_edgeSet`), so the state map of an
edge map intertwines the scaling by `ε'` on `H` with the scaling by the pulled-back sign on `G`
(`EdgeMap.stateMap_edgeSignState`). This is the identity behind the composition law.

The signed state map preserves the state product and the unit state, is the identity for the
identity signed edge map, and composes functorially with the composite signs
`e ↦ ε_φ(e) · ε_ψ(φ e)`. For trivial signs it is the state map of the edge map, and for the
identity edge map it is the edge-sign scaling.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp

/-! ## Pulling edge signs back along edge maps -/

namespace EdgeMap

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- The edge sign of `G` obtained from an edge sign of `H` through the edge function. -/
def pullSign (ε' : EdgeSign E') : EdgeSign E := fun e => ε' (φ.edge e)

@[simp] theorem pullSign_apply (ε' : EdgeSign E') (e : E) : φ.pullSign ε' e = ε' (φ.edge e) := rfl

@[simp] theorem pullSign_one : φ.pullSign (1 : EdgeSign E') = 1 := rfl

theorem pullSign_mul (ε' ε'' : EdgeSign E') :
    φ.pullSign (ε' * ε'') = φ.pullSign ε' * φ.pullSign ε'' := rfl

/-- The sign of the image of an edge set on which the edge function is injective is the
pulled-back sign of the edge set. -/
theorem setSign_edgeSet [DecidableEq E'] (ε' : EdgeSign E') (R : Type*) [CommRing R]
    {S : Finset E} (h : Set.InjOn φ.edge S) :
    ε'.setSign R (φ.edgeSet S) = (φ.pullSign ε').setSign R S := by
  rw [EdgeSign.setSign, edgeSet_def, Finset.prod_image h]
  rfl

variable [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E']
  (R : Type) [CommRing R]

/-- The state map of an edge map intertwines the edge-sign scaling by `ε'` on `H` with the
scaling by the pulled-back sign on `G`. -/
theorem stateMap_edgeSignState (ε' : EdgeSign E') (z : G.IncResolutionBasis →₀ R) :
    φ.stateMap R (G.edgeSignState (φ.pullSign ε') R z) =
      H.edgeSignState ε' R (φ.stateMap R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single b r =>
    rw [edgeSignState_single, stateMap_single, stateMap_single]
    split_ifs with h
    · rw [edgeSignState_single, stateIndex_fst, setSign_edgeSet φ ε' R h]
      congr 1
      ring
    · rw [map_zero]

end EdgeMap

/-! ## The signed exterior map `e ↦ ε_e e_{φ e}` -/

namespace SignedEdgeMap

section Exterior

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)
  [LinearOrder E] [LinearOrder E'] (R : Type*) [CommRing R]

/-- The linear map of free modules on the edges `e ↦ ε_e e_{φ e}`. -/
noncomputable def signedEdgeLinearMap : (E →₀ R) →ₗ[R] (E' →₀ R) :=
  Finsupp.linearCombination R fun e => Finsupp.single (φ.edge e) ((φ.edgeSign e : ℤ) : R)

/-- The linear map of free modules on a basis vector: `r e ↦ ε_e r e_{φ e}`. -/
theorem signedEdgeLinearMap_single (e : E) (r : R) :
    φ.signedEdgeLinearMap R (Finsupp.single e r) =
      Finsupp.single (φ.edge e) (((φ.edgeSign e : ℤ) : R) * r) := by
  rw [signedEdgeLinearMap, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul,
    mul_comm]

/-- The map of exterior state modules induced by `e ↦ ε_e e_{φ e}` through Mathlib's exterior
algebra: the exterior map of the functoriality proposition. -/
noncomputable def signedExteriorMap : Koszul.Space E R →ₗ[R] Koszul.Space E' R :=
  (Koszul.exteriorAlgebraEquiv E' R).symm.toLinearMap ∘ₗ
    (ExteriorAlgebra.map (φ.signedEdgeLinearMap R)).toLinearMap ∘ₗ
      (Koszul.exteriorAlgebraEquiv E R).toLinearMap

/-- The signed exterior map in Mathlib's exterior algebra. -/
theorem exteriorAlgebraEquiv_signedExteriorMap (x : Koszul.Space E R) :
    Koszul.exteriorAlgebraEquiv E' R (φ.signedExteriorMap R x) =
      ExteriorAlgebra.map (φ.signedEdgeLinearMap R) (Koszul.exteriorAlgebraEquiv E R x) := by
  simp [signedExteriorMap]

/-- The signed exterior map sends left exterior multiplication by `e` to `ε_e` times left
exterior multiplication by `φ e`. -/
theorem signedExteriorMap_insert (e : E) (x : Koszul.Space E R) :
    φ.signedExteriorMap R (Koszul.insert e x) =
      ((φ.edgeSign e : ℤ) : R) • Koszul.insert (φ.edge e) (φ.signedExteriorMap R x) := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_signedExteriorMap, Koszul.exteriorAlgebraEquiv_insert, map_mul,
    ExteriorAlgebra.map_apply_ι, signedEdgeLinearMap_single, map_smul,
    Koszul.exteriorAlgebraEquiv_insert, exteriorAlgebraEquiv_signedExteriorMap, mul_one,
    ← smul_mul_assoc, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The signed exterior map sends the exterior product to the exterior product. -/
theorem signedExteriorMap_wedge (x y : Koszul.Space E R) :
    φ.signedExteriorMap R (Koszul.wedge x y) =
      Koszul.wedge (φ.signedExteriorMap R x) (φ.signedExteriorMap R y) := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_signedExteriorMap, Koszul.exteriorAlgebraEquiv_wedge, map_mul,
    Koszul.exteriorAlgebraEquiv_wedge, exteriorAlgebraEquiv_signedExteriorMap,
    exteriorAlgebraEquiv_signedExteriorMap]

/-- The signed exterior map fixes the empty state. -/
theorem signedExteriorMap_single_empty (r : R) :
    φ.signedExteriorMap R (single ∅ r) = single ∅ r := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_signedExteriorMap, Koszul.exteriorAlgebraEquiv_single_empty,
    AlgHom.commutes, Koszul.exteriorAlgebraEquiv_single_empty]

/-- **The signed exterior map on basis vectors.** The basis vector of an edge set `S` goes to
`wedgeSign S · ∏_{e ∈ S} ε_e` times the basis vector of `φ S`; in particular it goes to zero when
the edge function is not injective on `S`. This is the factor of the signed state map. -/
theorem signedExteriorMap_single (S : Finset E) (r : R) :
    φ.signedExteriorMap R (single S r) =
      single (φ.toEdgeMap.edgeSet S)
        ((φ.toEdgeMap.wedgeSign S : R) * φ.edgeSign.setSign R S * r) := by
  induction S using Finset.induction_on_min generalizing r with
  | empty =>
    rw [signedExteriorMap_single_empty, EdgeMap.edgeSet_empty, EdgeMap.wedgeSign_empty,
      EdgeSign.setSign_empty, Int.cast_one, one_mul, one_mul]
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hins : (single (insert a S) r : Koszul.Space E R) = Koszul.insert a (single S r) := by
      rw [Koszul.insert_single, ite_eq_right haS, Koszul.sign_of_forall_lt ha, one_mul]
    rw [hins, signedExteriorMap_insert, ih, Koszul.insert_single, EdgeMap.edgeSet_insert]
    by_cases hmem : φ.edge a ∈ φ.toEdgeMap.edgeSet S
    · have hinj : ¬ Set.InjOn φ.edge (insert a S : Finset E) := by
        intro h
        obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hmem
        have : b = a := h (by simp [hb]) (by simp) hab
        exact haS (this ▸ hb)
      rw [ite_eq_left hmem, smul_zero, EdgeMap.wedgeSign_of_not_injOn _ hinj, Int.cast_zero,
        zero_mul, zero_mul, single_zero]
    · have hs : φ.edgeSign.setSign R (insert a S) =
          ((φ.edgeSign a : ℤ) : R) * φ.edgeSign.setSign R S :=
        Finset.prod_insert haS
      rw [ite_eq_right hmem, EdgeMap.wedgeSign_insert_min _ ha hmem, Finsupp.smul_single,
        smul_eq_mul, hs, Int.cast_mul, Koszul.intCast_sign]
      congr 1
      ring

/-- The linear map of free modules of a composite is the composite of the linear maps. -/
theorem signedEdgeLinearMap_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''}
    (ψ : SignedEdgeMap H K) :
    (φ.trans ψ).signedEdgeLinearMap R = ψ.signedEdgeLinearMap R ∘ₗ φ.signedEdgeLinearMap R := by
  apply Finsupp.lhom_ext
  intro e r
  rw [LinearMap.comp_apply, signedEdgeLinearMap_single, signedEdgeLinearMap_single,
    signedEdgeLinearMap_single, trans_edgeSign_apply, Units.val_mul, Int.cast_mul]
  congr 1
  ring

/-- The signed exterior map of a composite is the composite of the signed exterior maps. -/
theorem signedExteriorMap_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''}
    (ψ : SignedEdgeMap H K) (x : Koszul.Space E R) :
    (φ.trans ψ).signedExteriorMap R x = ψ.signedExteriorMap R (φ.signedExteriorMap R x) := by
  apply (Koszul.exteriorAlgebraEquiv E'' R).injective
  rw [exteriorAlgebraEquiv_signedExteriorMap, exteriorAlgebraEquiv_signedExteriorMap,
    exteriorAlgebraEquiv_signedExteriorMap, signedEdgeLinearMap_trans,
    ← ExteriorAlgebra.map_comp_map]
  rfl

end Exterior

end SignedEdgeMap

/-! ## The signed state map -/

namespace SignedEdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)
  (R : Type) [CommRing R]

/-- The signed state map: the edge-sign scaling of `G` followed by the state map of the edge
map. -/
noncomputable def signedStateMap :
    (G.IncResolutionBasis →₀ R) →ₗ[R] (H.IncResolutionBasis →₀ R) :=
  φ.toEdgeMap.stateMap R ∘ₗ (G.edgeSignState φ.edgeSign R).toLinearMap

/-- The signed state map is the edge-sign scaling followed by the state map of the edge map. -/
theorem signedStateMap_apply (z : G.IncResolutionBasis →₀ R) :
    φ.signedStateMap R z = φ.toEdgeMap.stateMap R (G.edgeSignState φ.edgeSign R z) := rfl

/-- **The signed state map on a basis state.** The basis state of an edge set `S` goes to
`wedgeSign S · ∏_{e ∈ S} ε_e` times the same state of `φ S` when the edge function is injective on
`S`, and to zero otherwise. -/
theorem signedStateMap_single (b : G.IncResolutionBasis) (r : R) :
    φ.signedStateMap R (single b r) =
      if h : Set.InjOn φ.edge b.1 then
        single (φ.toEdgeMap.stateIndex b h)
          ((φ.toEdgeMap.wedgeSign b.1 : R) * φ.edgeSign.setSign R b.1 * r)
      else 0 := by
  rw [signedStateMap_apply, edgeSignState_single, EdgeMap.stateMap_single]
  split_ifs
  · rw [mul_assoc]
  · rfl

/-- The signed state map on a basis state whose edge set is mapped injectively. -/
theorem signedStateMap_single_of_injOn (b : G.IncResolutionBasis) (h : Set.InjOn φ.edge b.1)
    (r : R) :
    φ.signedStateMap R (single b r) =
      single (φ.toEdgeMap.stateIndex b h)
        ((φ.toEdgeMap.wedgeSign b.1 : R) * φ.edgeSign.setSign R b.1 * r) := by
  rw [signedStateMap_single, dite_eq_left h]

/-- The signed state map kills basis states whose edge set is not mapped injectively. -/
theorem signedStateMap_single_of_not_injOn (b : G.IncResolutionBasis)
    (h : ¬ Set.InjOn φ.edge b.1) (r : R) : φ.signedStateMap R (single b r) = 0 := by
  rw [signedStateMap_single, dite_eq_right h]

/-- Coefficientwise ring change commutes with the signed state map. -/
theorem signedStateMap_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    φ.signedStateMap R' (mapRange f (map_zero f) z) =
      mapRange f (map_zero f) (φ.signedStateMap R z) := by
  rw [signedStateMap_apply, signedStateMap_apply, edgeSignState_mapRange,
    EdgeMap.stateMap_mapRange]

/-- The signed state map preserves the state product. -/
theorem signedStateMap_incStateCup (x y : G.IncResolutionBasis →₀ R) :
    φ.signedStateMap R (G.incStateCup R x y) =
      H.incStateCup R (φ.signedStateMap R x) (φ.signedStateMap R y) := by
  rw [signedStateMap_apply, edgeSignState_incStateCup, EdgeMap.stateMap_incStateCup]
  rfl

/-- The signed state map sends the unit state to the unit state. -/
theorem signedStateMap_incStateUnit : φ.signedStateMap R (G.incStateUnit R) = H.incStateUnit R := by
  rw [signedStateMap_apply, edgeSignState_incStateUnit, EdgeMap.stateMap_incStateUnit]

/-- The signed state map of the identity signed edge map is the identity. -/
theorem signedStateMap_refl (G : Multigraph V E) (z : G.IncResolutionBasis →₀ R) :
    (refl G).signedStateMap R z = z := by
  rw [signedStateMap_apply]
  exact (EdgeMap.stateMap_refl R G _).trans (G.edgeSignState_one R z)

/-- The signed state map of a composite is the composite of the signed state maps. -/
theorem signedStateMap_trans {E'' : Type} [LinearOrder E''] [Fintype E''] {K : Multigraph V E''}
    (ψ : SignedEdgeMap H K) (z : G.IncResolutionBasis →₀ R) :
    (φ.trans ψ).signedStateMap R z = ψ.signedStateMap R (φ.signedStateMap R z) := by
  have hsign : (φ.trans ψ).edgeSign = φ.toEdgeMap.pullSign ψ.edgeSign * φ.edgeSign :=
    funext fun e => mul_comm _ _
  rw [signedStateMap_apply, signedStateMap_apply, signedStateMap_apply, hsign, edgeSignState_mul,
    trans_toEdgeMap, EdgeMap.stateMap_trans, EdgeMap.stateMap_edgeSignState]

/-- For trivial signs the signed state map is the state map of the edge map. -/
theorem ofEdgeMap_signedStateMap (ψ : EdgeMap G H) (z : G.IncResolutionBasis →₀ R) :
    (ofEdgeMap ψ).signedStateMap R z = ψ.stateMap R z := by
  rw [signedStateMap_apply]
  exact congrArg (ψ.stateMap R) (G.edgeSignState_one R z)

/-- For the identity edge map the signed state map is the edge-sign scaling. -/
theorem ofEdgeSign_signedStateMap (ε : EdgeSign E) (z : G.IncResolutionBasis →₀ R) :
    (ofEdgeSign G ε).signedStateMap R z = G.edgeSignState ε R z := by
  rw [signedStateMap_apply]
  exact EdgeMap.stateMap_refl R G _

end SignedEdgeMap

end BPFixedPoints.Multigraph
