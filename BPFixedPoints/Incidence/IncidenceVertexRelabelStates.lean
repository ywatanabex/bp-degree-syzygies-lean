import BPFixedPoints.Incidence.IncidenceVertexRelabelRings
import BPFixedPoints.Incidence.CechProductPermutation
import BPFixedPoints.Incidence.StateExteriorCup
import BPFixedPoints.Incidence.ResolutionBasisCount

/-!
# Vertex relabelings act on resolution states with Koszul signs

For a vertex relabeling `φ : VertexRelabel G H` the edge sets are unchanged and the degree vector
of `S` in `H` is the degree vector in `G` transported along `φ.vertex`. A resolution state
`⟨S, κ⟩` of `G` goes to the state `⟨S, κ ∘ φ.vertex.symm⟩` of `H` (`stateIndex`), and the signed
relabeling of state vectors (`statePerm`) multiplies it by the Koszul sign
`vertexPermSign φ.vertex (twistSupport (G.deg S))` of reordering its degree-one factors, which
sit exactly at the vertices where `S` has nonzero degree (`stateSign`).

This sign is forced by the conventions of `CechProduct`: the multi-vertex cup product enumerates
the vertices by `Fintype.equivFin`, and only the signed relabeling carries the state product
`incStateCup` of `G` to that of `H` (`statePerm_incStateCup`). The unit state goes to the unit
state, homological and internal degrees are preserved, and the identity and composition laws hold.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)

/-- Relabeling of the state basis of the twist of an edge set. -/
def hBasisEquiv (S : Finset E) : HBasis (G.deg S) ≃ HBasis (H.deg S) :=
  (Equiv.piCongrLeft' (fun v => Fin (phi (G.deg S v))) φ.vertex).trans
    (Equiv.cast (congrArg HBasis (φ.deg_eq S).symm))

theorem hBasisEquiv_apply (S : Finset E) (κ : HBasis (G.deg S)) :
    φ.hBasisEquiv S κ = cast (congrArg HBasis (φ.deg_eq S).symm) (fun w => κ (φ.vertex.symm w)) :=
  rfl

/-- Relabeling of resolution state indices: the edge set is unchanged and the state is
transported along the vertex bijection. -/
def stateIndex : G.IncResolutionBasis ≃ H.IncResolutionBasis :=
  Equiv.sigmaCongrRight fun S => φ.hBasisEquiv S

theorem stateIndex_mk (S : Finset E) (κ : HBasis (G.deg S)) :
    φ.stateIndex ⟨S, κ⟩ = ⟨S, φ.hBasisEquiv S κ⟩ := rfl

@[simp] theorem stateIndex_fst (b : G.IncResolutionBasis) : (φ.stateIndex b).1 = b.1 := rfl

@[simp] theorem stateIndex_symm_fst (b : H.IncResolutionBasis) : (φ.stateIndex.symm b).1 = b.1 :=
  rfl

/-- The support of an edge set in `H` is the image of its support in `G`. -/
theorem support_eq (S : Finset E) : H.support S = (G.support S).map φ.vertex.toEmbedding := by
  ext w
  simp only [support, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [φ.deg_eq S]

include φ in
theorem card_support (S : Finset E) : (H.support S).card = (G.support S).card := by
  rw [φ.support_eq, Finset.card_map]

/-- Relabeling preserves the homological degree of resolution states. -/
theorem incResolutionDegree_stateIndex (b : G.IncResolutionBasis) :
    H.incResolutionDegree (φ.stateIndex b) = G.incResolutionDegree b := by
  simp [incResolutionDegree, card_support φ]

/-- Relabeling preserves the internal degree of resolution states. -/
theorem incResolutionInternalDegree_stateIndex (b : G.IncResolutionBasis) :
    H.incResolutionInternalDegree (φ.stateIndex b) = G.incResolutionInternalDegree b := rfl

/-- The twist support of an edge set in `H` is the image of its twist support in `G`. -/
theorem twistSupport_deg (S : Finset E) :
    twistSupport (H.deg S) = (twistSupport (G.deg S)).map φ.vertex.toEmbedding := by
  rw [φ.deg_eq S, twistSupport_comp]

include φ in
/-- Cohomological degrees of edge sets are preserved. -/
theorem cohomologyDegree_deg (S : Finset E) :
    cohomologyDegree (H.deg S) = cohomologyDegree (G.deg S) := by
  rw [φ.deg_eq S]
  exact cohomologyDegree_comp_equiv φ.vertex.symm (G.deg S)

variable (R : Type) [CommRing R]

/-- The Koszul sign of an edge set: the reordering sign of the degree-one factors of its states. -/
noncomputable def stateSign (S : Finset E) : R :=
  vertexPermSign R φ.vertex (twistSupport (G.deg S))

@[simp] theorem stateSign_mul_self (S : Finset E) : φ.stateSign R S * φ.stateSign R S = 1 :=
  vertexPermSign_mul_self R _ _

@[simp] theorem map_stateSign {R' : Type} [CommRing R'] (f : R →+* R') (S : Finset E) :
    f (φ.stateSign R S) = φ.stateSign R' S :=
  map_vertexPermSign f _ _

/-- The signed relabeling of state vectors, as a linear map. -/
noncomputable def statePermMap : (G.IncResolutionBasis →₀ R) →ₗ[R] (H.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => φ.stateSign R b.1 • Finsupp.lsingle (φ.stateIndex b)

/-- The inverse signed relabeling of state vectors. -/
noncomputable def statePermInvMap :
    (H.IncResolutionBasis →₀ R) →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => φ.stateSign R b.1 • Finsupp.lsingle (φ.stateIndex.symm b)

theorem statePermMap_single (b : G.IncResolutionBasis) (r : R) :
    φ.statePermMap R (single b r) = single (φ.stateIndex b) (φ.stateSign R b.1 * r) := by
  simp [statePermMap, Finsupp.smul_single, smul_eq_mul]

theorem statePermInvMap_single (b : H.IncResolutionBasis) (r : R) :
    φ.statePermInvMap R (single b r) = single (φ.stateIndex.symm b) (φ.stateSign R b.1 * r) := by
  simp [statePermInvMap, Finsupp.smul_single, smul_eq_mul]

/-- **The signed relabeling of state vectors** along a vertex relabeling: the basis state
`⟨S, κ⟩` goes to the Koszul sign of `S` times the basis state `⟨S, κ ∘ φ.vertex.symm⟩`. -/
noncomputable def statePerm : (G.IncResolutionBasis →₀ R) ≃ₗ[R] (H.IncResolutionBasis →₀ R) :=
  LinearEquiv.ofLinearMap (φ.statePermMap R) (φ.statePermInvMap R)
    (by
      apply Finsupp.lhom_ext
      intro b r
      simp only [LinearMap.comp_apply, statePermInvMap_single, statePermMap_single,
        Equiv.apply_symm_apply, LinearMap.id_apply, stateIndex_symm_fst, ← mul_assoc,
        stateSign_mul_self, one_mul])
    (by
      apply Finsupp.lhom_ext
      intro b r
      simp only [LinearMap.comp_apply, statePermMap_single, statePermInvMap_single,
        Equiv.symm_apply_apply, LinearMap.id_apply, stateIndex_fst, ← mul_assoc,
        stateSign_mul_self, one_mul])

/-- The signed relabeling of a basis state. -/
theorem statePerm_single (b : G.IncResolutionBasis) (r : R) :
    φ.statePerm R (single b r) = single (φ.stateIndex b) (φ.stateSign R b.1 * r) :=
  φ.statePermMap_single R b r

/-- Coefficients of a relabeled state vector at relabeled indices. -/
theorem statePerm_apply_stateIndex (z : G.IncResolutionBasis →₀ R) (b : G.IncResolutionBasis) :
    φ.statePerm R z (φ.stateIndex b) = φ.stateSign R b.1 * z b := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [statePerm_single]
    by_cases hc : c = b
    · subst hc
      simp
    · rw [single_eq_of_ne (fun h => hc (φ.stateIndex.injective h).symm),
        single_eq_of_ne (Ne.symm hc), mul_zero]

/-- Coefficients of a relabeled state vector. -/
theorem statePerm_apply (z : G.IncResolutionBasis →₀ R) (b : H.IncResolutionBasis) :
    φ.statePerm R z b = φ.stateSign R b.1 * z (φ.stateIndex.symm b) := by
  conv_lhs => rw [← φ.stateIndex.apply_symm_apply b]
  exact φ.statePerm_apply_stateIndex R z _

/-- Coefficients of the inverse relabeling. -/
theorem statePerm_symm_apply (z : H.IncResolutionBasis →₀ R) (b : G.IncResolutionBasis) :
    (φ.statePerm R).symm z b = φ.stateSign R b.1 * z (φ.stateIndex b) := by
  have h := φ.statePerm_apply_stateIndex R ((φ.statePerm R).symm z) b
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, stateSign_mul_self, one_mul]

/-- Coefficientwise ring change commutes with the signed relabeling. -/
theorem statePerm_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    φ.statePerm R' (mapRange f (map_zero f) z) = mapRange f (map_zero f) (φ.statePerm R z) := by
  ext b
  rw [statePerm_apply, mapRange_apply, mapRange_apply, statePerm_apply, map_mul, map_stateSign]

/-- Transport of twists commutes with the signed reindexing of states. -/
theorem hVertexPerm_heq {X Y : Type} [Fintype X] [Fintype Y] (ψ : X ≃ Y) {d d' : X → ℕ}
    (h : d = d') {x : CechProduct.H R d} {x' : CechProduct.H R d'} (hx : HEq x x') :
    HEq (hVertexPerm R ψ d x) (hVertexPerm R ψ d' x') := by
  subst h
  cases hx
  rfl

/-- The signed relabeling of an embedded state of one edge set. -/
theorem statePerm_incStateEmbed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    φ.statePerm R (G.incStateEmbed R S x) =
      H.incStateEmbed R S (castH R (φ.deg_eq S).symm (hVertexPerm R φ.vertex (G.deg S) x)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | single κ r =>
    rw [incStateEmbed_single, statePerm_single, hVertexPerm_single, castH_single,
      incStateEmbed_single, stateIndex_mk]
    rfl

/-- **The signed relabeling carries the state product of `G` to the state product of `H`.** -/
theorem statePerm_incStateCup (x y : G.IncResolutionBasis →₀ R) :
    φ.statePerm R (G.incStateCup R x y) =
      H.incStateCup R (φ.statePerm R x) (φ.statePerm R y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single p r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single q s =>
      obtain ⟨S, κ⟩ := p
      obtain ⟨T, κ'⟩ := q
      rw [← G.incStateEmbed_single R S κ r, ← G.incStateEmbed_single R T κ' s,
        incStateCup_embed, statePerm_incStateEmbed, statePerm_incStateEmbed, incStateCup_embed]
      by_cases h : Disjoint S T
      · rw [dite_eq_left h, dite_eq_left h, map_smul, statePerm_incStateEmbed,
          cohomologyDegree_deg φ T]
        congr 1
        apply H.incStateEmbed_heq R rfl
        refine (castH_heq R _ _).trans ?_
        refine (hVertexPerm_heq R φ.vertex (G.deg_union_eq_add h) (castH_heq R _ _)).trans ?_
        rw [hVertexPerm_cohomologyCup]
        refine HEq.trans ?_ (castH_heq R _ _).symm
        exact cohomologyCup_heq R (φ.deg_eq S).symm (φ.deg_eq T).symm (castH_heq R _ _).symm
          (castH_heq R _ _).symm
      · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- **The signed relabeling carries the unit state of `G` to the unit state of `H`.** -/
theorem statePerm_incStateUnit : φ.statePerm R (G.incStateUnit R) = H.incStateUnit R := by
  rw [incStateUnit, statePerm_incStateEmbed, incStateUnit]
  apply H.incStateEmbed_heq R rfl
  refine (castH_heq R _ _).trans ?_
  refine (hVertexPerm_heq R φ.vertex G.deg_empty_eq_zero (castH_heq R _ _)).trans ?_
  rw [hVertexPerm_cohomologyUnit]
  exact (castH_heq R _ _).symm

/-! ## Identity and composition -/

/-- The identity relabeling relabels states trivially. -/
theorem statePerm_refl (G : Multigraph V E) (z : G.IncResolutionBasis →₀ R) :
    (refl G).statePerm R z = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [statePerm_single, stateIndex_mk, stateSign, refl_vertex, vertexPermSign_refl, one_mul]
    rfl

/-- The signed relabeling of a composite is the composite of the signed relabelings. -/
theorem statePerm_trans {X : Type} [DecidableEq X] [Fintype X] {K : Multigraph X E}
    (χ : VertexRelabel H K) (z : G.IncResolutionBasis →₀ R) :
    (φ.trans χ).statePerm R z = χ.statePerm R (φ.statePerm R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [statePerm_single, statePerm_single, statePerm_single, stateIndex_mk, stateIndex_mk,
      stateIndex_mk]
    have hs : (φ.trans χ).stateSign R S = χ.stateSign R S * φ.stateSign R S := by
      rw [stateSign, stateSign, stateSign, trans_vertex, vertexPermSign_trans, φ.twistSupport_deg]
    rw [hs, mul_assoc]
    congr 1
    apply Sigma.ext
    · rfl
    rw [hBasisEquiv_apply, hBasisEquiv_apply, hBasisEquiv_apply]
    refine (cast_heq _ _).trans ?_
    refine HEq.trans ?_ (cast_heq _ _).symm
    have hfun : ∀ (d : W → ℕ) (h : d = fun w => G.deg S (φ.vertex.symm w))
        (y : HBasis d), HEq y (fun w => κ (φ.vertex.symm w)) →
        HEq (fun x => κ ((φ.vertex.trans χ.vertex).symm x)) (fun x => y (χ.vertex.symm x)) := by
      intro d h y hy
      subst h
      cases hy
      rfl
    exact hfun (H.deg S) (φ.deg_eq S) _ (cast_heq _ _)

end VertexRelabel

end BPFixedPoints.Multigraph
