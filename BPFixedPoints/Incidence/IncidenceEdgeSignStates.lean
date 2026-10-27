import BPFixedPoints.Incidence.IncidenceEdgeSignRings

/-!
# The edge-sign scaling of resolution states

For an edge sign `ε`, the sign of an edge set `S` is `∏_{e ∈ S} ε_e` (`EdgeSign.setSign`). It is
the factor by which the exterior basis vector `e_S` changes when every Koszul generator `e` is
replaced by `ε_e e`. The edge-sign scaling of state vectors (`edgeSignState`) multiplies the basis
state of an edge set `S` by the sign of `S`. It is a linear involution of the full state module
over every commutative ring, carries the state product `incStateCup` to itself (the sign of a
disjoint union is the product of the signs) and fixes the unit state. The trivial sign gives the
identity, products of signs give composites, and the scaling commutes with coefficientwise ring
change.

For an edge relabeling `φ : EdgeRelabel G H` and an edge sign `ε'` of `H`, the signed relabeling of
states intertwines the scaling by `ε'` on `H` with the scaling by the pulled-back sign
`e ↦ ε'_{φ e}` on `G` (`stateRelabel_edgeSignState`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

namespace EdgeSign

variable {E : Type} (ε : EdgeSign E)

/-- The sign of an edge set: the product of the edge signs of its edges. -/
def setSign (R : Type*) [CommRing R] (S : Finset E) : R := ∏ e ∈ S, ((ε e : ℤ) : R)

@[simp] theorem setSign_empty (R : Type*) [CommRing R] : ε.setSign R ∅ = 1 := by simp [setSign]

/-- The sign of an edge set squares to one. -/
@[simp] theorem setSign_mul_self (R : Type*) [CommRing R] (S : Finset E) :
    ε.setSign R S * ε.setSign R S = 1 := by
  rw [setSign, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun e _ => units_intCast_mul_self (ε e)

/-- A ring homomorphism maps edge-set signs to edge-set signs. -/
@[simp] theorem map_setSign {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (S : Finset E) : f (ε.setSign R S) = ε.setSign R' S := by
  simp [setSign, map_prod]

/-- The integer sign of an edge set maps to its sign in any commutative ring. -/
@[simp] theorem intCast_setSign {R : Type*} [CommRing R] (S : Finset E) :
    ((ε.setSign ℤ S : ℤ) : R) = ε.setSign R S := by
  simp [setSign]

/-- The sign of a disjoint union is the product of the signs. -/
theorem setSign_union [DecidableEq E] (R : Type*) [CommRing R] {S T : Finset E}
    (h : Disjoint S T) : ε.setSign R (S ∪ T) = ε.setSign R S * ε.setSign R T :=
  Finset.prod_union h

/-- Removing an edge from an edge set divides its sign by the edge sign. -/
theorem setSign_erase_mul [DecidableEq E] (R : Type*) [CommRing R] {S : Finset E} {e : E}
    (he : e ∈ S) : ε.setSign R (S.erase e) * ((ε e : ℤ) : R) = ε.setSign R S :=
  Finset.prod_erase_mul S _ he

/-- The trivial sign gives sign one to every edge set. -/
@[simp] theorem setSign_one (R : Type*) [CommRing R] (S : Finset E) :
    (1 : EdgeSign E).setSign R S = 1 := by
  simp [setSign]

/-- The sign of an edge set for a product of edge signs is the product of the signs. -/
theorem setSign_mul (ε' : EdgeSign E) (R : Type*) [CommRing R] (S : Finset E) :
    (ε * ε').setSign R S = ε.setSign R S * ε'.setSign R S := by
  simp [setSign, Finset.prod_mul_distrib]

end EdgeSign

/-! ## Pulling edge signs back along relabelings -/

namespace EdgeRelabel

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- The edge sign of `G` obtained from an edge sign of `H` through the edge bijection. -/
def pullSign (ε' : EdgeSign E') : EdgeSign E := fun e => ε' (φ.edge e)

@[simp] theorem pullSign_apply (ε' : EdgeSign E') (e : E) : φ.pullSign ε' e = ε' (φ.edge e) := rfl

/-- The sign of an image edge set is the pulled-back sign of the original edge set. -/
theorem setSign_edgeSet (ε' : EdgeSign E') (R : Type*) [CommRing R] (S : Finset E) :
    ε'.setSign R (φ.edgeSet S) = (φ.pullSign ε').setSign R S := by
  simp [EdgeSign.setSign, edgeSet_def, Finset.prod_map]

@[simp] theorem pullSign_one : φ.pullSign (1 : EdgeSign E') = 1 := rfl

theorem pullSign_mul (ε' ε'' : EdgeSign E') : φ.pullSign (ε' * ε'') = φ.pullSign ε' * φ.pullSign ε'' :=
  rfl

end EdgeRelabel

/-! ## The scaling of state vectors -/

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (ε : EdgeSign E) (R : Type) [CommRing R]

/-- The edge-sign scaling of state vectors, as a linear map. -/
noncomputable def edgeSignStateMap : (G.IncResolutionBasis →₀ R) →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => ε.setSign R b.1 • Finsupp.lsingle b

theorem edgeSignStateMap_single (b : G.IncResolutionBasis) (r : R) :
    G.edgeSignStateMap ε R (single b r) = single b (ε.setSign R b.1 * r) := by
  simp [edgeSignStateMap, Finsupp.smul_single, smul_eq_mul]

theorem edgeSignStateMap_comp_self :
    G.edgeSignStateMap ε R ∘ₗ G.edgeSignStateMap ε R = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro b r
  simp only [LinearMap.comp_apply, edgeSignStateMap_single, LinearMap.id_apply, ← mul_assoc,
    EdgeSign.setSign_mul_self, one_mul]

/-- The edge-sign scaling of state vectors: the basis state of an edge set `S` is multiplied by
the sign `∏_{e ∈ S} ε_e`. It is its own inverse. -/
noncomputable def edgeSignState :
    (G.IncResolutionBasis →₀ R) ≃ₗ[R] (G.IncResolutionBasis →₀ R) :=
  LinearEquiv.ofLinearMap (G.edgeSignStateMap ε R) (G.edgeSignStateMap ε R)
    (G.edgeSignStateMap_comp_self ε R) (G.edgeSignStateMap_comp_self ε R)

/-- The edge-sign scaling of a basis state. -/
theorem edgeSignState_single (b : G.IncResolutionBasis) (r : R) :
    G.edgeSignState ε R (single b r) = single b (ε.setSign R b.1 * r) :=
  G.edgeSignStateMap_single ε R b r

/-- Coefficients of a scaled state vector. -/
theorem edgeSignState_apply (z : G.IncResolutionBasis →₀ R) (b : G.IncResolutionBasis) :
    G.edgeSignState ε R z b = ε.setSign R b.1 * z b := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [edgeSignState_single]
    by_cases hc : c = b
    · subst hc
      simp
    · rw [single_eq_of_ne (Ne.symm hc), single_eq_of_ne (Ne.symm hc), mul_zero]

/-- The edge-sign scaling is an involution. -/
@[simp] theorem edgeSignState_edgeSignState (z : G.IncResolutionBasis →₀ R) :
    G.edgeSignState ε R (G.edgeSignState ε R z) = z :=
  LinearMap.congr_fun (G.edgeSignStateMap_comp_self ε R) z

theorem edgeSignState_symm_apply (z : G.IncResolutionBasis →₀ R) :
    (G.edgeSignState ε R).symm z = G.edgeSignState ε R z := rfl

/-- The trivial sign scales states trivially. -/
@[simp] theorem edgeSignState_one (z : G.IncResolutionBasis →₀ R) :
    G.edgeSignState (1 : EdgeSign E) R z = z := by
  ext b
  rw [edgeSignState_apply, EdgeSign.setSign_one, one_mul]

/-- The scaling by a product of signs is the composite of the scalings. -/
theorem edgeSignState_mul (ε' : EdgeSign E) (z : G.IncResolutionBasis →₀ R) :
    G.edgeSignState (ε * ε') R z = G.edgeSignState ε R (G.edgeSignState ε' R z) := by
  ext b
  rw [edgeSignState_apply, edgeSignState_apply, edgeSignState_apply, EdgeSign.setSign_mul,
    mul_assoc]

/-- Coefficientwise ring change commutes with the edge-sign scaling. -/
theorem edgeSignState_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    G.edgeSignState ε R' (mapRange f (map_zero f) z) =
      mapRange f (map_zero f) (G.edgeSignState ε R z) := by
  ext b
  rw [edgeSignState_apply, mapRange_apply, mapRange_apply, edgeSignState_apply, map_mul,
    EdgeSign.map_setSign]

/-- The edge-sign scaling of an embedded state of one edge set. -/
theorem edgeSignState_incStateEmbed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    G.edgeSignState ε R (G.incStateEmbed R S x) = ε.setSign R S • G.incStateEmbed R S x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | single κ r =>
    rw [incStateEmbed_single, edgeSignState_single, Finsupp.smul_single, smul_eq_mul]

/-- The edge-sign scaling carries the state product to itself. -/
theorem edgeSignState_incStateCup (x y : G.IncResolutionBasis →₀ R) :
    G.edgeSignState ε R (G.incStateCup R x y) =
      G.incStateCup R (G.edgeSignState ε R x) (G.edgeSignState ε R y) := by
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
        incStateCup_embed, edgeSignState_incStateEmbed, edgeSignState_incStateEmbed]
      simp only [map_smul, LinearMap.smul_apply]
      rw [incStateCup_embed]
      by_cases h : Disjoint S T
      · rw [dite_eq_left h, map_smul, edgeSignState_incStateEmbed, smul_smul,
          smul_smul, smul_smul, ε.setSign_union R h]
        congr 1
        ring
      · rw [dite_eq_right h, map_zero, smul_zero, smul_zero]

/-- The edge-sign scaling fixes the unit state. -/
theorem edgeSignState_incStateUnit : G.edgeSignState ε R (G.incStateUnit R) = G.incStateUnit R := by
  rw [incStateUnit, edgeSignState_incStateEmbed, EdgeSign.setSign_empty, one_smul]

/-! ## Compatibility with relabelings -/

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)
  (R : Type) [CommRing R]

/-- The signed relabeling of states intertwines the edge-sign scaling by `ε'` on `H` with the
scaling by the pulled-back sign on `G`. -/
theorem stateRelabel_edgeSignState (ε' : EdgeSign E') (z : G.IncResolutionBasis →₀ R) :
    φ.stateRelabel R (G.edgeSignState (φ.pullSign ε') R z) =
      H.edgeSignState ε' R (φ.stateRelabel R z) := by
  ext b
  rw [stateRelabel_apply, edgeSignState_apply, edgeSignState_apply, stateRelabel_apply]
  have hb : b.1 = φ.edgeSet (φ.stateIndex.symm b).1 := by
    rw [← stateIndex_fst, Equiv.apply_symm_apply]
  rw [hb, setSign_edgeSet]
  ring

end EdgeRelabel

end BPFixedPoints.Multigraph
