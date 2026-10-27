import BPFixedPoints.Incidence.IncidenceRelabelStates
import BPFixedPoints.Incidence.ExteriorAlgebraBridge

/-!
# Edge maps of multigraphs and the exterior map of states

An `EdgeMap G H` is a map of multigraphs on the same vertex set that may identify edges: an
arbitrary function of edge types carrying the endpoint pair of every edge to the endpoint pair of
its image, in the same order or reversed (`reversed e`). Edge relabelings are the bijective edge
maps (`EdgeRelabel.toEdgeMap`). The image `φ S` of an edge set on which the edge function is
injective has the same vertex degrees, support and cardinality as `S`.

## The exterior map

The edge function induces the linear map `e ↦ e_{φ e}` of free modules and hence, through
Mathlib's exterior algebra and the identification `Koszul.exteriorAlgebraEquiv` of the project's
exterior state module with it, a linear map `exteriorMap` of exterior state modules. It sends the
left exterior multiplication by `e` to that by `φ e` (`exteriorMap_insert`), the exterior product to
the exterior product (`exteriorMap_wedge`) and composes functorially (`exteriorMap_trans`). The
basis vector of an edge set `S` goes to `wedgeSign S` times the basis vector of `φ S`
(`exteriorMap_single`), where `wedgeSign S` is `(-1)` to the number of pairs of `S` whose order is
reversed by the edge function when that function is injective on `S`, and `0` otherwise
(`e ∧ e = 0`). The contraction by an edge `e'` of the target corresponds to the sum of the
contractions by the edges above `e'` (`erase_exteriorMap`); this is the identity that makes the
total Koszul–Čech map a chain map.

## The state map

On full state modules, `stateMap` sends the basis state of an edge set `S` to `wedgeSign S` times
the same state of the image edge set when the edge function is injective on `S`, and to zero
otherwise. It carries the state product of `G` to that of `H`, the unit state to the unit state,
is the identity for the identity edge map, composes functorially, and is the signed relabeling of
states for an edge relabeling.

Vertex maps are not considered: both graphs have the same vertex type and the vertices are fixed.
Orientation signs of edges are not part of this model: the coefficients are indexed by ordered
endpoint pairs, so reversal is absorbed by the coefficient map exchanging endpoint indices.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Koszul

variable {E A : Type*} [LinearOrder E] [CommRing A]

/-- Contraction after left exterior multiplication, as a formula. -/
theorem erase_insert_apply (e f : E) (z : Space E A) :
    erase e (insert f z) = (if e = f then z else 0) - insert f (erase e z) := by
  have h := LinearMap.congr_fun (erase_insert_add_insert_erase (A := A) e f) z
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  rw [eq_sub_iff_add_eq, h]
  split_ifs <;> simp

/-- The removal sign of an edge smaller than every edge of the set is one. -/
theorem sign_of_forall_lt {S : Finset E} {a : E} (ha : ∀ x ∈ S, a < x) :
    sign (A := A) S a = 1 := by
  have h : index S a = 0 := by
    unfold index
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxa
    exact lt_asymm (ha x hx) hxa
  rw [sign, h, pow_zero]

/-- The integer shuffle sign maps to the shuffle sign of any commutative ring. -/
@[simp] theorem intCast_shuffleSign (S T : Finset E) :
    ((shuffleSign (R := ℤ) S T : ℤ) : A) = shuffleSign (R := A) S T := by
  simp [shuffleSign]

/-- The integer removal sign maps to the removal sign of any commutative ring. -/
@[simp] theorem intCast_sign (S : Finset E) (e : E) :
    ((sign (A := ℤ) S e : ℤ) : A) = sign (A := A) S e := by
  simp [sign]

end BPFixedPoints.Koszul

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

/-- A map of multigraphs on the same vertex set: an arbitrary function of edges taking the
endpoint pair of each edge to the endpoint pair of its image, possibly in reversed order.
Different edges may have the same image. -/
structure EdgeMap {V E E' : Type} (G : Multigraph V E) (H : Multigraph V E') where
  /-- The function of edges. -/
  edge : E → E'
  /-- Whether the endpoint order of an edge is reversed by the map. -/
  reversed : E → Bool
  /-- The first endpoint of the image edge. -/
  fst_edge : ∀ e, H.fst (edge e) = if reversed e then G.snd e else G.fst e
  /-- The second endpoint of the image edge. -/
  snd_edge : ∀ e, H.snd (edge e) = if reversed e then G.fst e else G.snd e

/-- An edge relabeling as an edge map. -/
def EdgeRelabel.toEdgeMap {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    (φ : EdgeRelabel G H) : EdgeMap G H where
  edge := φ.edge
  reversed := φ.reversed
  fst_edge := φ.fst_edge
  snd_edge := φ.snd_edge

@[simp] theorem EdgeRelabel.toEdgeMap_edge {V E E' : Type} {G : Multigraph V E}
    {H : Multigraph V E'} (φ : EdgeRelabel G H) (e : E) : φ.toEdgeMap.edge e = φ.edge e := rfl

namespace EdgeMap

/-- The identity edge map of a multigraph. -/
def refl {V E : Type} (G : Multigraph V E) : EdgeMap G G where
  edge := id
  reversed _ := false
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The composite of two edge maps; an edge is reversed when exactly one of the two maps reverses
it. -/
def trans {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'} {K : Multigraph V E''}
    (φ : EdgeMap G H) (ψ : EdgeMap H K) : EdgeMap G K where
  edge := ψ.edge ∘ φ.edge
  reversed e := xor (φ.reversed e) (ψ.reversed (φ.edge e))
  fst_edge e := by
    simp only [Function.comp_apply]
    rw [ψ.fst_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl
  snd_edge e := by
    simp only [Function.comp_apply]
    rw [ψ.snd_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl

@[simp] theorem refl_edge {V E : Type} (G : Multigraph V E) (e : E) : (refl G).edge e = e := rfl

@[simp] theorem trans_edge {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : EdgeMap G H) (ψ : EdgeMap H K) (e : E) :
    (φ.trans ψ).edge e = ψ.edge (φ.edge e) := rfl

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- Edge maps preserve the endpoint count of an edge at every vertex. -/
@[simp] theorem endCount_edge [DecidableEq V] (e : E) (v : V) :
    H.endCount (φ.edge e) v = G.endCount e v := by
  unfold endCount
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · simp
  · simp only [ite_true]
    omega

/-! ## Image edge sets -/

variable [DecidableEq E']

/-- The image of an edge set. -/
def edgeSet (S : Finset E) : Finset E' := S.image φ.edge

theorem edgeSet_def (S : Finset E) : φ.edgeSet S = S.image φ.edge := rfl

@[simp] theorem edgeSet_empty : φ.edgeSet ∅ = ∅ := Finset.image_empty _

theorem edgeSet_eq_empty_iff {S : Finset E} : φ.edgeSet S = ∅ ↔ S = ∅ :=
  Finset.image_eq_empty

theorem edgeSet_insert [DecidableEq E] (S : Finset E) (a : E) :
    φ.edgeSet (insert a S) = insert (φ.edge a) (φ.edgeSet S) :=
  Finset.image_insert _ _ _

theorem edgeSet_union [DecidableEq E] (S T : Finset E) :
    φ.edgeSet (S ∪ T) = φ.edgeSet S ∪ φ.edgeSet T :=
  Finset.image_union _ _

theorem mem_edgeSet_of_mem {S : Finset E} {e : E} (he : e ∈ S) : φ.edge e ∈ φ.edgeSet S :=
  Finset.mem_image_of_mem _ he

/-- On an edge set where the edge function is injective, the image has the same cardinality. -/
theorem card_edgeSet {S : Finset E} (h : Set.InjOn φ.edge S) : (φ.edgeSet S).card = S.card :=
  Finset.card_image_of_injOn h

/-- The image of an edge set where the edge function is injective has the same vertex degrees. -/
theorem deg_edgeSet [DecidableEq V] {S : Finset E} (h : Set.InjOn φ.edge S) :
    H.deg (φ.edgeSet S) = G.deg S := by
  funext v
  unfold deg
  rw [edgeSet_def, Finset.sum_image h]
  simp

/-- The image of an edge set where the edge function is injective has the same support. -/
theorem support_edgeSet [DecidableEq V] [Fintype V] {S : Finset E} (h : Set.InjOn φ.edge S) :
    H.support (φ.edgeSet S) = G.support S := by
  simp [support, φ.deg_edgeSet h]

/-- Images of disjoint edge sets on whose union the edge function is injective are disjoint. -/
theorem disjoint_edgeSet [DecidableEq E] {S T : Finset E} (hST : Disjoint S T)
    (h : Set.InjOn φ.edge ↑(S ∪ T)) : Disjoint (φ.edgeSet S) (φ.edgeSet T) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxS
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hxT
  have : b = a := h (by simp [hb]) (by simp [ha]) hab
  subst this
  exact Finset.disjoint_left.mp hST ha hb

theorem edgeSet_refl {V E : Type} [DecidableEq E] (G : Multigraph V E) (S : Finset E) :
    (refl G).edgeSet S = S := by
  simp [edgeSet_def, refl]

theorem edgeSet_trans {E'' : Type} [DecidableEq E''] {K : Multigraph V E''} (ψ : EdgeMap H K)
    (S : Finset E) : (φ.trans ψ).edgeSet S = ψ.edgeSet (φ.edgeSet S) := by
  simp [edgeSet_def, trans, Finset.image_image]

/-- A composite edge map is injective on an edge set exactly when the first map is injective on
it and the second map is injective on its image. -/
theorem injOn_trans_iff {E'' : Type} {K : Multigraph V E''} (ψ : EdgeMap H K) (S : Finset E) :
    Set.InjOn (φ.trans ψ).edge S ↔
      Set.InjOn φ.edge S ∧ Set.InjOn ψ.edge (φ.edgeSet S : Set E') := by
  change Set.InjOn (ψ.edge ∘ φ.edge) S ↔ _
  rw [edgeSet_def, Finset.coe_image]
  exact ⟨fun h => ⟨h.of_comp, h.image_of_comp⟩, fun h => h.1.comp_iff.mpr h.2⟩

end EdgeMap

/-- For an edge relabeling, the image edge set of the underlying edge map is the relabeled edge
set. -/
theorem EdgeRelabel.toEdgeMap_edgeSet {V E E' : Type} [DecidableEq E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : EdgeRelabel G H) (S : Finset E) :
    φ.toEdgeMap.edgeSet S = φ.edgeSet S := by
  rw [EdgeMap.edgeSet_def, EdgeRelabel.edgeSet_def, Finset.map_eq_image]
  rfl

/-! ## The exterior map and the wedge sign -/

namespace EdgeMap

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)
variable [LinearOrder E] [LinearOrder E']

/-- The map of exterior state modules induced by the edge function `e ↦ e_{φ e}` through
Mathlib's exterior algebra. -/
noncomputable def exteriorMap (R : Type*) [CommRing R] :
    Koszul.Space E R →ₗ[R] Koszul.Space E' R :=
  (Koszul.exteriorAlgebraEquiv E' R).symm.toLinearMap ∘ₗ
    (ExteriorAlgebra.map (Finsupp.lmapDomain R R φ.edge)).toLinearMap ∘ₗ
      (Koszul.exteriorAlgebraEquiv E R).toLinearMap

variable (R : Type*) [CommRing R]

/-- The exterior map in Mathlib's exterior algebra. -/
theorem exteriorAlgebraEquiv_exteriorMap (x : Koszul.Space E R) :
    Koszul.exteriorAlgebraEquiv E' R (φ.exteriorMap R x) =
      ExteriorAlgebra.map (Finsupp.lmapDomain R R φ.edge) (Koszul.exteriorAlgebraEquiv E R x) := by
  simp [exteriorMap]

/-- The exterior map sends left exterior multiplication by an edge to left exterior
multiplication by its image. -/
theorem exteriorMap_insert (e : E) (x : Koszul.Space E R) :
    φ.exteriorMap R (Koszul.insert e x) = Koszul.insert (φ.edge e) (φ.exteriorMap R x) := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_exteriorMap, Koszul.exteriorAlgebraEquiv_insert, map_mul,
    ExteriorAlgebra.map_apply_ι, Koszul.exteriorAlgebraEquiv_insert,
    exteriorAlgebraEquiv_exteriorMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The exterior map sends the exterior product to the exterior product. -/
theorem exteriorMap_wedge (x y : Koszul.Space E R) :
    φ.exteriorMap R (Koszul.wedge x y) = Koszul.wedge (φ.exteriorMap R x) (φ.exteriorMap R y) := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_exteriorMap, Koszul.exteriorAlgebraEquiv_wedge, map_mul,
    Koszul.exteriorAlgebraEquiv_wedge, exteriorAlgebraEquiv_exteriorMap,
    exteriorAlgebraEquiv_exteriorMap]

/-- The exterior map fixes the empty state. -/
theorem exteriorMap_single_empty (r : R) :
    φ.exteriorMap R (single ∅ r) = single ∅ r := by
  apply (Koszul.exteriorAlgebraEquiv E' R).injective
  rw [exteriorAlgebraEquiv_exteriorMap, Koszul.exteriorAlgebraEquiv_single_empty, AlgHom.commutes,
    Koszul.exteriorAlgebraEquiv_single_empty]

/-- The number of pairs of an edge set whose order is reversed by the edge function. -/
def inversions (S : Finset E) : ℕ :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b ∧ φ.edge b < φ.edge a then 1 else 0

open Classical in
/-- The wedge sign of an edge set: `(-1)` to the number of inversions when the edge function is
injective on the set, and zero otherwise. The exterior map sends the basis vector of `S` to the
wedge sign times the basis vector of the image edge set. -/
noncomputable def wedgeSign (S : Finset E) : ℤ :=
  if Set.InjOn φ.edge S then (-1) ^ φ.inversions S else 0

/-- The wedge sign of an edge set on which the edge function is injective. -/
theorem wedgeSign_of_injOn {S : Finset E} (h : Set.InjOn φ.edge S) :
    φ.wedgeSign S = (-1) ^ φ.inversions S := by
  rw [wedgeSign, ite_eq_left h]

/-- The wedge sign of an edge set on which the edge function is not injective is zero. -/
theorem wedgeSign_of_not_injOn {S : Finset E} (h : ¬ Set.InjOn φ.edge S) :
    φ.wedgeSign S = 0 := by
  rw [wedgeSign, ite_eq_right h]

@[simp] theorem wedgeSign_empty : φ.wedgeSign ∅ = 1 := by
  rw [wedgeSign_of_injOn φ (by simp)]
  simp [inversions]

/-- The wedge sign squares to one on edge sets where the edge function is injective. -/
theorem wedgeSign_mul_self {S : Finset E} (h : Set.InjOn φ.edge S) :
    φ.wedgeSign S * φ.wedgeSign S = 1 := by
  rw [wedgeSign_of_injOn φ h]
  exact Koszul.neg_one_pow_mul_self _

/-- Inversions of an edge set with a new smallest edge. -/
theorem inversions_insert_min {S : Finset E} {a : E} (ha : ∀ x ∈ S, a < x) :
    φ.inversions (insert a S) =
      (S.filter fun b => φ.edge b < φ.edge a).card + φ.inversions S := by
  have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
  unfold inversions
  rw [Finset.sum_insert haS, Finset.sum_insert haS]
  simp only [lt_irrefl, false_and, ite_false, zero_add]
  rw [Finset.card_filter]
  have h1 : ∀ x ∈ S, (∑ b ∈ insert a S, if x < b ∧ φ.edge b < φ.edge x then 1 else 0) =
      ∑ b ∈ S, if x < b ∧ φ.edge b < φ.edge x then 1 else 0 := by
    intro x hx
    rw [Finset.sum_insert haS, ite_eq_right (fun h => lt_asymm (ha x hx) h.1), zero_add]
  rw [Finset.sum_congr rfl h1]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  simp [ha b hb]

/-- Recursion of the wedge sign for a new smallest edge whose image is new. -/
theorem wedgeSign_insert_min {S : Finset E} {a : E} (ha : ∀ x ∈ S, a < x)
    (hmem : φ.edge a ∉ φ.edgeSet S) :
    φ.wedgeSign (insert a S) = Koszul.sign (A := ℤ) (φ.edgeSet S) (φ.edge a) * φ.wedgeSign S := by
  have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
  by_cases hinj : Set.InjOn φ.edge S
  · have hinj' : Set.InjOn φ.edge (insert a S : Finset E) := by
      rw [Finset.coe_insert, Set.injOn_insert (by simpa using haS)]
      refine ⟨hinj, fun h => hmem ?_⟩
      rw [← Finset.mem_coe, edgeSet_def, Finset.coe_image]
      exact h
    rw [wedgeSign_of_injOn φ hinj', wedgeSign_of_injOn φ hinj, Koszul.sign, ← pow_add,
      inversions_insert_min φ ha]
    congr 2
    unfold Koszul.index
    rw [edgeSet_def, Finset.filter_image,
      Finset.card_image_of_injOn (hinj.mono (fun x hx => (Finset.mem_filter.mp hx).1))]
  · have hinj' : ¬ Set.InjOn φ.edge (insert a S : Finset E) := fun h =>
      hinj (h.mono (by simp))
    rw [wedgeSign_of_not_injOn φ hinj', wedgeSign_of_not_injOn φ hinj, mul_zero]

/-- **The exterior map on basis states.** The basis vector of an edge set goes to the wedge sign
times the basis vector of the image edge set; in particular it goes to zero when the edge function
is not injective on the set. -/
theorem exteriorMap_single (S : Finset E) (r : R) :
    φ.exteriorMap R (single S r) = single (φ.edgeSet S) ((φ.wedgeSign S : R) * r) := by
  induction S using Finset.induction_on_min generalizing r with
  | empty => rw [exteriorMap_single_empty, edgeSet_empty, wedgeSign_empty, Int.cast_one, one_mul]
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hins : (single (insert a S) r : Koszul.Space E R) = Koszul.insert a (single S r) := by
      rw [Koszul.insert_single, ite_eq_right haS, Koszul.sign_of_forall_lt ha, one_mul]
    rw [hins, exteriorMap_insert, ih, Koszul.insert_single, edgeSet_insert]
    by_cases hmem : φ.edge a ∈ φ.edgeSet S
    · have hinj : ¬ Set.InjOn φ.edge (insert a S : Finset E) := by
        intro h
        obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hmem
        have : b = a := h (by simp [hb]) (by simp) hab
        exact haS (this ▸ hb)
      rw [ite_eq_left hmem, wedgeSign_of_not_injOn φ hinj, Int.cast_zero, zero_mul, single_zero]
    · rw [ite_eq_right hmem, wedgeSign_insert_min φ ha hmem, Int.cast_mul, Koszul.intCast_sign,
        mul_assoc]

/-- The contraction by an edge of the target after the exterior map is the exterior map after the
sum of the contractions by the edges above it. -/
theorem erase_exteriorMap [Fintype E] (e' : E') (x : Koszul.Space E R) :
    Koszul.erase e' (φ.exteriorMap R x) =
      φ.exteriorMap R (∑ e ∈ Finset.univ.filter (fun e => φ.edge e = e'), Koszul.erase e x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
  | single S r =>
    induction S using Finset.induction_on_min generalizing r with
    | empty =>
      rw [exteriorMap_single_empty, Koszul.erase_single, ite_eq_right (Finset.notMem_empty _)]
      rw [Finset.sum_eq_zero (fun e _ => by
        rw [Koszul.erase_single, ite_eq_right (Finset.notMem_empty _)]), map_zero]
    | insert a S ha ih =>
      have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
      have hins : (single (insert a S) r : Koszul.Space E R) = Koszul.insert a (single S r) := by
        rw [Koszul.insert_single, ite_eq_right haS, Koszul.sign_of_forall_lt ha, one_mul]
      rw [hins, exteriorMap_insert, Koszul.erase_insert_apply, ih]
      simp only [Koszul.erase_insert_apply]
      rw [Finset.sum_sub_distrib, ← map_sum, map_sub, exteriorMap_insert]
      congr 1
      rw [Finset.sum_ite_eq' (Finset.univ.filter (fun e => φ.edge e = e')) a (fun _ => single S r)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · exact (map_zero _).symm

/-- **The contraction identity in coefficients.** Summing over the edges of `S` above `e'` the
signed images of the contracted edge sets gives the contraction by `e'` of the image of `S`. -/
theorem sum_fiber_wedgeSign [Fintype E] (S : Finset E) (e' : E') :
    ∑ e ∈ S.filter (fun e => φ.edge e = e'),
        (single (φ.edgeSet (S.erase e)) (φ.wedgeSign (S.erase e) * Koszul.sign (A := ℤ) S e) :
          Koszul.Space E' ℤ) =
      if e' ∈ φ.edgeSet S then
        single ((φ.edgeSet S).erase e') (Koszul.sign (A := ℤ) (φ.edgeSet S) e' * φ.wedgeSign S)
      else 0 := by
  have h := φ.erase_exteriorMap ℤ e' (single S 1)
  rw [exteriorMap_single, mul_one, Int.cast_id, Koszul.erase_single, map_sum] at h
  rw [h]
  symm
  rw [← Finset.sum_subset (s₁ := S.filter (fun e => φ.edge e = e'))
    (fun e he => by simp [(Finset.mem_filter.mp he).2])
    (fun e _ he => by
      have heS : e ∉ S := fun h' => he (by simp_all)
      rw [Koszul.erase_single, ite_eq_right heS, map_zero])]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Koszul.erase_single, ite_eq_left (Finset.mem_filter.mp he).1, exteriorMap_single, mul_one,
    Int.cast_id]

/-- The wedge signs of disjoint edge sets on whose union the edge function is injective transform
the shuffle signs. -/
theorem wedgeSign_union_mul_shuffleSign {S T : Finset E} (hST : Disjoint S T)
    (h : Set.InjOn φ.edge ↑(S ∪ T)) :
    φ.wedgeSign (S ∪ T) * Koszul.shuffleSign (R := ℤ) S T =
      Koszul.shuffleSign (R := ℤ) (φ.edgeSet S) (φ.edgeSet T) *
        (φ.wedgeSign S * φ.wedgeSign T) := by
  have hw := φ.exteriorMap_wedge ℤ (single S 1) (single T 1)
  rw [Koszul.wedge_single, Koszul.wedgeSingle_apply, ite_eq_left hST, exteriorMap_single,
    exteriorMap_single, exteriorMap_single, Koszul.wedge_single, Koszul.wedgeSingle_apply,
    ite_eq_left (φ.disjoint_edgeSet hST h), edgeSet_union] at hw
  have := congrArg (fun z : Koszul.Space E' ℤ => z (φ.edgeSet S ∪ φ.edgeSet T)) hw
  simp only [single_eq_same, smul_eq_mul, Int.cast_id, mul_one] at this
  rw [this]

/-! ## Identity, composition and relabelings -/

/-- The exterior map of a composite edge map is the composite of the exterior maps. -/
theorem exteriorMap_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''}
    (ψ : EdgeMap H K) (x : Koszul.Space E R) :
    (φ.trans ψ).exteriorMap R x = ψ.exteriorMap R (φ.exteriorMap R x) := by
  apply (Koszul.exteriorAlgebraEquiv E'' R).injective
  rw [exteriorAlgebraEquiv_exteriorMap, exteriorAlgebraEquiv_exteriorMap,
    exteriorAlgebraEquiv_exteriorMap]
  change ExteriorAlgebra.map (Finsupp.lmapDomain R R (ψ.edge ∘ φ.edge)) _ = _
  rw [Finsupp.lmapDomain_comp, ← ExteriorAlgebra.map_comp_map]
  rfl

/-- The wedge sign of a composite edge map is the product of the wedge signs. -/
theorem wedgeSign_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''} (ψ : EdgeMap H K)
    (S : Finset E) :
    (φ.trans ψ).wedgeSign S = ψ.wedgeSign (φ.edgeSet S) * φ.wedgeSign S := by
  have h := φ.exteriorMap_trans ℤ ψ (single S 1)
  rw [exteriorMap_single, exteriorMap_single, exteriorMap_single, edgeSet_trans] at h
  have := congrArg (fun z : Koszul.Space E'' ℤ => z (ψ.edgeSet (φ.edgeSet S))) h
  simp only [single_eq_same, Int.cast_id, mul_one] at this
  exact this

/-- The identity edge map has wedge sign one. -/
@[simp] theorem wedgeSign_refl {V : Type} (G : Multigraph V E) (S : Finset E) :
    (refl G).wedgeSign S = 1 := by
  rw [wedgeSign_of_injOn _ (Set.injOn_id _)]
  have h0 : (refl G).inversions S = 0 := by
    unfold inversions
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff]
    rintro ⟨h, h'⟩
    exact absurd h' (lt_asymm h)
  rw [h0, pow_zero]

end EdgeMap

/-- For an edge relabeling the wedge sign is the relabeling sign. -/
theorem EdgeRelabel.toEdgeMap_wedgeSign {V E E' : Type} [LinearOrder E] [LinearOrder E']
    {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H) (S : Finset E) :
    φ.toEdgeMap.wedgeSign S = φ.sign ℤ S := by
  rw [EdgeMap.wedgeSign_of_injOn _ (φ.edge.injective.injOn)]
  rfl

/-! ## The state map -/

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- The image state index of a state whose edge set is mapped injectively. -/
def stateIndex (b : G.IncResolutionBasis) (h : Set.InjOn φ.edge b.1) : H.IncResolutionBasis :=
  ⟨φ.edgeSet b.1, cast (congrArg HBasis (φ.deg_edgeSet h).symm) b.2⟩

@[simp] theorem stateIndex_fst (b : G.IncResolutionBasis) (h : Set.InjOn φ.edge b.1) :
    (φ.stateIndex b h).1 = φ.edgeSet b.1 := rfl

/-- The image state index preserves the homological degree. -/
theorem incResolutionDegree_stateIndex (b : G.IncResolutionBasis) (h : Set.InjOn φ.edge b.1) :
    H.incResolutionDegree (φ.stateIndex b h) = G.incResolutionDegree b := by
  simp [incResolutionDegree, φ.support_edgeSet h, φ.card_edgeSet h]

/-- The image state index preserves the internal degree. -/
theorem incResolutionInternalDegree_stateIndex (b : G.IncResolutionBasis)
    (h : Set.InjOn φ.edge b.1) :
    H.incResolutionInternalDegree (φ.stateIndex b h) = G.incResolutionInternalDegree b := by
  simp [incResolutionInternalDegree, φ.card_edgeSet h]

variable (R : Type) [CommRing R]

open Classical in
/-- The state map of an edge map: the basis state of an edge set goes to the wedge sign times the
same state of the image edge set when the edge function is injective on the edge set, and to zero
otherwise. -/
noncomputable def stateMap :
    (G.IncResolutionBasis →₀ R) →ₗ[R] (H.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b =>
    if h : Set.InjOn φ.edge b.1 then
      (φ.wedgeSign b.1 : R) • Finsupp.lsingle (φ.stateIndex b h)
    else 0

/-- The state map on a basis state. -/
theorem stateMap_single (b : G.IncResolutionBasis) (r : R) :
    φ.stateMap R (single b r) =
      if h : Set.InjOn φ.edge b.1 then single (φ.stateIndex b h) ((φ.wedgeSign b.1 : R) * r)
      else 0 := by
  simp only [stateMap, Finsupp.lsum_single]
  split_ifs <;> simp [Finsupp.smul_single, smul_eq_mul]

/-- The state map on a basis state whose edge set is mapped injectively. -/
theorem stateMap_single_of_injOn (b : G.IncResolutionBasis) (h : Set.InjOn φ.edge b.1) (r : R) :
    φ.stateMap R (single b r) = single (φ.stateIndex b h) ((φ.wedgeSign b.1 : R) * r) := by
  rw [stateMap_single, dite_eq_left h]

/-- The state map kills basis states whose edge set is not mapped injectively. -/
theorem stateMap_single_of_not_injOn (b : G.IncResolutionBasis) (h : ¬ Set.InjOn φ.edge b.1)
    (r : R) : φ.stateMap R (single b r) = 0 := by
  rw [stateMap_single, dite_eq_right h]

/-- Coefficientwise ring change commutes with the state map. -/
theorem stateMap_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    φ.stateMap R' (mapRange f (map_zero f) z) = mapRange f (map_zero f) (φ.stateMap R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapRange_add (map_add f), map_add, hx, hy, map_add,
      mapRange_add (map_add f)]
  | single b r =>
    rw [mapRange_single, stateMap_single, stateMap_single]
    split_ifs
    · rw [mapRange_single, map_mul, map_intCast]
    · rw [mapRange_zero]

/-- The state map on an embedded state of one edge set. -/
theorem stateMap_incStateEmbed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    φ.stateMap R (G.incStateEmbed R S x) =
      if h : Set.InjOn φ.edge S then
        (φ.wedgeSign S : R) • H.incStateEmbed R (φ.edgeSet S) (castH R (φ.deg_edgeSet h).symm x)
      else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => split_ifs <;> simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    split_ifs <;> simp [smul_add]
  | single κ r =>
    rw [incStateEmbed_single, stateMap_single]
    split_ifs with h
    · rw [castH_single, incStateEmbed_single, Finsupp.smul_single, smul_eq_mul]
      rfl
    · rfl

/-- **The state map preserves the state product.** -/
theorem stateMap_incStateCup (x y : G.IncResolutionBasis →₀ R) :
    φ.stateMap R (G.incStateCup R x y) =
      H.incStateCup R (φ.stateMap R x) (φ.stateMap R y) := by
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
        incStateCup_embed, stateMap_incStateEmbed, stateMap_incStateEmbed]
      by_cases hST : Disjoint S T
      · rw [dite_eq_left hST, map_smul, stateMap_incStateEmbed]
        by_cases hU : Set.InjOn φ.edge ↑(S ∪ T)
        · have hS : Set.InjOn φ.edge S := hU.mono (by simp)
          have hT : Set.InjOn φ.edge T := hU.mono (by simp)
          have hST' := φ.disjoint_edgeSet hST hU
          rw [dite_eq_left hU, dite_eq_left hS, dite_eq_left hT]
          simp only [map_smul, LinearMap.smul_apply]
          rw [incStateCup_embed, dite_eq_left hST', smul_smul, smul_smul, smul_smul]
          have hcd : cohomologyDegree (H.deg (φ.edgeSet T)) = cohomologyDegree (G.deg T) := by
            rw [φ.deg_edgeSet hT]
          congr 1
          · rw [φ.card_edgeSet hS, hcd]
            have hsign := congrArg (fun z : ℤ => (z : R)) (φ.wedgeSign_union_mul_shuffleSign hST hU)
            simp only [Int.cast_mul, Koszul.intCast_shuffleSign] at hsign
            calc Koszul.shuffleSign (R := R) S T *
                  (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) * (φ.wedgeSign (S ∪ T) : R)
                = ((φ.wedgeSign (S ∪ T) : R) * Koszul.shuffleSign (R := R) S T) *
                    (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) := by ring
              _ = Koszul.shuffleSign (R := R) (φ.edgeSet S) (φ.edgeSet T) *
                    ((φ.wedgeSign S : R) * (φ.wedgeSign T : R)) *
                    (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) := by rw [hsign]
              _ = _ := by ring
          · apply H.incStateEmbed_heq R (φ.edgeSet_union S T)
            refine (castH_heq R _ _).trans ((castH_heq R _ _).trans ?_)
            refine HEq.symm ((castH_heq R _ _).trans ?_)
            exact cohomologyCup_heq R (φ.deg_edgeSet hS) (φ.deg_edgeSet hT) (castH_heq R _ _)
              (castH_heq R _ _)
        · rw [dite_eq_right hU, smul_zero]
          by_cases hS : Set.InjOn φ.edge S
          · by_cases hT : Set.InjOn φ.edge T
            · rw [dite_eq_left hS, dite_eq_left hT]
              simp only [map_smul, LinearMap.smul_apply]
              have hnd : ¬ Disjoint (φ.edgeSet S) (φ.edgeSet T) := by
                intro hd
                apply hU
                rw [Finset.coe_union, Set.injOn_union (Finset.disjoint_coe.mpr hST)]
                refine ⟨hS, hT, fun a ha b hb hab => ?_⟩
                exact Finset.disjoint_left.mp hd (φ.mem_edgeSet_of_mem ha)
                  (hab ▸ φ.mem_edgeSet_of_mem hb)
              rw [incStateCup_embed, dite_eq_right hnd, smul_zero, smul_zero]
            · rw [dite_eq_right hT, map_zero]
          · rw [dite_eq_right hS, map_zero, LinearMap.zero_apply]
      · rw [dite_eq_right hST, map_zero]
        by_cases hS : Set.InjOn φ.edge S
        · by_cases hT : Set.InjOn φ.edge T
          · rw [dite_eq_left hS, dite_eq_left hT]
            simp only [map_smul, LinearMap.smul_apply]
            have hnd : ¬ Disjoint (φ.edgeSet S) (φ.edgeSet T) := by
              intro hd
              obtain ⟨a, haS, haT⟩ := Finset.not_disjoint_iff.mp hST
              exact Finset.disjoint_left.mp hd (φ.mem_edgeSet_of_mem haS)
                (φ.mem_edgeSet_of_mem haT)
            rw [incStateCup_embed, dite_eq_right hnd, smul_zero, smul_zero]
          · rw [dite_eq_right hT, map_zero]
        · rw [dite_eq_right hS, map_zero, LinearMap.zero_apply]

/-- The state map sends the unit state to the unit state. -/
theorem stateMap_incStateUnit : φ.stateMap R (G.incStateUnit R) = H.incStateUnit R := by
  have h0 : Set.InjOn φ.edge (∅ : Finset E) := by simp
  rw [incStateUnit, stateMap_incStateEmbed, dite_eq_left h0, wedgeSign_empty, Int.cast_one, one_smul,
    incStateUnit]
  apply H.incStateEmbed_heq R φ.edgeSet_empty
  exact (castH_heq R _ _).trans ((castH_heq R _ _).trans (castH_heq R _ _).symm)

/-- The state map of the identity edge map is the identity. -/
theorem stateMap_refl (G : Multigraph V E) (z : G.IncResolutionBasis →₀ R) :
    (refl G).stateMap R z = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [stateMap_single_of_injOn _ R _ (Set.injOn_id _), wedgeSign_refl, Int.cast_one, one_mul]
    congr 1
    apply Sigma.ext (edgeSet_refl G S)
    exact cast_heq _ κ

/-- The state map of a composite edge map is the composite of the state maps. -/
theorem stateMap_trans {E'' : Type} [LinearOrder E''] [Fintype E''] {K : Multigraph V E''}
    (ψ : EdgeMap H K) (z : G.IncResolutionBasis →₀ R) :
    (φ.trans ψ).stateMap R z = ψ.stateMap R (φ.stateMap R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    by_cases h : Set.InjOn (φ.trans ψ).edge S
    · have h' := (φ.injOn_trans_iff ψ S).mp h
      rw [stateMap_single_of_injOn _ R _ h, stateMap_single_of_injOn _ R _ h'.1,
        stateMap_single_of_injOn _ R _ h'.2, wedgeSign_trans, Int.cast_mul, mul_assoc]
      congr 1
      apply Sigma.ext (edgeSet_trans φ ψ S)
      exact (cast_heq _ κ).trans ((cast_heq _ _).trans (cast_heq _ κ)).symm
    · rw [stateMap_single_of_not_injOn _ R _ h]
      by_cases h1 : Set.InjOn φ.edge S
      · rw [stateMap_single_of_injOn _ R _ h1, stateMap_single_of_not_injOn]
        exact fun h2 => h ((φ.injOn_trans_iff ψ S).mpr ⟨h1, h2⟩)
      · rw [stateMap_single_of_not_injOn _ R _ h1, map_zero]

end EdgeMap

/-- For an edge relabeling the state map is the signed relabeling of states. -/
theorem EdgeRelabel.toEdgeMap_stateMap {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E]
    [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}
    (φ : EdgeRelabel G H) (R : Type) [CommRing R] (z : G.IncResolutionBasis →₀ R) :
    φ.toEdgeMap.stateMap R z = φ.stateRelabel R z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [EdgeMap.stateMap_single_of_injOn _ R _ (φ.edge.injective.injOn), stateRelabel_single,
      toEdgeMap_wedgeSign, intCast_sign, stateIndex_mk]
    congr 1
    apply Sigma.ext (φ.toEdgeMap_edgeSet S)
    exact (cast_heq _ κ).trans (cast_heq _ κ).symm

end BPFixedPoints.Multigraph
