import BPFixedPoints.Incidence.StateExteriorCup
import BPFixedPoints.Incidence.ResolutionBasisCount

/-!
# Edge relabelings of multigraphs and the signed relabeling of states

An `EdgeRelabel G H` is an isomorphism of multigraphs on the same vertex set: a bijection of
edge types carrying the endpoint pair of every edge to the endpoint pair of its image, either in
the same order or reversed (`reversed e`). The linear orders of the two edge types are arbitrary
and unrelated; they enter only through the exterior sign conventions of each graph. Vertex
degrees of edge sets, supports, cardinalities and disjointness are preserved.

The exterior basis vector of an increasingly ordered edge set `S` of `G` is sent to the wedge of
the image edges, which is the relabeling sign `φ.sign R S` times the increasingly ordered basis
vector of the image edge set in `H`; the sign is `(-1)` to the number of pairs of `S` whose order
is reversed by the edge bijection. Orientation reversal contributes no sign in this model: the
coefficients of an edge are indexed by ordered endpoint pairs, so reversal is absorbed by the
coefficient isomorphism exchanging the two endpoint indices.

On the full state modules `(G.IncResolutionBasis →₀ R)` the signed relabeling `stateRelabel` is a
linear isomorphism. It carries the shared state product `incStateCup` of `G` to that of `H` and
the unit state to the unit state, for every commutative ring `R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

/-- An isomorphism of multigraphs on the same vertex set: an edge bijection taking the endpoint
pair of each edge to the endpoint pair of its image, possibly in reversed order. -/
structure EdgeRelabel {V E E' : Type} (G : Multigraph V E) (H : Multigraph V E') where
  /-- The bijection of edges. -/
  edge : E ≃ E'
  /-- Whether the endpoint order of an edge is reversed by the relabeling. -/
  reversed : E → Bool
  /-- The first endpoint of the image edge. -/
  fst_edge : ∀ e, H.fst (edge e) = if reversed e then G.snd e else G.fst e
  /-- The second endpoint of the image edge. -/
  snd_edge : ∀ e, H.snd (edge e) = if reversed e then G.fst e else G.snd e

namespace EdgeRelabel

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- The image of an edge set. -/
def edgeSet (S : Finset E) : Finset E' := Equiv.finsetCongr φ.edge S

theorem edgeSet_def (S : Finset E) : φ.edgeSet S = S.map φ.edge.toEmbedding := rfl

theorem mem_edgeSet {S : Finset E} {e : E} : φ.edge e ∈ φ.edgeSet S ↔ e ∈ S := by
  simp [edgeSet_def]

@[simp] theorem card_edgeSet (S : Finset E) : (φ.edgeSet S).card = S.card := by
  simp [edgeSet_def]

theorem edgeSet_injective : Function.Injective φ.edgeSet :=
  (Equiv.finsetCongr φ.edge).injective

@[simp] theorem edgeSet_empty : φ.edgeSet ∅ = ∅ := by simp [edgeSet_def]

variable [DecidableEq E] [DecidableEq E']

theorem edgeSet_union (S T : Finset E) : φ.edgeSet (S ∪ T) = φ.edgeSet S ∪ φ.edgeSet T := by
  simp [edgeSet_def, Finset.map_union]

theorem edgeSet_erase (S : Finset E) (e : E) :
    φ.edgeSet (S.erase e) = (φ.edgeSet S).erase (φ.edge e) := by
  simp [edgeSet_def, Finset.map_erase]

theorem disjoint_edgeSet_iff {S T : Finset E} :
    Disjoint (φ.edgeSet S) (φ.edgeSet T) ↔ Disjoint S T := by
  simp [edgeSet_def]

variable [DecidableEq V]

/-- Relabeling preserves the endpoint count of an edge at every vertex. -/
@[simp] theorem endCount_edge (e : E) (v : V) : H.endCount (φ.edge e) v = G.endCount e v := by
  unfold endCount
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · simp
  · simp only [ite_true]
    omega

/-- Relabeling preserves the vertex degrees of every edge set, as functions. -/
theorem deg_edgeSet (S : Finset E) : H.deg (φ.edgeSet S) = G.deg S := by
  funext v
  simp [deg, edgeSet_def, Finset.sum_map]

/-- Relabeling preserves the supports of edge sets. -/
theorem support_edgeSet [Fintype V] (S : Finset E) : H.support (φ.edgeSet S) = G.support S := by
  simp [support, φ.deg_edgeSet]

end EdgeRelabel

/-! ## Identity and composition of edge relabelings -/

namespace EdgeRelabel

/-- The identity relabeling of a multigraph. -/
def refl {V E : Type} (G : Multigraph V E) : EdgeRelabel G G where
  edge := Equiv.refl E
  reversed _ := false
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The composite of two edge relabelings; an edge is reversed when exactly one of the two
relabelings reverses it. -/
def trans {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'} {K : Multigraph V E''}
    (φ : EdgeRelabel G H) (ψ : EdgeRelabel H K) : EdgeRelabel G K where
  edge := φ.edge.trans ψ.edge
  reversed e := xor (φ.reversed e) (ψ.reversed (φ.edge e))
  fst_edge e := by
    simp only [Equiv.trans_apply]
    rw [ψ.fst_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl
  snd_edge e := by
    simp only [Equiv.trans_apply]
    rw [ψ.snd_edge, φ.fst_edge, φ.snd_edge]
    cases φ.reversed e <;> cases ψ.reversed (φ.edge e) <;> rfl

@[simp] theorem refl_edge {V E : Type} (G : Multigraph V E) (e : E) : (refl G).edge e = e := rfl

@[simp] theorem trans_edge {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : EdgeRelabel G H) (ψ : EdgeRelabel H K) (e : E) :
    (φ.trans ψ).edge e = ψ.edge (φ.edge e) := rfl

theorem edgeSet_refl {V E : Type} (G : Multigraph V E) (S : Finset E) :
    (refl G).edgeSet S = S := by
  simp [edgeSet_def, refl]

theorem edgeSet_trans {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : EdgeRelabel G H) (ψ : EdgeRelabel H K) (S : Finset E) :
    (φ.trans ψ).edgeSet S = ψ.edgeSet (φ.edgeSet S) := by
  simp [edgeSet_def, trans, Finset.map_map]

end EdgeRelabel

/-! ## Inversions and the relabeling sign -/

section Signs

/-- Pointwise inversion identity: for distinct `a b` with distinct images,
`[b<a] + [σb<σa] = [a<b ∧ σb<σa] + [b<a ∧ σa<σb] + 2·[b<a ∧ σb<σa]`. -/
theorem inversion_indicator {E E' : Type} [LinearOrder E] [LinearOrder E'] (σ : E ≃ E')
    {a b : E} (hab : a ≠ b) :
    (if b < a then 1 else 0) + (if σ b < σ a then 1 else 0) =
      (if a < b ∧ σ b < σ a then 1 else 0) + (if b < a ∧ σ a < σ b then 1 else 0) +
        2 * (if b < a ∧ σ b < σ a then 1 else 0 : ℕ) := by
  have hσ : σ a ≠ σ b := fun h => hab (σ.injective h)
  rcases lt_or_gt_of_ne hab with h | h <;> rcases lt_or_gt_of_ne hσ with h' | h' <;>
    simp [h, h', not_lt_of_gt]

/-- Two pairs of signs agree when the total exponent is even. -/
theorem neg_one_pow_pair {R : Type*} [CommRing R] {a b c d : ℕ} (h : Even (a + b + c + d)) :
    (-1 : R) ^ a * (-1 : R) ^ b = (-1 : R) ^ c * (-1 : R) ^ d := by
  have h1 : (-1 : R) ^ (a + b + c + d) = 1 := h.neg_one_pow
  have h2 : (-1 : R) ^ (c + d) * (-1 : R) ^ (c + d) = 1 := Koszul.neg_one_pow_mul_self (c + d)
  calc (-1 : R) ^ a * (-1 : R) ^ b = (-1 : R) ^ (a + b) * ((-1 : R) ^ (c + d) * (-1) ^ (c + d)) := by
        rw [h2, mul_one, pow_add]
    _ = (-1 : R) ^ (a + b + c + d) * (-1) ^ (c + d) := by
        rw [← mul_assoc, ← pow_add, add_assoc (a + b) c d]
    _ = (-1 : R) ^ c * (-1 : R) ^ d := by rw [h1, one_mul, pow_add]

namespace EdgeRelabel

variable {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)
variable [LinearOrder E] [LinearOrder E']

/-- The number of pairs of an edge set whose order is reversed by the edge bijection. -/
def inversions (S : Finset E) : ℕ :=
  ∑ a ∈ S, ∑ b ∈ S, if a < b ∧ φ.edge b < φ.edge a then 1 else 0

/-- The relabeling sign of an edge set: the wedge of the image edges in the order of `S` is this
sign times the increasingly ordered exterior basis vector of the image edge set. -/
def sign (R : Type*) [CommRing R] (S : Finset E) : R := (-1) ^ φ.inversions S

@[simp] theorem inversions_empty : φ.inversions ∅ = 0 := by simp [inversions]

@[simp] theorem sign_empty (R : Type*) [CommRing R] : φ.sign R ∅ = 1 := by simp [sign]

/-- The relabeling sign squares to one. -/
@[simp] theorem sign_mul_self (R : Type*) [CommRing R] (S : Finset E) :
    φ.sign R S * φ.sign R S = 1 :=
  Koszul.neg_one_pow_mul_self _

/-- A ring homomorphism maps relabeling signs to relabeling signs. -/
@[simp] theorem map_sign {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (S : Finset E) :
    f (φ.sign R S) = φ.sign R' S := by
  simp [sign]

/-- The integer relabeling sign maps to the relabeling sign of any commutative ring. -/
@[simp] theorem intCast_sign {R : Type*} [CommRing R] (S : Finset E) :
    ((φ.sign ℤ S : ℤ) : R) = φ.sign R S := by
  simp [sign]

/-- Inversions of an edge set split into those of two disjoint parts and the crossing pairs. -/
theorem inversions_union {S T : Finset E} (h : Disjoint S T) :
    φ.inversions (S ∪ T) = φ.inversions S + φ.inversions T +
      ∑ s ∈ S, ∑ t ∈ T, ((if s < t ∧ φ.edge t < φ.edge s then 1 else 0) +
        (if t < s ∧ φ.edge s < φ.edge t then 1 else 0)) := by
  unfold inversions
  simp only [Finset.sum_union h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := T) (t := S)]
  ring

/-- The shuffle index of a pair of disjoint edge sets as a double sum. -/
theorem shuffleIndex_eq_sum (S T : Finset E) :
    Koszul.shuffleIndex S T = ∑ s ∈ S, ∑ t ∈ T, if t < s then 1 else 0 := by
  unfold Koszul.shuffleIndex Koszul.index
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

/-- The shuffle index of the image edge sets as a double sum over the original edge sets. -/
theorem shuffleIndex_edgeSet (S T : Finset E) :
    Koszul.shuffleIndex (φ.edgeSet S) (φ.edgeSet T) =
      ∑ s ∈ S, ∑ t ∈ T, if φ.edge t < φ.edge s then 1 else 0 := by
  unfold Koszul.shuffleIndex Koszul.index
  rw [edgeSet_def, Finset.sum_map]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter, edgeSet_def, Finset.sum_map]
  rfl

/-- Shuffle signs of disjoint edge sets transform by the relabeling signs. -/
theorem sign_union_mul_shuffleSign (R : Type*) [CommRing R] {S T : Finset E} (h : Disjoint S T) :
    φ.sign R (S ∪ T) * Koszul.shuffleSign (R := R) S T =
      Koszul.shuffleSign (R := R) (φ.edgeSet S) (φ.edgeSet T) * (φ.sign R S * φ.sign R T) := by
  unfold sign Koszul.shuffleSign
  rw [← pow_add (-1 : R) (φ.inversions S)]
  apply neg_one_pow_pair
  rw [φ.inversions_union h, shuffleIndex_eq_sum, φ.shuffleIndex_edgeSet]
  have hpt : ∀ s ∈ S, ∀ t ∈ T,
      (if t < s then 1 else 0) + (if φ.edge t < φ.edge s then 1 else 0) =
        ((if s < t ∧ φ.edge t < φ.edge s then 1 else 0) +
          (if t < s ∧ φ.edge s < φ.edge t then 1 else 0)) +
          2 * (if t < s ∧ φ.edge t < φ.edge s then 1 else 0 : ℕ) := by
    intro s hs t ht
    have hst : s ≠ t := fun hst => Finset.disjoint_left.mp h hs (hst ▸ ht)
    rw [inversion_indicator φ.edge hst]
  have hsum : (∑ s ∈ S, ∑ t ∈ T, if t < s then 1 else 0) +
      (∑ s ∈ S, ∑ t ∈ T, if φ.edge t < φ.edge s then 1 else 0) =
      (∑ s ∈ S, ∑ t ∈ T, ((if s < t ∧ φ.edge t < φ.edge s then 1 else 0) +
          (if t < s ∧ φ.edge s < φ.edge t then 1 else 0))) +
        2 * ∑ s ∈ S, ∑ t ∈ T, (if t < s ∧ φ.edge t < φ.edge s then 1 else 0 : ℕ) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => hpt s hs t ht
  refine ⟨φ.inversions S + φ.inversions T + ∑ s ∈ S, ∑ t ∈ T,
      ((if s < t ∧ φ.edge t < φ.edge s then 1 else 0) +
        (if t < s ∧ φ.edge s < φ.edge t then 1 else 0)) +
      ∑ s ∈ S, ∑ t ∈ T, (if t < s ∧ φ.edge t < φ.edge s then 1 else 0 : ℕ), ?_⟩
  omega

/-- Inversions of an edge set containing `e` split into those of the remaining edges and the
pairs involving `e`. -/
theorem inversions_of_mem [DecidableEq E] {S : Finset E} {e : E} (he : e ∈ S) :
    φ.inversions S = φ.inversions (S.erase e) +
      ∑ a ∈ S.erase e, ((if e < a ∧ φ.edge a < φ.edge e then 1 else 0) +
        (if a < e ∧ φ.edge e < φ.edge a then 1 else 0)) := by
  conv_lhs => rw [← Finset.insert_erase he]
  unfold inversions
  rw [Finset.sum_insert (Finset.notMem_erase e S)]
  simp only [Finset.sum_insert (Finset.notMem_erase e S), lt_irrefl, false_and, ite_false,
    zero_add, Finset.sum_add_distrib]
  ring

/-- Removal signs of an edge transform by the relabeling signs: the relabeling of the Koszul
contraction by `e` is the Koszul contraction by the image edge. -/
theorem sign_erase_mul_koszulSign [DecidableEq E] [DecidableEq E'] (R : Type*) [CommRing R]
    {S : Finset E} {e : E} (he : e ∈ S) :
    Koszul.sign (A := R) S e * φ.sign R (S.erase e) =
      Koszul.sign (A := R) (φ.edgeSet S) (φ.edge e) * φ.sign R S := by
  unfold sign Koszul.sign
  apply neg_one_pow_pair
  have hidx : Koszul.index S e = ∑ a ∈ S.erase e, if a < e then 1 else 0 := by
    unfold Koszul.index
    rw [Finset.card_filter]
    conv_lhs => rw [← Finset.insert_erase he]
    rw [Finset.sum_insert (Finset.notMem_erase e S)]
    simp
  have hidx' : Koszul.index (φ.edgeSet S) (φ.edge e) =
      ∑ a ∈ S.erase e, if φ.edge a < φ.edge e then 1 else 0 := by
    unfold Koszul.index
    rw [Finset.card_filter, edgeSet_def, Finset.sum_map]
    conv_lhs => rw [← Finset.insert_erase he]
    rw [Finset.sum_insert (Finset.notMem_erase e S)]
    simp
  have hpt : ∀ a ∈ S.erase e,
      (if a < e then 1 else 0) + (if φ.edge a < φ.edge e then 1 else 0) =
        ((if e < a ∧ φ.edge a < φ.edge e then 1 else 0) +
          (if a < e ∧ φ.edge e < φ.edge a then 1 else 0)) +
          2 * (if a < e ∧ φ.edge a < φ.edge e then 1 else 0 : ℕ) := by
    intro a ha
    exact inversion_indicator φ.edge (Ne.symm (Finset.ne_of_mem_erase ha))
  have hsum : (∑ a ∈ S.erase e, if a < e then 1 else 0) +
      (∑ a ∈ S.erase e, if φ.edge a < φ.edge e then 1 else 0) =
      (∑ a ∈ S.erase e, ((if e < a ∧ φ.edge a < φ.edge e then 1 else 0) +
          (if a < e ∧ φ.edge e < φ.edge a then 1 else 0))) +
        2 * ∑ a ∈ S.erase e, (if a < e ∧ φ.edge a < φ.edge e then 1 else 0 : ℕ) := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hpt
  rw [hidx, hidx', φ.inversions_of_mem he]
  refine ⟨φ.inversions (S.erase e) + ∑ a ∈ S.erase e,
      ((if e < a ∧ φ.edge a < φ.edge e then 1 else 0) +
        (if a < e ∧ φ.edge e < φ.edge a then 1 else 0)) +
      ∑ a ∈ S.erase e, (if a < e ∧ φ.edge a < φ.edge e then 1 else 0 : ℕ), ?_⟩
  omega

/-- The identity relabeling has no inversions. -/
@[simp] theorem inversions_refl {V : Type} (G : Multigraph V E) (S : Finset E) :
    (refl G).inversions S = 0 := by
  unfold inversions
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  simp only [refl_edge]
  rw [ite_eq_right_iff]
  rintro ⟨h, h'⟩
  exact absurd h' (lt_asymm h)

@[simp] theorem sign_refl {V : Type} (R : Type*) [CommRing R] (G : Multigraph V E) (S : Finset E) :
    (refl G).sign R S = 1 := by
  simp [sign]

/-- Inversions of a composite relabeling have the parity of the sum of the inversions. -/
theorem even_inversions_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''}
    (ψ : EdgeRelabel H K) (S : Finset E) :
    Even ((φ.trans ψ).inversions S + ψ.inversions (φ.edgeSet S) + φ.inversions S) := by
  let f : E → E → ℕ := fun a b =>
    (if a < b ∧ ψ.edge (φ.edge b) < ψ.edge (φ.edge a) then 1 else 0) +
      (if φ.edge a < φ.edge b ∧ ψ.edge (φ.edge b) < ψ.edge (φ.edge a) then 1 else 0) +
      (if a < b ∧ φ.edge b < φ.edge a then 1 else 0)
  have hsum : (φ.trans ψ).inversions S + ψ.inversions (φ.edgeSet S) + φ.inversions S =
      ∑ a ∈ S, ∑ b ∈ S, f a b := by
    simp only [f, Finset.sum_add_distrib, inversions, edgeSet_def, Finset.sum_map, trans_edge]
    rfl
  have hdiag : ∀ a, f a a = 0 := by
    intro a
    simp [f]
  have hpair : ∀ a b, Even (f a b + f b a) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hdiag]
      exact Even.zero
    have h1 : φ.edge a ≠ φ.edge b := fun h => hab (φ.edge.injective h)
    have h2 : ψ.edge (φ.edge a) ≠ ψ.edge (φ.edge b) := fun h => h1 (ψ.edge.injective h)
    rcases lt_or_gt_of_ne hab with h | h <;> rcases lt_or_gt_of_ne h1 with h' | h' <;>
      rcases lt_or_gt_of_ne h2 with h'' | h'' <;>
      simp [f, h, h', h'', not_lt_of_gt]
  have hsplit : ∑ a ∈ S, ∑ b ∈ S, f a b =
      ∑ a ∈ S, ∑ b ∈ S, (if a < b then f a b + f b a else 0) := by
    have hswap : ∑ a ∈ S, ∑ b ∈ S, (if a < b then f b a else 0) =
        ∑ a ∈ S, ∑ b ∈ S, (if b < a then f a b else 0) := Finset.sum_comm
    have hterm : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0) := by
      intro a b
      rcases lt_trichotomy a b with h | rfl | h
      · simp [h, not_lt_of_gt h]
      · simp [hdiag]
      · simp [h, not_lt_of_gt h]
    calc ∑ a ∈ S, ∑ b ∈ S, f a b
        = ∑ a ∈ S, ∑ b ∈ S, ((if a < b then f a b else 0) + (if b < a then f a b else 0)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
      _ = ∑ a ∈ S, ∑ b ∈ S, (if a < b then f a b else 0) +
          ∑ a ∈ S, ∑ b ∈ S, (if b < a then f a b else 0) := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ a ∈ S, ∑ b ∈ S, (if a < b then f a b else 0) +
          ∑ a ∈ S, ∑ b ∈ S, (if a < b then f b a else 0) := by rw [hswap]
      _ = ∑ a ∈ S, ∑ b ∈ S, (if a < b then f a b + f b a else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
  rw [hsum, hsplit]
  refine Finset.even_sum _ fun a _ => Finset.even_sum _ fun b _ => ?_
  split_ifs
  · exact hpair a b
  · exact Even.zero

/-- The relabeling sign of a composite is the product of the relabeling signs. -/
theorem sign_trans {E'' : Type} [LinearOrder E''] {K : Multigraph V E''} (ψ : EdgeRelabel H K)
    (R : Type*) [CommRing R] (S : Finset E) :
    (φ.trans ψ).sign R S = ψ.sign R (φ.edgeSet S) * φ.sign R S := by
  have h := neg_one_pow_pair (R := R) (b := 0) (φ.even_inversions_trans ψ S)
  rw [pow_zero, mul_one] at h
  exact h

end EdgeRelabel

end Signs

/-! ## The signed relabeling of resolution states -/

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- Relabeling of resolution state indices: an edge set goes to its image edge set, and a state of
its twist to the same state of the equal twist. -/
def stateIndex : G.IncResolutionBasis ≃ H.IncResolutionBasis :=
  Equiv.sigmaCongr (Equiv.finsetCongr φ.edge)
    (fun S => Equiv.cast (congrArg HBasis (φ.deg_edgeSet S).symm))

theorem stateIndex_mk (S : Finset E) (κ : HBasis (G.deg S)) :
    φ.stateIndex ⟨S, κ⟩ = ⟨φ.edgeSet S, cast (congrArg HBasis (φ.deg_edgeSet S).symm) κ⟩ := rfl

/-- The edge set of a relabeled state index is the image edge set. -/
@[simp] theorem stateIndex_fst (b : G.IncResolutionBasis) :
    (φ.stateIndex b).1 = φ.edgeSet b.1 := rfl

/-- Relabeling preserves the homological degree of resolution states. -/
theorem incResolutionDegree_stateIndex (b : G.IncResolutionBasis) :
    H.incResolutionDegree (φ.stateIndex b) = G.incResolutionDegree b := by
  simp [incResolutionDegree, φ.support_edgeSet]

/-- Relabeling preserves the internal degree of resolution states. -/
theorem incResolutionInternalDegree_stateIndex (b : G.IncResolutionBasis) :
    H.incResolutionInternalDegree (φ.stateIndex b) = G.incResolutionInternalDegree b := by
  simp [incResolutionInternalDegree]

variable (R : Type) [CommRing R]

/-- The signed relabeling of state vectors: the basis state of an edge set goes to the relabeling
sign times the corresponding basis state of the image edge set. -/
noncomputable def stateRelabelMap :
    (G.IncResolutionBasis →₀ R) →ₗ[R] (H.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => φ.sign R b.1 • Finsupp.lsingle (φ.stateIndex b)

/-- The inverse signed relabeling. -/
noncomputable def stateRelabelInvMap :
    (H.IncResolutionBasis →₀ R) →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => φ.sign R (φ.stateIndex.symm b).1 • Finsupp.lsingle (φ.stateIndex.symm b)

theorem stateRelabelMap_single (b : G.IncResolutionBasis) (r : R) :
    φ.stateRelabelMap R (single b r) = single (φ.stateIndex b) (φ.sign R b.1 * r) := by
  simp [stateRelabelMap, Finsupp.smul_single, smul_eq_mul]

theorem stateRelabelInvMap_single (b : H.IncResolutionBasis) (r : R) :
    φ.stateRelabelInvMap R (single b r) =
      single (φ.stateIndex.symm b) (φ.sign R (φ.stateIndex.symm b).1 * r) := by
  simp [stateRelabelInvMap, Finsupp.smul_single, smul_eq_mul]

/-- The signed relabeling of state vectors is a linear isomorphism. -/
noncomputable def stateRelabel :
    (G.IncResolutionBasis →₀ R) ≃ₗ[R] (H.IncResolutionBasis →₀ R) :=
  LinearEquiv.ofLinearMap (φ.stateRelabelMap R) (φ.stateRelabelInvMap R)
    (by
      apply Finsupp.lhom_ext
      intro b r
      simp only [LinearMap.comp_apply, stateRelabelInvMap_single, stateRelabelMap_single,
        Equiv.apply_symm_apply, LinearMap.id_apply, ← mul_assoc, sign_mul_self, one_mul])
    (by
      apply Finsupp.lhom_ext
      intro b r
      simp only [LinearMap.comp_apply, stateRelabelMap_single, stateRelabelInvMap_single,
        Equiv.symm_apply_apply, LinearMap.id_apply, ← mul_assoc, sign_mul_self, one_mul])

/-- The signed relabeling of a basis state. -/
theorem stateRelabel_single (b : G.IncResolutionBasis) (r : R) :
    φ.stateRelabel R (single b r) = single (φ.stateIndex b) (φ.sign R b.1 * r) :=
  φ.stateRelabelMap_single R b r

/-- Coefficients of a relabeled state vector at relabeled indices. -/
theorem stateRelabel_apply_stateIndex (z : G.IncResolutionBasis →₀ R) (b : G.IncResolutionBasis) :
    φ.stateRelabel R z (φ.stateIndex b) = φ.sign R b.1 * z b := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [stateRelabel_single]
    by_cases hc : c = b
    · subst hc
      simp
    · rw [single_eq_of_ne (fun h => hc (φ.stateIndex.injective h).symm),
        single_eq_of_ne (Ne.symm hc), mul_zero]

/-- Coefficients of a relabeled state vector. -/
theorem stateRelabel_apply (z : G.IncResolutionBasis →₀ R) (b : H.IncResolutionBasis) :
    φ.stateRelabel R z b = φ.sign R (φ.stateIndex.symm b).1 * z (φ.stateIndex.symm b) := by
  conv_lhs => rw [← φ.stateIndex.apply_symm_apply b]
  exact φ.stateRelabel_apply_stateIndex R z _

/-- Coefficientwise ring change commutes with the signed relabeling. -/
theorem stateRelabel_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    φ.stateRelabel R' (mapRange f (map_zero f) z) =
      mapRange f (map_zero f) (φ.stateRelabel R z) := by
  ext b
  rw [stateRelabel_apply, mapRange_apply, mapRange_apply, stateRelabel_apply, map_mul,
    map_sign]

/-- The signed relabeling of an embedded state of one edge set. -/
theorem stateRelabel_incStateEmbed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    φ.stateRelabel R (G.incStateEmbed R S x) =
      φ.sign R S • H.incStateEmbed R (φ.edgeSet S) (castH R (φ.deg_edgeSet S).symm x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | single κ r =>
    rw [incStateEmbed_single, stateRelabel_single, castH_single, incStateEmbed_single,
      Finsupp.smul_single, smul_eq_mul]
    rfl

/-- The signed relabeling carries the state product of `G` to the state product of `H`. -/
theorem stateRelabel_incStateCup (x y : G.IncResolutionBasis →₀ R) :
    φ.stateRelabel R (G.incStateCup R x y) =
      H.incStateCup R (φ.stateRelabel R x) (φ.stateRelabel R y) := by
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
        incStateCup_embed, stateRelabel_incStateEmbed, stateRelabel_incStateEmbed]
      simp only [map_smul, LinearMap.smul_apply]
      rw [incStateCup_embed]
      by_cases h : Disjoint S T
      · have h' : Disjoint (φ.edgeSet S) (φ.edgeSet T) := φ.disjoint_edgeSet_iff.mpr h
        rw [dite_eq_left h, dite_eq_left h', map_smul, stateRelabel_incStateEmbed,
          smul_smul, smul_smul, smul_smul]
        have hcd : cohomologyDegree (H.deg (φ.edgeSet T)) = cohomologyDegree (G.deg T) := by
          rw [φ.deg_edgeSet]
        congr 1
        · rw [φ.card_edgeSet, hcd]
          have hsign := φ.sign_union_mul_shuffleSign R h
          calc Koszul.shuffleSign (R := R) S T * (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) *
                φ.sign R (S ∪ T)
              = (φ.sign R (S ∪ T) * Koszul.shuffleSign (R := R) S T) *
                  (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) := by ring
            _ = Koszul.shuffleSign (R := R) (φ.edgeSet S) (φ.edgeSet T) *
                  (φ.sign R S * φ.sign R T) *
                  (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) := by rw [hsign]
            _ = _ := by ring
        · apply H.incStateEmbed_heq R (φ.edgeSet_union S T)
          refine (castH_heq R _ _).trans ((castH_heq R _ _).trans ?_)
          refine HEq.symm ((castH_heq R _ _).trans ?_)
          exact cohomologyCup_heq R (φ.deg_edgeSet S) (φ.deg_edgeSet T) (castH_heq R _ _)
            (castH_heq R _ _)
      · have h' : ¬ Disjoint (φ.edgeSet S) (φ.edgeSet T) := fun h' =>
          h (φ.disjoint_edgeSet_iff.mp h')
        rw [dite_eq_right h, dite_eq_right h', map_zero, smul_zero, smul_zero]

/-- The signed relabeling carries the unit state of `G` to the unit state of `H`. -/
theorem stateRelabel_incStateUnit : φ.stateRelabel R (G.incStateUnit R) = H.incStateUnit R := by
  rw [incStateUnit, stateRelabel_incStateEmbed, sign_empty, one_smul, incStateUnit]
  apply H.incStateEmbed_heq R φ.edgeSet_empty
  exact (castH_heq R _ _).trans ((castH_heq R _ _).trans (castH_heq R _ _).symm)

/-- The identity relabeling relabels states trivially. -/
theorem stateRelabel_refl (G : Multigraph V E) (z : G.IncResolutionBasis →₀ R) :
    (refl G).stateRelabel R z = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [stateRelabel_single, stateIndex_mk, sign_refl, one_mul]
    congr 1
    apply Sigma.ext (edgeSet_refl G S)
    exact cast_heq _ κ

/-- The signed relabeling of a composite is the composite of the signed relabelings. -/
theorem stateRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E''] {K : Multigraph V E''}
    (ψ : EdgeRelabel H K) (z : G.IncResolutionBasis →₀ R) :
    (φ.trans ψ).stateRelabel R z = ψ.stateRelabel R (φ.stateRelabel R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [stateRelabel_single, stateRelabel_single, stateRelabel_single, stateIndex_mk,
      stateIndex_mk, stateIndex_mk, sign_trans, mul_assoc]
    congr 1
    apply Sigma.ext (edgeSet_trans φ ψ S)
    exact (cast_heq _ κ).trans ((cast_heq _ _).trans (cast_heq _ κ)).symm

end EdgeRelabel

end BPFixedPoints.Multigraph
