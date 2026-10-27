import Mathlib

/-!
# Finite multigraphs

Represent finite undirected multigraphs with individual edge IDs and degrees
counting multiplicity. V and E are the vertex and edge types; assume Fintype
and DecidableEq where needed. Each edge has an ordered endpoint pair
(fst e,snd e), used for presentation; the quantities are orientation-independent.
Self-loops satisfy fst e=snd e. The BP layer requires `Loopless`, while
combinatorial Q allows loops and counts them twice. Distinct edge IDs retain
parallel-edge multiplicities.
For S:Finset E, `deg S v` counts endpoints equal to v, counting loops twice.
Deletion and contraction keep the types fixed and modify edge sets or endpoint
maps (`contractMap`). After contraction snd e is isolated, contributing φ(0)=1.
The relation to the usual vertex-identifying G/e is described under
“Differences in hypotheses” in `FORMALIZATION.md`.
-/

namespace BPFixedPoints

/-- Multigraph with vertex type V, edge IDs E and an ordered endpoint pair for each edge. -/
structure Multigraph (V E : Type*) where
  fst : E → V
  snd : E → V

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- Self-loop. -/
def IsLoop (e : E) : Prop := G.fst e = G.snd e

/-- Loopless graph. -/
def Loopless : Prop := ∀ e, G.fst e ≠ G.snd e

/-- Edge e is incident to vertex v. -/
def Incident (e : E) (v : V) : Prop := G.fst e = v ∨ G.snd e = v

instance [DecidableEq V] (e : E) (v : V) : Decidable (G.Incident e v) := by
  unfold Incident; infer_instance

section Degree

variable [DecidableEq V]

/-- Number of endpoints of e equal to v: 0, 1 or 2. -/
def endCount (e : E) (v : V) : ℕ :=
  (if G.fst e = v then 1 else 0) + (if G.snd e = v then 1 else 0)

/-- Degree in S with multiplicities, counting a loop twice. -/
def deg (S : Finset E) (v : V) : ℕ := ∑ e ∈ S, G.endCount e v

@[simp] theorem deg_empty (v : V) : G.deg ∅ v = 0 := by simp [deg]

theorem deg_insert [DecidableEq E] {S : Finset E} {e : E} (he : e ∉ S) (v : V) :
    G.deg (insert e S) v = G.deg S v + G.endCount e v := by
  unfold deg; rw [Finset.sum_insert he, add_comm]

theorem deg_mono {S T : Finset E} (h : S ⊆ T) (v : V) : G.deg S v ≤ G.deg T v :=
  Finset.sum_le_sum_of_subset h

theorem endCount_eq_zero_iff (e : E) (v : V) :
    G.endCount e v = 0 ↔ ¬ G.Incident e v := by
  unfold endCount Incident
  split_ifs <;> simp_all

theorem endCount_of_not_incident {e : E} {v : V} (h : ¬ G.Incident e v) : G.endCount e v = 0 :=
  (G.endCount_eq_zero_iff e v).2 h

theorem deg_eq_zero_iff (S : Finset E) (v : V) :
    G.deg S v = 0 ↔ ∀ e ∈ S, ¬ G.Incident e v := by
  simp [deg, Finset.sum_eq_zero_iff, endCount_eq_zero_iff]

theorem endCount_fst_of_ne {e : E} (h : G.fst e ≠ G.snd e) : G.endCount e (G.fst e) = 1 := by
  simp [endCount, h.symm]

theorem endCount_snd_of_ne {e : E} (h : G.fst e ≠ G.snd e) : G.endCount e (G.snd e) = 1 := by
  simp [endCount, h]

theorem endCount_of_ne_ne {e : E} {w : V} (h1 : G.fst e ≠ w) (h2 : G.snd e ≠ w) :
    G.endCount e w = 0 := by
  simp [endCount, h1, h2]

theorem endCount_loop {e : E} (h : G.fst e = G.snd e) : G.endCount e (G.fst e) = 2 := by
  simp [endCount, h]

theorem endCount_le_two (e : E) (v : V) : G.endCount e v ≤ 2 := by
  unfold endCount; split_ifs <;> omega

theorem deg_erase_fst [DecidableEq E] {A : Finset E} {e : E} (he : e ∈ A)
    (h : G.fst e ≠ G.snd e) : G.deg (A.erase e) (G.fst e) + 1 = G.deg A (G.fst e) := by
  conv_rhs => rw [← Finset.insert_erase he]
  rw [G.deg_insert (Finset.notMem_erase e A), endCount_fst_of_ne _ h]

theorem deg_erase_snd [DecidableEq E] {A : Finset E} {e : E} (he : e ∈ A)
    (h : G.fst e ≠ G.snd e) : G.deg (A.erase e) (G.snd e) + 1 = G.deg A (G.snd e) := by
  conv_rhs => rw [← Finset.insert_erase he]
  rw [G.deg_insert (Finset.notMem_erase e A), endCount_snd_of_ne _ h]

end Degree

section Contract

variable [DecidableEq V]

/-- Vertex map for contraction: send snd e to fst e and fix all other vertices. -/
def contractVertex (e : E) (x : V) : V := if x = G.snd e then G.fst e else x

/--
Contraction by endpoint reassignment, retaining the ambient vertex and edge
types. The former snd vertex becomes isolated and e becomes a loop;
Q is computed after restricting to A.erase e.
-/
def contractMap (e : E) : Multigraph V E where
  fst f := G.contractVertex e (G.fst f)
  snd f := G.contractVertex e (G.snd f)

variable {G} {e : E}

theorem contractVertex_ne_snd (he : G.fst e ≠ G.snd e) (x : V) :
    G.contractVertex e x ≠ G.snd e := by
  unfold contractVertex; split_ifs with h
  · exact he
  · exact h

theorem contractVertex_eq_fst_iff (x : V) :
    G.contractVertex e x = G.fst e ↔ x = G.fst e ∨ x = G.snd e := by
  unfold contractVertex; split_ifs with h
  · simp [h]
  · simp [h]

theorem contractVertex_eq_iff_of_ne {w : V} (hw1 : w ≠ G.fst e) (hw2 : w ≠ G.snd e) (x : V) :
    G.contractVertex e x = w ↔ x = w := by
  unfold contractVertex; split_ifs with h
  · subst h; exact ⟨fun h' => absurd h'.symm hw1, fun h' => absurd h' hw2.symm⟩
  · rfl

theorem contractVertex_of_ne {x : V} (hx : x ≠ G.snd e) : G.contractVertex e x = x := by
  simp [contractVertex, hx]

theorem contractMap_endCount_snd (he : G.fst e ≠ G.snd e) (f : E) :
    (G.contractMap e).endCount f (G.snd e) = 0 := by
  unfold contractMap endCount
  simp [contractVertex_ne_snd he]

/-- An indicator of two disjoint conditions splits as their sum. -/
theorem ite_or_add {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (if p ∨ q then 1 else 0 : ℕ) = (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem contractMap_endCount_fst (he : G.fst e ≠ G.snd e) (f : E) :
    (G.contractMap e).endCount f (G.fst e) = G.endCount f (G.fst e) + G.endCount f (G.snd e) := by
  unfold contractMap endCount
  simp only [contractVertex_eq_fst_iff]
  have h1 : ¬ (G.fst f = G.fst e ∧ G.fst f = G.snd e) := fun h => he (h.1.symm.trans h.2)
  have h2 : ¬ (G.snd f = G.fst e ∧ G.snd f = G.snd e) := fun h => he (h.1.symm.trans h.2)
  rw [ite_or_add h1, ite_or_add h2]
  ring

theorem contractMap_endCount_of_ne (f : E) {w : V} (hw1 : w ≠ G.fst e) (hw2 : w ≠ G.snd e) :
    (G.contractMap e).endCount f w = G.endCount f w := by
  unfold contractMap endCount
  simp only [contractVertex_eq_iff_of_ne hw1 hw2]

theorem contractMap_deg_snd (he : G.fst e ≠ G.snd e) (S : Finset E) :
    (G.contractMap e).deg S (G.snd e) = 0 := by
  simp [deg, contractMap_endCount_snd he]

theorem contractMap_deg_fst (he : G.fst e ≠ G.snd e) (S : Finset E) :
    (G.contractMap e).deg S (G.fst e) = G.deg S (G.fst e) + G.deg S (G.snd e) := by
  simp [deg, contractMap_endCount_fst he, Finset.sum_add_distrib]

theorem contractMap_deg_of_ne (S : Finset E) {w : V} (hw1 : w ≠ G.fst e) (hw2 : w ≠ G.snd e) :
    (G.contractMap e).deg S w = G.deg S w := by
  simp [deg, contractMap_endCount_of_ne _ hw1 hw2]

end Contract

section Connected

/-- Undirected adjacency using edges in A. -/
def Adj (A : Finset E) (a b : V) : Prop :=
  ∃ e ∈ A, (G.fst e = a ∧ G.snd e = b) ∨ (G.fst e = b ∧ G.snd e = a)

/-- Connected subgraph on W and A: W is nonempty, all edge endpoints lie in W, and every pair in W is joined by A-edges. -/
def ConnectedOn (A : Finset E) (W : Finset V) : Prop :=
  W.Nonempty ∧ (∀ e ∈ A, G.fst e ∈ W ∧ G.snd e ∈ W) ∧
    ∀ a ∈ W, ∀ b ∈ W, Relation.ReflTransGen (G.Adj A) a b

/-- The whole graph is connected. -/
def Connected [Fintype V] [Fintype E] : Prop := G.ConnectedOn Finset.univ Finset.univ

theorem adj_of_all_loops {A : Finset E} (hA : ∀ e ∈ A, G.IsLoop e) {a b : V}
    (h : G.Adj A a b) : a = b := by
  obtain ⟨e, he, h | h⟩ := h
  · rw [← h.1, ← h.2]; exact hA e he
  · rw [← h.1, ← h.2]; exact (hA e he).symm

theorem reflTransGen_adj_of_all_loops {A : Finset E} (hA : ∀ e ∈ A, G.IsLoop e) {a b : V}
    (h : Relation.ReflTransGen (G.Adj A) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (G.adj_of_all_loops hA hbc)

/-- A connected graph with at least two vertices contains a nonloop edge. -/
theorem exists_nonloop_of_connectedOn {A : Finset E} {W : Finset V} (hc : G.ConnectedOn A W)
    (hW : 1 < W.card) : ∃ e ∈ A, G.fst e ≠ G.snd e := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hW
  by_contra hall
  exact hab (G.reflTransGen_adj_of_all_loops
    (fun e he => Classical.by_contradiction fun hne => hall ⟨e, he, hne⟩) (hc.2.2 a ha b hb))

end Connected

end Multigraph

end BPFixedPoints
