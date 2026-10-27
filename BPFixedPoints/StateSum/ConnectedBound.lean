import BPFixedPoints.StateSum.DeletionContraction
import BPFixedPoints.StateSum.Bouquet

/-!
# Connected lower bound (ν−1)2^ν+2≤Q and reduction of θ(1,2) to bouquets

Contract a spanning tree of a nonempty connected graph to B_ν. Q does not
increase under contraction, while θ(1,2) stays fixed by deletion–contraction
at t=1. State this for a connected subgraph on vertex set W and edge set A
(`ConnectedOn`) and induct on |W|. Contraction uses endpoint reassignment
`contractMap`, removing the contracted vertex from W.
-/

namespace BPFixedPoints

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V]

theorem contractVertex_mem {G : Multigraph V E} {e : E} {W : Finset V} (hu : G.fst e ∈ W)
    {x : V} (hx : x ∈ W) : G.contractVertex e x ∈ W := by
  unfold contractVertex; split_ifs <;> assumption

/-- Contracting a nonloop edge preserves connectedness. -/
theorem connectedOn_contractMap {G : Multigraph V E} {A : Finset E} {W : Finset V}
    (hc : G.ConnectedOn A W) {e : E} (he : e ∈ A) (hne : G.fst e ≠ G.snd e) :
    (G.contractMap e).ConnectedOn (A.erase e) (W.erase (G.snd e)) := by
  obtain ⟨_, hin, hconn⟩ := hc
  have hu : G.fst e ∈ W := (hin e he).1
  refine ⟨⟨G.fst e, Finset.mem_erase.2 ⟨hne, hu⟩⟩, ?_, ?_⟩
  · intro f hf
    rw [Finset.mem_erase] at hf
    have h := hin f hf.2
    exact ⟨Finset.mem_erase.2 ⟨contractVertex_ne_snd hne _, contractVertex_mem hu h.1⟩,
      Finset.mem_erase.2 ⟨contractVertex_ne_snd hne _, contractVertex_mem hu h.2⟩⟩
  · have key : ∀ x y, Relation.ReflTransGen (G.Adj A) x y →
        Relation.ReflTransGen ((G.contractMap e).Adj (A.erase e))
          (G.contractVertex e x) (G.contractVertex e y) := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hyz ih =>
        refine ih.trans ?_
        obtain ⟨f, hf, hf'⟩ := hyz
        by_cases hfe : f = e
        · subst hfe
          have h1 : G.contractVertex f (G.fst f) = G.fst f := contractVertex_of_ne hne
          have h2 : G.contractVertex f (G.snd f) = G.fst f := by simp [contractVertex]
          rcases hf' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [h1, h2]
          · rw [h1, h2]
        · apply Relation.ReflTransGen.single
          refine ⟨f, Finset.mem_erase.2 ⟨hfe, hf⟩, ?_⟩
          rcases hf' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
    intro a ha b hb
    rw [Finset.mem_erase] at ha hb
    have := key a b (hconn a ha.2 b hb.2)
    rwa [contractVertex_of_ne ha.1, contractVertex_of_ne hb.1] at this

/-- Induction for connected subgraphs: |W|≤|A|+1, Q≥bouquetQ ν and theta(1,2)=bouquetTheta ν, with ν=|A|+1-|W|. -/
theorem connectedOn_bounds :
    ∀ (n : ℕ) (G : Multigraph V E) (A : Finset E) (W : Finset V), W.card = n →
      G.ConnectedOn A W →
      W.card ≤ A.card + 1 ∧ bouquetQ (A.card + 1 - W.card) ≤ G.QOn A ∧
        G.thetaOn A = bouquetTheta (A.card + 1 - W.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G A W hn hc
  rcases Nat.lt_or_ge 1 W.card with hW | hW
  · obtain ⟨e, he, hne⟩ := G.exists_nonloop_of_connectedOn hc hW
    have hc' := connectedOn_contractMap hc he hne
    have hv : G.snd e ∈ W := (hc.2.1 e he).2
    have hcard : (W.erase (G.snd e)).card = W.card - 1 := Finset.card_erase_of_mem hv
    have hAcard : (A.erase e).card = A.card - 1 := Finset.card_erase_of_mem he
    have hA1 : 0 < A.card := Finset.card_pos.2 ⟨e, he⟩
    obtain ⟨h1, h2, h3⟩ := ih (W.card - 1) (by omega) (G.contractMap e) (A.erase e)
      (W.erase (G.snd e)) hcard hc'
    rw [hcard, hAcard] at h1 h2 h3
    have hν : A.card - 1 + 1 - (W.card - 1) = A.card + 1 - W.card := by omega
    rw [hν] at h2 h3
    refine ⟨by omega, h2.trans (contractMap_QOn_le hne he), ?_⟩
    rw [thetaOn_eq_contractMap hne he, h3]
  · have hW1 : W.card = 1 := by have := hc.1.card_pos; omega
    obtain ⟨w₀, rfl⟩ := Finset.card_eq_one.1 hW1
    have hB : G.IsBouquetAt A w₀ := fun e he => by
      have := hc.2.1 e he
      simp only [Finset.mem_singleton] at this
      exact this
    rw [QOn_of_isBouquetAt hB, thetaOn_of_isBouquetAt hB]
    simp

variable [Fintype E] (G : Multigraph V E)

/-- A connected graph satisfies |V|≤|E|+1. -/
theorem card_vertex_le_of_connected (hc : G.Connected) :
    Fintype.card V ≤ Fintype.card E + 1 := by
  have := (connectedOn_bounds _ G Finset.univ Finset.univ rfl hc).1
  simpa using this

/-- Connected-graph cycle rank ν=|E|-|V|+1, written |E|+1-|V| in naturals. -/
def cycleRank (_G : Multigraph V E) : ℕ := Fintype.card E + 1 - Fintype.card V

/-- For a nonempty connected graph, Q(G)≥(ν−1)2^ν+2, expressed using bouquetQ ν. -/
theorem bouquetQ_le_Q_of_connected (hc : G.Connected) : bouquetQ G.cycleRank ≤ G.Q := by
  have := (connectedOn_bounds _ G Finset.univ Finset.univ rfl hc).2.1
  simpa [cycleRank, Q] using this

/-- (ν−1)2^ν+2 ≤ Q(G)。 -/
theorem lower_bound_of_connected (hc : G.Connected) :
    ((G.cycleRank : ℤ) - 1) * 2 ^ G.cycleRank + 2 ≤ (G.Q : ℤ) := by
  rw [← bouquetQ_eq]
  exact_mod_cast G.bouquetQ_le_Q_of_connected hc

/-- For connected G, θ(1,2)=bouquetTheta ν: reduction of the special value to a bouquet. -/
theorem theta_eq_bouquetTheta_of_connected (hc : G.Connected) :
    G.theta = bouquetTheta G.cycleRank := by
  have := (connectedOn_bounds _ G Finset.univ Finset.univ rfl hc).2.2
  simpa [cycleRank, theta] using this

end Multigraph

end BPFixedPoints
