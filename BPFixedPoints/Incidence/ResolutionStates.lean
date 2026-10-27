import BPFixedPoints.Incidence.Ring

/-!
# Actual free-basis indices of the incidence resolution

Index basis elements by an edge subset and a Laurent cohomology monomial at
each vertex. Existing state-sum combinatorics gives the degree range and a
nonempty top degree.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Monomial exponents of an edge section on the zero chart. -/
def incSectionLeft (e : E) (α β : Fin 2) (v : V) : ℕ :=
  (if G.fst e = v then α.val else 0) + (if G.snd e = v then β.val else 0)

/-- Monomial exponents of the same section on the infinity chart. -/
def incSectionRight (e : E) (α β : Fin 2) (v : V) : ℕ :=
  (if G.fst e = v then 1 - α.val else 0) + (if G.snd e = v then 1 - β.val else 0)

theorem incSection_sum (e : E) (α β : Fin 2) (v : V) :
    G.incSectionLeft e α β v + G.incSectionRight e α β v = G.endCount e v := by
  have hα := α.isLt
  have hβ := β.isLt
  unfold incSectionLeft incSectionRight endCount
  split_ifs <;> omega

theorem deg_eq_erase_add_endCount {S : Finset E} {e : E} (he : e ∈ S) (v : V) :
    G.deg S v = G.deg (S.erase e) v + G.endCount e v := by
  simpa only [Finset.insert_erase he] using
    G.deg_insert (Finset.notMem_erase e S) v

theorem incSection_sum_le_degree {S : Finset E} {e : E} (he : e ∈ S)
    (α β : Fin 2) (v : V) :
    G.incSectionLeft e α β v + G.incSectionRight e α β v ≤ G.deg S v := by
  rw [G.incSection_sum, G.deg_eq_erase_add_endCount he v]
  omega

theorem degree_sub_incSection {S : Finset E} {e : E} (he : e ∈ S)
    (α β : Fin 2) :
    (fun v => G.deg S v - (G.incSectionLeft e α β v + G.incSectionRight e α β v)) =
      G.deg (S.erase e) := by
  funext v
  rw [G.incSection_sum, G.deg_eq_erase_add_endCount he v, Nat.add_sub_cancel]

/-- Free basis of the minimal model; states with a degree-one vertex have no basis elements. -/
abbrev IncResolutionBasis := Σ S : Finset E, (v : V) → Fin (phi (G.deg S v))

/-- Homological degree of a basis element. -/
def incResolutionDegree (b : G.IncResolutionBasis) : ℕ :=
  b.1.card - (G.support b.1).card

theorem incResolutionBasis_contributing (b : G.IncResolutionBasis) :
    G.IsContributing b.1 := by
  intro v hv
  have h := (b.2 v).isLt
  simp [hv, phi] at h

theorem incResolutionBasis_card_support_le (b : G.IncResolutionBasis) :
    (G.support b.1).card ≤ b.1.card :=
  G.card_support_le_of_isContributing (G.incResolutionBasis_contributing b)

theorem incResolutionDegree_le (b : G.IncResolutionBasis) :
    G.incResolutionDegree b ≤ G.rho := by
  have h := G.card_le_card_support_add_rho (G.incResolutionBasis_contributing b)
  unfold incResolutionDegree
  omega

theorem exists_incResolutionDegree_top :
    ∃ b : G.IncResolutionBasis, G.incResolutionDegree b = G.rho := by
  classical
  obtain ⟨S, hS, hcard⟩ := G.exists_isContributing_card_eq
  have hpos : ∀ v, 0 < phi (G.deg S v) := by
    intro v
    have hv := hS v
    cases hd : G.deg S v with
    | zero => simp [phi]
    | succ n =>
      have hn : 0 < n := by omega
      simpa only [phi] using hn
  refine ⟨⟨S, fun v => ⟨0, hpos v⟩⟩, ?_⟩
  change S.card - (G.support S).card = G.rho
  omega

end BPFixedPoints.Multigraph
