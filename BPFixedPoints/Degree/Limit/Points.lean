import BPFixedPoints.Degree.Equations
import BPFixedPoints.Degree.Limit.VertexRoots

/-!
# The weak-coupling limit system has Q(G) solutions

At t=0, s_e=1+t c_e gives (A_α−F_i)(A_ᾱ+1)=0 (16) and
β_i=F_i^{1−d_i}∏_{e∋i}A_{e,i} (5). With F_i≠0,−1, each edge is either
inactive (A=F_i,B=F_j) or active (A=B=−1) (17).
For active set S the vertex equation is F_i^{d_S(i)−1}=(−1)^{d_S(i)}/β_i (18),
with φ(d_S(i)) roots. Hence there are Σ_S∏_i φ(d_S(i))=Q(G) limit points.
Active coordinates A=B=−1 belong to the auxiliary limit equations and are
not identified with admissible BP solutions at t=0.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E) {K : Type*} [Field K] [DecidableEq K]

/-- Limit solution: F_i≠0,−1, all dart edge equations and all vertex equations. -/
structure IsLimitSolution (β : V → K) (A : Dart E → K) (F : V → K) : Prop where
  ne_zero : ∀ i, F i ≠ 0
  ne_neg_one : ∀ i, F i ≠ -1
  edge : ∀ α, (A α - F (G.tail α)) * (A (rev α) + 1) = 0
  vertex : ∀ i, β i = F i ^ ((1 : ℤ) - G.degree i) * ∏ α ∈ G.inDarts i, A (rev α)

/-- Limit coordinates from support S and F: A=-1 on active edges, A_α=F_tailα on inactive edges. -/
def limitCoords (S : Finset E) (F : V → K) (α : Dart E) : K :=
  if α.1 ∈ S then -1 else F (G.tail α)

/-- Active edge support read from A. -/
def activeSet (A : Dart E → K) : Finset E := Finset.univ.filter fun e => A (e, true) = -1

/-- Number of darts with head i whose underlying edge belongs to S. -/
def activeDeg (S : Finset E) (i : V) : ℕ := ((G.inDarts i).filter fun α => α.1 ∈ S).card

theorem activeDeg_eq_deg (S : Finset E) (i : V) : G.activeDeg S i = G.deg S i := by
  unfold activeDeg inDarts Multigraph.deg
  rw [Finset.filter_filter, Finset.card_filter, Fintype.sum_prod_type]
  rw [← Finset.univ_inter S, ← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  by_cases he : e ∈ S <;> simp [he, head, Multigraph.endCount, add_comm]

theorem deg_le_degree (S : Finset E) (i : V) : G.deg S i ≤ G.degree i := by
  rw [G.degree_eq_deg]
  exact G.deg_mono (Finset.subset_univ S) i

theorem zpow_limit_aux {F : K} (hF : F ≠ 0) {d k : ℕ} (hk : k ≤ d) (c : K) :
    F ^ ((1 : ℤ) - d) * (c * F ^ (d - k)) = c * F ^ ((1 : ℤ) - k) := by
  rw [← zpow_natCast, Nat.cast_sub hk, mul_left_comm, ← zpow_add₀ hF]
  congr 2
  ring

theorem prod_limitCoords (S : Finset E) (F : V → K) (i : V) :
    ∏ α ∈ G.inDarts i, G.limitCoords S F (rev α) =
      (-1) ^ G.activeDeg S i * F i ^ (G.degree i - G.activeDeg S i) := by
  have h : ∀ α ∈ G.inDarts i, G.limitCoords S F (rev α) = if α.1 ∈ S then -1 else F i := by
    intro α hα
    rw [inDarts, Finset.mem_filter] at hα
    unfold limitCoords
    rw [rev_fst, tail_rev, hα.2]
  rw [Finset.prod_congr rfl h, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc := Finset.card_filter_add_card_filter_not (s := G.inDarts i) (fun α => α.1 ∈ S)
  unfold activeDeg degree
  congr 2
  omega

/-- An active edge set S and vertex roots F produce a limit solution (reverse direction). -/
theorem isLimitSolution_limitCoords {β : V → K} (hβ1 : ∀ i, β i ≠ -1) {S : Finset E} {F : V → K}
    (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    G.IsLimitSolution β (G.limitCoords S F) F where
  ne_zero i := (hF i).1
  ne_neg_one i := vertexLimitEq_ne_neg_one (hβ1 i) (hF i)
  edge α := by
    unfold limitCoords
    rw [rev_fst]
    split_ifs <;> ring
  vertex i := by
    rw [G.prod_limitCoords, activeDeg_eq_deg,
      zpow_limit_aux (hF i).1 (G.deg_le_degree S i)]
    exact (hF i).2

section Solution

variable {G} {β : V → K} {A : Dart E → K} {F : V → K}

/-- Each edge is exactly active (A=B=−1) or inactive (A=F_i,B=F_j). -/
theorem IsLimitSolution.edge_cases (h : G.IsLimitSolution β A F) (α : Dart E) :
    (A α = -1 ∧ A (rev α) = -1) ∨ (A α = F (G.tail α) ∧ A (rev α) = F (G.head α)) := by
  have h1 := h.edge α
  have h2 := h.edge (rev α)
  rw [rev_rev, tail_rev] at h2
  rcases mul_eq_zero.1 h1 with h1 | h1
  · rcases mul_eq_zero.1 h2 with h2 | h2
    · exact Or.inr ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩
    · exfalso
      apply h.ne_neg_one (G.tail α)
      rw [← sub_eq_zero.1 h1]
      exact add_eq_zero_iff_eq_neg.1 h2
  · rcases mul_eq_zero.1 h2 with h2 | h2
    · exfalso
      apply h.ne_neg_one (G.head α)
      rw [← sub_eq_zero.1 h2]
      exact add_eq_zero_iff_eq_neg.1 h1
    · exact Or.inl ⟨add_eq_zero_iff_eq_neg.1 h2, add_eq_zero_iff_eq_neg.1 h1⟩

/-- Coordinates of a limit solution are determined by its active edge set. -/
theorem IsLimitSolution.eq_limitCoords (h : G.IsLimitSolution β A F) :
    A = G.limitCoords (activeSet A) F := by
  funext α
  unfold limitCoords activeSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h.edge_cases α with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have ht : A (α.1, true) = -1 := by
      rcases α with ⟨e, _ | _⟩
      · exact h2
      · exact h1
    simp only [ht, ite_true]
    exact h1
  · have ht : A (α.1, true) ≠ -1 := by
      rcases α with ⟨e, _ | _⟩
      · rw [show (e, true) = rev (e, false) from rfl, h2]; exact h.ne_neg_one _
      · rw [h1]; exact h.ne_neg_one _
    simp only [ht, ite_false]
    exact h1

/-- The vertex equation of a limit solution is equation (18), with active degree d_S(i). -/
theorem IsLimitSolution.vertexLimitEq (h : G.IsLimitSolution β A F) (i : V) :
    VertexLimitEq (G.deg (activeSet A) i) (β i) (F i) := by
  refine ⟨h.ne_zero i, ?_⟩
  have hv := h.vertex i
  have hA := h.eq_limitCoords
  rw [hA, G.prod_limitCoords, activeDeg_eq_deg,
    zpow_limit_aux (h.ne_zero i) (G.deg_le_degree _ i)] at hv
  exact hv

theorem activeSet_limitCoords {β : V → K} (hβ1 : ∀ i, β i ≠ -1) {S : Finset E} {F : V → K}
    (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    activeSet (G.limitCoords S F) = S := by
  ext e
  rw [activeSet, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    by_contra he
    unfold limitCoords at h
    simp only [he, ite_false] at h
    exact vertexLimitEq_ne_neg_one (hβ1 _) (hF _) h
  · intro he
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold limitCoords
    simp [he]

end Solution

/-- Set of limit-system solutions. -/
def LimitSolutions (β : V → K) : Type _ :=
  {p : (Dart E → K) × (V → K) // G.IsLimitSolution β p.1 p.2}

/-- An active support S together with a root at each vertex. -/
def LimitParams (β : V → K) : Type _ :=
  {q : Finset E × (V → K) // ∀ i, VertexLimitEq (G.deg q.1 i) (β i) (q.2 i)}

/-- Equivalence between limit solutions and pairs of an active support and vertex roots. -/
def limitSolutionsEquiv (β : V → K) (hβ1 : ∀ i, β i ≠ -1) :
    G.LimitSolutions β ≃ G.LimitParams β where
  toFun p := ⟨(activeSet p.1.1, p.1.2), fun i => p.2.vertexLimitEq i⟩
  invFun q := ⟨(G.limitCoords q.1.1 q.1.2, q.1.2), G.isLimitSolution_limitCoords hβ1 q.2⟩
  left_inv p := by
    obtain ⟨⟨A, F⟩, h⟩ := p
    apply Subtype.ext
    simp only
    rw [← h.eq_limitCoords]
  right_inv q := by
    obtain ⟨⟨S, F⟩, h⟩ := q
    apply Subtype.ext
    simp only
    rw [activeSet_limitCoords hβ1 h]

/-- The limit system has Q(G) solutions over algebraically closed characteristic-zero K with β_i≠0,−1. -/
theorem card_limitSolutions [IsAlgClosed K] [CharZero K] (β : V → K) (hβ0 : ∀ i, β i ≠ 0)
    (hβ1 : ∀ i, β i ≠ -1) : Nat.card (G.LimitSolutions β) = G.Q := by
  rw [Nat.card_congr (G.limitSolutionsEquiv β hβ1)]
  unfold LimitParams
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun S : Finset E => fun F : V → K => ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)))]
  have : ∀ S : Finset E, ∀ i : V, Finite {x : K // VertexLimitEq (G.deg S i) (β i) x} :=
    fun S i => finite_vertexLimitEq K _ _ (hβ0 i) (hβ1 i)
  have : ∀ S : Finset E,
      Finite {F : V → K // ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)} :=
    fun S => Finite.of_equiv _ (Equiv.subtypePiEquivPi
      (p := fun i (x : K) => VertexLimitEq (G.deg S i) (β i) x)).symm
  rw [Nat.card_sigma]
  unfold Q QOn wt
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun i (x : K) => VertexLimitEq (G.deg S i) (β i) x)), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact card_vertexLimitEq K _ _ (hβ0 i) (hβ1 i)

end Multigraph

end BPFixedPoints
