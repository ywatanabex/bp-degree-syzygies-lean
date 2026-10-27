import BPFixedPoints.StateSum.Theta

/-!
# The 2-core: iterative pruning equals the union of generalized loops

The usual 2-core removes degree-zero/one vertices repeatedly; `core A` is the
union of generalized loops in A. `PruneStep A B` removes the edge incident to
a degree-one vertex (degree-zero removal leaves the edge set unchanged).
`IsPruned A P` means a finite pruning sequence reaches P with no degree-one
vertices. A terminal state exists (`exists_isPruned`) and equals `core A`
regardless of removal order (`isPruned_iff`). A generalized loop survives each
step, since an incident selected edge would force d_S(v)≥2>d_A(v).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] (G : Multigraph V E)

/-- One pruning step removes the edge at a vertex of degree one in A. -/
def PruneStep (A B : Finset E) : Prop :=
  ∃ v, G.deg A v = 1 ∧ B = A.filter fun e => ¬ G.Incident e v

/-- Terminal pruning state: P is reachable from A by pruning and has no degree-one vertex. -/
def IsPruned (A P : Finset E) : Prop :=
  Relation.ReflTransGen G.PruneStep A P ∧ G.IsGenLoop P

theorem subset_of_pruneStep {A B : Finset E} (h : G.PruneStep A B) : B ⊆ A := by
  obtain ⟨v, -, rfl⟩ := h
  exact Finset.filter_subset _ _

theorem subset_of_reflTransGen {A B : Finset E} (h : Relation.ReflTransGen G.PruneStep A B) :
    B ⊆ A := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (G.subset_of_pruneStep hstep).trans ih

/-- Generalized loops survive a pruning step. -/
theorem genLoop_subset_of_pruneStep {S A B : Finset E} (hS : G.IsGenLoop S) (hSA : S ⊆ A)
    (h : G.PruneStep A B) : S ⊆ B := by
  obtain ⟨v, hv, rfl⟩ := h
  intro e he
  refine Finset.mem_filter.2 ⟨hSA he, fun hinc => ?_⟩
  have h1 : 1 ≤ G.deg S v := by
    have : G.endCount e v ≠ 0 := fun h0 => (G.endCount_eq_zero_iff e v).1 h0 hinc
    calc 1 ≤ G.endCount e v := Nat.one_le_iff_ne_zero.2 this
      _ ≤ G.deg S v := Finset.single_le_sum (f := fun e => G.endCount e v)
          (fun _ _ => Nat.zero_le _) he
  have h2 : G.deg S v ≤ 1 := hv ▸ G.deg_mono hSA v
  exact hS v (le_antisymm h2 h1)

theorem genLoop_subset_of_reflTransGen {S A B : Finset E} (hS : G.IsGenLoop S) (hSA : S ⊆ A)
    (h : Relation.ReflTransGen G.PruneStep A B) : S ⊆ B := by
  induction h with
  | refl => exact hSA
  | tail _ hstep ih => exact G.genLoop_subset_of_pruneStep hS ih hstep

/-- **Every terminal pruning state is the 2-core**, independently of the removal order. -/
theorem eq_core_of_isPruned {A P : Finset E} (h : G.IsPruned A P) : P = G.core A := by
  apply le_antisymm
  · exact G.subset_core (G.subset_of_reflTransGen h.1) h.2
  · exact G.genLoop_subset_of_reflTransGen (G.isGenLoop_core A) (G.core_subset A) h.1

/-- A terminal pruning state exists. -/
theorem exists_isPruned (A : Finset E) : ∃ P, G.IsPruned A P := by
  induction h : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    by_cases hA : G.IsGenLoop A
    · exact ⟨A, Relation.ReflTransGen.refl, hA⟩
    · obtain ⟨v, hv⟩ := G.exists_deg_eq_one_of_not_isGenLoop hA
      set B := A.filter fun e => ¬ G.Incident e v with hB
      have hlt : B.card < A.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
        have hzero : G.deg A v = 0 := by
          rw [deg_eq_zero_iff]
          intro e he
          exact (Finset.mem_filter.1 (hsub he)).2
        omega
      obtain ⟨P, hP⟩ := ih B.card (h ▸ hlt) B rfl
      exact ⟨P, Relation.ReflTransGen.head ⟨v, hv, rfl⟩ hP.1, hP.2⟩

/-- **Equivalence of 2-core definitions.** P is a terminal pruning state of A iff P=core A. -/
theorem isPruned_iff {A P : Finset E} : G.IsPruned A P ↔ P = G.core A := by
  constructor
  · exact G.eq_core_of_isPruned
  · rintro rfl
    obtain ⟨P, hP⟩ := G.exists_isPruned A
    rwa [← G.eq_core_of_isPruned hP]

end Multigraph

end BPFixedPoints
