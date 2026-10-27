import BPFixedPoints.Incidence.CechProductCupLaws
import BPFixedPoints.Incidence.VertexProjectiveTwistCellStates

/-!
# Cup product laws on state degree pieces

The state module of a twist vector is concentrated in the cohomological degree of
that twist, so a state degree piece is either the whole state module or zero. The
cup product maps degree pieces to the piece of the summed degree, the unit lies in
degree zero, and graded commutativity holds with the sign (−1)^(i*j) of the two
piece degrees.
-/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type) [CommRing R] {V : Type} [Fintype V]

/-- A state degree piece of a degree other than that of the twist is zero. -/
theorem eq_zero_of_mem_stateDegreePiece {d : V → ℕ} {n : ℕ} {x : H R d}
    (hx : x ∈ stateDegreePiece R d n) (hn : cohomologyDegree d ≠ n) : x = 0 := by
  ext κ
  by_contra hκ
  have h := (mem_supported R x).mp hx (mem_support_iff.mpr hκ)
  exact hn (by exact_mod_cast h)

/-- The state degree piece of the twist's own degree is the whole state module. -/
theorem mem_stateDegreePiece_self (d : V → ℕ) (x : H R d) :
    x ∈ stateDegreePiece R d (cohomologyDegree d) :=
  (mem_supported R x).mpr fun _ _ => rfl

/-- Cohomological degrees add when no vertex has both twists positive. -/
theorem cohomologyDegree_add_of_disjoint (d e : V → ℕ) (h : ∀ v, ¬ (0 < d v ∧ 0 < e v)) :
    cohomologyDegree (d + e) = cohomologyDegree d + cohomologyDegree e := by
  unfold cohomologyDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv := h v
  simp only [Pi.add_apply, lineCohomologyDegree]
  split_ifs <;> omega

/-- The cohomology unit lies in the state degree piece of degree zero. -/
theorem cohomologyUnit_mem_stateDegreePiece :
    cohomologyUnit R ∈ stateDegreePiece R (0 : V → ℕ) 0 := by
  have h0 : cohomologyDegree (0 : V → ℕ) = 0 := by
    simp [cohomologyDegree, lineCohomologyDegree]
  simpa only [h0] using mem_stateDegreePiece_self R (0 : V → ℕ) (cohomologyUnit R)

/-- The cup product maps state degree pieces to the piece of the summed degree. -/
theorem cohomologyCup_mem_stateDegreePiece (d e : V → ℕ) {i j : ℕ} {x : H R d} {y : H R e}
    (hx : x ∈ stateDegreePiece R d i) (hy : y ∈ stateDegreePiece R e j) :
    cohomologyCup R d e x y ∈ stateDegreePiece R (d + e) (i + j) := by
  by_cases hi : cohomologyDegree d = i
  · by_cases hj : cohomologyDegree e = j
    · by_cases hov : ∃ v, 0 < d v ∧ 0 < e v
      · obtain ⟨v, hdv, hev⟩ := hov
        rw [cohomologyCup_eq_zero_of_overlap R d e v hdv hev]
        exact Submodule.zero_mem _
      · have hdisj : ∀ v, ¬ (0 < d v ∧ 0 < e v) := fun v hv => hov ⟨v, hv⟩
        rw [← hi, ← hj, ← cohomologyDegree_add_of_disjoint d e hdisj]
        exact mem_stateDegreePiece_self R _ _
    · rw [eq_zero_of_mem_stateDegreePiece R hy hj, map_zero]
      exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_stateDegreePiece R hx hi, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- Graded commutativity on state degree pieces: swapping factors of degrees i and j
multiplies by (−1)^(i*j), after transport along `add_comm`. -/
theorem cohomologyCup_comm_of_mem_stateDegreePiece (d e : V → ℕ) {i j : ℕ}
    {x : H R d} {y : H R e}
    (hx : x ∈ stateDegreePiece R d i) (hy : y ∈ stateDegreePiece R e j) :
    cohomologyCup R e d y x =
      (-1 : R) ^ (i * j) • castH R (add_comm d e) (cohomologyCup R d e x y) := by
  by_cases hi : cohomologyDegree d = i
  · by_cases hj : cohomologyDegree e = j
    · subst hi hj
      exact cohomologyCup_comm R d e x y
    · rw [eq_zero_of_mem_stateDegreePiece R hy hj]
      simp
  · rw [eq_zero_of_mem_stateDegreePiece R hx hi]
    simp

end BPFixedPoints.CechProduct
