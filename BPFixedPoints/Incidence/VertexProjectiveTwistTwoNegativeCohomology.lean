import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1Kernel
import BPFixedPoints.Incidence.VertexProjectiveTwistH0States
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH2Piece

/-! # Actual two-vertex negative cohomology is concentrated in degree two -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance twoNegativeCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Every actual degree outside two vanishes for the original strictly negative two-vertex twists. -/
theorem vertexTwistTwoNegative_cohomology_eq_zero (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (n : ℕ) (hn : n ≠ 2)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H n) : x = 0 := by
  rcases n with _ | _ | _ | k
  · exact vertexTwistH0_eq_zero_of_pos R (Fin 2) d 0 (hd 0) x
  · exact vertexTwistTwoH1_eq_zero_of_pos R d (hd 0) (hd 1) x
  · exact (hn rfl).elim
  · have he : Fintype.card (Fin 2)+k+1 = k+3 := by simp; omega
    have hz := vertexTwistSheaf_higher_cohomology_eq_zero R (Fin 2) (fun v => -(d v : ℤ)) k
    rw [he] at hz
    exact hz x

/-- A degree-one factor annihilates every actual group when both original twist entries are negative. -/
theorem vertexTwistTwoNegative_cohomology_eq_zero_of_one (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (v : Fin 2) (hv : d v = 1) (n : ℕ)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H n) : x = 0 := by
  by_cases hn : n = 2
  · subst n
    exact vertexTwistTwoH2_eq_zero_of_one_all R d v hv x
  · exact vertexTwistTwoNegative_cohomology_eq_zero R d hd n hn x

/-- The original twist (-1,-2) has zero actual cohomology in every degree. -/
theorem vertexTwistTwo_minus_one_minus_two_cohomology_eq_zero (n : ℕ)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (![-1,-2] : Fin 2 → ℤ)).H n) : x = 0 := by
  let d : Fin 2 → ℕ := ![1,2]
  have ha : (fun v => -(d v : ℤ)) = (![-1,-2] : Fin 2 → ℤ) := by
    funext v
    fin_cases v <;> norm_num [d]
  have hz := vertexTwistTwoNegative_cohomology_eq_zero_of_one R d (by
    intro v; fin_cases v <;> norm_num [d]) 0 rfl n
  rw [ha] at hz
  exact hz x

end BPFixedPoints.ProjectiveLine
