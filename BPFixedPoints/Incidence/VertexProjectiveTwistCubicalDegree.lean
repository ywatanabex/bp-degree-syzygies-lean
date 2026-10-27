import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalComparison

/-! # Original overlap-degree submodules of actual cubical sections -/

namespace BPFixedPoints.ProjectiveLine
open CechProduct
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original overlap-degree part, defined directly on the actual face sections. -/
noncomputable def vertexTwistCubicalDegree (a : V → ℤ) (n : ℤ) :
    Submodule R (VertexTwistCubicalSections R V a) where
  carrier := {x | VertexTwistCubicalHomogeneous R V a n x}
  zero_mem' := by intro q _; rfl
  add_mem' := by
    intro x y hx hy q hq
    change x q + y q = 0
    rw [hx q hq,hy q hq,add_zero]
  smul_mem' := by
    intro r x hx q hq
    change r • x q = 0
    rw [hx q hq,smul_zero]

/-- The specified existing signed chain comparison retains precisely each original degree submodule. -/
theorem vertexTwistCubicalDegree_chain (d : V → ℕ) (n : ℤ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    vertexTwistCubicalChainEquiv R V d x ∈ Finsupp.supported R R {b | (cechDegree b : ℤ) = n} ↔
      x ∈ vertexTwistCubicalDegree R V (fun v => -(d v : ℤ)) n :=
  vertexTwistCubicalChainEquiv_degree R V d n x

end BPFixedPoints.ProjectiveLine
