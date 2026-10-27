import BPFixedPoints.StateSum.Basic
import BPFixedPoints.StateSum.DeletionContraction

/-!
# Small graph examples and values of Q

Specify multigraphs on Fin n using `![...]` and compute Q and θ with `decide`;
the default evaluator produces proofs checked by the kernel, without `native_decide`.
Paper examples are C₃ (`ex:triangle-admissible` and the §3 table), K₄ (introduction,
§3 and `fig:k4-states`) and the bowtie of two triangles sharing one vertex
(§3 table). Paths, parallel edges and a square check the lemmas.
Increase `maxRecDepth` globally because evaluation can exceed the default 512.
Examples absent from the paper and Tutte computations using `native_decide`
are excluded from this project.
-/

set_option maxRecDepth 20000

namespace BPFixedPoints.Examples

open Multigraph

/-! ## Concrete graphs -/

/-- One isolated vertex and no edges. -/
def single : Multigraph (Fin 1) (Fin 0) where
  fst := ![]
  snd := ![]

/-- Path 0-1-2, a tree on three vertices. -/
def path3 : Multigraph (Fin 3) (Fin 2) where
  fst := ![0, 1]
  snd := ![1, 2]

/-- Two parallel edges joining two vertices. -/
def parallel2 : Multigraph (Fin 2) (Fin 2) where
  fst := ![0, 0]
  snd := ![1, 1]

/-- Triangle C₃. -/
def triangle : Multigraph (Fin 3) (Fin 3) where
  fst := ![0, 1, 2]
  snd := ![1, 2, 0]

/-- Square C₄. -/
def square : Multigraph (Fin 4) (Fin 4) where
  fst := ![0, 1, 2, 3]
  snd := ![1, 2, 3, 0]

/-- Bowtie: triangles {0,1,2} and {0,3,4} sharing vertex 0. -/
def bowtie : Multigraph (Fin 5) (Fin 6) where
  fst := ![0, 1, 2, 0, 3, 4]
  snd := ![1, 2, 0, 3, 4, 0]

/-- Complete graph K₄. -/
def K4 : Multigraph (Fin 4) (Fin 6) where
  fst := ![0, 0, 0, 1, 1, 2]
  snd := ![1, 2, 3, 2, 3, 3]

/-!
## Values of Q and theta

All proved with `decide`.
-/

theorem single_Q : single.Q = 1 := by decide
theorem path3_Q : path3.Q = 1 := by decide
theorem parallel2_Q : parallel2.Q = 2 := by decide
theorem triangle_Q : triangle.Q = 2 := by decide
theorem square_Q : square.Q = 2 := by decide
theorem bowtie_Q : bowtie.Q = 6 := by decide
theorem K4_Q : K4.Q = 48 := by decide
theorem K4_theta : K4.theta = 48 := by decide

end BPFixedPoints.Examples
