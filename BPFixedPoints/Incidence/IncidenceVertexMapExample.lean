import BPFixedPoints.Incidence.IncidenceVertexMapCycleScalars

/-!
# A vertex map identifying vertices of two disjoint cycles

The graph `twoTwoCycles` has the vertices `0, 1, 2, 3` and the edges `0, 1` between `0` and `1` and
`2, 3` between `2` and `3`: two vertex-disjoint cycles `C = {0, 1}` and `D = {2, 3}` of length two.
The vertex function `mergeOneTwo = ![0, 1, 1, 2]` identifies the vertex `1` of `C` with the vertex
`2` of `D`; the target graph is `twoTwoCycles.pushVertices mergeOneTwo`, where both cycles pass
through the vertex `1`. It is noncontracting (`mergeOneTwoMap_isNoncontracting`).

* `z_C z_D ≠ 0` in the cycle-compatibility algebra of `twoTwoCycles`, and its image is zero
  (`twoTwoCycles_acceptance`).
* The vertex function is injective on the vertices of `C`, so `z_C` goes to a nonzero multiple of
  `z_C` in the target (`mergeOneTwo_cycleC`).

The simple-cycle and support conditions are checked by `decide`.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-- Two vertex-disjoint cycles of length two: edges `0, 1` join `0` and `1`, edges `2, 3` join `2`
and `3`. -/
def twoTwoCycles : Multigraph (Fin 4) (Fin 4) where
  fst e := if e.val < 2 then 0 else 2
  snd e := if e.val < 2 then 1 else 3

/-- The vertex function identifying the vertex `1` with the vertex `2`. -/
def mergeOneTwo : Fin 4 → Fin 3 := ![0, 1, 1, 2]

/-- The vertex map of `mergeOneTwo` onto the graph with pushed-forward endpoints. -/
def mergeOneTwoMap : VertexMap twoTwoCycles (twoTwoCycles.pushVertices mergeOneTwo) :=
  VertexMap.ofFun twoTwoCycles mergeOneTwo

/-- The vertex map identifies no two endpoints of an edge. -/
theorem mergeOneTwoMap_isNoncontracting : mergeOneTwoMap.IsNoncontracting := by
  unfold VertexMap.IsNoncontracting
  decide

/-- The edges `0, 1` form a simple cycle. -/
theorem twoTwoCycles_isSimpleCycle_C : twoTwoCycles.IsSimpleCycle ({0, 1} : Finset (Fin 4)) := by
  decide

/-- The edges `2, 3` form a simple cycle. -/
theorem twoTwoCycles_isSimpleCycle_D : twoTwoCycles.IsSimpleCycle ({2, 3} : Finset (Fin 4)) := by
  decide

/-- The simple cycle `C = {0, 1}`. -/
def twoTwoCyclesC : twoTwoCycles.SimpleCycle := ⟨{0, 1}, twoTwoCycles_isSimpleCycle_C⟩

/-- The simple cycle `D = {2, 3}`. -/
def twoTwoCyclesD : twoTwoCycles.SimpleCycle := ⟨{2, 3}, twoTwoCycles_isSimpleCycle_D⟩

/-- **Acceptance example.** `z_C z_D` is nonzero in the cycle-compatibility algebra of the two
disjoint cycles, and identifying a vertex of `C` with a vertex of `D` sends it to zero. -/
theorem twoTwoCycles_acceptance :
    Ideal.Quotient.mk twoTwoCycles.cycleCompatibilityIdeal (X twoTwoCyclesC * X twoTwoCyclesD) ≠ 0 ∧
      mergeOneTwoMap.cycleAlgebraHom
        (Ideal.Quotient.mk twoTwoCycles.cycleCompatibilityIdeal
          (X twoTwoCyclesC * X twoTwoCyclesD)) = 0 :=
  mergeOneTwoMap.cycleAlgebraHom_acceptance twoTwoCyclesC twoTwoCyclesD (by decide) (c := 1)
    (d := 2) (by decide) (by decide) rfl

/-- The vertex function is injective on the vertices of `C`. -/
theorem mergeOneTwo_injOn_C :
    Set.InjOn mergeOneTwoMap.vertex (twoTwoCycles.support twoTwoCyclesC.val) := by
  intro a ha b hb h
  have ha' : a ∈ twoTwoCycles.support ({0, 1} : Finset (Fin 4)) := ha
  have hb' : b ∈ twoTwoCycles.support ({0, 1} : Finset (Fin 4)) := hb
  revert ha' hb' h
  revert a b
  decide

/-- The cycle `C` keeps its vertices apart, so `z_C` goes to a nonzero multiple of `z_C`. -/
theorem mergeOneTwo_cycleC : ∃ c : ℂ, c ≠ 0 ∧
    mergeOneTwoMap.cycleAlgebraHom
        (Ideal.Quotient.mk twoTwoCycles.cycleCompatibilityIdeal (X twoTwoCyclesC)) =
      c • Ideal.Quotient.mk (twoTwoCycles.pushVertices mergeOneTwo).cycleCompatibilityIdeal
        (X (mergeOneTwoMap.mapCycle twoTwoCyclesC mergeOneTwo_injOn_C)) :=
  mergeOneTwoMap.exists_ne_zero_cycleAlgebraHom_X twoTwoCyclesC mergeOneTwo_injOn_C

end BPFixedPoints.Multigraph
