import BPFixedPoints.Incidence.IncidenceVertexMapSupport
import BPFixedPoints.Incidence.IncidenceVertexMapCycleScalars

/-!
# Degree zero as a special case of collision vanishing

Collision vanishing (`VertexMap.incidenceTorMap_eq_zero_of_not_injOn`, in
`IncidenceVertexMapSupport`) holds in every homological degree. In degree zero it recovers the
vanishing statements of `IncidenceVertexMapCycles` without the cycle-specific argument there:
* the degree-zero class of every edge set `S` lies in the edge-set piece of `S`
  (`cycleUnionClass_mem_edgeSetPiece`), so it is killed whenever the vertex function is not
  injective on `G.support S` (`incidenceTorMap_cycleUnionClass_eq_zero_of_not_injOn`; it requires
  neither that `S` be a cycle union nor two explicit identified vertices);
* `z_C ↦ 0` when the vertex function is not injective on the vertices of the simple cycle `C`
  (`cycleAlgebraHom_X_eq_zero_of_collision`), which is the vanishing direction of
  `cycleAlgebraHom_X_eq_zero_iff`; the other direction still uses the nonvanishing of the cycle
  scalar from `IncidenceVertexMapCycleScalars` (`cycleAlgebraHom_X_eq_zero_iff_collision`);
* the vanishing half of the acceptance example: if the vertex function identifies a vertex of `C`
  with a vertex of `D`, then `z_C z_D ↦ 0`; for vertex-disjoint cycles the product is a multiple of
  the class of `C ∪ D`, on whose support the vertex function collides
  (`cycleAlgebraHom_X_mul_X_eq_zero_of_collision`, `cycleAlgebraHom_acceptance_of_collision`).

Not covered here: the value `±1` of the cycle scalar.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp MvPolynomial

section CycleUnionPieces

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The degree-zero class of an edge set lies in the edge-set piece of that edge set. -/
theorem cycleUnionClass_mem_edgeSetPiece (S : Finset E) :
    G.cycleUnionClass S ∈ G.incidenceTorEdgeSetPiece 0 S := by
  by_cases hS : G.IsCycleUnion S
  · exact G.mem_incidenceTorEdgeSetPiece_of_fullState_single
      (G.incidenceTorFullState_cycleUnionClass hS)
  · rw [G.cycleUnionClass_of_not hS]
    exact Submodule.zero_mem _

/-- A vertex in the support of an edge set lies in the support of every larger edge set. -/
theorem mem_support_of_subset {S T : Finset E} (h : S ⊆ T) {v : V} (hv : v ∈ G.support S) :
    v ∈ G.support T := by
  rw [mem_support_iff] at hv ⊢
  exact lt_of_lt_of_le hv (G.deg_mono h v)

end CycleUnionPieces

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- **Degree-zero collision vanishing.** If the vertex function is not injective on the support of
an edge set `S`, the degree-zero Tor map kills the class of `S`. This is collision vanishing at
`p = 0`. -/
theorem incidenceTorMap_cycleUnionClass_eq_zero_of_not_injOn {S : Finset E}
    (h : ¬ Set.InjOn φ.vertex (G.support S)) :
    φ.incidenceTorMap 0 (G.cycleUnionClass S) = 0 :=
  φ.incidenceTorMap_eq_zero_of_not_injOn h (G.cycleUnionClass_mem_edgeSetPiece S)

/-- **`z_C ↦ 0` from collision vanishing.** If the vertex function is not injective on the vertices
of the simple cycle `C`, then `z_C` goes to zero. -/
theorem cycleAlgebraHom_X_eq_zero_of_collision (C : G.SimpleCycle)
    (h : ¬ Set.InjOn φ.vertex (G.support C.val)) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) = 0 := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_X, map_zero]
  exact φ.incidenceTorMap_cycleUnionClass_eq_zero_of_not_injOn h

/-- `cycleAlgebraHom_X_eq_zero_iff`, with the vanishing direction obtained from collision
vanishing; the other direction is the nonvanishing of the cycle scalar. -/
theorem cycleAlgebraHom_X_eq_zero_iff_collision (C : G.SimpleCycle) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) = 0 ↔
      ¬ Set.InjOn φ.vertex (G.support C.val) :=
  ⟨(φ.cycleAlgebraHom_X_eq_zero_iff C).mp, φ.cycleAlgebraHom_X_eq_zero_of_collision C⟩

/-- **Products under an identification, from collision vanishing.** If the vertex function sends a
vertex of `C` and a vertex of `D` to the same vertex, then `z_C z_D ↦ 0`. For vertex-disjoint
cycles the product is a multiple of the class of `C ∪ D`, and the two identified vertices are
distinct vertices of the support of `C ∪ D`; otherwise the product is already zero. -/
theorem cycleAlgebraHom_X_mul_X_eq_zero_of_collision (C D : G.SimpleCycle) {c d : V}
    (hc : c ∈ G.support C.val) (hd : d ∈ G.support D.val) (h : φ.vertex c = φ.vertex d) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D)) = 0 := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, map_mul, map_mul, map_zero, cycleAlgebraEquivTor_X,
    cycleAlgebraEquivTor_X]
  by_cases hCD : Disjoint (G.support C.val) (G.support D.val)
  · rw [cycleClass, cycleClass,
      G.cycleUnionClass_mul_of_disjoint C.property.isCycleUnion D.property.isCycleUnion hCD,
      map_smul]
    have hne : c ≠ d := fun hcd => Finset.disjoint_left.mp hCD hc (hcd ▸ hd)
    have hcol : ¬ Set.InjOn φ.vertex (G.support (C.val ∪ D.val)) := fun hinj =>
      hne (hinj (G.mem_support_of_subset Finset.subset_union_left hc)
        (G.mem_support_of_subset Finset.subset_union_right hd) h)
    rw [φ.incidenceTorMap_cycleUnionClass_eq_zero_of_not_injOn hcol, smul_zero]
  · rw [cycleClass, cycleClass, G.cycleUnionClass_mul_of_not_disjoint hCD, map_zero]

/-- **Acceptance example, vanishing half from collision vanishing.** For vertex-disjoint simple
cycles `C` and `D` and a vertex function identifying a vertex of `C` with a vertex of `D`, the
product `z_C z_D` is nonzero and goes to zero. -/
theorem cycleAlgebraHom_acceptance_of_collision (C D : G.SimpleCycle)
    (hCD : Disjoint (G.support C.val) (G.support D.val)) {c d : V} (hc : c ∈ G.support C.val)
    (hd : d ∈ G.support D.val) (h : φ.vertex c = φ.vertex d) :
    Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D) ≠ 0 ∧
      φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D)) = 0 :=
  ⟨cycleAlgebra_X_mul_X_ne_zero C D hCD, φ.cycleAlgebraHom_X_mul_X_eq_zero_of_collision C D hc hd h⟩

end VertexMap

end BPFixedPoints.Multigraph
