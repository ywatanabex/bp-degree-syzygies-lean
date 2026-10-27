import BPFixedPoints.Incidence.IncidenceFaceDiagram
import BPFixedPoints.Incidence.CechFaceIntersection

/-! # Genuine intersections of incidence localization opens

The image of a face restriction is the principal open cut out by the product of
its newly inverted coordinates. For faces with a common parent, the join gives
exactly the intersection of their images.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Product formula in the actual quotient, rather than only its ambient polynomial ring. -/
theorem incidenceRefinementDen_eq_prod {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceRefinementDen h = ∏ v, if q v = r v then 1
      else Ideal.Quotient.mk (G.incFaceIdeal q) (C (faceVariable ℂ q v)) := by
  rw [incidenceRefinementDen, refinementDen_eq_prod]
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro v _
  split_ifs <;> simp

theorem incidenceRefinementDen_not_mem {q r : V → Fin 3} (h : FaceRefines q r)
    (x : PrimeSpectrum (G.IncFaceRing q)) :
    G.incidenceRefinementDen h ∉ x.asIdeal ↔
      ∀ v, q v ≠ r v →
        Ideal.Quotient.mk (G.incFaceIdeal q) (C (faceVariable ℂ q v)) ∉ x.asIdeal := by
  rw [G.incidenceRefinementDen_eq_prod]
  simp only [Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
  apply forall_congr'
  intro v
  by_cases hv : q v = r v <;> simp [hv, x.isPrime.one_notMem]

/-- The image of the actual scheme map is exactly its expected localization open. -/
theorem incidenceFaceMap_mem_range {q r : V → Fin 3} (h : FaceRefines q r)
    (x : G.incidenceAffineFace q) :
    x ∈ Set.range (G.incidenceFaceMap h) ↔ G.incidenceRefinementDen h ∉ x.asIdeal := by
  letI := G.incidenceRefinementAlgebra h
  haveI := G.incidenceRefinement_isLocalization h
  have he : Set.range (G.incidenceFaceMap h) =
      (PrimeSpectrum.basicOpen (G.incidenceRefinementDen h) : Set (PrimeSpectrum (G.IncFaceRing q))) :=
    PrimeSpectrum.localization_away_comap_range (G.IncFaceRing r) (G.incidenceRefinementDen h)
  rw [he]
  rfl

/-- The expected higher face is exactly the intersection, including points
outside the common all-Laurent torus. -/
theorem incidenceFaceMap_join_range {p q r : V → Fin 3}
    (hq : FaceRefines p q) (hr : FaceRefines p r) :
    Set.range (G.incidenceFaceMap (faceRefines_join hq hr)) =
      Set.range (G.incidenceFaceMap hq) ∩ Set.range (G.incidenceFaceMap hr) := by
  ext x
  simp only [Set.mem_inter_iff, G.incidenceFaceMap_mem_range,
    G.incidenceRefinementDen_not_mem]
  constructor
  · intro h
    constructor
    · intro v hv
      apply h v
      exact fun he => hv ((faceJoin_eq_parent_iff hq hr v).mp he).1
    · intro v hv
      apply h v
      exact fun he => hv ((faceJoin_eq_parent_iff hq hr v).mp he).2
  · rintro ⟨h, h'⟩ v hv
    by_cases he : p v = q v
    · exact h' v (fun he' => hv ((faceJoin_eq_parent_iff hq hr v).mpr ⟨he, he'⟩))
    · exact h v he

end BPFixedPoints.Multigraph
