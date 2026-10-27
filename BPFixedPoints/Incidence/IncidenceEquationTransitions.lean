import BPFixedPoints.Incidence.CechFaceTransitionUnits
import BPFixedPoints.Incidence.KoszulFaces

/-! # Homogeneous incidence equations agree up to explicit transition units

The equality is proved in the ambient polynomial/Laurent rings before taking
quotients. Thus the zero ideals descend on the genuine projective chart overlaps,
not only after mapping their quotients into a common torus.
-/

namespace BPFixedPoints.CechProduct
open BPFixedPoints.Multigraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V : Type*} [DecidableEq V] (R : Type*) [CommRing R]

/-- The two homogeneous coordinates transform by one common invertible factor. -/
theorem faceRefinement_incCoord {q r : V → Fin 3} (h : FaceRefines q r) (v : V) (α : Fin 2) :
    faceRefinementMap R h (incCoord (decide (q v = 1)) α (faceVariable R q v)) =
      (faceTransitionUnit R h v : FaceRing R r) *
        incCoord (decide (r v = 1)) α (faceVariable R r v) := by
  rw [map_incCoord, faceRefinement_variable]
  by_cases hf : q v = 1 ∧ r v = 2
  · rw [dif_pos hf, faceTransitionUnit, dif_pos hf]
    have hv := (faceLaurentUnit R r v hf.2).val_inv
    simpa [hf.1, hf.2, faceLaurentUnit] using incCoord_true hv α
  · rw [dif_neg hf, faceTransitionUnit, dif_neg hf, Units.val_one, one_mul]
    have he : q v = 1 ↔ r v = 1 := by
      have hh := h v
      omega
    simp only [faceOrientation, he]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph
open MvPolynomial CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Transition unit of the incidence line bundle for an edge, including both
endpoint occurrences when the endpoints coincide. -/
noncomputable def incidenceEquationTransitionUnit {q r : V → Fin 3}
    (h : FaceRefines q r) (e : E) :
    (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r))ˣ :=
  Units.map C.toMonoidHom (faceTransitionUnit ℂ h (G.fst e) * faceTransitionUnit ℂ h (G.snd e))

/-- The original homogeneous edge equation transforms by its explicit line-bundle unit. -/
theorem incFaceEquation_refinement {q r : V → Fin 3} (h : FaceRefines q r) (e : E) :
    facePolynomialRefinement ℂ (IncCoeffIdx E) h (G.incFaceEquation q e) =
      (G.incidenceEquationTransitionUnit h e : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)) *
        G.incFaceEquation r e := by
  let u := faceTransitionUnit ℂ h (G.fst e)
  let v := faceTransitionUnit ℂ h (G.snd e)
  have hu (α : Fin 2) := faceRefinement_incCoord ℂ h (G.fst e) α
  have hv (β : Fin 2) := faceRefinement_incCoord ℂ h (G.snd e) β
  have hval : (G.incidenceEquationTransitionUnit h e :
      MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)) = C ((u : FaceRing ℂ r) * (v : FaceRing ℂ r)) := rfl
  rw [hval, map_mul]
  simp only [incFaceEquation, facePolynomialRefinement, mapAlgHom_apply,
    map_sum, map_mul, map_X, map_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  have hu' := congrArg (C : FaceRing ℂ r →+* MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)) (hu α)
  have hv' := congrArg (C : FaceRing ℂ r →+* MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)) (hv β)
  simp only [map_mul] at hu' hv'
  calc
    _ = X (e, α, β) *
        (C (u : FaceRing ℂ r) * C (incCoord (decide (r (G.fst e) = 1)) α (faceVariable ℂ r (G.fst e)))) *
        (C (v : FaceRing ℂ r) * C (incCoord (decide (r (G.snd e) = 1)) β (faceVariable ℂ r (G.snd e)))) := by
      exact congrArg₂ (fun a b => X (e, α, β) * a * b) hu' hv'
    _ = _ := by ring

end BPFixedPoints.Multigraph
