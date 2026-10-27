import BPFixedPoints.Incidence.CechFaceIncidence
import BPFixedPoints.Incidence.KoszulBilinear
import BPFixedPoints.Incidence.Chart

/-! # Contract the incidence Koszul complex on each actual Čech face -/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

def incFaceFirstFlip (q : V → Fin 3) (e : E) : Fin 2 ≃ Fin 2 :=
  incFlip (decide (q (G.fst e) = 1))

def incFaceSecondFlip (q : V → Fin 3) (e : E) : Fin 2 ≃ Fin 2 :=
  incFlip (decide (q (G.snd e) = 1))

theorem incFaceEquation_eq_bilinear (q : V → Fin 3) (e : E) :
    G.incFaceEquation q e =
      Koszul.flippedBilinearEquation (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
        (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)) e := by
  by_cases h₁ : q (G.fst e) = 1 <;>
    by_cases h₂ : q (G.snd e) = 1 <;>
    simp [incFaceEquation, Koszul.flippedBilinearEquation, Koszul.bilinearEquation,
      Koszul.coeffFlip, incFaceFirstFlip, incFaceSecondFlip, incFlip,
      Fin.sum_univ_two, incCoord, h₁, h₂] <;> ring

/-- Ideal of incidence equations on the face. -/
noncomputable def incFaceIdeal (q : V → Fin 3) :
    Ideal (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :=
  Ideal.span (Set.range (G.incFaceEquation q))

/-- Incidence coordinate ring on the face. -/
abbrev IncFaceRing (q : V → Fin 3) :=
  MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q) ⧸ G.incFaceIdeal q

theorem incFaceIdeal_eq_bilinear (q : V → Fin 3) :
    G.incFaceIdeal q =
      Koszul.bilinearIdeal (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
        (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)) := by
  have h := funext (G.incFaceEquation_eq_bilinear q)
  rw [incFaceIdeal, Koszul.bilinearIdeal, h]

/-- Local Koszul strong contraction linear over the face coordinate ring. -/
noncomputable def incFaceContractionOver (q : V → Fin 3) :
    IncidencePerturbation.Contraction (FaceRing ℂ q)
      (Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) (G.IncFaceRing q) :=
  (Koszul.bilinearContraction (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
    (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j))).congr
      (LinearEquiv.refl _ _) (Ideal.quotientEquivAlgOfEq _
        (G.incFaceIdeal_eq_bilinear q).symm).toLinearEquiv

theorem incFaceContractionOver_d (q : V → Fin 3) :
    (G.incFaceContractionOver q).d =
      (Koszul.differential (G.incFaceEquation q)).restrictScalars (FaceRing ℂ q) := by
  rw [incFaceContractionOver, IncidencePerturbation.Contraction.congr_refl_d]
  rw [Koszul.bilinearContraction_d]
  rw [funext (G.incFaceEquation_eq_bilinear q)]

theorem incFaceContractionOver_p (q : V → Fin 3)
    (z : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) :
    (G.incFaceContractionOver q).p z = Ideal.Quotient.mk (G.incFaceIdeal q) (z ∅) := by
  rw [incFaceContractionOver, IncidencePerturbation.Contraction.congr_refl_p_apply]
  rw [Koszul.bilinearContraction_p]
  exact Ideal.quotientEquivAlgOfEq_mk _ (G.incFaceIdeal_eq_bilinear q).symm (z ∅)

/-- Complex-linear local Koszul strong contraction for the direct sum of all faces. -/
noncomputable def incFaceContraction (q : V → Fin 3) :
    IncidencePerturbation.Contraction ℂ
      (Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) (G.IncFaceRing q) :=
  (G.incFaceContractionOver q).restrictScalars

theorem incFaceContraction_d (q : V → Fin 3) :
    (G.incFaceContraction q).d =
      (Koszul.differential (G.incFaceEquation q)).restrictScalars ℂ := by
  apply LinearMap.ext
  intro z
  change (G.incFaceContractionOver q).d z = _
  rw [G.incFaceContractionOver_d]
  rfl

theorem incFaceContraction_p (q : V → Fin 3)
    (z : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) :
    (G.incFaceContraction q).p z = Ideal.Quotient.mk (G.incFaceIdeal q) (z ∅) :=
  G.incFaceContractionOver_p q z

end BPFixedPoints.Multigraph
