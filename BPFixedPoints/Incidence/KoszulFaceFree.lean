import BPFixedPoints.Incidence.KoszulFaces
import BPFixedPoints.Incidence.KoszulQuotient

/-! # Free-coefficient presentation of each incidence face ring -/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Free-coefficient presentation of the local Koszul degree-zero quotient. -/
noncomputable def incFaceFreeEquiv (q : V → Fin 3) :
    G.IncFaceRing q ≃ₐ[FaceRing ℂ q] MvPolynomial (E × Fin 3) (FaceRing ℂ q) :=
  (Ideal.quotientEquivAlgOfEq _ (G.incFaceIdeal_eq_bilinear q)).trans
    (Koszul.bilinearFreeEquiv (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
      (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)))

theorem incFaceFreeEquiv_mk (q : V → Fin 3)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :
    G.incFaceFreeEquiv q (Ideal.Quotient.mk _ p) =
      aeval (fun (e, α, β) => Koszul.bilinearFreeCoeff
        (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)) e α β)
        (rename (Koszul.coeffFlip (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)).symm p) := rfl

@[simp] theorem incFaceFreeEquiv_C (q : V → Fin 3) (r : FaceRing ℂ q) :
    G.incFaceFreeEquiv q (Ideal.Quotient.mk _ (C r)) = C r := by
  rw [G.incFaceFreeEquiv_mk]
  simp

@[simp] theorem incFaceFreeEquiv_X (q : V → Fin 3) (e : E) (α β : Fin 2) :
    G.incFaceFreeEquiv q (Ideal.Quotient.mk _ (X (e, α, β))) =
      Koszul.bilinearFreeCoeff
        (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j))
        e (incFlip (decide (q (G.fst e) = 1)) α) (incFlip (decide (q (G.snd e) = 1)) β) := by
  rw [G.incFaceFreeEquiv_mk]
  by_cases h₁ : q (G.fst e) = 1 <;> by_cases h₂ : q (G.snd e) = 1 <;>
    simp [Koszul.coeffFlip, incFaceFirstFlip, incFaceSecondFlip, incFlip, h₁, h₂]

end BPFixedPoints.Multigraph
