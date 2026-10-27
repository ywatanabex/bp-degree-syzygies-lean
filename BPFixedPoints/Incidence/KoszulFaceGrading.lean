import BPFixedPoints.Incidence.KoszulFaces
import BPFixedPoints.Incidence.KoszulTransportGrading

/-!
# Degrees of local incidence-face Koszul contractions

Restricting each local contraction to complex scalars retains its exterior-degree properties.
-/

namespace BPFixedPoints.Multigraph

open Koszul ResolutionTools IncidencePerturbation CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incFaceContractionOver_h_degree (q : V → Fin 3) :
    HasDegree exteriorDegree exteriorDegree 1 (G.incFaceContractionOver q).h := by
  intro n x hx
  rw [incFaceContractionOver, Contraction.congr_h_apply]
  exact bilinearContraction_h_degree (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
    (fun e => faceVariable ℂ q (G.fst e)) (fun e => faceVariable ℂ q (G.snd e)) n x hx

theorem incFaceContractionOver_i_mem_degree_zero (q : V → Fin 3) (x : G.IncFaceRing q) :
    (G.incFaceContractionOver q).i x ∈
      Finsupp.supported (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) (FaceRing ℂ q)
        {S | exteriorDegree S = 0} := by
  rw [incFaceContractionOver, Contraction.congr_i_apply]
  have h := bilinearContraction_i_mem_degree_zero
    (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)
    (fun e => faceVariable ℂ q (G.fst e)) (fun e => faceVariable ℂ q (G.snd e))
    ((Ideal.quotientEquivAlgOfEq (FaceRing ℂ q) (G.incFaceIdeal_eq_bilinear q).symm).symm x)
  simpa only [LinearEquiv.refl_apply, AlgEquiv.coe_symm_toLinearEquiv] using h

theorem incFaceContraction_h_degree (q : V → Fin 3) :
    HasDegree exteriorDegree exteriorDegree 1 (G.incFaceContraction q).h := by
  intro n x hx
  exact G.incFaceContractionOver_h_degree q n x hx

theorem incFaceContraction_i_mem_degree_zero (q : V → Fin 3) (x : G.IncFaceRing q) :
    (G.incFaceContraction q).i x ∈
      Finsupp.supported (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) ℂ
        {S | exteriorDegree S = 0} :=
  G.incFaceContractionOver_i_mem_degree_zero q x

theorem incFaceContraction_p_eq_zero (q : V → Fin 3)
    {n : ℤ} {x : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))}
    (hx : x ∈ Finsupp.supported (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) ℂ
      {S | exteriorDegree S = n}) (hn : n ≠ 0) :
    (G.incFaceContraction q).p x = 0 := by
  rw [G.incFaceContraction_p]
  have hx0 : x ∅ = 0 := (Finsupp.mem_supported' ℂ x).mp hx ∅ (by
    change exteriorDegree ∅ ≠ n
    simpa only [exteriorDegree, Finset.card_empty, Nat.cast_zero] using hn.symm)
  rw [hx0, map_zero]


/-- The homotopy has positive exterior degree, so its empty-state coefficient is zero. -/
theorem incFaceContraction_h_empty (q : V → Fin 3)
    (x : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) :
    ((G.incFaceContraction q).h x) ∅ = 0 := by
  have hh : (Finsupp.lapply ∅).comp (G.incFaceContraction q).h = 0 := by
    apply Finsupp.lhom_ext
    intro S a
    change ((G.incFaceContraction q).h (Finsupp.single S a)) ∅ = 0
    apply (Finsupp.mem_supported' ℂ _).mp
      ((G.incFaceContraction_h_degree q).apply_single S a) ∅
    change exteriorDegree ∅ ≠ exteriorDegree S + 1
    simp only [exteriorDegree, Finset.card_empty, Nat.cast_zero]
    omega
  exact LinearMap.congr_fun hh x

theorem incFaceContraction_i_apply_of_ne_empty (q : V → Fin 3) (x : G.IncFaceRing q)
    (S : Finset E) (hS : S ≠ ∅) : ((G.incFaceContraction q).i x) S = 0 := by
  apply (Finsupp.mem_supported' ℂ _).mp (G.incFaceContraction_i_mem_degree_zero q x) S
  change (S.card : ℤ) ≠ 0
  intro h
  apply hS
  exact Finset.card_eq_zero.mp (by exact_mod_cast h)

end BPFixedPoints.Multigraph
