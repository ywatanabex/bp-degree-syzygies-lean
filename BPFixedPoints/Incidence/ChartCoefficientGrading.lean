import BPFixedPoints.Incidence.CoefficientGrading
import BPFixedPoints.Incidence.CechFaceMaps
import BPFixedPoints.Incidence.KoszulFaceFree

/-!
# Natural coefficient degree of chart presentations

Vertex coordinates have degree zero and edge coefficients degree one. Exchanging
face coordinates and eliminating each pivot coefficient preserve this grading.
-/

namespace BPFixedPoints.CechProduct

open MvPolynomial Finsupp

variable {R σ V : Type*} [CommRing R]

theorem facePolynomialEquiv_single_homogeneous (q : V → Fin 3)
    (m : FaceMonoid q) {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (facePolynomialEquiv R σ q (AddMonoidAlgebra.single m p)).IsHomogeneous n := by
  classical
  rw [p.as_sum]
  change ((facePolynomialEquiv R σ q)
    ((AddMonoidAlgebra.singleAddHom m) (∑ d ∈ p.support, monomial d (p.coeff d)))).IsHomogeneous n
  rw [map_sum, map_sum]
  apply IsHomogeneous.sum
  intro d hd
  change MvPolynomial.IsHomogeneous (AddMonoidAlgebra.commAlgEquiv R
    (AddMonoidAlgebra.single m (AddMonoidAlgebra.single d (p.coeff d)))) n
  rw [AddMonoidAlgebra.commAlgEquiv_single_single]
  exact isHomogeneous_monomial _ (by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (Finsupp.mem_support_iff.mp hd))

theorem polynomialFaceEquiv_homogeneous [Fintype V]
    {x : C (MvPolynomial σ R) V} {n : ℕ}
    (hx : ∀ b, (x b).IsHomogeneous n) (q : V → Fin 3) :
    (polynomialFaceEquiv R σ x q).IsHomogeneous n := by
  classical
  rw [polynomialFaceEquiv_apply]
  set y := faceEquiv (MvPolynomial σ R) x q
  have hy : ∀ m, (y.coeff m).IsHomogeneous n := by
    intro m
    simpa only [y, faceEquiv_coeff] using hx (embedFace q m)
  rw [← AddMonoidAlgebra.sum_coeff_single y, Finsupp.sum, map_sum]
  exact IsHomogeneous.sum _ _ _ fun m _ => facePolynomialEquiv_single_homogeneous q m (hy m)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Koszul

open MvPolynomial

variable {E R : Type*} [CommRing R]

theorem bilinearTail_homogeneous (x y : E → R) (e : E) :
    (bilinearTail x y e).IsHomogeneous 1 := by
  unfold bilinearTail
  have h (i : E × Fin 3) (r : R) : (X i * C r).IsHomogeneous 1 := by
    simpa only [mul_comm] using isHomogeneous_C_mul_X r i
  exact ((h _ _).add (h _ _)).add (by
    simpa only [mul_comm] using (h (e, 2) (x e)).C_mul (y e))

theorem bilinearFreeCoeff_homogeneous [LinearOrder E] [Fintype E]
    (x y : E → R) (e : E) (α β : Fin 2) :
    (bilinearFreeCoeff x y e α β).IsHomogeneous 1 := by
  unfold bilinearFreeCoeff
  split_ifs <;> first | exact (bilinearTail_homogeneous x y e).neg | exact isHomogeneous_X _ _

end BPFixedPoints.Koszul

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incFaceFreeEquiv_mk_homogeneous (q : V → Fin 3)
    {p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (G.incFaceFreeEquiv q (Ideal.Quotient.mk _ p)).IsHomogeneous n := by
  rw [G.incFaceFreeEquiv_mk]
  have hr := hp.rename_isHomogeneous
    (f := (Koszul.coeffFlip (G.incFaceFirstFlip q) (G.incFaceSecondFlip q)).symm)
  simpa only [one_mul] using hr.aeval
    (fun (e, α, β) => Koszul.bilinearFreeCoeff
      (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)) e α β)
    (fun (e, α, β) => Koszul.bilinearFreeCoeff_homogeneous _ _ e α β)

end BPFixedPoints.Multigraph
