import BPFixedPoints.Incidence.ProjectiveLineEvaluation

/-! # Actual inverse images of projective-line standard opens

Mathlib's homogeneous-localization inverse-image theorem gives the original
polynomial basic opens. Evaluation therefore tests the actual coordinate in
the prime ideal, including non-closed points and arbitrary coefficient rings.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The genuine Proj standard opens pull back to the original polynomial coordinate opens. -/
theorem chartι_preimage_standardOpen (i j : Fin 2) :
    chartι R i ⁻¹ᵁ standardOpen R j =
      PrimeSpectrum.basicOpen (if j = i then (1 : Polynomial R) else Polynomial.X) := by
  change Spec.map (chartEquiv R i).toCommRingCatIso.hom ⁻¹ᵁ
    (Proj.awayι (grading R) (X i) (isHomogeneous_X R i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (grading R) (X j)) = _
  rw [Proj.awayι_preimage_basicOpen (grading R) (isHomogeneous_X R i) (by decide)
    (isHomogeneous_X R j) (by decide), SpecMap_preimage_basicOpen]
  congr 1
  change toPolynomial R i
    (HomogeneousLocalization.Away.mk (grading R) (isHomogeneous_X R i) 1 (X j ^ 1) _) = _
  rw [toPolynomial_mk]
  simp [normalize]

universe u
variable {S A : Type u} [CommRing S] [CommRing A]

/-- On an evaluated original chart, the opposite open is defined by the actual coordinate. -/
theorem evaluationChart_preimage_standardOpen (f : S →+* A) (a : A) (i j : Fin 2) :
    evaluationChart f a i ⁻¹ᵁ standardOpen S j =
      PrimeSpectrum.basicOpen (if j = i then (1 : A) else a) := by
  change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f a)) ⁻¹ᵁ
    (chartι S i ⁻¹ᵁ standardOpen S j) = _
  rw [chartι_preimage_standardOpen, SpecMap_preimage_basicOpen]
  by_cases h : j = i <;> simp [h]

/-- Every prime on the original chart maps into that same actual standard open. -/
theorem evaluationChart_mem_standardOpen (f : S →+* A) (a : A) (i : Fin 2)
    (x : Spec (CommRingCat.of A)) : evaluationChart f a i x ∈ standardOpen S i := by
  have h := evaluationChart_preimage_standardOpen f a i i
  have hx : x ∈ evaluationChart f a i ⁻¹ᵁ standardOpen S i := by
    rw [h]
    simp
  exact hx

/-- The opposite projective open is tested in the original prime ideal. -/
theorem evaluationChart_mem_opposite (f : S →+* A) (a : A) (i : Fin 2)
    (x : Spec (CommRingCat.of A)) :
    evaluationChart f a i x ∈ standardOpen S i.rev ↔ a ∉ x.asIdeal := by
  change x ∈ evaluationChart f a i ⁻¹ᵁ standardOpen S i.rev ↔ _
  rw [evaluationChart_preimage_standardOpen]
  fin_cases i <;> rfl

end BPFixedPoints.ProjectiveLine
