import BPFixedPoints.Incidence.ProjectiveLineGeometricSections
import BPFixedPoints.Incidence.ProjectiveLineEvaluation
import BPFixedPoints.Incidence.ProjectiveLineTwistPairFrames

/-! # Actual Laurent evaluation and the original geometric overlap units -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {R A : Type} [CommRing R] [CommRing A]

/-- Evaluating the original Laurent overlap retains its original left affine coordinate. -/
theorem evaluationChart_unit_overlap (f : R →+* A) (u : Aˣ) :
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫ overlapι R =
      evaluationChart f (u : A) 0 := by
  rw [← left_overlap_chart]
  dsimp only [evaluationChart]
  rw [← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- The actual native pullback on overlap-global functions is their original Laurent evaluation. -/
theorem laurentEvaluation_global_sections (f : R →+* A) (u : Aˣ)
    (s : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫
        (standardIntersectionLaurentIso R).inv).appTop s) =
      LaurentPolynomial.eval₂ f u (standardIntersectionSectionsEquiv R s) := by
  change (((standardIntersectionLaurentIso R).inv.appTop ≫
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u))).appTop) ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom) s = _
  rw [Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

/-- Original geometric Laurent units evaluate with their original integer exponents. -/
theorem laurentEvaluation_twist_unit (f : R →+* A) (u : Aˣ) (n : ℤ) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫
        (standardIntersectionLaurentIso R).inv).appTop
          (twistOverlapUnit R n : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))) =
      (u ^ n : Aˣ) := by
  rw [laurentEvaluation_global_sections, twistOverlapUnit_coordinate]
  simp

/-- Equal original pivots have the original constant-one pair unit. -/
theorem twistSheafPairUnit_self (R : Type) [CommRing R] (n : ℤ) (i : Fin 2) :
    twistSheafPairUnit R n i i = 1 := by
  fin_cases i <;> rfl

/-- A reverse original pair unit evaluates to the inverse Laurent power along its actual projection. -/
theorem pairUnit_evaluation_reverse (f : R →+* A) (u : Aˣ) (n : ℤ)
    (g : Spec (CommRingCat.of A) ⟶ (standardPairOpen R 1 0).toScheme)
    (hg : g ≫ (standardPairOpen R 1 0).ι = evaluationChart f (u : A) 0) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop (twistSheafPairUnit R n 1 0 : Γ((standardPairOpen R 1 0).toScheme, ⊤))) =
        (u⁻¹ ^ n : Aˣ) := by
  have he : g = Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫
      (standardIntersectionLaurentIso R).inv := by
    apply (cancel_mono (standardPairOpen R 1 0).ι).mp
    rw [hg, Category.assoc]
    change evaluationChart f (u : A) 0 =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫
        (standardIntersectionLaurentIso R).inv ≫ (standardOpen R 0 ⊓ standardOpen R 1).ι
    rw [standardIntersectionLaurentIso_inv_ι, evaluationChart_unit_overlap]
  rw [he]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ f u)) ≫
      (standardIntersectionLaurentIso R).inv).appTop
        (↑((twistOverlapUnit R n)⁻¹) : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))) = _
  rw [← twistOverlapUnit_neg]
  simpa only [inv_zpow, zpow_neg] using laurentEvaluation_twist_unit f u (-n)

/-- The reverse-pair evaluation keeps the original pair object before substituting its pivot equalities. -/
theorem pairUnit_evaluation_reverse_of_eq (f : R →+* A) (u : Aˣ) (n : ℤ)
    (i j : Fin 2) (hi : i = 1) (hj : j = 0)
    (g : Spec (CommRingCat.of A) ⟶ (standardPairOpen R i j).toScheme)
    (hg : g ≫ (standardPairOpen R i j).ι = evaluationChart f (u : A) 0) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop (twistSheafPairUnit R n i j : Γ((standardPairOpen R i j).toScheme, ⊤))) =
        (u⁻¹ ^ n : Aˣ) := by
  subst i
  subst j
  exact pairUnit_evaluation_reverse f u n g hg

/-- Equal original pair pivots retain their constant-one unit without changing the pair object. -/
theorem twistSheafPairUnit_eq_one_of_eq (R : Type) [CommRing R] (n : ℤ) (i j : Fin 2) (h : i = j) :
    twistSheafPairUnit R n i j = 1 := by
  subst j
  exact twistSheafPairUnit_self R n i

end BPFixedPoints.ProjectiveLine
