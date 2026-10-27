import BPFixedPoints.Incidence.ProjectiveLineTwistLocallyFree

/-! # Original twist frames on every pair of standard projective-line opens

The original scheme modules, structure-ring maps and native comparisons are used.
Comparison with the coefficient face atlas and derived cohomology is separate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R]

/-- The common standard factor open for the two original pivot choices. -/
noncomputable def standardPairOpen (i j : Fin 2) : (projectiveLine R).Opens :=
  Fin.cases (Fin.cases (standardOpen R 0)
    (fun _ => standardOpen R 0 ⊓ standardOpen R 1) j)
    (fun _ => Fin.cases (standardOpen R 0 ⊓ standardOpen R 1)
      (fun _ => standardOpen R 1) j) i

/-- The specified original twist frame on the common factor open. -/
noncomputable def twistSheafPairIso (n : ℤ) (i j : Fin 2) (right : Bool) :
    (twistSheaf R n).restrict (standardPairOpen R i j).ι ≅
      SheafOfModules.unit (standardPairOpen R i j).toScheme.ringCatSheaf := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · refine Fin.cases (twistSheafLeftIso R n) (fun _ => ?_) j
    exact if right then twistSheafOverlapRightIso R n else twistSheafOverlapLeftIso R n
  · refine Fin.cases ?_ (fun _ => twistSheafRightIso R n) j
    exact if right then twistSheafOverlapLeftIso R n else twistSheafOverlapRightIso R n

/-- The original pair transition: one, the original Laurent monomial, or its inverse. -/
noncomputable def twistSheafPairUnit (n : ℤ) (i j : Fin 2) :
    Γ((standardPairOpen R i j).toScheme, ⊤)ˣ := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact Fin.cases 1 (fun _ => twistOverlapUnit R n) j
  · exact Fin.cases ((twistOverlapUnit R n)⁻¹) (fun _ => 1) j

/-- The actual original factor frames have exactly the specified original Laurent transition. -/
theorem twistSheafPairIso_transition (n : ℤ) (i j : Fin 2) :
    (twistSheafPairIso R n i j false).hom =
      (twistSheafPairIso R n i j true).hom ≫
        SheafTools.unitGlobalMultiplication (standardPairOpen R i j).toScheme
          (twistSheafPairUnit R n i j : Γ((standardPairOpen R i j).toScheme, ⊤)) := by
  fin_cases i <;> fin_cases j
  · change (twistSheafLeftIso R n).hom = (twistSheafLeftIso R n).hom ≫
      SheafTools.unitGlobalMultiplication (standardOpen R 0).toScheme 1
    rw [SheafTools.unitGlobalMultiplication_one, Category.comp_id]
  · exact twistSheaf_overlap_transition R n
  · change (twistSheafOverlapRightIso R n).hom =
        (twistSheafOverlapLeftIso R n).hom ≫ SheafTools.unitGlobalMultiplication
          (standardOpen R 0 ⊓ standardOpen R 1).toScheme
            (↑((twistOverlapUnit R n)⁻¹) : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))
    have h := congrArg (fun f => f ≫ SheafTools.unitGlobalMultiplication
        (standardOpen R 0 ⊓ standardOpen R 1).toScheme
          (↑((twistOverlapUnit R n)⁻¹) : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)))
        (twistSheaf_overlap_transition R n)
    simpa only [Category.assoc, SheafTools.unitGlobalMultiplication_mul, Units.mul_inv,
        SheafTools.unitGlobalMultiplication_one, Category.comp_id] using h.symm
  · change (twistSheafRightIso R n).hom = (twistSheafRightIso R n).hom ≫
      SheafTools.unitGlobalMultiplication (standardOpen R 1).toScheme 1
    rw [SheafTools.unitGlobalMultiplication_one, Category.comp_id]

/-- A point lying in both original standard opens lies in the specified common factor open. -/
theorem mem_standardPairOpen (i j : Fin 2) (x : projectiveLine R)
    (hi : x ∈ standardOpen R i) (hj : x ∈ standardOpen R j) : x ∈ standardPairOpen R i j := by
  fin_cases i <;> fin_cases j
  · exact hi
  · exact ⟨hi, hj⟩
  · exact ⟨hj, hi⟩
  · exact hi

/-- The original forward pair unit has the original Laurent monomial as its coordinate. -/
theorem twistSheafPairUnit_forward_coordinate (n : ℤ) :
    standardIntersectionSectionsEquiv R
      (twistSheafPairUnit R n 0 1 : Γ((standardPairOpen R 0 1).toScheme, ⊤)) =
        LaurentPolynomial.T n := twistOverlapUnit_coordinate R n

/-- The original reverse pair unit has the original inverse Laurent monomial as its coordinate. -/
theorem twistSheafPairUnit_reverse_coordinate (n : ℤ) :
    standardIntersectionSectionsEquiv R
      (twistSheafPairUnit R n 1 0 : Γ((standardPairOpen R 1 0).toScheme, ⊤)) =
        LaurentPolynomial.T (-n) := by
  change standardIntersectionSectionsEquiv R
    (↑((twistOverlapUnit R n)⁻¹) : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)) = _
  rw [← twistOverlapUnit_neg]
  exact twistOverlapUnit_coordinate R (-n)

end BPFixedPoints.ProjectiveLine
