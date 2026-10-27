import BPFixedPoints.Incidence.ProjectiveLineTwistSheaf
import BPFixedPoints.Incidence.TwoOpenTwistLocallyFree
import BPFixedPoints.Incidence.TwoOpenTwistTransitions

/-! # Genuine rank-one twists on the actual projective line

The original Laurent transition T^n defines an actual locally free sheaf.
Its explicit local trivializations use the original two standard Proj opens.
Higher cohomology and the polynomial Cech presentation are further comparisons.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original left standard-open rank-one trivialization of the actual integral twist. -/
noncomputable def twistSheafLeftIso (n : ℤ) :
    (twistSheaf R n).restrict (standardOpen R 0).ι ≅
      SheafOfModules.unit (standardOpen R 0).toScheme.ringCatSheaf :=
  SheafTools.twoOpenTwistLeftIso (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- The original right standard-open rank-one trivialization of the actual integral twist. -/
noncomputable def twistSheafRightIso (n : ℤ) :
    (twistSheaf R n).restrict (standardOpen R 1).ι ≅
      SheafOfModules.unit (standardOpen R 1).toScheme.ringCatSheaf :=
  SheafTools.twoOpenTwistRightIso (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- The actual twist has rank-one trivializations on both original standard opens. -/
theorem twistSheaf_rankOne (n : ℤ) :
    Nonempty ((twistSheaf R n).restrict (standardOpen R 0).ι ≅
      SheafOfModules.unit (standardOpen R 0).toScheme.ringCatSheaf) ∧
    Nonempty ((twistSheaf R n).restrict (standardOpen R 1).ι ≅
      SheafOfModules.unit (standardOpen R 1).toScheme.ringCatSheaf) :=
  ⟨⟨twistSheafLeftIso R n⟩, ⟨twistSheafRightIso R n⟩⟩

/-- Every original integral Laurent twist is locally free in Mathlib's native sense. -/
instance twistSheaf_isLocallyFree (n : ℤ) : (twistSheaf R n).IsLocallyFree :=
  SheafTools.twoOpenTwist_isLocallyFree (projectiveLine R) _ _
    (twistOverlapUnit R n) (standardOpen_cover R)

/-- Its quasicoherence follows from Mathlib's native locally-free-sheaf theorem. -/
instance twistSheaf_isQuasicoherent (n : ℤ) : (twistSheaf R n).IsQuasicoherent := by
  infer_instance

/-- The left overlap frame is the restriction of the original left chart projection. -/
noncomputable def twistSheafOverlapLeftIso (n : ℤ) :
    (twistSheaf R n).restrict (standardOpen R 0 ⊓ standardOpen R 1).ι ≅
      SheafOfModules.unit (standardOpen R 0 ⊓ standardOpen R 1).toScheme.ringCatSheaf :=
  SheafTools.twoOpenTwistOverlapLeftIso (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- The right overlap frame is the restriction of the original right chart projection. -/
noncomputable def twistSheafOverlapRightIso (n : ℤ) :
    (twistSheaf R n).restrict (standardOpen R 0 ⊓ standardOpen R 1).ι ≅
      SheafOfModules.unit (standardOpen R 0 ⊓ standardOpen R 1).toScheme.ringCatSheaf :=
  SheafTools.twoOpenTwistOverlapRightIso (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- The actual rank-one overlap frames have precisely the original integral Laurent transition. -/
theorem twistSheaf_overlap_transition (n : ℤ) :
    (twistSheafOverlapLeftIso R n).hom = (twistSheafOverlapRightIso R n).hom ≫
      SheafTools.unitGlobalMultiplication (standardOpen R 0 ⊓ standardOpen R 1).toScheme
        (twistOverlapUnit R n : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)) :=
  SheafTools.twoOpenTwist_overlap_transition (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- The actual overlap transition endomorphism sends the unit frame to the original T^n. -/
theorem twistSheaf_overlap_transition_coordinate (n : ℤ) :
    standardIntersectionSectionsEquiv R
      ((SheafTools.unitGlobalMultiplication (standardOpen R 0 ⊓ standardOpen R 1).toScheme
        (twistOverlapUnit R n : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))).val.app
          (Opposite.op ⊤) (1 : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))) =
      LaurentPolynomial.T n := by
  rw [SheafTools.unitGlobalMultiplication_top_one]
  exact twistOverlapUnit_coordinate R n

end BPFixedPoints.ProjectiveLine
