import BPFixedPoints.Incidence.OpenUnitFrameRestriction
import BPFixedPoints.Incidence.ProjectiveLineTwistPairFrames
import BPFixedPoints.Incidence.VertexProjectiveTwistLocalFrames

/-! # The specified standard pair frames are restrictions of the original chart frames -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true
attribute [local irreducible] projectiveLine standardOpen
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- The original pair open is contained in its original left pivot open. -/
theorem standardPairOpen_le_left (i j : Fin 2) : standardPairOpen R i j ≤ standardOpen R i := by
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact inf_le_left
  · exact inf_le_right
  · exact le_rfl

/-- The original pair open is contained in its original right pivot open. -/
theorem standardPairOpen_le_right (i j : Fin 2) : standardPairOpen R i j ≤ standardOpen R j := by
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact inf_le_right
  · exact inf_le_left
  · exact le_rfl

/-- The specified left pair frame is the native restriction of the original left pivot frame. -/
theorem twistSheafPairIso_eq_left_restriction (n : ℤ) (i j : Fin 2) :
    SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (standardPairOpen_le_left R i j)) (twistSheaf R n)
        (twistSheafStandardIso R n i) = twistSheafPairIso R n i j false := by
  fin_cases i <;> fin_cases j
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (𝟙 (standardOpen R 0)) (twistSheaf R n) (twistSheafLeftIso R n) = twistSheafLeftIso R n
    exact SheafTools.moduleLocalFrameRestriction_id _ _ _ _
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left))
        (twistSheaf R n) (twistSheafLeftIso R n) = twistSheafOverlapLeftIso R n
    simpa only [twistSheafLeftIso, twistSheafOverlapLeftIso, twistSheaf] using
      SheafTools.twoOpenTwistLeftIso_restriction (projectiveLine R)
        (standardOpen R 0) (standardOpen R 1) (twistOverlapUnit R n)
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 1 from inf_le_right))
        (twistSheaf R n) (twistSheafRightIso R n) = twistSheafOverlapRightIso R n
    simpa only [twistSheafRightIso, twistSheafOverlapRightIso, twistSheaf] using
      SheafTools.twoOpenTwistRightIso_restriction (projectiveLine R)
        (standardOpen R 0) (standardOpen R 1) (twistOverlapUnit R n)
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (𝟙 (standardOpen R 1)) (twistSheaf R n) (twistSheafRightIso R n) = twistSheafRightIso R n
    exact SheafTools.moduleLocalFrameRestriction_id _ _ _ _

/-- The specified right pair frame is the native restriction of the original right pivot frame. -/
theorem twistSheafPairIso_eq_right_restriction (n : ℤ) (i j : Fin 2) :
    SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (standardPairOpen_le_right R i j)) (twistSheaf R n)
        (twistSheafStandardIso R n j) = twistSheafPairIso R n i j true := by
  fin_cases i <;> fin_cases j
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (𝟙 (standardOpen R 0)) (twistSheaf R n) (twistSheafLeftIso R n) = twistSheafLeftIso R n
    exact SheafTools.moduleLocalFrameRestriction_id _ _ _ _
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 1 from inf_le_right))
        (twistSheaf R n) (twistSheafRightIso R n) = twistSheafOverlapRightIso R n
    simpa only [twistSheafRightIso, twistSheafOverlapRightIso, twistSheaf] using
      SheafTools.twoOpenTwistRightIso_restriction (projectiveLine R)
        (standardOpen R 0) (standardOpen R 1) (twistOverlapUnit R n)
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left))
        (twistSheaf R n) (twistSheafLeftIso R n) = twistSheafOverlapLeftIso R n
    simpa only [twistSheafLeftIso, twistSheafOverlapLeftIso, twistSheaf] using
      SheafTools.twoOpenTwistLeftIso_restriction (projectiveLine R)
        (standardOpen R 0) (standardOpen R 1) (twistOverlapUnit R n)
  · change SheafTools.moduleLocalFrameRestriction (projectiveLine R)
      (𝟙 (standardOpen R 1)) (twistSheaf R n) (twistSheafRightIso R n) = twistSheafRightIso R n
    exact SheafTools.moduleLocalFrameRestriction_id _ _ _ _

end BPFixedPoints.ProjectiveLine
