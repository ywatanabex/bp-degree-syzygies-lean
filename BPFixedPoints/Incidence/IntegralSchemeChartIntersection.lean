import BPFixedPoints.Incidence.SheafChartIntersection
import Mathlib.AlgebraicGeometry.Properties

/-! # Chart-image intersections for the structure sheaf of an integral scheme

For any integral scheme and any open cover, a nonempty common open detects
sections on charts and on their intersections. Applying actual sheaf gluing
identifies global regular functions with the intersection of the chart images.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens Opposite CategoryTheory

universe u
variable (X : Scheme.{u}) [IsIntegral X] {ι : Type u} [Nonempty ι]
  (U : ι → X.Opens) (W : X.Opens) [Nonempty W]
  (hW : ∀ i, W ≤ U i) (hcover : (⊤ : X.Opens) ≤ iSup U)

/-- Global regular functions on an integral scheme are the intersection of
chart images in the regular functions of a nonempty common open. -/
noncomputable def integralGlobalSectionsEquivChartIntersection :
    Γ(X, ⊤) ≃+* chartImageIntersection X.sheaf U W hW :=
  globalSectionsEquivChartIntersection X.sheaf U W hW hcover
    (fun i => map_injective_of_isIntegral X (homOfLE (hW i)))
    (fun i j => map_injective_of_isIntegral X (homOfLE (le_inf (hW i) (hW j))))

end BPFixedPoints.SheafTools
