import BPFixedPoints.Incidence.BinaryCoverCellSectionDifferential
import BPFixedPoints.Incidence.SchemeModuleResolutionCohomology

/-! # Original geometric scalars on original cubical sections

Postcomposition by the original geometric scalar acts on every actual
original face section by the original base coefficient restriction.
The coefficient action is specified before any cohomology comparison.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → X.Opens)

/-- At each original cubical face, the original scalar self-map is the original geometric coefficient action. -/
theorem schemeBaseCellSection_scalar (n : ℕ) (r : R)
    (g : sheafTerm U n ⟶ (SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (q : FaceIndex (V := V) n) :
    let s : Γ(M, SheafTools.binaryCoverFaceOpen U q.val) := sectionsEquiv U _ n g q
    let sr : Γ(M, SheafTools.binaryCoverFaceOpen U q.val) :=
      sectionsEquiv U _ n (g ≫ schemeBaseAbelianScalar f M r) q
    sr = schemeBaseCoefficientAt f (SheafTools.binaryCoverFaceOpen U q.val) r • s := rfl

end BPFixedPoints.SchemeTools
