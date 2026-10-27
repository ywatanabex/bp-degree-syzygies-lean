import BPFixedPoints.Incidence.ProjectiveLineCanonicalCech
import BPFixedPoints.Incidence.SheafGlobalCechComparison
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual twist Cech classes and the original degree-one states

The quotient uses the actual twist's canonical section restrictions. Its
state projection is the original Laurent coefficient projection. The final
comparison with genuine global sheaf cohomology retains both local
degree-one vanishing hypotheses explicitly.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original state projection on actual overlap sections of the negative twist. -/
noncomputable def canonicalCechProjectionOne (d : ℕ) :
    Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1) →+ CechLine.H1 R d :=
  (CechLine.projectionOne R d).toAddMonoidHom.comp
    (canonicalCechOneCoordinates R d).toAddMonoidHom

/-- The actual canonical Cech image is exactly the kernel of the original state projection. -/
theorem canonicalCechRange_eq_kernel (d : ℕ) :
    (SheafTools.twoOpenSectionDifference (twistAbelianSheaf R (-(d : ℤ)))
      (standardOpen R 0) (standardOpen R 1)).range = (canonicalCechProjectionOne R d).ker := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    change CechLine.projectionOne R d (canonicalCechOneCoordinates R d
      (SheafTools.twoOpenSectionDifference (twistAbelianSheaf R (-(d : ℤ)))
        (standardOpen R 0) (standardOpen R 1) s)) = 0
    rw [canonicalCechCoordinates_differential, map_neg]
    have hp := LinearMap.congr_fun (CechLine.projectionOne_differential R d)
      (canonicalCechZeroCoordinates R d s)
    change CechLine.projectionOne R d
      (CechLine.differential R d (canonicalCechZeroCoordinates R d s)) = 0 at hp
    rw [hp, neg_zero]
  · intro hz
    change CechLine.projectionOne R d (canonicalCechOneCoordinates R d z) = 0 at hz
    refine ⟨(canonicalCechZeroCoordinates R d).symm
      (-(CechLine.homotopy R d (canonicalCechOneCoordinates R d z))), ?_⟩
    apply (canonicalCechOneCoordinates R d).injective
    rw [canonicalCechCoordinates_differential, AddEquiv.apply_symm_apply, map_neg, neg_neg]
    have hh := LinearMap.congr_fun (CechLine.differential_homotopy R d)
      (canonicalCechOneCoordinates R d z)
    change CechLine.differential R d (CechLine.homotopy R d
      (canonicalCechOneCoordinates R d z)) =
        canonicalCechOneCoordinates R d z - CechLine.inclusionOne R d
          (CechLine.projectionOne R d (canonicalCechOneCoordinates R d z)) at hh
    simpa only [hz, map_zero, sub_zero] using hh

/-- The actual canonical Cech quotient is the original finite degree-one state module. -/
noncomputable def canonicalCechH1Equiv (d : ℕ) :
    SheafTools.twoOpenSectionH1 (twistAbelianSheaf R (-(d : ℤ)))
      (standardOpen R 0) (standardOpen R 1) ≃+ CechLine.H1 R d :=
  (QuotientAddGroup.quotientAddEquivOfEq (canonicalCechRange_eq_kernel R d)).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse (canonicalCechProjectionOne R d)
      (fun x => (canonicalCechOneCoordinates R d).symm (CechLine.inclusionOne R d x)) (by
        intro x
        change CechLine.projectionOne R d (canonicalCechOneCoordinates R d
          ((canonicalCechOneCoordinates R d).symm (CechLine.inclusionOne R d x))) = x
        rw [AddEquiv.apply_symm_apply]
        exact LinearMap.congr_fun (CechLine.projectionOne_inclusionOne R d) x))

/-- Existence form of the unconditional comparison for the actual canonical Cech quotient. -/
theorem canonicalCechH1_comparison (d : ℕ) :
    Nonempty (SheafTools.twoOpenSectionH1 (twistAbelianSheaf R (-(d : ℤ)))
      (standardOpen R 0) (standardOpen R 1) ≃+ CechLine.H1 R d) :=
  ⟨canonicalCechH1Equiv R d⟩

/-- Actual Cech classes are computed by the original state projection on their representatives. -/
theorem canonicalCechH1Equiv_mk (d : ℕ)
    (z : Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1)) :
    canonicalCechH1Equiv R d (QuotientAddGroup.mk z) = canonicalCechProjectionOne R d z := rfl

noncomputable local instance twistAbelianSheafHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveLine R)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Genuine global H1 has the original state module under the two explicit local vanishings. -/
noncomputable def twistSheafH1Equiv (d : ℕ)
    [Subsingleton ((twistAbelianSheaf R (-(d : ℤ))).H' 1 (standardOpen R 0))]
    [Subsingleton ((twistAbelianSheaf R (-(d : ℤ))).H' 1 (standardOpen R 1))] :
    (twistAbelianSheaf R (-(d : ℤ))).H 1 ≃+ CechLine.H1 R d :=
  (SheafTools.twoOpenSectionGlobalH1Equiv (twistAbelianSheaf R (-(d : ℤ)))
    (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R)).symm.trans
      (canonicalCechH1Equiv R d)

/-- Existence form retaining both local vanishings in the genuine derived H1 comparison. -/
theorem twistSheafH1_comparison (d : ℕ)
    [Subsingleton ((twistAbelianSheaf R (-(d : ℤ))).H' 1 (standardOpen R 0))]
    [Subsingleton ((twistAbelianSheaf R (-(d : ℤ))).H' 1 (standardOpen R 1))] :
    Nonempty ((twistAbelianSheaf R (-(d : ℤ))).H 1 ≃+ CechLine.H1 R d) :=
  ⟨twistSheafH1Equiv R d⟩

end BPFixedPoints.ProjectiveLine
