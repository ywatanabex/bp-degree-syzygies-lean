import BPFixedPoints.Incidence.AffineOpenCohomology
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual local cohomology on every native affine open

The canonical spectrum of the original section ring supplies the chart.
Mathlib's local Noetherianity gives the required Noetherian section ring.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (X : Scheme.{0}) [IsLocallyNoetherian X]
noncomputable local instance noetherianAffineOpenHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Every positive actual local Ext group vanishes on an original affine open of a quasicoherent module. -/
theorem quasicoherent_affineOpen_local_cohomology_eq_zero
    (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) U) : x = 0 := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h := affineOpen_quasicoherent_local_cohomology_eq_zero Γ(X, U) hU.fromSpec M n
  rw [hU.opensRange_fromSpec] at h
  exact h x

/-- Subsingleton form of the actual local Ext vanishing on an original affine open. -/
theorem quasicoherent_affineOpen_local_cohomology_subsingleton
    (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) U) :=
  subsingleton_of_forall_eq 0 (quasicoherent_affineOpen_local_cohomology_eq_zero X U hU M n)

end BPFixedPoints.SheafTools
