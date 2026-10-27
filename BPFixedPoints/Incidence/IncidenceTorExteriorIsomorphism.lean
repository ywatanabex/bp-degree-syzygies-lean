import BPFixedPoints.Incidence.IncidenceTorStateProduct
import BPFixedPoints.Incidence.EdgeExteriorBundleCohomology
import BPFixedPoints.Incidence.EdgeExteriorBundleProduct

/-! # Bigraded Tor of the incidence ring is cohomology of the exterior bundle

For p ≤ q, the internal-degree-q piece of the actual Tor_p of the original
incidence ring over the coefficient origin and the actual Ext-defined
cohomology H^{q-p} of the q-th exterior bundle (the actual finite biproduct
of the twist sheaves L(-d_S), |S| = q, on the product of projective lines
over ℂ) are both identified with the product over q-element edge sets of the
original state pieces of cohomological degree q-p. Composing the two
independently constructed identifications gives a ℂ-linear isomorphism.
Neither side is defined from the other or from the states.

The isomorphism sends the standard Tor product to the exterior product
(-1)^(q·j) · (standard cup with the exterior pairing), with the explicit
degree identity (q-p)+(q'-p') = (q+q')-(p+p'), and the Tor unit to the
exterior unit. Both products are defined independently (the Tor product by
the resolution, the exterior product by sheaf cohomology); their agreement
is read off through the injective state vectors of both sides.
-/

namespace BPFixedPoints.Multigraph
open CategoryTheory TopologicalSpace AlgebraicGeometry CechProduct ProjectiveLine SchemeTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section
variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
local instance incidenceTorExteriorHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The internal-degree-q piece of actual Tor_p is the actual cohomology H^{q-p} of the q-th exterior bundle. -/
def incidenceTorExteriorEquiv {p q : ℕ} (h : p ≤ q) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p) :=
  letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
  (G.incidenceTorBigradedStateEquiv h).trans (G.exteriorBundleStateLinearEquiv ℂ q (q - p)).symm

/-- Both sides have the same original state coordinates. -/
theorem incidenceTorExteriorEquiv_state {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    G.exteriorBundleStateLinearEquiv ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) =
      G.incidenceTorBigradedStateEquiv h x := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  simp [incidenceTorExteriorEquiv]

/-- In coordinates: the S-component state of the image has the original full Tor state coefficients. -/
theorem incidenceTorExteriorEquiv_coefficient {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q)
    (S : Set.powersetCard E q) (κ : HBasis (G.deg (S : Finset E))) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    (G.exteriorBundleStateLinearEquiv ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) S : H ℂ (G.deg S)) κ =
      G.incidenceTorFullState p x.val ⟨S, κ⟩ := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  rw [incidenceTorExteriorEquiv_state,incidenceTorBigradedStateEquiv_apply]

/-- The state vector of the image is the original full state vector of the Tor class. -/
theorem exteriorCohomologyState_incidenceTorExteriorEquiv {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    G.exteriorCohomologyState ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) =
      G.incidenceTorFullState p x.val := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  rw [exteriorCohomologyState_eq_sum,incidenceTorExteriorEquiv_state,G.incidenceTorFullState_eq_sum h x]

/-- The isomorphism sends the standard Tor product to the exterior cohomology product. -/
theorem incidenceTorExteriorEquiv_product {p q p' q' : ℕ} (h : p ≤ q) (h' : p' ≤ q')
    (x : G.incidenceTorInternalPiece p q) (y : G.incidenceTorInternalPiece p' q') :
    G.incidenceTorExteriorEquiv (Nat.add_le_add h h')
        ⟨G.incidenceTorProduct p p' x.val y.val,
          G.incidenceTorProduct_internal_degree p p' q q' x.property y.property⟩ =
      G.exteriorHCast ℂ rfl (by omega : (q - p) + (q' - p') = (q + q') - (p + p'))
        (G.exteriorCohomologyProduct ℂ q q' (q - p) (q' - p')
          (G.incidenceTorExteriorEquiv h x) (G.incidenceTorExteriorEquiv h' y)) := by
  apply G.exteriorCohomologyState_injective ℂ (q + q') ((q + q') - (p + p'))
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv,exteriorCohomologyState_cast,
    exteriorCohomologyState_product,exteriorCohomologyState_incidenceTorExteriorEquiv,
    exteriorCohomologyState_incidenceTorExteriorEquiv]
  exact G.incidenceTorFullState_product p p' x.val y.val

/-- The isomorphism sends the Tor unit to the exterior cohomology unit. -/
theorem incidenceTorExteriorEquiv_one :
    G.incidenceTorExteriorEquiv (le_refl 0) ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩ =
      G.exteriorCohomologyUnit ℂ := by
  apply G.exteriorCohomologyState_injective ℂ 0 0
  rw [exteriorCohomologyState_unit]
  exact (G.exteriorCohomologyState_incidenceTorExteriorEquiv (le_refl 0) _).trans
    G.incidenceTorFullState_one

end
end BPFixedPoints.Multigraph
