import BPFixedPoints.Incidence.IncidenceSignedEdgeMapTor
import BPFixedPoints.Incidence.IncidenceEdgeMapExterior

/-!
# Signed edge maps act on the actual exterior bundle and its cohomology

For a signed edge map `φ : SignedEdgeMap G H` with edge sign `ε`, the morphism of actual abelian
sheaves `exteriorSignedEdgeMapHom` of the `q`-th exterior bundles is the sign change of the
exterior bundle of `G` followed by the exterior bundle map of the edge map. Explicitly
(`exteriorSignedEdgeMapHom_eq`), it sends the summand `O(-d_S)` of a `q`-element edge subset `S` on
which the edge function is injective to the summand of `φ S` with the factor
`wedgeSign S · ∏_{e ∈ S} ε_e`, and is zero on the other summands: the map induced by
`e ↦ ε_e e_{φ e}` (`signedExteriorMap_single`). A version as a morphism of sheaves of modules is
not constructed here.

The induced map on actual Ext-defined cohomology (`exteriorCohomologySignedEdgeMap`) is the
exterior sign change followed by the exterior map of the edge map
(`exteriorCohomologySignedEdgeMap_apply`); it sends the state vector of a class to the signed
state map of its state vector (`exteriorCohomologyState_signedEdgeMap`), is linear for the
original geometric base action (`exteriorCohomologySignedEdgeMapLinear`), preserves the exterior
cohomology products, sends the unit to the unit, is the identity for the identity signed edge map,
composes functorially, and for a signed relabeling is `exteriorCohomologySignedRelabel`. Together
with the Tor side it gives the naturality square of `incidenceTorExteriorEquiv`
(`incidenceTorExteriorEquiv_signedEdgeMap`).
-/

namespace BPFixedPoints

open CategoryTheory CategoryTheory.Limits

namespace Multigraph
open AlgebraicGeometry CategoryTheory.Abelian
open TopologicalSpace ProjectiveLine SchemeTools CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] exteriorProductHasExt

namespace SignedEdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)
variable (R : Type) [CommRing R]

/-- **The map of exterior bundles of a signed edge map**, as a morphism of the underlying actual
abelian sheaves: the sign change of the exterior bundle of `G` followed by the exterior bundle map
of the edge map. -/
def exteriorSignedEdgeMapHom (q : ℕ) : G.exteriorBundleAbelian R q ⟶ H.exteriorBundleAbelian R q :=
  G.exteriorSignHom φ.edgeSign R q ≫ φ.toEdgeMap.exteriorEdgeMapHom R q

/-- Integer scalars of a composite of morphisms in a preadditive category multiply. -/
private theorem zsmul_zsmul_comp {C : Type*} [Category C] [Preadditive C] {X Y Z : C} (m n : ℤ)
    (f : X ⟶ Y) (g : Y ⟶ Z) : m • ((n • f) ≫ g) = (m * n) • (f ≫ g) := by
  rw [Preadditive.zsmul_comp, smul_smul]

open Classical in
/-- The exterior bundle map of a signed edge map on summands: on the summand of an edge subset `S`
on which the edge function is injective, `wedgeSign S · ∏_{e ∈ S} ε_e` times the identification
with the summand of the image edge subset; zero on the other summands. -/
theorem exteriorSignedEdgeMapHom_eq (q : ℕ) :
    φ.exteriorSignedEdgeMapHom R q =
      ∑ S : Set.powersetCard E q,
        if h : Set.InjOn φ.edge (S : Finset E) then
          (φ.toEdgeMap.wedgeSign S * exteriorSign φ.edgeSign q S) •
            (G.exteriorProj R q S ≫ φ.toEdgeMap.exteriorTwistHom R S h ≫
              H.exteriorIncl R q (φ.toEdgeMap.imageSubset S h))
        else 0 := by
  rw [exteriorSignedEdgeMapHom, EdgeMap.exteriorEdgeMapHom, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with h
  · rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorSignHom_proj]
    exact zsmul_zsmul_comp _ _ _ _
  · rw [comp_zero]

/-- The map induced on actual cohomology of the exterior bundles by a signed edge map. -/
def exteriorCohomologySignedEdgeMap (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  Sheaf.H.map (φ.exteriorSignedEdgeMapHom R q) j

/-- The cohomology map of a signed edge map is the exterior sign change followed by the exterior
cohomology map of the edge map. -/
theorem exteriorCohomologySignedEdgeMap_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologySignedEdgeMap R q j x =
      φ.toEdgeMap.exteriorCohomologyEdgeMap R q j (G.exteriorCohomologySign φ.edgeSign R q j x) :=
  Sheaf.H.map_comp_apply _ _ x

variable [IsNoetherianRing R]

/-- **State formula.** The state vector of the image of an exterior class is the signed state map
of its state vector. -/
theorem exteriorCohomologyState_signedEdgeMap (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologySignedEdgeMap R q j x) =
      φ.signedStateMap R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologySignedEdgeMap_apply, EdgeMap.exteriorCohomologyState_edgeMap,
    exteriorCohomologyState_sign]
  rfl

/-- The map induced on actual exterior cohomology by a signed edge map, as a linear map for the
original geometric base actions. -/
def exteriorCohomologySignedEdgeMapLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →ₗ[R] Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := H.exteriorBundleCohomologyModule R q j
  { φ.exteriorCohomologySignedEdgeMap R q j with
    map_smul' := fun r x => by
      apply H.exteriorCohomologyState_injective R q j
      change H.exteriorCohomologyState R q j (φ.exteriorCohomologySignedEdgeMap R q j (r • x)) =
        H.exteriorCohomologyState R q j (r • φ.exteriorCohomologySignedEdgeMap R q j x)
      rw [exteriorCohomologyState_signedEdgeMap, map_smul, map_smul, map_smul,
        exteriorCohomologyState_signedEdgeMap] }

/-- The linear map has the same underlying map. -/
theorem exteriorCohomologySignedEdgeMapLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologySignedEdgeMapLinear R q j x = φ.exteriorCohomologySignedEdgeMap R q j x :=
  rfl

/-- The linear map is the linear exterior sign change followed by the linear exterior cohomology
map of the edge map. -/
theorem exteriorCohomologySignedEdgeMapLinear_eq_comp (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    φ.exteriorCohomologySignedEdgeMapLinear R q j =
      φ.toEdgeMap.exteriorCohomologyEdgeMapLinear R q j ∘ₗ
        (G.exteriorCohomologySignLinear φ.edgeSign R q j).toLinearMap :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := H.exteriorBundleCohomologyModule R q j
  LinearMap.ext (φ.exteriorCohomologySignedEdgeMap_apply R q j)

/-- Signed edge maps preserve the exterior cohomology products. -/
theorem exteriorCohomologySignedEdgeMap_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologySignedEdgeMap R (q + q') (i + j)
        (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologySignedEdgeMap R q i x)
        (φ.exteriorCohomologySignedEdgeMap R q' j y) := by
  rw [exteriorCohomologySignedEdgeMap_apply, exteriorCohomologySign_product,
    EdgeMap.exteriorCohomologyEdgeMap_product, exteriorCohomologySignedEdgeMap_apply,
    exteriorCohomologySignedEdgeMap_apply]

/-- Signed edge maps send the exterior cohomology unit to the unit. -/
theorem exteriorCohomologySignedEdgeMap_unit :
    φ.exteriorCohomologySignedEdgeMap R 0 0 (G.exteriorCohomologyUnit R) =
      H.exteriorCohomologyUnit R := by
  rw [exteriorCohomologySignedEdgeMap_apply, exteriorCohomologySign_unit,
    EdgeMap.exteriorCohomologyEdgeMap_unit]

/-- The exterior cohomology map of the identity signed edge map is the identity. -/
theorem exteriorCohomologySignedEdgeMap_refl (G : Multigraph V E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (refl G).exteriorCohomologySignedEdgeMap R q j x = x :=
  G.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_signedEdgeMap, signedStateMap_refl])

/-- The exterior cohomology map of a composite of signed edge maps, with signs
`e ↦ ε_φ(e) · ε_ψ(φ e)`, is the composite of the maps. -/
theorem exteriorCohomologySignedEdgeMap_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : SignedEdgeMap H K) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (φ.trans ψ).exteriorCohomologySignedEdgeMap R q j x =
      ψ.exteriorCohomologySignedEdgeMap R q j (φ.exteriorCohomologySignedEdgeMap R q j x) :=
  K.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_signedEdgeMap, exteriorCohomologyState_signedEdgeMap,
      exteriorCohomologyState_signedEdgeMap, signedStateMap_trans])

/-- An unsigned edge map, regarded as a signed edge map, has its unsigned exterior cohomology
map. -/
theorem exteriorCohomologySignedEdgeMap_ofEdgeMap (ψ : EdgeMap G H) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (ofEdgeMap ψ).exteriorCohomologySignedEdgeMap R q j x = ψ.exteriorCohomologyEdgeMap R q j x :=
  H.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_signedEdgeMap, EdgeMap.exteriorCohomologyState_edgeMap,
      ofEdgeMap_signedStateMap])

/-- A pure sign change, regarded as a signed edge map, has the exterior cohomology sign
change. -/
theorem exteriorCohomologySignedEdgeMap_ofEdgeSign (ε : EdgeSign E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (ofEdgeSign G ε).exteriorCohomologySignedEdgeMap R q j x =
      G.exteriorCohomologySign ε R q j x :=
  G.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_signedEdgeMap, exteriorCohomologyState_sign,
      ofEdgeSign_signedStateMap])

end SignedEdgeMap

/-- For a signed relabeling the exterior cohomology map of the underlying signed edge map is the
exterior cohomology map `exteriorCohomologySignedRelabel`. -/
theorem SignedEdgeRelabel.exteriorCohomologySignedEdgeMap_toSignedEdgeMap {V E E' : Type}
    [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E']
    {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeRelabel G H) (R : Type) [CommRing R]
    [IsNoetherianRing R] (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.toSignedEdgeMap.exteriorCohomologySignedEdgeMap R q j x =
      φ.exteriorCohomologySignedRelabel R q j x :=
  H.exteriorCohomologyState_injective R q j (by
    rw [SignedEdgeMap.exteriorCohomologyState_signedEdgeMap, exteriorCohomologyState_signedRelabel,
      toSignedEdgeMap_signedStateMap])

namespace SignedEdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)

/-- **Naturality of the bigraded Tor isomorphism under signed edge maps.** For a signed edge map
`φ : G → H`, the isomorphism `incidenceTorExteriorEquiv` of `H` composed with the Tor map of `φ`
is the exterior cohomology map of `φ` composed with the isomorphism of `G`. -/
theorem incidenceTorExteriorEquiv_signedEdgeMap {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalSignedEdgeMap p q x) =
      φ.exteriorCohomologySignedEdgeMapLinear ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv,
    exteriorCohomologySignedEdgeMapLinear_apply, exteriorCohomologyState_signedEdgeMap,
    exteriorCohomologyState_incidenceTorExteriorEquiv, incidenceTorInternalSignedEdgeMap_val,
    incidenceTorFullState_signedEdgeMap]

end SignedEdgeMap

end

end Multigraph

end BPFixedPoints
