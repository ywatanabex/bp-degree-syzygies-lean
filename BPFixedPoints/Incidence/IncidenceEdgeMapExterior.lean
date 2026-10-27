import BPFixedPoints.Incidence.IncidenceEdgeMapTor

/-!
# Edge maps act on the actual exterior bundle and its cohomology

For an edge map `φ : EdgeMap G H` the vertex set and the vertex projective product are unchanged.
For a `q`-element edge subset `S` on which the edge function is injective, `φ S` is a `q`-element
edge subset of `H` with the same vertex degrees, so the summand `O(-d_S)` of the `q`-th exterior
bundle of `G` is literally the summand `O(-d_{φ S})` of `H`. The morphism of actual abelian
sheaves `exteriorEdgeMapHom` sends the summand of such an `S` to the summand of `φ S` with the wedge
sign of `S`, and is zero on the summands of edge subsets where the edge function is not injective.
It is built from the actual biproduct projections and inclusions of the exterior bundles. A version
as a morphism of sheaves of modules is not constructed here.

The induced map on actual Ext-defined cohomology (`exteriorCohomologyEdgeMap`) sends the state
vector of a class to the state map of its state vector (`exteriorCohomologyState_edgeMap`), is
linear for the original geometric base action (`exteriorCohomologyEdgeMapLinear`), preserves the
exterior cohomology products and sends the unit to the unit. Together with the Tor side it gives the
naturality square of `incidenceTorExteriorEquiv` for edge maps
(`incidenceTorExteriorEquiv_edgeMap_natural`).
-/

namespace BPFixedPoints

open CategoryTheory CategoryTheory.Limits

namespace Multigraph
open AlgebraicGeometry CategoryTheory.Abelian
open TopologicalSpace ProjectiveLine SchemeTools CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] exteriorProductHasExt

/-- Cohomology of a finite sum of sheaf morphisms is the sum of the cohomology maps. -/
theorem sheafH_map_sum_apply {V : Type} [Fintype V] (R : Type) [CommRing R] {ι : Type}
    (s : Finset ι)
    {F₁ F₂ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (f : ι → (F₁ ⟶ F₂)) (n : ℕ) (z : Sheaf.H.{1} F₁ n) :
    Sheaf.H.map (∑ i ∈ s, f i) n z = ∑ i ∈ s, Sheaf.H.map (f i) n z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, sheafH_map_zero_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Sheaf.H.map_add_apply, ih]

/-- The state vector of the inclusion of a summand class is the embedding of its state
coordinate. -/
theorem exteriorCohomologyState_incl {V E₀ : Type} [DecidableEq V] [Fintype V] [LinearOrder E₀]
    [Fintype E₀] (K : Multigraph V E₀) (R : Type) [CommRing R] [IsNoetherianRing R] (q j : ℕ)
    (U : Set.powersetCard E₀ q)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(K.deg U v : ℤ))) j) :
    K.exteriorCohomologyState R q j (Sheaf.H.map (K.exteriorIncl R q U) j z) =
      K.incStateEmbed R U (vertexTwistActualStateAt R V (K.deg U) j z).val := by
  rw [exteriorCohomologyState_apply, Finset.sum_eq_single U]
  · rw [← Sheaf.H.map_comp_apply, exteriorIncl_proj_self, Sheaf.H.map_id_apply]
  · intro U' _ hU'
    rw [← Sheaf.H.map_comp_apply, exteriorIncl_proj_ne K R q (Ne.symm hU'), sheafH_map_zero_apply,
      map_zero, ZeroMemClass.coe_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ U) h

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)
variable (R : Type) [CommRing R]

/-- The image of a `q`-element edge subset on which the edge function is injective, as a
`q`-element edge subset. -/
def imageSubset {q : ℕ} (S : Set.powersetCard E q) (h : Set.InjOn φ.edge (S : Finset E)) :
    Set.powersetCard E' q :=
  ⟨φ.edgeSet S, Set.powersetCard.mem_iff.mpr ((φ.card_edgeSet h).trans (Set.powersetCard.card_eq S))⟩

@[simp] theorem coe_imageSubset {q : ℕ} (S : Set.powersetCard E q)
    (h : Set.InjOn φ.edge (S : Finset E)) :
    ((φ.imageSubset S h : Set.powersetCard E' q) : Finset E') = φ.edgeSet S := rfl

/-- The twist of an edge subset equals the twist of its image edge subset. -/
theorem twist_imageSubset {q : ℕ} (S : Set.powersetCard E q) (h : Set.InjOn φ.edge (S : Finset E)) :
    (fun v => -(G.deg (S : Finset E) v : ℤ)) =
      fun v => -(H.deg ((φ.imageSubset S h : Set.powersetCard E' q) : Finset E') v : ℤ) := by
  rw [coe_imageSubset, φ.deg_edgeSet h]

/-- The identification of the abelian summand of an edge subset with the abelian summand of its
image edge subset. -/
def exteriorTwistHom {q : ℕ} (S : Set.powersetCard E q) (h : Set.InjOn φ.edge (S : Finset E)) :
    vertexTwistAbelianSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ)) ⟶
      vertexTwistAbelianSheaf R V
        (fun v => -(H.deg ((φ.imageSubset S h : Set.powersetCard E' q) : Finset E') v : ℤ)) :=
  eqToHom (congrArg (vertexTwistAbelianSheaf R V) (φ.twist_imageSubset S h))

open Classical in
/-- **The map of exterior bundles of an edge map**, as a morphism of the underlying actual abelian
sheaves: on the summand of an edge subset on which the edge function is injective, the wedge sign
times the identification with the summand of the image edge subset; zero on the other summands. -/
def exteriorEdgeMapHom (q : ℕ) : G.exteriorBundleAbelian R q ⟶ H.exteriorBundleAbelian R q :=
  ∑ S : Set.powersetCard E q,
    if h : Set.InjOn φ.edge (S : Finset E) then
      φ.wedgeSign S • (G.exteriorProj R q S ≫ φ.exteriorTwistHom R S h ≫
        H.exteriorIncl R q (φ.imageSubset S h))
    else 0

/-- The map induced on actual cohomology of the exterior bundles by an edge map. -/
def exteriorCohomologyEdgeMap (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  Sheaf.H.map (φ.exteriorEdgeMapHom R q) j

theorem exteriorCohomologyEdgeMap_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyEdgeMap R q j x = Sheaf.H.map (φ.exteriorEdgeMapHom R q) j x := rfl

/-- Cohomology of the identification of summands is the transport of actual cohomology. -/
theorem sheafH_map_exteriorTwistHom {q : ℕ} (S : Set.powersetCard E q)
    (h : Set.InjOn φ.edge (S : Finset E)) (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ))) n) :
    Sheaf.H.map (φ.exteriorTwistHom R S h) n z =
      vertexNegativeHCast R V (φ.deg_edgeSet h).symm rfl z := by
  rw [exteriorTwistHom]
  exact EdgeRelabel.sheafH_map_eqToHom_negative R (φ.deg_edgeSet h).symm _ n z

variable [IsNoetherianRing R]

/-- **State formula.** The state vector of the image of an exterior class is the state map of its
state vector. -/
theorem exteriorCohomologyState_edgeMap (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyEdgeMap R q j x) =
      φ.stateMap R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologyEdgeMap_apply, exteriorEdgeMapHom, sheafH_map_sum_apply, map_sum,
    exteriorCohomologyState_apply, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [stateMap_incStateEmbed]
  split_ifs with h
  · rw [sheafH_map_zsmul_apply, map_zsmul, Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply,
      exteriorCohomologyState_incl, sheafH_map_exteriorTwistHom, ← Int.cast_smul_eq_zsmul R]
    congr 2
    exact vertexTwistActualStateAt_cast R V (φ.deg_edgeSet h).symm rfl _
  · rw [sheafH_map_zero_apply, map_zero]

/-- The map induced on actual exterior cohomology by an edge map, as a linear map for the
original geometric base actions. -/
def exteriorCohomologyEdgeMapLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →ₗ[R] Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := H.exteriorBundleCohomologyModule R q j
  { φ.exteriorCohomologyEdgeMap R q j with
    map_smul' := fun r x => by
      apply H.exteriorCohomologyState_injective R q j
      change H.exteriorCohomologyState R q j (φ.exteriorCohomologyEdgeMap R q j (r • x)) =
        H.exteriorCohomologyState R q j (r • φ.exteriorCohomologyEdgeMap R q j x)
      rw [exteriorCohomologyState_edgeMap, map_smul, map_smul, map_smul,
        exteriorCohomologyState_edgeMap] }

/-- The linear map has the same underlying map. -/
theorem exteriorCohomologyEdgeMapLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyEdgeMapLinear R q j x = φ.exteriorCohomologyEdgeMap R q j x := rfl

/-- Edge maps preserve the exterior cohomology products. -/
theorem exteriorCohomologyEdgeMap_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologyEdgeMap R (q + q') (i + j) (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologyEdgeMap R q i x)
        (φ.exteriorCohomologyEdgeMap R q' j y) := by
  apply H.exteriorCohomologyState_injective R (q + q') (i + j)
  rw [exteriorCohomologyState_edgeMap, exteriorCohomologyState_product,
    exteriorCohomologyState_product, exteriorCohomologyState_edgeMap,
    exteriorCohomologyState_edgeMap, stateMap_incStateCup]

/-- Edge maps send the exterior cohomology unit to the unit. -/
theorem exteriorCohomologyEdgeMap_unit :
    φ.exteriorCohomologyEdgeMap R 0 0 (G.exteriorCohomologyUnit R) = H.exteriorCohomologyUnit R := by
  apply H.exteriorCohomologyState_injective R 0 0
  rw [exteriorCohomologyState_edgeMap, exteriorCohomologyState_unit, exteriorCohomologyState_unit,
    stateMap_incStateUnit]

/-- The exterior cohomology map of the identity edge map is the identity. -/
theorem exteriorCohomologyEdgeMap_refl (G : Multigraph V E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (refl G).exteriorCohomologyEdgeMap R q j x = x :=
  G.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_edgeMap, stateMap_refl])

/-- The exterior cohomology map of a composite edge map is the composite of the maps. -/
theorem exteriorCohomologyEdgeMap_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : EdgeMap H K) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    (φ.trans ψ).exteriorCohomologyEdgeMap R q j x =
      ψ.exteriorCohomologyEdgeMap R q j (φ.exteriorCohomologyEdgeMap R q j x) :=
  K.exteriorCohomologyState_injective R q j (by
    rw [exteriorCohomologyState_edgeMap, exteriorCohomologyState_edgeMap,
      exteriorCohomologyState_edgeMap, stateMap_trans])

end EdgeMap

/-- For an edge relabeling the exterior cohomology map of the underlying edge map is the exterior
cohomology relabeling. -/
theorem EdgeRelabel.exteriorCohomologyEdgeMap_toEdgeMap {V E E' : Type} [DecidableEq V]
    [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : EdgeRelabel G H) (R : Type) [CommRing R] [IsNoetherianRing R]
    (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.toEdgeMap.exteriorCohomologyEdgeMap R q j x = φ.exteriorCohomologyRelabel R q j x :=
  H.exteriorCohomologyState_injective R q j (by
    rw [EdgeMap.exteriorCohomologyState_edgeMap, exteriorCohomologyState_relabel,
      toEdgeMap_stateMap])

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- **Graph naturality of the bigraded Tor isomorphism for edge maps.** For an edge map
`φ : G → H`, the isomorphism `incidenceTorExteriorEquiv` of `H` composed with the Tor map of `φ`
is the exterior cohomology map of `φ` composed with the isomorphism of `G`. -/
theorem incidenceTorExteriorEquiv_edgeMap_natural {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalEdgeMap p q x) =
      φ.exteriorCohomologyEdgeMapLinear ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, exteriorCohomologyEdgeMapLinear_apply,
    exteriorCohomologyState_edgeMap, exteriorCohomologyState_incidenceTorExteriorEquiv,
    incidenceTorInternalEdgeMap_val, incidenceTorFullState_edgeMap]

end EdgeMap

end

end Multigraph

end BPFixedPoints
