import BPFixedPoints.Incidence.IncidenceGraphMapTor
import BPFixedPoints.Incidence.IncidenceSignedEdgeMapExterior
import BPFixedPoints.Incidence.VertexMapTwistStateFormula
import BPFixedPoints.Incidence.IncidenceTorNormalizationInduction

/-!
# The exterior cohomology map of a general graph map and its naturality square

For a graph map `φ : GraphMap G H`, the map of actual Ext-defined exterior cohomology
`exteriorCohomologyMap R q j : H^j((P¹)^V, ∧^q F_G^∨) → H^j((P¹)^W, ∧^q F_H^∨)` is the composite of
the geometric pullback of the vertex factor along its coordinate map
(`VertexMap.exteriorCohomologyPullback`, built from the actual morphism of schemes) and the exterior
map of the signed edge factor (`SignedEdgeMap.exteriorCohomologySignedEdgeMap`). It is defined for
every commutative coefficient ring `R`, through this factorization.

**The naturality square** (`incidenceTorExteriorEquiv_graphMap`): the bigraded Tor-to-exterior
isomorphism `incidenceTorExteriorEquiv` carries the intrinsic Tor map of `φ` to the exterior map of
`φ`. It is obtained by pasting the squares of the two factors
(`VertexMap.incidenceTorExteriorEquiv_vertexMap`,
`SignedEdgeMap.incidenceTorExteriorEquiv_signedEdgeMap`) along the factorization of the Tor map
(`GraphMap.incidenceTorHom_eq_comp`).

**Consequences over `ℂ`**, in every exterior degree `q` and every cohomological degree `j`: in
degrees `j ≤ q` the isomorphism is surjective onto `H^j`, so the Tor-side statements transfer; in
degrees `j > q` the cohomology vanishes. The proofs use the induction principles
`exteriorCohomology_induction_on_tor`, `exteriorCohomology_induction₂_on_tor` and
`exteriorCohomology_ext_via_tor` for this case split. This gives
* the functor laws of the geometric map: the identity graph map acts trivially
  (`exteriorCohomologyMap_refl`) and composites act by composites (`exteriorCohomologyMap_trans`);
* agreement with the geometric maps of vertex maps and of signed edge maps regarded as graph maps
  (`VertexMap.toGraphMap_exteriorCohomologyMap`,
  `SignedEdgeMap.toGraphMap_exteriorCohomologyMap`), hence **independence of the factorization**:
  for every factorization of `φ` into a vertex map followed by a signed edge map, the composite of
  their geometric maps is the exterior map of `φ` (`exteriorCohomologyMap_eq_of_factorization`;
  the Tor-side version `incidenceTorHom_eq_of_factorization` holds as well);
* `ℂ`-linearity for the original geometric base action (`exteriorCohomologyMapLinear`);
* compatibility with the exterior cohomology products (`exteriorCohomologyMap_product`, through
  `incidenceTorExteriorEquiv_product` and the Tor-side product law) and with the unit
  (`exteriorCohomologyMap_unit`).

Not proved: any of these consequences over a general coefficient ring `R`. The argument goes
through the Tor side over `ℂ`; functoriality of the vertex pullback `sheafHPullback` under
composition of maps of schemes, and its compatibility with the exterior products, are not
formalized. The naturality square and the definition themselves do not depend on this.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] exteriorProductHasExt

namespace GraphMap

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
  {H : Multigraph W E'} (φ : GraphMap G H)

/-! ## The exterior cohomology map -/

section Definition

variable (R : Type) [CommRing R]

/-- **The exterior cohomology map of a graph map**: the geometric pullback along the coordinate map
of the vertex factor, followed by the exterior cohomology map of the signed edge factor. -/
def exteriorCohomologyMap (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  (φ.edgeFactor.exteriorCohomologySignedEdgeMap R q j).comp
    (φ.vertexFactor.exteriorCohomologyPullback R q j)

theorem exteriorCohomologyMap_apply (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyMap R q j x =
      φ.edgeFactor.exteriorCohomologySignedEdgeMap R q j
        (φ.vertexFactor.exteriorCohomologyPullback R q j x) :=
  rfl

end Definition

/-! ## The naturality square -/

/-- **The naturality square for graph maps.** The Tor-to-exterior isomorphism carries the
intrinsic Tor map of a graph map to its exterior cohomology map. -/
theorem incidenceTorExteriorEquiv_graphMap {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalMap p q x) =
      φ.exteriorCohomologyMap ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  rw [incidenceTorInternalMap_apply_eq, SignedEdgeMap.incidenceTorExteriorEquiv_signedEdgeMap,
    VertexMap.incidenceTorExteriorEquiv_vertexMap]
  rfl

/-! ## Consequences over `ℂ` -/

/-- A cohomological degree `j ≤ q` is of the form `q - p` with `p ≤ q`. -/
theorem exists_eq_sub_of_le {q j : ℕ} (hj : j ≤ q) : ∃ p, p ≤ q ∧ j = q - p :=
  ⟨q - j, Nat.sub_le q j, by omega⟩

/-- **Identity law for the geometric map** over `ℂ`: the exterior cohomology map of the identity
graph map is the identity, in every degree. -/
theorem exteriorCohomologyMap_refl (G : Multigraph V E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (refl G).exteriorCohomologyMap ℂ q j x = x := by
  refine DFunLike.congr_fun (exteriorCohomology_ext_via_tor
    (f := fun j => (refl G).exteriorCohomologyMap ℂ q j) (g := fun j => AddMonoidHom.id _)
    (fun p hp y => ?_) j) x
  rw [AddMonoidHom.id_apply, ← incidenceTorExteriorEquiv_graphMap]
  congr 1
  apply Subtype.ext
  rw [incidenceTorInternalMap_val, incidenceTorMap_refl]

/-- **Composition law for the geometric map** over `ℂ`: the exterior cohomology map of a composite
of graph maps is the composite of the exterior cohomology maps, in every degree. -/
theorem exteriorCohomologyMap_trans {X E'' : Type} [DecidableEq X] [Fintype X] [LinearOrder E'']
    [Fintype E''] {K : Multigraph X E''} (ψ : GraphMap H K) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (φ.trans ψ).exteriorCohomologyMap ℂ q j x =
      ψ.exteriorCohomologyMap ℂ q j (φ.exteriorCohomologyMap ℂ q j x) := by
  induction j, x using exteriorCohomology_induction_on_tor with
  | tor p hp y =>
    rw [← incidenceTorExteriorEquiv_graphMap, ← incidenceTorExteriorEquiv_graphMap,
      ← incidenceTorExteriorEquiv_graphMap]
    congr 1
    apply Subtype.ext
    rw [incidenceTorInternalMap_val, incidenceTorInternalMap_val, incidenceTorInternalMap_val]
    exact incidenceTorMap_trans φ ψ p y.val
  | vanish j _ => rw [map_zero, map_zero, map_zero]

/-- The exterior cohomology map of a graph map is `ℂ`-linear for the original geometric base
actions. -/
theorem exteriorCohomologyMap_smul (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule ℂ q j
    letI := H.exteriorBundleCohomologyModule ℂ q j
    ∀ (c : ℂ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j),
      φ.exteriorCohomologyMap ℂ q j (c • x) = c • φ.exteriorCohomologyMap ℂ q j x := by
  intro c x
  induction j, x using exteriorCohomology_induction_on_tor with
  | tor p hp y =>
    rw [← LinearEquiv.map_smul, ← incidenceTorExteriorEquiv_graphMap,
      ← incidenceTorExteriorEquiv_graphMap, LinearMap.map_smul, LinearEquiv.map_smul]
  | vanish j _ =>
    let _ := G.exteriorBundleCohomologyModule ℂ q j
    let _ := H.exteriorBundleCohomologyModule ℂ q j
    rw [smul_zero, map_zero, smul_zero]

/-- The exterior cohomology map of a graph map, as a `ℂ`-linear map for the original geometric base
actions. -/
def exteriorCohomologyMapLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule ℂ q j
    letI := H.exteriorBundleCohomologyModule ℂ q j
    Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j →ₗ[ℂ] Sheaf.H.{1} (H.exteriorBundleAbelian ℂ q) j :=
  letI := G.exteriorBundleCohomologyModule ℂ q j
  letI := H.exteriorBundleCohomologyModule ℂ q j
  { φ.exteriorCohomologyMap ℂ q j with
    map_smul' := φ.exteriorCohomologyMap_smul q j }

/-- The linear map has the same underlying map. -/
theorem exteriorCohomologyMapLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    φ.exteriorCohomologyMapLinear q j x = φ.exteriorCohomologyMap ℂ q j x :=
  rfl

/-- The exterior cohomology map of a graph map sends the exterior unit to the unit. -/
theorem exteriorCohomologyMap_unit :
    φ.exteriorCohomologyMap ℂ 0 0 (G.exteriorCohomologyUnit ℂ) = H.exteriorCohomologyUnit ℂ := by
  rw [← G.incidenceTorExteriorEquiv_one, ← H.incidenceTorExteriorEquiv_one]
  refine (φ.incidenceTorExteriorEquiv_graphMap (le_refl 0)
    ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩).symm.trans ?_
  congr 1
  apply Subtype.ext
  rw [incidenceTorInternalMap_val]
  exact φ.incidenceTorMap_one

/-- The exterior cohomology map commutes with transport along equalities of cohomological
degrees. -/
theorem exteriorCohomologyMap_hCast (R : Type) [CommRing R] (q : ℕ) {n n' : ℕ} (hn : n = n')
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) n) :
    φ.exteriorCohomologyMap R q n' (G.exteriorHCast R rfl hn x) =
      H.exteriorHCast R rfl hn (φ.exteriorCohomologyMap R q n x) := by
  subst hn
  rfl

/-- **Products.** Over `ℂ` the exterior cohomology map of a graph map preserves the exterior
cohomology products, in all degrees. -/
theorem exteriorCohomologyMap_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q') j) :
    φ.exteriorCohomologyMap ℂ (q + q') (i + j) (G.exteriorCohomologyProduct ℂ q q' i j x y) =
      H.exteriorCohomologyProduct ℂ q q' i j (φ.exteriorCohomologyMap ℂ q i x)
        (φ.exteriorCohomologyMap ℂ q' j y) := by
  induction i, j, x, y using exteriorCohomology_induction₂_on_tor with
  | tor p p' hp hp' a b =>
    have hn : (q - p) + (q' - p') = (q + q') - (p + p') := by omega
    have hG := G.incidenceTorExteriorEquiv_product hp hp' a b
    have hH := H.incidenceTorExteriorEquiv_product hp hp' (φ.incidenceTorInternalMap p q a)
      (φ.incidenceTorInternalMap p' q' b)
    rw [← incidenceTorExteriorEquiv_graphMap, ← incidenceTorExteriorEquiv_graphMap]
    apply (H.exteriorHCast ℂ rfl hn).injective
    rw [← hH, ← exteriorCohomologyMap_hCast, ← hG, ← incidenceTorExteriorEquiv_graphMap]
    congr 1
    apply Subtype.ext
    exact φ.incidenceTorMap_product p p' a.val b.val
  | vanish_left i j y _ => simp only [map_zero, AddMonoidHom.zero_apply]
  | vanish_right i j x _ => simp only [map_zero]

end GraphMap

/-! ## Vertex maps, signed edge maps and independence of the factorization -/

/-- **Agreement with vertex maps** over `ℂ`. For a vertex map, regarded as a graph map, the exterior
cohomology map is the geometric pullback along the coordinate map, in every degree. -/
theorem VertexMap.toGraphMap_exteriorCohomologyMap {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexMap G H) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    φ.toGraphMap.exteriorCohomologyMap ℂ q j x = φ.exteriorCohomologyPullback ℂ q j x := by
  induction j, x using exteriorCohomology_induction_on_tor with
  | tor p hp y =>
    rw [← GraphMap.incidenceTorExteriorEquiv_graphMap,
      ← VertexMap.incidenceTorExteriorEquiv_vertexMap]
    congr 1
    apply Subtype.ext
    rw [GraphMap.incidenceTorInternalMap_val, VertexMap.incidenceTorInternalVertexMap_val,
      VertexMap.toGraphMap_incidenceTorMap]
  | vanish j _ => rw [map_zero, map_zero]

/-- **Agreement with signed edge maps** over `ℂ`. For a signed edge map, regarded as a graph map,
the exterior cohomology map is the exterior cohomology map of the signed edge map, in every
degree. -/
theorem SignedEdgeMap.toGraphMap_exteriorCohomologyMap {V E E' : Type} [DecidableEq V]
    [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeMap G H) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    φ.toGraphMap.exteriorCohomologyMap ℂ q j x = φ.exteriorCohomologySignedEdgeMap ℂ q j x := by
  induction j, x using exteriorCohomology_induction_on_tor with
  | tor p hp y =>
    rw [← GraphMap.incidenceTorExteriorEquiv_graphMap,
      ← SignedEdgeMap.exteriorCohomologySignedEdgeMapLinear_apply,
      ← SignedEdgeMap.incidenceTorExteriorEquiv_signedEdgeMap]
    congr 1
    apply Subtype.ext
    rw [GraphMap.incidenceTorInternalMap_val, SignedEdgeMap.incidenceTorInternalSignedEdgeMap_val,
      SignedEdgeMap.toGraphMap_incidenceTorMap]
  | vanish j _ => rw [map_zero, map_zero]

namespace GraphMap

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
  {H : Multigraph W E'} (φ : GraphMap G H)

/-- **Independence of the factorization for the geometric map** over `ℂ`. For every factorization
of a graph map into a vertex map followed by a signed edge map, the composite of their geometric
maps is the exterior cohomology map of the graph map, in every degree. -/
theorem exteriorCohomologyMap_eq_of_factorization {G' : Multigraph W E} (α : VertexMap G G')
    (β : SignedEdgeMap G' H) (hφ : α.toGraphMap.trans β.toGraphMap = φ) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    φ.exteriorCohomologyMap ℂ q j x =
      β.exteriorCohomologySignedEdgeMap ℂ q j (α.exteriorCohomologyPullback ℂ q j x) := by
  subst hφ
  rw [exteriorCohomologyMap_trans, VertexMap.toGraphMap_exteriorCohomologyMap,
    SignedEdgeMap.toGraphMap_exteriorCohomologyMap]

end GraphMap

end

end BPFixedPoints.Multigraph
