import BPFixedPoints.Graph.Basic
import BPFixedPoints.Incidence.VertexProjectiveTwistCechAcyclic

/-! # The actual edge bundles and exterior bundle as finite biproducts of twist sheaves

Each edge `e` gives the actual multi-twist line sheaf `L_e` on the original
vertex projective product, with twist the endpoint count of `e` at every
vertex; a loop contributes twist two at its vertex, and parallel edges give
separate summands. The edge bundle `F` and its dual are actual finite
biproducts of these line sheaves in the abelian category of sheaves of
modules. Neither exterior powers nor duals of sheaves of modules are
available, so the `q`-th exterior power of the dual bundle is defined
directly as the actual finite biproduct, over the `q`-element edge subsets
`S`, of the twist sheaves `O(-d_S)` with `d_S` the multigraph degree of `S`.
In degree one this is the dual edge bundle; in degree zero it is the
structure twist. The chart-by-chart identification with Mathlib exterior
powers and the exterior product are separate obligations.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite biproducts of actual sheaves of modules on the original vertex projective product. -/
instance vertexSheafOfModules_hasFiniteBiproducts (R : Type) [CommRing R] (V : Type) [Fintype V] :
    HasFiniteBiproducts (SheafOfModules (vertexScheme R V).ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {V E : Type} [DecidableEq V] [Fintype V] (G : Multigraph V E)
variable (R : Type) [CommRing R]

/-- The actual line sheaf of an edge: the multi-twist by the endpoint count, so a loop has twist two. -/
noncomputable def edgeLineSheaf (e : E) : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  vertexTwistSheaf R V (fun v => (G.endCount e v : ℤ))

/-- The actual dual line sheaf of an edge: the multi-twist by minus the endpoint count. -/
noncomputable def edgeDualLineSheaf (e : E) : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  vertexTwistSheaf R V (fun v => -(G.endCount e v : ℤ))

/-- The actual exterior summand of an edge subset: the multi-twist by minus its multigraph degree. -/
noncomputable def exteriorSummand (S : Finset E) : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  vertexTwistSheaf R V (fun v => -(G.deg S v : ℤ))

/-- The underlying abelian sheaf of an exterior summand is the actual abelian multi-twist. -/
theorem exteriorSummand_abelian (S : Finset E) :
    (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj (G.exteriorSummand R S) =
      vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ)) := rfl

/-- The exterior summand of the empty edge subset is the untwisted multi-twist sheaf. -/
theorem exteriorSummand_empty :
    G.exteriorSummand R ∅ = vertexTwistSheaf R V (fun _ => 0) := by
  simp only [exteriorSummand, deg_empty, Nat.cast_zero, neg_zero]

/-- The exterior summand of a single edge is that edge's dual line sheaf, loops included. -/
theorem exteriorSummand_singleton (e : E) :
    G.exteriorSummand R {e} = G.edgeDualLineSheaf R e := by
  simp only [exteriorSummand, edgeDualLineSheaf, deg, Finset.sum_singleton]

/-- There is exactly one edge subset of cardinality zero. -/
instance powersetCardZeroUnique : Unique (Set.powersetCard E 0) where
  default := ⟨∅, by simp⟩
  uniq S := Subtype.ext (Finset.card_eq_zero.mp (Set.powersetCard.card_eq S))

variable [Fintype E]

/-- The actual edge bundle: the finite biproduct of all edge line sheaves. -/
noncomputable def edgeBundle : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  ⨁ fun e : E => G.edgeLineSheaf R e

/-- The actual dual edge bundle: the finite biproduct of all dual edge line sheaves. -/
noncomputable def edgeDualBundle : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  ⨁ fun e : E => G.edgeDualLineSheaf R e

/-- The actual `q`-th exterior bundle of the dual edge bundle: the finite biproduct, over all
`q`-element edge subsets, of the multi-twists by minus their multigraph degrees. -/
noncomputable def exteriorBundle (q : ℕ) : SheafOfModules (vertexScheme R V).ringCatSheaf :=
  ⨁ fun S : Set.powersetCard E q => G.exteriorSummand R S

/-- The underlying actual abelian sheaf of the `q`-th exterior bundle. -/
noncomputable def exteriorBundleAbelian (q : ℕ) :
    Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj (G.exteriorBundle R q)

/-- The first exterior bundle is the dual edge bundle, matching the singleton `{e}` with `e`. -/
noncomputable def exteriorBundleOneIso : G.exteriorBundle R 1 ≅ G.edgeDualBundle R :=
  (biproduct.whiskerEquiv Set.powersetCard.ofSingleton
    (fun e => eqToIso (G.exteriorSummand_singleton R e))).symm

/-- The inverse of the degree-one identification sends the summand of `e` to the summand of `{e}`. -/
@[reassoc] theorem ι_exteriorBundleOneIso_inv (e : E) :
    biproduct.ι (fun e : E => G.edgeDualLineSheaf R e) e ≫ (G.exteriorBundleOneIso R).inv =
      eqToHom (G.exteriorSummand_singleton R e).symm ≫
        biproduct.ι (fun S : Set.powersetCard E 1 => G.exteriorSummand R S)
          (Set.powersetCard.ofSingleton e) := by
  simp only [exteriorBundleOneIso, Iso.symm_inv, biproduct.whiskerEquiv_hom, biproduct.ι_desc,
    eqToIso.inv]

/-- The zeroth exterior bundle is the untwisted multi-twist sheaf. -/
noncomputable def exteriorBundleZeroIso :
    G.exteriorBundle R 0 ≅ vertexTwistSheaf R V (fun _ => 0) :=
  biproductUniqueIso (fun S : Set.powersetCard E 0 => G.exteriorSummand R S) ≪≫
    eqToIso (G.exteriorSummand_empty R)

end BPFixedPoints.Multigraph
