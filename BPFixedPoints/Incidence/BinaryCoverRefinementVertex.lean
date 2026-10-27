import BPFixedPoints.Incidence.BinaryCoverRefinementCup
import BPFixedPoints.Incidence.VertexProjectiveTwistStandardCup
import BPFixedPoints.Incidence.VertexProjectiveTwistCellAcyclic

/-! # The standard product on vertex twist cohomology does not depend on the binary cover

On the product of projective lines over a Noetherian base, the standard
product on actual Ext-defined cohomology of the integral multi-twists was
defined through the standard coordinate cover `vertexCoordinateOpen R V`.
Let `W` be any binary cover family on the same scheme, indexed by any finite
type, whose charts cover and whose cell opens are all affine. The scheme is
separated, so every intersection of a standard cell open with a cell open of `W`
is affine. Affine vanishing of quasi-coherent cohomology then supplies the
relative acyclicity of the cell complexes of `W` and of the concatenated family
against every twist, and the standard product computed through `W` equals the
standard one (`vertexTwistStandardClassCup_cover_independent`).

The standard coordinate cover relabelled along any surjection `σ : J → V` of
direction sets (in particular any reordering by an equivalence, or a cover
with repeated directions) satisfies these hypotheses, so the product computed
through it is the standard one (`vertexTwistStandardClassCup_relabel`).

Covers with non-affine cell opens are not treated.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace Function
open SheafTools.BinaryCells ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexRefinementHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance vertexRefinementDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _
variable [IsNoetherianRing R]
variable {J : Type} [Fintype J] [DecidableEq J]

/-- Affine cell opens make the cell terms of a binary cover family of the vertex product acyclic
against every integral twist. -/
theorem binaryCoverTwist_terms_acyclic (W : J → Fin 2 → (vertexScheme R V).Opens)
    (haff : ∀ q, IsAffineOpen (SheafTools.binaryCoverFaceOpen W q)) (a : V → ℤ) :
    ComplexAcyclicAgainst (sheafComplex W) (vertexTwistAbelianSheaf R V a) := by
  apply sheafComplex_acyclic
  intro n q k
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (haff q.val) (vertexTwistSheaf R V a) k

/-- The cell terms of the concatenation of the standard cover with a family with affine cell
opens are acyclic against every integral twist. -/
theorem binaryCoverTwist_sum_terms_acyclic (W : J → Fin 2 → (vertexScheme R V).Opens)
    (haff : ∀ q, IsAffineOpen (SheafTools.binaryCoverFaceOpen W q)) (a : V → ℤ) :
    ComplexAcyclicAgainst (sheafComplex (Sum.elim (vertexCoordinateOpen R V) W))
      (vertexTwistAbelianSheaf R V a) :=
  sheafComplex_sum_acyclic _ _ _ fun p p' k =>
    SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
      ((vertexBinaryFaceOpen_isAffine R V p).inf (haff p')) (vertexTwistSheaf R V a) k

/-- The standard product on vertex twist cohomology computed through any binary cover family
with covering charts and affine cell opens is the standard product computed through the standard
coordinate cover. -/
theorem vertexTwistStandardClassCup_cover_independent (W : J → Fin 2 → (vertexScheme R V).Opens)
    (hcov : (⊤ : (vertexScheme R V).Opens) ≤ ⨆ k, chartOpen W k)
    (haff : ∀ q, IsAffineOpen (SheafTools.binaryCoverFaceOpen W q)) (a b : V → ℤ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    actualStandardClassCup W hcov (vertexTwistAbelianSectionPairing R V a b)
        (binaryCoverTwist_terms_acyclic R V W haff a) (binaryCoverTwist_terms_acyclic R V W haff b)
        i j x y =
      vertexTwistStandardClassCup R V a b i j x y :=
  (actualStandardClassCup_concat (vertexTwistAbelianSectionPairing R V a b)
    (vertexCoordinateOpen R V) W (vertexCellChartOpen_cover R V) hcov
    (binaryCoverTwist_sum_terms_acyclic R V W haff a) (binaryCoverTwist_sum_terms_acyclic R V W haff b)
    (vertexTwistCellSheaf_terms_acyclic R V a) (vertexTwistCellSheaf_terms_acyclic R V b)
    (binaryCoverTwist_terms_acyclic R V W haff a) (binaryCoverTwist_terms_acyclic R V W haff b)
    i j x y).symm

omit [IsNoetherianRing R] in
/-- The standard coordinate cover relabelled along a surjection of direction sets has affine cell
opens. -/
theorem vertexRelabelFaceOpen_isAffine (σ : J → V) (hσ : Surjective σ) (q : J → Fin 3) :
    IsAffineOpen (SheafTools.binaryCoverFaceOpen (fun j => vertexCoordinateOpen R V (σ j)) q) := by
  rw [binaryCoverFaceOpen_comp_surjective (vertexCoordinateOpen R V) hσ q]
  exact vertexBinaryFaceOpen_isAffine R V _

omit [IsNoetherianRing R] in
/-- The charts of the standard coordinate cover relabelled along any map of direction sets cover. -/
theorem vertexRelabelChartOpen_cover (σ : J → V) :
    (⊤ : (vertexScheme R V).Opens) ≤ ⨆ k, chartOpen (fun j => vertexCoordinateOpen R V (σ j)) k :=
  chartOpen_comp_cover (vertexCoordinateOpen R V) σ (vertexCellChartOpen_cover R V)

/-- The standard product computed through the standard coordinate cover relabelled along a
surjection of direction sets is the standard product. -/
theorem vertexTwistStandardClassCup_relabel (σ : J → V) (hσ : Surjective σ) (a b : V → ℤ)
    (i j : ℕ) (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    actualStandardClassCup (fun j => vertexCoordinateOpen R V (σ j))
        (vertexRelabelChartOpen_cover R V σ) (vertexTwistAbelianSectionPairing R V a b)
        (binaryCoverTwist_terms_acyclic R V _ (vertexRelabelFaceOpen_isAffine R V σ hσ) a)
        (binaryCoverTwist_terms_acyclic R V _ (vertexRelabelFaceOpen_isAffine R V σ hσ) b) i j x y =
      vertexTwistStandardClassCup R V a b i j x y :=
  vertexTwistStandardClassCup_cover_independent R V _ _ (vertexRelabelFaceOpen_isAffine R V σ hσ) a b i j x y

/-- In particular the standard product does not depend on the order of the directions: the
standard coordinate cover reindexed along an equivalence computes the same product. -/
theorem vertexTwistStandardClassCup_reindex (e : J ≃ V) (a b : V → ℤ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    actualStandardClassCup (fun j => vertexCoordinateOpen R V (e j))
        (vertexRelabelChartOpen_cover R V e) (vertexTwistAbelianSectionPairing R V a b)
        (binaryCoverTwist_terms_acyclic R V _ (vertexRelabelFaceOpen_isAffine R V e e.surjective) a)
        (binaryCoverTwist_terms_acyclic R V _ (vertexRelabelFaceOpen_isAffine R V e e.surjective) b)
        i j x y =
      vertexTwistStandardClassCup R V a b i j x y :=
  vertexTwistStandardClassCup_relabel R V e e.surjective a b i j x y

end
end BPFixedPoints.ProjectiveLine
