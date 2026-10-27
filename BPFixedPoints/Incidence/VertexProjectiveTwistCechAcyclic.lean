import BPFixedPoints.Incidence.NoetherianAffineOpenCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistLocalFrames
import BPFixedPoints.Incidence.VertexProjectiveTwistPairFrames
import BPFixedPoints.Incidence.IncidenceProjectiveProper
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual higher local Ext groups on the original vertex-product Cech opens

All nonempty finite intersections of the original polynomial charts are
affine by native separatedness. Their section rings are Noetherian over a
Noetherian base, so the actual quasicoherent twist is acyclic on each such
intersection. No cohomology-vanishing hypotheses are supplied as inputs.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original vertex-labelled projective product is separated as an actual scheme. -/
instance vertexScheme_isSeparated : (vertexScheme R V).IsSeparated := by
  constructor
  rw [← terminal.comp_from (vertexToBase R V)]
  infer_instance

/-- The original polynomial chart image is a native affine open. -/
theorem vertexChartOpen_isAffine (σ : V → Fin 2) :
    IsAffineOpen (vertexChartOpen R V σ) :=
  isAffineOpen_opensRange (vertexChartι R V σ)

/-- Every nonempty finite intersection of the original chart images is affine. -/
theorem vertexChartIntersection_isAffine {ι : Sort*} [Finite ι] [Nonempty ι]
    (σ : ι → V → Fin 2) : IsAffineOpen (⨅ i, vertexChartOpen R V (σ i)) :=
  IsAffineOpen.iInf (fun i => vertexChartOpen_isAffine R V (σ i))

/-- The actual pair intersection is an affine open of the original product. -/
theorem vertexChartPairOpen_isAffine (σ τ : V → Fin 2) :
    IsAffineOpen (vertexChartPairOpen R V σ τ) :=
  (vertexChartOpen_isAffine R V σ).inf (vertexChartOpen_isAffine R V τ)

/-- Forget the module structure in the original multi-twist sheaf. -/
noncomputable def vertexTwistAbelianSheaf (a : V → ℤ) :
    Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj (vertexTwistSheaf R V a)

variable [IsNoetherianRing R]

/-- Native finite type over the original base makes the vertex product locally Noetherian. -/
instance vertexScheme_isLocallyNoetherian : IsLocallyNoetherian (vertexScheme R V) :=
  LocallyOfFiniteType.isLocallyNoetherian (vertexToBase R V)

noncomputable local instance vertexTwistCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- All positive actual local Ext groups vanish on every nonempty finite chart intersection. -/
theorem vertexTwistSheaf_chartIntersection_cohomology_eq_zero
    (a : V → ℤ) {ι : Sort*} [Finite ι] [Nonempty ι] (σ : ι → V → Fin 2)
    (n : ℕ) (x : (vertexTwistAbelianSheaf R V a).H' (n+1)
      (⨅ i, vertexChartOpen R V (σ i))) : x = 0 :=
  SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (vertexChartIntersection_isAffine R V σ) (vertexTwistSheaf R V a) n x

/-- Actual higher local Ext vanishes on the separately specified pair overlap. -/
theorem vertexTwistSheaf_pair_cohomology_eq_zero (a : V → ℤ) (σ τ : V → Fin 2)
    (n : ℕ) (x : (vertexTwistAbelianSheaf R V a).H' (n+1)
      (vertexChartPairOpen R V σ τ)) : x = 0 :=
  SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (vertexChartPairOpen_isAffine R V σ τ) (vertexTwistSheaf R V a) n x

/-- Every positive local Ext group on every ordered Cech intersection is a subsingleton. -/
theorem vertexTwistSheaf_cech_acyclic (a : V → ℤ) (q n : ℕ)
    (σ : Fin (q+1) → V → Fin 2) :
    Subsingleton ((vertexTwistAbelianSheaf R V a).H' (n+1)
      (⨅ i, vertexChartOpen R V (σ i))) :=
  subsingleton_of_forall_eq 0 (vertexTwistSheaf_chartIntersection_cohomology_eq_zero R V a σ n)

end BPFixedPoints.ProjectiveLine
