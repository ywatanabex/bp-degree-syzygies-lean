import BPFixedPoints.Incidence.VertexProjectiveTwistCechAcyclic
import BPFixedPoints.Incidence.SheafCohomologyBinaryCover

/-! # Actual multi-twist cohomology above the number of vertices

The original vertex projections supply the binary covers. Every original
rectangular face is a pair intersection of actual polynomial charts. Native
Mayer--Vietoris and affine acyclicity therefore kill the genuine Ext groups
above the number of vertices, without a Kunneth or dimension formula input.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original standard open in one vertex direction of the actual product. -/
noncomputable def vertexCoordinateOpen (v : V) (i : Fin 2) : (vertexScheme R V).Opens :=
  (vertexProjectionOver R V v).left ⁻¹ᵁ standardOpen R i

/-- The two original standard opens cover each original vertex direction. -/
theorem vertexCoordinateOpen_cover (v : V) :
    vertexCoordinateOpen R V v 0 ⊔ vertexCoordinateOpen R V v 1 = ⊤ := by
  rw [vertexCoordinateOpen, vertexCoordinateOpen, ← Scheme.Hom.preimage_sup,
    standardOpen_cover R, Scheme.Hom.preimage_top]

/-- The original polynomial chart is the intersection of its original vertex-coordinate opens. -/
theorem vertexChartOpen_eq_coordinateOpen (σ : V → Fin 2) :
    vertexChartOpen R V σ = ⨅ v, vertexCoordinateOpen R V v (σ v) := by
  ext x
  simp only [Opens.coe_iInf, Set.mem_iInter, vertexCoordinateOpen]
  exact mem_vertexChartOpen R V σ x

/-- A rectangular left/right/overlap face is the intersection of the corresponding two original charts. -/
theorem vertexBinaryFaceOpen_eq_pair (q : V → Fin 3) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q =
      vertexChartPairOpen R V (fun v => if q v = 1 then 1 else 0)
        (fun v => if q v = 0 then 0 else 1) := by
  have h (v : V) : SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v) =
      vertexCoordinateOpen R V v (if q v = 1 then 1 else 0) ⊓
        vertexCoordinateOpen R V v (if q v = 0 then 0 else 1) := by
    generalize q v = j
    fin_cases j <;> simp [SheafTools.binaryCoverFaceFactor]
  simp only [SheafTools.binaryCoverFaceOpen, vertexChartPairOpen, vertexChartOpen_eq_coordinateOpen, h]
  apply le_antisymm
  · exact le_inf (le_iInf fun v => (iInf_le _ v).trans inf_le_left)
      (le_iInf fun v => (iInf_le _ v).trans inf_le_right)
  · apply le_iInf
    intro v
    exact le_inf (inf_le_left.trans (iInf_le _ v)) (inf_le_right.trans (iInf_le _ v))

/-- Every original rectangular face is a native affine open, including the empty vertex set. -/
theorem vertexBinaryFaceOpen_isAffine (q : V → Fin 3) :
    IsAffineOpen (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) := by
  rw [vertexBinaryFaceOpen_eq_pair]
  exact vertexChartPairOpen_isAffine R V _ _

variable [IsNoetherianRing R]
noncomputable local instance vertexTwistHigherHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- All genuine local cohomology above the number of vertices vanishes on the full original product. -/
theorem vertexTwistSheaf_top_higher_cohomology_eq_zero (a : V → ℤ) (k : ℕ)
    (x : (vertexTwistAbelianSheaf R V a).H' (Fintype.card V+k+1) ⊤) : x = 0 := by
  apply SheafTools.sheaf_cohomology_finiteBinaryCover_bound (vertexTwistAbelianSheaf R V a)
    (vertexCoordinateOpen R V) (vertexCoordinateOpen_cover R V) ⊤ _ k x
  intro q j
  rw [top_inf_eq]
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (vertexBinaryFaceOpen_isAffine R V q) (vertexTwistSheaf R V a) j

/-- The actual global Ext cohomology of every integral multi-twist vanishes above the number of vertices. -/
theorem vertexTwistSheaf_higher_cohomology_eq_zero (a : V → ℤ) (k : ℕ)
    (x : (vertexTwistAbelianSheaf R V a).H (Fintype.card V+k+1)) : x = 0 := by
  let e := SheafTools.localSheafTopEquiv (vertexTwistAbelianSheaf R V a) (Fintype.card V+k+1)
  have h : e.symm x = 0 := vertexTwistSheaf_top_higher_cohomology_eq_zero R V a k (e.symm x)
  simpa only [AddEquiv.apply_symm_apply, map_zero] using congrArg e h

end BPFixedPoints.ProjectiveLine
