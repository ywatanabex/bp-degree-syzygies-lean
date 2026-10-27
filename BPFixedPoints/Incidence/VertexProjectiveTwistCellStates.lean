import BPFixedPoints.Incidence.VertexProjectiveTwistCellCoefficients

/-! # Original state projection and inclusion on the original cell cocycles

The source uses the original cell Hom differential. Projection and inclusion
are exactly those of the previously specified signed tensor contraction,
restricted to the independently defined original overlap degree.
-/

namespace BPFixedPoints.CechProduct
open Finsupp
variable (R : Type) [CommRing R] {V : Type} [Fintype V]

/-- The original state module restricted to its original cohomological degree. -/
abbrev stateDegreePiece (d : V → ℕ) (n : ℕ) : Submodule R (H R d) :=
  supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = n}

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original cocycles in original cell degree n, defined by the original Hom differential. -/
noncomputable abbrev vertexTwistCellCycles (d : V → ℕ) (n : ℕ) :=
  (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n

/-- Original tensor state projection on the original coefficient degree. -/
noncomputable def vertexTwistCellDegreeProjection (d : V → ℕ) (n : ℕ) :
    supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n} →ₗ[R]
      stateDegreePiece R d n :=
  ((contraction R d).p.comp (supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n}).subtype).codRestrict _
    fun x => by
      change (contraction R d).p x.val ∈ supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = n}
      simpa only [add_zero] using contraction_p_degree R d n x.val x.property

/-- The specified original state coordinate on each original cell cocycle. -/
noncomputable def vertexTwistCellCycleProjection (d : V → ℕ) (n : ℕ) :
    vertexTwistCellCycles R V d n →+ stateDegreePiece R d n :=
  (vertexTwistCellDegreeProjection R V d n).toAddMonoidHom.comp
    ((vertexTwistCellCoefficientEquiv R V d n).toAddMonoidHom.comp
      ((cubicalTower (vertexCoordinateOpen R V)).cycles
        (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n).subtype)

/-- The state coordinate is precisely the original full contraction projection in the specified signed coordinates. -/
theorem vertexTwistCellCycleProjection_val (d : V → ℕ) (n : ℕ) (x : vertexTwistCellCycles R V d n) :
    (vertexTwistCellCycleProjection R V d n x).val =
      (contraction R d).p (vertexTwistCellCoefficientEquiv R V d n x.val).val := rfl

/-- Original closedness is retained in the original tensor coefficient complex. -/
theorem vertexTwistCellCycleCoefficient_closed (d : V → ℕ) (n : ℕ) (x : vertexTwistCellCycles R V d n) :
    (contraction R d).d (vertexTwistCellCoefficientEquiv R V d n x.val).val = 0 := by
  rw [← vertexTwistCellCoefficientEquiv_tower_d]
  change (vertexTwistCellCoefficientEquiv R V d (n+1)
    ((cubicalTower (vertexCoordinateOpen R V)).cochainDifferential _ n x.val)).val = 0
  rw [x.property,map_zero]
  rfl

/-- The original degree-n state inclusion in the original coefficient chain degree. -/
noncomputable def vertexTwistCellDegreeInclusion (d : V → ℕ) (n : ℕ) : stateDegreePiece R d n →ₗ[R]
    supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n} :=
  ((contraction R d).i.comp (stateDegreePiece R d n).subtype).codRestrict _ fun x => by
    change (contraction R d).i x.val ∈ supported R R {b | (cechDegree b : ℤ) = n}
    simpa only [add_zero] using contraction_i_degree R d n x.val x.property

/-- The original full inclusion supplies the original cell cocycle representative in every original degree. -/
noncomputable def vertexTwistCellStateInclusion (d : V → ℕ) (n : ℕ) :
    stateDegreePiece R d n →+ vertexTwistCellCycles R V d n where
  toFun s := ⟨(vertexTwistCellCoefficientEquiv R V d n).symm (vertexTwistCellDegreeInclusion R V d n s),by
    apply (vertexTwistCellCoefficientEquiv R V d (n+1)).injective
    apply Subtype.ext
    rw [vertexTwistCellCoefficientEquiv_tower_d,map_zero,AddEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (contraction R d).d_i s.val⟩
  map_zero' := by
    apply Subtype.ext
    change (vertexTwistCellCoefficientEquiv R V d n).symm (vertexTwistCellDegreeInclusion R V d n 0) = 0
    rw [map_zero,map_zero]
  map_add' s t := by
    apply Subtype.ext
    change (vertexTwistCellCoefficientEquiv R V d n).symm (vertexTwistCellDegreeInclusion R V d n (s+t)) =
      (vertexTwistCellCoefficientEquiv R V d n).symm (vertexTwistCellDegreeInclusion R V d n s) +
        (vertexTwistCellCoefficientEquiv R V d n).symm (vertexTwistCellDegreeInclusion R V d n t)
    rw [map_add,map_add]

/-- Each inverse representative has exactly the originally specified full tensor inclusion. -/
theorem vertexTwistCellStateInclusion_coefficient (d : V → ℕ) (n : ℕ) (s : stateDegreePiece R d n) :
    (vertexTwistCellCoefficientEquiv R V d n (vertexTwistCellStateInclusion R V d n s).val).val =
      (contraction R d).i s.val :=
  congrArg Subtype.val ((vertexTwistCellCoefficientEquiv R V d n).apply_symm_apply _)

/-- The original cell state projection and inclusion retain the original contraction identity. -/
theorem vertexTwistCellCycleProjection_inclusion (d : V → ℕ) (n : ℕ) (s : stateDegreePiece R d n) :
    vertexTwistCellCycleProjection R V d n (vertexTwistCellStateInclusion R V d n s) = s := by
  apply Subtype.ext
  rw [vertexTwistCellCycleProjection_val,vertexTwistCellStateInclusion_coefficient]
  exact LinearMap.congr_fun (contraction R d).p_i s.val

/-- Every original state in every original degree is represented by an original cell cocycle. -/
theorem vertexTwistCellCycleProjection_surjective (d : V → ℕ) (n : ℕ) :
    Function.Surjective (vertexTwistCellCycleProjection R V d n) :=
  fun s => ⟨vertexTwistCellStateInclusion R V d n s,vertexTwistCellCycleProjection_inclusion R V d n s⟩

end BPFixedPoints.ProjectiveLine
