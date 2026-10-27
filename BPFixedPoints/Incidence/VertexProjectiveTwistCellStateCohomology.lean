import BPFixedPoints.Incidence.VertexProjectiveTwistCellStates

/-! # Original cell cohomology equals the original state degree piece

The kernel of the specified original projection is exactly the original
preceding cell Hom boundary image. Its primitive is the previously specified
original tensor homotopy, in the original preceding overlap degree.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

@[reducible] noncomputable local instance cellStatePieceAddCommGroup (d : V → ℕ) (n : ℕ) :
    AddCommGroup (stateDegreePiece R d n) := (stateDegreePiece R d n).addCommGroup
@[reducible] noncomputable local instance cellStatePieceModule (d : V → ℕ) (n : ℕ) :
    Module R (stateDegreePiece R d n) := (stateDegreePiece R d n).module
@[reducible] noncomputable local instance cellCocyclesAddCommGroup (d : V → ℕ) (n : ℕ) :
    AddCommGroup (vertexTwistCellCycles R V d n) := by infer_instance

/-- The original cell boundary image is precisely the kernel of the original specified full state projection. -/
theorem vertexTwistCellBoundary_range (d : V → ℕ) (n : ℕ) :
    ((cubicalTower (vertexCoordinateOpen R V)).boundary
      (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n).range =
        (vertexTwistCellCycleProjection R V d (n+1)).ker := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    apply Subtype.ext
    rw [vertexTwistCellCycleProjection_val]
    change (contraction R d).p (vertexTwistCellCoefficientEquiv R V d (n+1)
      ((cubicalTower (vertexCoordinateOpen R V)).cochainDifferential _ n f)).val = 0
    rw [vertexTwistCellCoefficientEquiv_tower_d]
    exact LinearMap.congr_fun (contraction R d).p_d _
  · intro hx
    have hp : (contraction R d).p (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).val = 0 :=
      congrArg Subtype.val hx
    have hg : (contraction R d).h (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).val ∈
        supported R R {b | (cechDegree b : ℤ) = n} := by
      have h := contraction_h_degree R d (n+1)
        (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).val
        (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).property
      simpa only [Nat.cast_add,Nat.cast_one,add_neg_cancel_right] using h
    let z : supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n} :=
      ⟨(contraction R d).h (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).val,hg⟩
    refine ⟨(vertexTwistCellCoefficientEquiv R V d n).symm z,?_⟩
    apply Subtype.ext
    apply (vertexTwistCellCoefficientEquiv R V d (n+1)).injective
    apply Subtype.ext
    change (vertexTwistCellCoefficientEquiv R V d (n+1)
      ((cubicalTower (vertexCoordinateOpen R V)).cochainDifferential _ n _)).val = _
    rw [vertexTwistCellCoefficientEquiv_tower_d,AddEquiv.apply_symm_apply]
    have he := GradedContraction.ChainPairing.cycle_decomposition
      (a := contraction R d) (vertexTwistCellCycleCoefficient_closed R V d (n+1) x)
    simpa only [hp,map_zero,add_zero] using he.symm

section StateEquivalence
attribute [local irreducible] contraction vertexTwistCellCycleProjection
  vertexScheme vertexTwistAbelianSheaf sheafComplex
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true

/-- Original positive cell cohomology is the original state piece by exactly the specified original projection. -/
noncomputable def vertexTwistCellStateAddEquiv (d : V → ℕ) (n : ℕ) :
    vertexTwistCellCohomology R V (fun v => -(d v : ℤ)) n ≃+ stateDegreePiece R d (n+1) := by
  let A := vertexTwistCellCycles R V d (n+1)
  let D := stateDegreePiece R d (n+1)
  let B : AddSubgroup A := ((cubicalTower (vertexCoordinateOpen R V)).boundary
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n).range
  let g : A →+ D := vertexTwistCellCycleProjection R V d (n+1)
  have he : B = g.ker := vertexTwistCellBoundary_range R V d n
  have hg : Function.Surjective g := vertexTwistCellCycleProjection_surjective R V d (n+1)
  let e₁ : (A ⧸ B) ≃+ (A ⧸ g.ker) := QuotientAddGroup.quotientAddEquivOfEq he
  let e₂ : (A ⧸ g.ker) ≃+ D := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  exact e₁.trans e₂

end StateEquivalence

/-- Every original cocycle representative retains the original full contraction projection. -/
theorem vertexTwistCellStateAddEquiv_mk (d : V → ℕ) (n : ℕ) (x : vertexTwistCellCycles R V d (n+1)) :
    vertexTwistCellStateAddEquiv R V d n (QuotientAddGroup.mk x) =
      vertexTwistCellCycleProjection R V d (n+1) x := rfl

/-- The specified original state comparison is linear for the original geometric coefficient action on cell cohomology. -/
noncomputable def vertexTwistCellStateLinearEquiv (d : V → ℕ) (n : ℕ) :
    letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
    vertexTwistCellCohomology R V (fun v => -(d v : ℤ)) n ≃ₗ[R] stateDegreePiece R d (n+1) := by
  letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
  refine { vertexTwistCellStateAddEquiv R V d n with map_smul' := ?_ }
  intro r x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change vertexTwistCellCycleProjection R V d (n+1)
      ((cubicalTower (vertexCoordinateOpen R V)).mapCycles
        (SchemeTools.schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (fun v => -(d v : ℤ))) r)
        (n+1) x) = r • vertexTwistCellCycleProjection R V d (n+1) x
    apply Subtype.ext
    change (contraction R d).p (vertexTwistCellCoefficientEquiv R V d (n+1)
      (x.val ≫ SchemeTools.schemeBaseAbelianScalar (vertexToBase R V)
        (vertexTwistSheaf R V (fun v => -(d v : ℤ))) r)).val =
      r • (contraction R d).p (vertexTwistCellCoefficientEquiv R V d (n+1) x.val).val
    rw [vertexTwistCellCoefficientEquiv_postcomp_scalar]
    exact (contraction R d).p.map_smul r _

end BPFixedPoints.ProjectiveLine
