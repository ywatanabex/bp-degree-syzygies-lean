import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalDegree
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoMiddleAll

/-! # Degree-one cohomology of actual cubical sections and actual two-vertex H1 -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]

/-- Original native degree-zero cochains on the actual original face sections. -/
noncomputable abbrev vertexTwistTwoNativeZeroChains (d : Fin 2 → ℕ) :=
  vertexTwistCubicalDegree R (Fin 2) (fun v => -(d v : ℤ)) 0

/-- Original native degree-one cocycles, using the independently defined actual restriction differential. -/
noncomputable def vertexTwistTwoNativeMiddleCycles (d : Fin 2 → ℕ) :
    Submodule R (VertexTwistCubicalSections R (Fin 2) (fun v => -(d v : ℤ))) :=
  vertexTwistCubicalDegree R (Fin 2) (fun v => -(d v : ℤ)) 1 ⊓
    LinearMap.ker (vertexTwistCubicalD R (Fin 2) (fun v => -(d v : ℤ)))

@[reducible] noncomputable local instance nativeZeroChainsAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (vertexTwistTwoNativeZeroChains R d) := (vertexTwistTwoNativeZeroChains R d).addCommGroup
@[reducible] noncomputable local instance nativeMiddleCyclesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (vertexTwistTwoNativeMiddleCycles R d) := (vertexTwistTwoNativeMiddleCycles R d).addCommGroup
@[reducible] noncomputable local instance nativeMiddleCyclesModule (d : Fin 2 → ℕ) :
    Module R (vertexTwistTwoNativeMiddleCycles R d) := (vertexTwistTwoNativeMiddleCycles R d).module
@[reducible] noncomputable local instance coefficientZeroChainsAddCommGroup :
    AddCommGroup (twoZeroChains R) := (twoZeroChains R).addCommGroup
@[reducible] noncomputable local instance coefficientMiddleCyclesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (twoMiddleCycles R d) := (twoMiddleCycles R d).addCommGroup
@[reducible] noncomputable local instance coefficientMiddleCyclesModule (d : Fin 2 → ℕ) :
    Module R (twoMiddleCycles R d) := (twoMiddleCycles R d).module

/-- Original native boundaries from the original actual degree-zero sections. -/
noncomputable def vertexTwistTwoNativeMiddleBoundary (d : Fin 2 → ℕ) :
    vertexTwistTwoNativeZeroChains R d →ₗ[R] vertexTwistTwoNativeMiddleCycles R d :=
  ((vertexTwistCubicalD R (Fin 2) (fun v => -(d v : ℤ))).comp
    (vertexTwistTwoNativeZeroChains R d).subtype).codRestrict _ fun x => by
      constructor
      · change VertexTwistCubicalHomogeneous R (Fin 2) (fun v => -(d v : ℤ)) 1
          (vertexTwistCubicalD R (Fin 2) (fun v => -(d v : ℤ)) x.val)
        simpa only [zero_add] using vertexTwistCubicalD_degree R (Fin 2) d 0 x.val x.property
      · exact vertexTwistCubicalD_square R (Fin 2) d x.val

/-- The existing signed native chain comparison restricts to the original degree-zero chains. -/
noncomputable def vertexTwistTwoNativeZeroChainEquiv (d : Fin 2 → ℕ) :
    vertexTwistTwoNativeZeroChains R d ≃ₗ[R] twoZeroChains R where
  toFun x := ⟨vertexTwistCubicalChainEquiv R (Fin 2) d x.val,
    (vertexTwistCubicalDegree_chain R (Fin 2) d 0 x.val).mpr x.property⟩
  invFun x := ⟨(vertexTwistCubicalChainEquiv R (Fin 2) d).symm x.val,by
    apply (vertexTwistCubicalDegree_chain R (Fin 2) d 0 _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply _ x.val)
  map_add' x y := Subtype.ext ((vertexTwistCubicalChainEquiv R (Fin 2) d).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((vertexTwistCubicalChainEquiv R (Fin 2) d).map_smul r x.val)

/-- The existing signed native chain comparison restricts to the original full middle cocycles. -/
noncomputable def vertexTwistTwoNativeMiddleCycleEquiv (d : Fin 2 → ℕ) :
    vertexTwistTwoNativeMiddleCycles R d ≃ₗ[R] twoMiddleCycles R d where
  toFun x := ⟨vertexTwistCubicalChainEquiv R (Fin 2) d x.val,⟨
    (vertexTwistCubicalDegree_chain R (Fin 2) d 1 x.val).mpr x.property.1,by
      change (contraction R d).d (vertexTwistCubicalChainEquiv R (Fin 2) d x.val) = 0
      rw [← vertexTwistCubicalChainEquiv_d,x.property.2,map_zero]⟩⟩
  invFun x := ⟨(vertexTwistCubicalChainEquiv R (Fin 2) d).symm x.val,⟨by
    apply (vertexTwistCubicalDegree_chain R (Fin 2) d 1 _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact x.property.1,by
    apply (vertexTwistCubicalChainEquiv R (Fin 2) d).injective
    rw [vertexTwistCubicalChainEquiv_d,LinearEquiv.apply_symm_apply,x.property.2,map_zero]⟩⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply _ x.val)
  map_add' x y := Subtype.ext ((vertexTwistCubicalChainEquiv R (Fin 2) d).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((vertexTwistCubicalChainEquiv R (Fin 2) d).map_smul r x.val)

/-- In degree one the specified signed comparison is minus the original unsigned frame coordinate. -/
theorem vertexTwistTwoNativeMiddleCycleEquiv_face (d : Fin 2 → ℕ)
    (x : vertexTwistTwoNativeMiddleCycles R d) (q : Fin 2 → Fin 3) (hq : faceDegree q = 1) :
    faceEquiv R (vertexTwistTwoNativeMiddleCycleEquiv R d x).val q =
      -vertexTwistSheafFaceSectionsEquiv R (Fin 2) (fun v => -(d v : ℤ)) q (x.val q) := by
  change faceEquiv R (vertexTwistCubicalChainEquiv R (Fin 2) d x.val) q = _
  rw [vertexTwistCubicalChainEquiv_face,hq,pow_one,neg_one_smul]

/-- The specified signed comparison carries each native degree-zero boundary to its original coefficient boundary. -/
theorem vertexTwistTwoNativeMiddleBoundary_compare (d : Fin 2 → ℕ)
    (x : vertexTwistTwoNativeZeroChains R d) :
    vertexTwistTwoNativeMiddleCycleEquiv R d (vertexTwistTwoNativeMiddleBoundary R d x) =
      twoMiddleBoundary R d (vertexTwistTwoNativeZeroChainEquiv R d x) := by
  apply Subtype.ext
  exact vertexTwistCubicalChainEquiv_d R (Fin 2) d x.val

/-- The original signed chain comparison preserves exactly the original native boundary image. -/
theorem vertexTwistTwoNativeMiddleCycleEquiv_range (d : Fin 2 → ℕ) :
    (LinearMap.range (vertexTwistTwoNativeMiddleBoundary R d)).map
      (vertexTwistTwoNativeMiddleCycleEquiv R d).toLinearMap = LinearMap.range (twoMiddleBoundary R d) := by
  ext z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    exact ⟨vertexTwistTwoNativeZeroChainEquiv R d y,(vertexTwistTwoNativeMiddleBoundary_compare R d y).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨vertexTwistTwoNativeMiddleBoundary R d ((vertexTwistTwoNativeZeroChainEquiv R d).symm y),
      ⟨_,rfl⟩,?_⟩
    change vertexTwistTwoNativeMiddleCycleEquiv R d
      (vertexTwistTwoNativeMiddleBoundary R d ((vertexTwistTwoNativeZeroChainEquiv R d).symm y)) = _
    rw [vertexTwistTwoNativeMiddleBoundary_compare,LinearEquiv.apply_symm_apply]

/-- Degree-one cohomology of the original actual cubical section complex, using its original native boundaries. -/
noncomputable abbrev vertexTwistTwoNativeMiddleCohomology (d : Fin 2 → ℕ) :=
  vertexTwistTwoNativeMiddleCycles R d ⧸ LinearMap.range (vertexTwistTwoNativeMiddleBoundary R d)

/-- The existing signed chain map induces the specified comparison on actual-section degree-one cohomology. -/
noncomputable def vertexTwistTwoNativeMiddleCoefficientEquiv (d : Fin 2 → ℕ) :
    vertexTwistTwoNativeMiddleCohomology R d ≃ₗ[R] twoMiddleCohomology R d :=
  Submodule.Quotient.equiv _ _ (vertexTwistTwoNativeMiddleCycleEquiv R d)
    (vertexTwistTwoNativeMiddleCycleEquiv_range R d)

/-- Every native cocycle class keeps the specified signed coefficient representative. -/
theorem vertexTwistTwoNativeMiddleCoefficientEquiv_mk (d : Fin 2 → ℕ)
    (x : vertexTwistTwoNativeMiddleCycles R d) :
    vertexTwistTwoNativeMiddleCoefficientEquiv R d (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (vertexTwistTwoNativeMiddleCycleEquiv R d x) := rfl

/-- The original state inclusion, expressed on the original native actual face sections. -/
noncomputable def vertexTwistTwoNativeMiddleInclusion (d : Fin 2 → ℕ) :
    twoMiddleStatePiece R d →ₗ[R] vertexTwistTwoNativeMiddleCycles R d :=
  (vertexTwistTwoNativeMiddleCycleEquiv R d).symm.toLinearMap.comp (twoMiddleInclusion R d)

/-- The native representative is exactly the previously established native cubical contraction inclusion. -/
theorem vertexTwistTwoNativeMiddleInclusion_val (d : Fin 2 → ℕ) (s : twoMiddleStatePiece R d) :
    (vertexTwistTwoNativeMiddleInclusion R d s).val =
      (vertexTwistCubicalContraction R (Fin 2) d).i s.val := rfl

variable [IsNoetherianRing R]

/-- Actual cubical degree-one cohomology equals actual sheaf H1 through the specified signed coordinates and native connecting comparison. -/
noncomputable def vertexTwistTwoNativeH1Equiv (d : Fin 2 → ℕ) :
    vertexTwistTwoNativeMiddleCohomology R d ≃ₗ[R] vertexTwistTwoH1Module R d :=
  (vertexTwistTwoNativeMiddleCoefficientEquiv R d).trans (vertexTwistTwoMiddleCohomologyAllEquiv R d)

/-- Each native cocycle class retains its specified signed coordinates and original native row-kernel or glued connecting class. -/
theorem vertexTwistTwoNativeH1Equiv_mk (d : Fin 2 → ℕ) (x : vertexTwistTwoNativeMiddleCycles R d) :
    vertexTwistTwoNativeH1Equiv R d (Submodule.Quotient.mk x) =
      vertexTwistTwoMiddleCocyclesToH1All R d (vertexTwistTwoNativeMiddleCycleEquiv R d x) := rfl

/-- On every native cocycle the actual state coordinate is the already established native cubical contraction projection. -/
theorem vertexTwistTwoNativeH1Equiv_projection (d : Fin 2 → ℕ) (x : vertexTwistTwoNativeMiddleCycles R d) :
    (vertexTwistTwoH1StateEquiv R d (vertexTwistTwoNativeH1Equiv R d (Submodule.Quotient.mk x))).val =
      (vertexTwistCubicalContraction R (Fin 2) d).p x.val := by
  rw [vertexTwistTwoNativeH1Equiv_mk,vertexTwistTwoMiddleCocyclesToH1All_projection]
  rfl

/-- Every native cohomology class retains the specified original full contraction coordinate. -/
theorem vertexTwistTwoNativeH1Equiv_class_projection (d : Fin 2 → ℕ)
    (x : vertexTwistTwoNativeMiddleCohomology R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoNativeH1Equiv R d x) =
      twoMiddleCohomologyStateEquiv R d (vertexTwistTwoNativeMiddleCoefficientEquiv R d x) :=
  vertexTwistTwoMiddleCohomologyAllEquiv_projection R d _

/-- The specified native contraction inclusion gives the actual inverse state class. -/
theorem vertexTwistTwoNativeH1Equiv_inclusion (d : Fin 2 → ℕ) (s : twoMiddleStatePiece R d) :
    vertexTwistTwoNativeH1Equiv R d
      (Submodule.Quotient.mk (vertexTwistTwoNativeMiddleInclusion R d s)) =
        (vertexTwistTwoH1StateEquiv R d).symm s := by
  change vertexTwistTwoMiddleCohomologyAllEquiv R d
    (Submodule.Quotient.mk (vertexTwistTwoNativeMiddleCycleEquiv R d
      ((vertexTwistTwoNativeMiddleCycleEquiv R d).symm (twoMiddleInclusion R d s)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact vertexTwistTwoMiddleCohomologyAllEquiv_inclusion R d s

end BPFixedPoints.ProjectiveLine
