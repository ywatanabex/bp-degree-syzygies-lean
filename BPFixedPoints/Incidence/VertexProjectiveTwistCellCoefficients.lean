import BPFixedPoints.Incidence.VertexProjectiveTwistCellNative

/-! # The original cell cochains retain the original signed coefficient chains

The previously specified native chain equivalence restricts to every
original degree. Original geometric scalar postcomposition and every
original differential are retained, before taking cocycles or quotients.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Original geometric scalar postcomposition is the original scalar on the native actual cochains. -/
theorem vertexTwistCellNativeEquiv_postcomp_scalar (a : V → ℤ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a) (r : R) :
    vertexTwistCellNativeEquiv R V a n
      (f ≫ SchemeTools.schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r) =
        r • vertexTwistCellNativeEquiv R V a n f := by
  apply (vertexTwistDegreeSectionsEquiv R V a n).injective
  funext q
  change (vertexTwistCellNativeEquiv R V a n _).val q.val =
    r • (vertexTwistCellNativeEquiv R V a n f).val q.val
  rw [vertexTwistCellNativeEquiv_apply,vertexTwistCellNativeEquiv_apply]
  rfl

/-- The original signed native chain map restricts to exactly the original coefficient degree. -/
noncomputable def vertexTwistNativeCoefficientDegreeEquiv (d : V → ℕ) (n : ℕ) :
    vertexTwistCubicalDegree R V (fun v => -(d v : ℤ)) (n : ℤ) ≃ₗ[R]
      supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n} where
  toFun x := ⟨vertexTwistCubicalChainEquiv R V d x.val,
    (vertexTwistCubicalDegree_chain R V d n x.val).mpr x.property⟩
  invFun x := ⟨(vertexTwistCubicalChainEquiv R V d).symm x.val,by
    apply (vertexTwistCubicalDegree_chain R V d n _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv x := Subtype.ext (LinearEquiv.apply_symm_apply _ x.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' r x := Subtype.ext (map_smul _ r x.val)

/-- Original cell Hom cochains are the original coefficient chains through the previously specified signed coordinates. -/
noncomputable def vertexTwistCellCoefficientEquiv (d : V → ℕ) (n : ℕ) :
    (sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) ≃+
      supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n} :=
  (vertexTwistCellNativeEquiv R V _ n).trans
    (vertexTwistNativeCoefficientDegreeEquiv R V d n).toAddEquiv

/-- Every original Hom differential has exactly the original signed tensor coefficient differential. -/
theorem vertexTwistCellCoefficientEquiv_d (d : V → ℕ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) :
    (vertexTwistCellCoefficientEquiv R V d (n+1)
      ((sheafComplex (vertexCoordinateOpen R V)).d (n+1) n ≫ f)).val =
        (contraction R d).d (vertexTwistCellCoefficientEquiv R V d n f).val := by
  change vertexTwistCubicalChainEquiv R V d
    (vertexTwistCellNativeEquiv R V _ (n+1) _).val = _
  rw [vertexTwistCellNativeEquiv_d,vertexTwistCubicalChainEquiv_d]
  rfl

/-- The canonical tower differential remains the same originally specified coefficient differential. -/
theorem vertexTwistCellCoefficientEquiv_tower_d (d : V → ℕ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) :
    (vertexTwistCellCoefficientEquiv R V d (n+1)
      ((cubicalTower (vertexCoordinateOpen R V)).cochainDifferential
        (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n f)).val =
      (contraction R d).d (vertexTwistCellCoefficientEquiv R V d n f).val := by
  change (vertexTwistCellCoefficientEquiv R V d (n+1)
    ((cubicalTower (vertexCoordinateOpen R V)).differential n ≫ f)).val = _
  rw [ExtResolutionTools.complexTower_differential]
  exact vertexTwistCellCoefficientEquiv_d R V d n f

/-- The specified signed coefficient coordinates retain the original geometric scalar action. -/
theorem vertexTwistCellCoefficientEquiv_postcomp_scalar (d : V → ℕ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) (r : R) :
    vertexTwistCellCoefficientEquiv R V d n
      (f ≫ SchemeTools.schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (fun v => -(d v : ℤ))) r) =
        r • vertexTwistCellCoefficientEquiv R V d n f := by
  change vertexTwistNativeCoefficientDegreeEquiv R V d n
    (vertexTwistCellNativeEquiv R V _ n _) = _
  rw [vertexTwistCellNativeEquiv_postcomp_scalar,map_smul]
  rfl

end BPFixedPoints.ProjectiveLine
