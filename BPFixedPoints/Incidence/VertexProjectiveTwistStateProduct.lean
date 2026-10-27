import BPFixedPoints.Incidence.VertexProjectiveTwistStandardCup
import BPFixedPoints.Incidence.VertexProjectiveTwistCupStates

/-! # The standard product on actual cohomology corresponds to the state product

For nonpositive twists the actual Ext-defined cohomology is compared with
the original state pieces in every degree: the inverse of the original
geometric Yoneda comparison followed by the original contraction
projection. This composite is injective in every degree (in degree zero by
the original contraction homotopy and the absence of negative Čech degree).
The standard product of actual classes, transported along the original
twist identity (-d)+(-e) = -(d+e), has as state coordinate exactly the
existing state product of the two state coordinates. No product is
transported from states: the standard product is defined geometrically and
this is a theorem. Twist transport is the identity after substitution.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct Finsupp
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexStateProductHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Transport of actual cohomology along an equality of integral twists. -/
def vertexTwistHCast {a a' : V → ℤ} (h : a = a') (n : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n ≃+ Sheaf.H.{1} (vertexTwistAbelianSheaf R V a') n := by
  subst h
  exact AddEquiv.refl _

/-- Transport along the reflexive equality is the identity. -/
@[simp] theorem vertexTwistHCast_rfl (a : V → ℤ) (n : ℕ) (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :
    vertexTwistHCast R V (rfl : a = a) n x = x := rfl

/-- Original postcomposition by the identity of the target sheaf fixes every original class. -/
theorem cubicalMapAt_id (a : V → ℤ) (n : ℕ) (z : vertexTwistCellCohomologyAt R V a n) :
    (cubicalTower (vertexCoordinateOpen R V)).mapAt (𝟙 (vertexTwistAbelianSheaf R V a)) n z = z := by
  obtain ⟨z,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ n z
  rw [ExactTower.mapAt_class]
  congr 1

/-- Transport commutes with the original postcomposition by the twist identity on original classes. -/
theorem vertexTwistHCast_mapAt {a a' : V → ℤ} (h : a = a') (n : ℕ)
    (z : vertexTwistCellCohomologyAt R V a n) (g : (c : V → ℤ) → vertexTwistCellCohomologyAt R V c n →
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V c) n) :
    g a' ((cubicalTower (vertexCoordinateOpen R V)).mapAt
        (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h)) n z) = vertexTwistHCast R V h n (g a z) := by
  subst h
  rw [eqToHom_refl,cubicalMapAt_id,vertexTwistHCast_rfl]

/-- The original degree-zero contraction projection is injective on original cell cocycles. -/
theorem vertexTwistCellCycleProjection_zero_injective (d : V → ℕ) :
    Function.Injective (vertexTwistCellCycleProjection R V d 0) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  let c := (vertexTwistCellCoefficientEquiv R V d 0 x.val).val
  have hp : (contraction R d).p c = 0 := by
    have := congrArg Subtype.val hx
    rwa [vertexTwistCellCycleProjection_val] at this
  have hd : (contraction R d).d c = 0 := vertexTwistCellCycleCoefficient_closed R V d 0 x
  have hh : (contraction R d).h c = 0 := by
    have hm := contraction_h_degree R d 0 c (vertexTwistCellCoefficientEquiv R V d 0 x.val).property
    rw [Finsupp.mem_supported] at hm
    ext b
    by_contra hb
    have := hm (Finsupp.mem_support_iff.mpr hb)
    simp only [Set.mem_ofPred_eq] at this
    omega
  have hc : c = 0 := by
    have hom := LinearMap.congr_fun (contraction R d).homotopy c
    simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.comp_apply,Module.End.one_apply,
      hh,hd,hp,map_zero,add_zero] at hom
    exact hom.symm
  have h0 : vertexTwistCellCoefficientEquiv R V d 0 x.val = 0 := Subtype.ext hc
  exact Subtype.ext ((AddEquiv.map_eq_zero_iff _).mp h0)

/-- The original all-degree state projection is injective on original cell cohomology. -/
theorem vertexTwistCellStateAt_injective (d : V → ℕ) (n : ℕ) :
    Function.Injective (vertexTwistCellStateAt R V d n) := by
  cases n with
  | zero => exact vertexTwistCellCycleProjection_zero_injective R V d
  | succ n => exact (vertexTwistCellStateAddEquiv R V d n).injective

variable [IsNoetherianRing R]

/-- Actual cohomology of a nonpositive twist in its original state coordinates. -/
def vertexTwistActualStateAt (d : V → ℕ) (n : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n →+ stateDegreePiece R d n :=
  letI := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) n
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (fun v => -(d v : ℤ))) n
  (vertexTwistCellStateAt R V d n).comp
    (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n).symm.toAddEquiv.toAddMonoidHom

/-- The state coordinate of an original class is the original state projection. -/
theorem vertexTwistActualStateAt_actual (d : V → ℕ) (n : ℕ)
    (z : vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) n) :
    vertexTwistActualStateAt R V d n (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n z) =
      vertexTwistCellStateAt R V d n z := by
  simp [vertexTwistActualStateAt]

/-- The state coordinates of actual cohomology are injective in every degree. -/
theorem vertexTwistActualStateAt_injective (d : V → ℕ) (n : ℕ) :
    Function.Injective (vertexTwistActualStateAt R V d n) := by
  intro x y hxy
  obtain ⟨x,rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n).surjective x
  obtain ⟨y,rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n).surjective y
  rw [vertexTwistActualStateAt_actual,vertexTwistActualStateAt_actual] at hxy
  rw [vertexTwistCellStateAt_injective R V d n hxy]

/-- The transported standard product of actual classes has the existing state product as its state coordinate. -/
theorem vertexTwistActualStateAt_standardCup (d e : V → ℕ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j) :
    (vertexTwistActualStateAt R V (d+e) (i+j) (vertexTwistHCast R V (vertexTwistNegativeAdd V d e) (i+j)
        (vertexTwistStandardClassCup R V _ _ i j x y))).val =
      cohomologyCup R d e (vertexTwistActualStateAt R V d i x).val (vertexTwistActualStateAt R V e j y).val := by
  obtain ⟨x,rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V _ i).surjective x
  obtain ⟨y,rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V _ j).surjective y
  rw [← vertexTwistStandardClassCup_yoneda,
    ← vertexTwistHCast_mapAt R V (vertexTwistNegativeAdd V d e) (i+j) _
      (fun c z => vertexTwistCellActualAtLinearEquiv R V c (i+j) z),
    vertexTwistActualStateAt_actual,vertexTwistActualStateAt_actual,vertexTwistActualStateAt_actual]
  exact vertexTwistNegativeCellCohomologyCup_states R V d e i j x y

end
end BPFixedPoints.ProjectiveLine
