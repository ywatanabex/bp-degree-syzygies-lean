import BPFixedPoints.Incidence.SchemeModuleMayerVietorisKernel
import BPFixedPoints.Incidence.CechTwoRowH1Kernel

/-! # Actual two-vertex H1 and the original outer restriction kernel -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SchemeTools TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R]
noncomputable local instance vertexTwoH1KernelHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original first-coordinate cover, with its actual whole-space target. -/
noncomputable def vertexTwoOuterSquare :
    (Opens.grothendieckTopology (vertexScheme R (Fin 2))).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1
      X₂ := vertexCoordinateOpen R (Fin 2) 0 0
      X₃ := vertexCoordinateOpen R (Fin 2) 0 1
      X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    (vertexCoordinateOpen_cover R (Fin 2) 0).symm rfl

/-- Actual global H1, with the independently defined original geometric action. -/
noncomputable def vertexTwistTwoH1Module (d : Fin 2 → ℕ) : ModuleCat.{1} R := by
  letI := schemeBaseCohomologyModule (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1
  exact ModuleCat.of R (Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))) 1)

/-- A negative second twist has zero actual degree-zero group on the original first overlap. -/
theorem vertexTwistTwoOverlapH0_subsingleton (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
      (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))).H' 0 (vertexTwoOuterSquare R).X₁) := by
  let e := schemeBaseLocalH0LinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R).X₁
  refine ⟨fun x y => e.injective ?_⟩
  exact (vertexTwistRowSection_eq_zero_of_pos R d 2 hd (e x)).trans
    (vertexTwistRowSection_eq_zero_of_pos R d 2 hd (e y)).symm

/-- When the second twist is negative, actual global H1 is the original kernel of row H1 restrictions. -/
noncomputable def vertexTwistTwoH1RestrictionKernelEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoH1Module R d ≃ₗ[R]
      LinearMap.ker (schemeBaseSquareCohomologyDifference (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1) := by
  let : Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))).H' 0 (vertexTwoOuterSquare R).X₁) :=
      vertexTwistTwoOverlapH0_subsingleton R d hd
  exact (schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1).symm.trans
      (schemeBaseSquareCohomologyKernelEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 0)

variable [IsNoetherianRing R]

/-- Both original row H1 comparisons retain their original order. -/
noncomputable def vertexTwistTwoRowH1Coordinates (d : Fin 2 → ℕ) :
    (vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 0 ×
      vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 1) ≃ₗ[R]
        (CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1)) :=
  (vertexTwistRowStateLinearEquiv R d 0).prodCongr (vertexTwistRowStateLinearEquiv R d 1)

/-- The outer actual cohomology restriction difference is the original first-factor state difference. -/
theorem vertexTwistTwoRowH1Coordinates_difference (d : Fin 2 → ℕ)
    (x : vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 0 ×
      vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 1) :
    vertexTwistRowStateLinearEquiv R d 2
      (schemeBaseSquareCohomologyDifference (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1 x) =
      twoRowStateDifference R d (vertexTwistTwoRowH1Coordinates R d x) := by
  change vertexTwistRowStateLinearEquiv R d 2
    (vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) (b := 0) (c := 2) (Or.inr rfl) x.1 -
      vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) (b := 1) (c := 2) (Or.inr rfl) x.2) = _
  rw [map_sub,vertexTwistRowStateLinearEquiv_restrict,vertexTwistRowStateLinearEquiv_restrict]
  rfl

/-- The original row-state coordinates identify exactly the actual outer restriction kernel. -/
theorem vertexTwistTwoRowH1Coordinates_map_ker (d : Fin 2 → ℕ) :
    (LinearMap.ker (schemeBaseSquareCohomologyDifference (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1)).map
        (vertexTwistTwoRowH1Coordinates R d).toLinearMap = LinearMap.ker (twoRowStateDifference R d) := by
  have hm (x : vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 0 ×
      vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 1) :
      twoRowStateDifference R d (vertexTwistTwoRowH1Coordinates R d x) = 0 ↔
        schemeBaseSquareCohomologyDifference (vertexToBase R (Fin 2))
          (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1 x = 0 := by
    rw [← vertexTwistTwoRowH1Coordinates_difference]
    exact (vertexTwistRowStateLinearEquiv R d 2).map_eq_zero_iff
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hm x).mpr hx
  · intro hz
    change twoRowStateDifference R d z = 0 at hz
    refine ⟨(vertexTwistTwoRowH1Coordinates R d).symm z,?_,LinearEquiv.apply_symm_apply _ _⟩
    apply (hm _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hz

/-- With negative second twist, actual H1 equals the original row-state restriction kernel over the geometric base. -/
noncomputable def vertexTwistTwoH1StateKernelEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoH1Module R d ≃ₗ[R] LinearMap.ker (twoRowStateDifference R d) :=
  (vertexTwistTwoH1RestrictionKernelEquiv R d hd).trans
    ((vertexTwistTwoRowH1Coordinates R d).ofSubmodules _ _ (vertexTwistTwoRowH1Coordinates_map_ker R d))

/-- Every actual H1 class retains both native restrictions and the original one-factor Laurent projections. -/
theorem vertexTwistTwoH1StateKernelEquiv_val (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (x : vertexTwistTwoH1Module R d) :
    (vertexTwistTwoH1StateKernelEquiv R d hd x).val = vertexTwistTwoRowH1Coordinates R d
      (schemeBaseSquareCohomologyPair (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1
          ((schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
            (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1).symm x)) := rfl

/-- Actual global H1 vanishes when both original twist entries are strictly negative. -/
theorem vertexTwistTwoH1_eq_zero_of_pos (d : Fin 2 → ℕ) (hd₀ : 0 < d 0) (hd₁ : 0 < d 1)
    (x : vertexTwistTwoH1Module R d) : x = 0 := by
  let e := vertexTwistTwoH1RestrictionKernelEquiv R d hd₁
  apply e.injective
  apply Subtype.ext
  let y := (e x).val
  have hy := (e x).property
  have hc := vertexTwistTwoRowH1Coordinates_difference R d y
  change schemeBaseSquareCohomologyDifference _ _ _ 1 y = 0 at hy
  rw [hy,map_zero] at hc
  have hz := (twoRowStateDifference_eq_zero_iff_of_pos R d hd₀ _).mp hc.symm
  have hy0 : y = 0 := (vertexTwistTwoRowH1Coordinates R d).injective (hz.trans (map_zero _).symm)
  exact hy0.trans (congrArg Subtype.val (e.map_zero)).symm

end BPFixedPoints.ProjectiveLine
