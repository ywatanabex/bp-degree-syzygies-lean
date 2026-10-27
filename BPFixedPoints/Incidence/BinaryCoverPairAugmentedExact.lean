import BPFixedPoints.Incidence.BinaryCoverPairExact
import BPFixedPoints.Incidence.BinaryCoverCellActualTensorAugmentation

/-! # The original tensor augmentation has exactly the original pair boundaries as kernel -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell CechProduct ResolutionTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] local instance pairedAugExactChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] local instance pairedAugExactChainsModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- The original total pair boundary is zero in original total dimension zero. -/
theorem pairBoundary_zero_degree (x : CellPairs R V)
    (hx : x ∈ supported R R {z | pairCellDegree V z=0}) : pairBoundary R V x=0 := by
  have h := (pairContraction_degrees R V (fun _ => 0)).d 0 x hx
  rw [pairContraction_d] at h
  apply Finsupp.ext
  intro z
  apply (mem_supported' R _).mp h z
  change -(faceDegree z.1 : ℤ) + -(faceDegree z.2 : ℤ)≠0+1
  omega

/-- Every original tensor augmentation kernel has its original same-open pair-prism primitive. -/
theorem pairedComponentAugmentation_range_eq_ker (W : Opens T) :
    LinearMap.range (pairedDifferential U R W 0)=LinearMap.ker (pairedComponentAugmentation U R W) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (pairedComponentAugmentation_boundary U R W) y
  · intro hx
    refine ⟨pairedPrism U R W 0 x,?_⟩
    apply Subtype.ext
    have hd : pairBoundary R V x.val=0 := pairBoundary_zero_degree R x.val (pairedChains_degree U R W 0 x)
    have hp : (pairContraction R V (baseVertex U W)).p x.val=0 := by
      rw [pairContraction_p R V (baseVertex U W) (fun _ => 0)]
      change componentPairCoordinates R V (pairedComponentAugmentation U R W x)=0
      rw [hx,map_zero]
    have h := LinearMap.congr_fun (pairContraction R V (baseVertex U W)).homotopy x.val
    change pairBoundary R V ((pairContraction R V (baseVertex U W)).h x.val)=x.val
    rw [← pairContraction_d R V (baseVertex U W)]
    simpa only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.comp_apply,Module.End.one_apply,
      hp,pairContraction_d,hd,map_zero,add_zero] using h

/-- The original pair presheaf augmentation kills the original degree-one differential. -/
theorem pairedComponentPresheafAugmentation_zero :
    (pairedPresheafComplex U R).d 1 0 ≫ pairedComponentPresheafAugmentation U R=0 := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  exact pairedComponentAugmentation_boundary U R W.unop

/-- Actual degree-zero augmented exactness holds for the same original pair presheaf augmentation. -/
theorem pairedComponentPresheafAugmentation_exact :
    (ShortComplex.mk ((pairedPresheafComplex U R).d 1 0) (pairedComponentPresheafAugmentation U R)
      (pairedComponentPresheafAugmentation_zero U R)).Exact := by
  let S := ShortComplex.mk ((pairedPresheafComplex U R).d 1 0) (pairedComponentPresheafAugmentation U R)
    (pairedComponentPresheafAugmentation_zero U R)
  rw [ShortComplex.exact_iff_isZero_homology,IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext W
  let E := (evaluation (Opens T)ᵒᵖ (ModuleCat R)).obj W
  have hW : (S.map E).Exact := by
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact pairedComponentAugmentation_range_eq_ker U R W.unop
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp hW)
    (S.mapHomologyIso E).symm).eq_of_src _ _

end
end BPFixedPoints.SheafTools.BinaryCells
