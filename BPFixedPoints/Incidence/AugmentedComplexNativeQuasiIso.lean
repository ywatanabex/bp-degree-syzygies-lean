import BPFixedPoints.Incidence.AcyclicResolutionComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.QuasiIso

/-! # The original exact augmentation is a native quasi-isomorphism

No projectivity of the original terms is used. The native degree-zero
opcycles cokernel keeps the original specified augmentation itself.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)

/-- The actual augmentation as a native chain map, with its original degree-zero component. -/
def augmentationChainMap : P ⟶ (ChainComplex.single₀ C).obj A :=
  (ChainComplex.toSingle₀Equiv P A).symm ⟨π,z⟩

/-- The native augmentation chain map retains the original augmentation itself. -/
@[simp] theorem augmentationChainMap_zero : (augmentationChainMap P π z).f 0=π :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero π z

variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π]

/-- The actual degree-zero opcycles have the original augmentation as their original cokernel projection. -/
def augmentationOpcyclesIso : P.opcycles 0 ≅ A :=
  (P.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso e.gIsCokernel

/-- The native cokernel isomorphism keeps the original augmentation map. -/
@[reassoc] theorem augmentationOpcyclesIso_projection :
    P.pOpcycles 0 ≫ (augmentationOpcyclesIso P π z e).hom=π := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (P.opcyclesIsCokernel 1 0 (by simp)) e.gIsCokernel WalkingParallelPair.one

/-- The original augmentation chain map induces exactly the original degree-zero cokernel identification. -/
theorem augmentationChainMap_opcycles :
    opcyclesMap (augmentationChainMap P π z) 0 = (augmentationOpcyclesIso P π z e).hom ≫
      (singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 A).hom := by
  apply (cancel_epi (P.pOpcycles 0)).mp
  rw [p_opcyclesMap,← Category.assoc,augmentationOpcyclesIso_projection,augmentationChainMap_zero]
  simp [singleObjOpcyclesSelfIso_hom]

include e in
/-- The native original augmentation is a quasi-isomorphism in degree zero. -/
theorem augmentationChainMap_quasiIsoAt_zero : QuasiIsoAt (augmentationChainMap P π z) 0 := by
  haveI : IsIso (opcyclesMap (augmentationChainMap P π z) 0) := by
    rw [augmentationChainMap_opcycles P π z e]
    infer_instance
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI : IsIso (P.isoHomologyι₀.inv ≫ homologyMap (augmentationChainMap P π z) 0) := by
    rw [ChainComplex.isoHomologyι₀_inv_naturality]
    infer_instance
  exact (isIso_comp_left_iff P.isoHomologyι₀.inv _).1 inferInstance

include e in
/-- Positive original exactness and the original exact epic augmentation give the native quasi-isomorphism. -/
theorem augmentationChainMap_quasiIso (hP : ∀ n, P.ExactAt (n+1)) :
    QuasiIso (augmentationChainMap P π z) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact augmentationChainMap_quasiIsoAt_zero P π z e
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact hP n

end
end BPFixedPoints.ExtResolutionTools
