import BPFixedPoints.Incidence.SheafMayerVietorisQuotient
import BPFixedPoints.Incidence.SheafLocalCohomologyZero

/-! # A two-open Cech quotient computes actual degree-one cohomology

The differential is the difference of the actual sheaf restrictions. The
comparison is induced by the genuine Mayer-Vietoris connecting map. Only the
explicit degree-one local vanishing assumptions are required here; proving them
for the intended affine line-bundle restrictions remains a separate theorem.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {T : Type} [TopologicalSpace T]
noncomputable local instance twoOpenCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (U V : Opens T)

/-- The ordinary two-open Cech differential, using actual sheaf sections and restrictions. -/
noncomputable def twoOpenSectionDifference :
    (F.obj.obj (op U) × F.obj.obj (op V)) →+ F.obj.obj (op (U ⊓ V)) :=
  ((F.obj.map (homOfLE inf_le_left).op).hom.comp (AddMonoidHom.fst _ _)) -
    ((F.obj.map (homOfLE inf_le_right).op).hom.comp (AddMonoidHom.snd _ _))

/-- Ordinary degree-one two-open Cech classes of actual sheaf sections. -/
noncomputable def twoOpenSectionH1 : Type :=
  F.obj.obj (op (U ⊓ V)) ⧸ (twoOpenSectionDifference F U V).range

noncomputable instance twoOpenSectionH1_addCommGroup : AddCommGroup (twoOpenSectionH1 F U V) := by
  unfold twoOpenSectionH1
  infer_instance

/-- The degree-zero Ext restriction difference is the ordinary Cech differential. -/
theorem localSheafH0_fromBiprod (x : F.H' 0 U) (y : F.H' 0 V) :
    localSheafH0Equiv F (U ⊓ V)
      ((Opens.mayerVietorisSquare U V).fromBiprod F 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv (x,y))) =
      twoOpenSectionDifference F U V (localSheafH0Equiv F U x, localSheafH0Equiv F V y) := by
  rw [GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply, map_sub]
  change localSheafH0Equiv F (U ⊓ V)
      ((F.cohomologyPresheaf 0).map (homOfLE inf_le_left).op x) -
      localSheafH0Equiv F (U ⊓ V)
        ((F.cohomologyPresheaf 0).map (homOfLE inf_le_right).op y) = _
  rw [localSheafH0Equiv_naturality, localSheafH0Equiv_naturality]
  rfl

/-- The coordinate equivalence takes the actual Ext restriction image to the
image of the ordinary Cech differential. -/
theorem localSheafH0_fromBiprod_range :
    (((Opens.mayerVietorisSquare U V).fromBiprod F 0).hom.range).map
        (localSheafH0Equiv F (U ⊓ V)).toAddMonoidHom =
      (twoOpenSectionDifference F U V).range := by
  ext z
  constructor
  · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
    obtain ⟨⟨a,b⟩, rfl⟩ := (AddCommGrpCat.biprodIsoProd (F.H' 0 U) (F.H' 0 V)).addCommGroupIsoToAddEquiv.symm.surjective w
    exact ⟨(localSheafH0Equiv F U a, localSheafH0Equiv F V b),
      (localSheafH0_fromBiprod F U V a b).symm⟩
  · rintro ⟨⟨a,b⟩, rfl⟩
    let a' := (localSheafH0Equiv F U).symm a
    let b' := (localSheafH0Equiv F V).symm b
    refine ⟨_, ⟨(AddCommGrpCat.biprodIsoProd (F.H' 0 U) (F.H' 0 V)).inv (a',b'), rfl⟩, ?_⟩
    have h := localSheafH0_fromBiprod F U V a' b'
    change localSheafH0Equiv F (U ⊓ V)
      ((Opens.mayerVietorisSquare U V).fromBiprod F 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv (a',b'))) = _
    exact h.trans (by simp only [a', b', AddEquiv.apply_symm_apply])

/-- The actual ordinary Cech quotient agrees with the genuine Ext restriction cokernel. -/
noncomputable def twoOpenSectionH1EquivCokernel :
    twoOpenSectionH1 F U V ≃+ mayerVietorisCokernel F U V 0 :=
  (QuotientAddGroup.congr _ _ (localSheafH0Equiv F (U ⊓ V))
    (localSheafH0_fromBiprod_range F U V)).symm

/-- The ordinary two-open Cech quotient computes genuine degree-one sheaf
cohomology when that degree vanishes on both opens. -/
noncomputable def twoOpenSectionH1Equiv
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] :
    twoOpenSectionH1 F U V ≃+ F.H' 1 (U ⊔ V) :=
  (twoOpenSectionH1EquivCokernel F U V).trans (mayerVietorisCokernelEquiv F U V 0)

/-- Existence form with the two local degree-one vanishings explicit. -/
theorem twoOpenSectionH1_comparison
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] :
    Nonempty (twoOpenSectionH1 F U V ≃+ F.H' 1 (U ⊔ V)) :=
  ⟨twoOpenSectionH1Equiv F U V⟩

end BPFixedPoints.SheafTools
