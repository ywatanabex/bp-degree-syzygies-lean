import BPFixedPoints.Incidence.AbelianSheafPairing

/-! # Actual tensor morphisms are determined by their original pure sections -/

namespace BPFixedPoints.SheafTools.AbelianTensor
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open CategoryTheory.Functor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
noncomputable section
variable {T : Type} [TopologicalSpace T]
variable {F G H F' G' : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- Native actual tensor morphisms preserve pure sections of the original images. -/
theorem sheafPureSection_map (f : F ⟶ F') (g : G ⟶ G') (W : Opens T)
    (x : F.obj.obj (op W)) (y : G.obj.obj (op W)) :
    (f ⊗ₘ g).hom.app (op W) (sheafPureSection F G W x y) =
      sheafPureSection F' G' W (f.hom.app (op W) x) (g.hom.app (op W) y) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun a => a.app (op W))
      (LaxMonoidal.μ_natural (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) f g))
        (groupPure (F.obj.obj (op W)) (G.obj.obj (op W)) x y)
  change (LaxMonoidal.μ (sheafToPresheaf _ _) F' G').app (op W)
    ((f.hom.app (op W) ⊗ₘ g.hom.app (op W))
      (groupPure (F.obj.obj (op W)) (G.obj.obj (op W)) x y)) =
        (f ⊗ₘ g).hom.app (op W) (sheafPureSection F G W x y) at h
  rw [groupPure_map] at h
  exact h.symm

/-- Equality on all original pure sections determines the actual tensor morphism. -/
theorem sheafTensor_hom_ext {f g : F ⊗ G ⟶ H}
    (h : ∀ (W : Opens T) (x : F.obj.obj (op W)) (y : G.obj.obj (op W)),
      f.hom.app (op W) (sheafPureSection F G W x y) =
        g.hom.app (op W) (sheafPureSection F G W x y)) : f = g := by
  apply (cancel_epi (sheafTensorPresentationIso F G).hom).1
  apply ((sheafificationAdjunction _ _).homEquiv _ H).injective
  rw [Adjunction.homEquiv_naturality_right,Adjunction.homEquiv_naturality_right,
    sheafTensorPresentation_adjoint]
  apply NatTrans.ext
  funext W
  apply groupTensor_hom_ext
  intro x y
  exact h W.unop x y

/-- The original section formula uniquely specifies the actual tensor pairing. -/
theorem SectionPairing.sheafMap_unique (b : SectionPairing F G H) (f : F ⊗ G ⟶ H)
    (hf : ∀ (W : Opens T) (x : F.obj.obj (op W)) (y : G.obj.obj (op W)),
      f.hom.app (op W) (sheafPureSection F G W x y) = b.pairing W x y) : f = b.sheafMap := by
  apply sheafTensor_hom_ext
  intro W x y
  exact (hf W x y).trans (b.sheafMap_pure W x y).symm

end
end BPFixedPoints.SheafTools.AbelianTensor
