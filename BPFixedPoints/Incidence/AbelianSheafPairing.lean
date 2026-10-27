import BPFixedPoints.Incidence.AbelianTensorPure

/-! # Actual sheaf tensor pairings from original products of sections

The original biadditive section product and its original restrictions
extend through the native tensor and sheafification adjunction. Evaluation
on native pure sections returns the original product, before any cell,
cohomology or state-space comparison.
-/

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
variable (F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The native sheafification right adjoint supplies the original tensor-section map. -/
scoped instance sheafForgetLaxMonoidal :
    (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).LaxMonoidal :=
  (sheafificationAdjunction _ _).rightAdjointLaxMonoidal

/-- The native tensor is presented by sheafifying the original tensor presheaf. -/
def sheafTensorPresentationIso :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj (F.obj ⊗ G.obj) ≅ F ⊗ G :=
  (Functor.Monoidal.μIso (presheafToSheaf _ _) F.obj G.obj).symm ≪≫
    ((asIso ((sheafificationAdjunction _ _).counit.app F)) ⊗ᵢ
      (asIso ((sheafificationAdjunction _ _).counit.app G)))

/-- The native right-adjoint tensorator is exactly the original adjoint of this presentation. -/
theorem sheafTensorPresentation_adjoint :
    (sheafificationAdjunction _ _).homEquiv _ _ (sheafTensorPresentationIso F G).hom =
      LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) F G := rfl

/-- Actual pure sections use the native right-adjoint tensorator. -/
def sheafPureSection (W : Opens T) (x : F.obj.obj (op W)) (y : G.obj.obj (op W)) :
    (F ⊗ G).obj.obj (op W) :=
  (LaxMonoidal.μ (sheafToPresheaf _ _) F G).app (op W)
    (groupPure (F.obj.obj (op W)) (G.obj.obj (op W)) x y)

/-- Original biadditive products of actual sections with their unchanged actual restrictions. -/
structure SectionPairing where
  pairing (W : Opens T) : F.obj.obj (op W) →+ G.obj.obj (op W) →+ H.obj.obj (op W)
  restrict {W U : Opens T} (i : W ⟶ U) (x : F.obj.obj (op U)) (y : G.obj.obj (op U)) :
    H.obj.map i.op (pairing U x y) = pairing W (F.obj.map i.op x) (G.obj.map i.op y)

variable {F G H}

/-- The native pointwise tensor morphism evaluates exactly the original section product. -/
def SectionPairing.presheafMap (b : SectionPairing F G H) : F.obj ⊗ G.obj ⟶ H.obj where
  app W := groupLift (F.obj.obj W) (G.obj.obj W) (H.obj.obj W) (b.pairing W.unop)
  naturality {W Z} i := by
    apply groupTensor_hom_ext
    intro x y
    change groupLift (F.obj.obj Z) (G.obj.obj Z) (H.obj.obj Z) (b.pairing Z.unop)
      ((F.obj.map i ⊗ₘ G.obj.map i) (groupPure (F.obj.obj W) (G.obj.obj W) x y)) =
        H.obj.map i (groupLift (F.obj.obj W) (G.obj.obj W) (H.obj.obj W)
          (b.pairing W.unop) (groupPure (F.obj.obj W) (G.obj.obj W) x y))
    rw [groupPure_map,groupLift_pure,groupLift_pure]
    exact (b.restrict i.unop x y).symm

/-- The actual sheaf pairing is the native adjoint extension of the original section product. -/
def SectionPairing.sheafMap (b : SectionPairing F G H) : F ⊗ G ⟶ H :=
  (sheafTensorPresentationIso F G).inv ≫
    ((sheafificationAdjunction _ _).homEquiv _ H).symm b.presheafMap

/-- The extension preserves the original presheaf pairing under the native right-adjoint tensorator. -/
theorem SectionPairing.sheafMap_presheaf (b : SectionPairing F G H) :
    LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) F G ≫
      b.sheafMap.hom = b.presheafMap := by
  rw [← sheafTensorPresentation_adjoint]
  change (sheafificationAdjunction _ _).homEquiv _ _ (sheafTensorPresentationIso F G).hom ≫
    (sheafToPresheaf _ _).map b.sheafMap = _
  rw [← Adjunction.homEquiv_naturality_right]
  simp only [SectionPairing.sheafMap,Iso.hom_inv_id_assoc]
  exact Equiv.apply_symm_apply _ _

/-- Native pure-section evaluation returns the original section product itself. -/
theorem SectionPairing.sheafMap_pure (b : SectionPairing F G H) (W : Opens T)
    (x : F.obj.obj (op W)) (y : G.obj.obj (op W)) :
    b.sheafMap.hom.app (op W) (sheafPureSection F G W x y) = b.pairing W x y := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app (op W)) b.sheafMap_presheaf)
      (groupPure (F.obj.obj (op W)) (G.obj.obj (op W)) x y)
  exact h.trans (groupLift_pure _ _ _ _ x y)

end
end BPFixedPoints.SheafTools.AbelianTensor
