import BPFixedPoints.Incidence.SheafMayerVietorisSectionConnecting

/-! # Two-direction connecting classes from actual rectangular sections -/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T]
noncomputable local instance rectangleConnectingHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original second cover, intersected with an arbitrary original open. -/
noncomputable def rectangleRowSquare (C D : Opens T) (hCD : C ⊔ D = ⊤) (W : Opens T) :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := W ⊓ (C ⊓ D)
      X₂ := W ⊓ C
      X₃ := W ⊓ D
      X₄ := W
      f₁₂ := homOfLE (inf_le_inf_left W inf_le_left)
      f₁₃ := homOfLE (inf_le_inf_left W inf_le_right)
      f₂₄ := homOfLE inf_le_left
      f₃₄ := homOfLE inf_le_left
      fac := Subsingleton.elim _ _ }
    (by rw [← inf_sup_left, hCD, inf_top_eq])
    (inf_inf_distrib_left W C D)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (C D : Opens T) (hCD : C ⊔ D = ⊤)

/-- The native first connecting class represented by a section on the row overlap. -/
noncomputable def rectangleRowConnecting (W : Opens T) :
    F.obj.obj (op (W ⊓ (C ⊓ D))) →+ F.H' 1 W :=
  mayerVietorisSectionConnecting (rectangleRowSquare C D hCD W) F

/-- Row connecting classes retain the actual restrictions in the first direction. -/
theorem rectangleRowConnecting_naturality {U W : Opens T} (h : U ≤ W)
    (x : F.obj.obj (op (W ⊓ (C ⊓ D)))) :
    rectangleRowConnecting F C D hCD U
      (F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) h)).op x) =
      (F.cohomologyPresheaf 1).map (homOfLE h).op (rectangleRowConnecting F C D hCD W x) :=
  mayerVietorisSectionConnecting_open_naturality (rectangleRowSquare C D hCD U) F
    (rectangleRowSquare C D hCD W)
    (homOfLE (inf_le_inf_right _ h)) (homOfLE (inf_le_inf_right C h))
    (homOfLE (inf_le_inf_right D h)) (homOfLE h) x

/-- Row boundaries are precisely the kernel of the original section connecting map. -/
theorem rectangleRowConnecting_eq_zero_iff (W : Opens T)
    (x : F.obj.obj (op (W ⊓ (C ⊓ D)))) :
    rectangleRowConnecting F C D hCD W x = 0 ↔
      ∃ (y : F.obj.obj (op (W ⊓ C))) (z : F.obj.obj (op (W ⊓ D))),
        F.obj.map (homOfLE (inf_le_inf_left W inf_le_left)).op y -
          F.obj.map (homOfLE (inf_le_inf_left W inf_le_right)).op z = x :=
  mayerVietorisSectionConnecting_eq_zero_iff (rectangleRowSquare C D hCD W) F x

/-- Every row degree-one class has an actual overlap-section representative under local vanishing. -/
theorem rectangleRowConnecting_surjective (W : Opens T)
    [Subsingleton (F.H' 1 (W ⊓ C))] [Subsingleton (F.H' 1 (W ⊓ D))] :
    Function.Surjective (rectangleRowConnecting F C D hCD W) :=
  @mayerVietorisSectionConnecting_surjective T _ (rectangleRowSquare C D hCD W) F
    (inferInstanceAs (Subsingleton (F.H' 1 (W ⊓ C))))
    (inferInstanceAs (Subsingleton (F.H' 1 (W ⊓ D))))

variable (A B : Opens T)

/-- The specified two-direction class is the composition of the original row and outer connecting maps. -/
noncomputable def rectangleTopConnecting :
    F.obj.obj (op ((A ⊓ B) ⊓ (C ⊓ D))) →+ F.H' 2 (A ⊔ B) :=
  ((Opens.mayerVietorisSquare A B).δ F 1 2 rfl).hom.comp
    (rectangleRowConnecting F C D hCD (A ⊓ B))

/-- Four actual one-overlap section modules form the source of the native top boundary. -/
abbrev RectangleBoundarySections :=
  (F.obj.obj (op (A ⊓ (C ⊓ D))) × F.obj.obj (op (B ⊓ (C ⊓ D)))) ×
    (F.obj.obj (op ((A ⊓ B) ⊓ C)) × F.obj.obj (op ((A ⊓ B) ⊓ D)))

/-- The original signed top boundary: the first-direction difference minus the second-direction difference. -/
noncomputable def rectangleSectionBoundary :
    RectangleBoundarySections F C D A B →+ F.obj.obj (op ((A ⊓ B) ⊓ (C ⊓ D))) :=
  { toFun := fun x =>
      (F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_left)).op x.1.1 -
        F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_right)).op x.1.2) -
      (F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_left)).op x.2.1 -
        F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_right)).op x.2.2)
    map_zero' := by simp
    map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel }

/-- Every actual second-degree class has an iterated connecting representative under the stated local vanishings. -/
theorem rectangleTopConnecting_surjective
    [Subsingleton (F.H' 2 A)] [Subsingleton (F.H' 2 B)]
    [Subsingleton (F.H' 1 ((A ⊓ B) ⊓ C))] [Subsingleton (F.H' 1 ((A ⊓ B) ⊓ D))] :
    Function.Surjective (rectangleTopConnecting F C D hCD A B) :=
  (mayerVietoris_delta_surjective F A B 1).comp
    (rectangleRowConnecting_surjective F C D hCD (A ⊓ B))

end BPFixedPoints.SheafTools
