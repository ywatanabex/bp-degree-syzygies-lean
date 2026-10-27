import BPFixedPoints.Incidence.SheafRectangleConnecting

/-! # Actual second cohomology as the signed rectangular section quotient -/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
variable {T : Type} [TopologicalSpace T]
noncomputable local instance rectangleTopQuotientHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (C D : Opens T) (hCD : C ⊔ D = ⊤) (A B : Opens T)

/-- Every native signed rectangular boundary has zero iterated connecting class. -/
theorem rectangleTopConnecting_boundary (x : RectangleBoundarySections F C D A B) :
    rectangleTopConnecting F C D hCD A B (rectangleSectionBoundary F C D A B x) = 0 := by
  let u := F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_left)).op x.1.1 -
    F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_right)).op x.1.2
  let w := F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_left)).op x.2.1 -
    F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_right)).op x.2.2
  have hw : rectangleRowConnecting F C D hCD (A ⊓ B) w = 0 :=
    (rectangleRowConnecting_eq_zero_iff F C D hCD (A ⊓ B) w).mpr ⟨x.2.1,x.2.2,rfl⟩
  have hu : (Opens.mayerVietorisSquare A B).δ F 1 2 rfl
      (rectangleRowConnecting F C D hCD (A ⊓ B) u) = 0 := by
    apply (mayerVietoris_delta_eq_zero_iff (Opens.mayerVietorisSquare A B) F 1 _).mpr
    refine ⟨rectangleRowConnecting F C D hCD A x.1.1,
      rectangleRowConnecting F C D hCD B x.1.2, ?_⟩
    change _ = rectangleRowConnecting F C D hCD (A ⊓ B) u
    dsimp only [u]
    rw [map_sub, rectangleRowConnecting_naturality F C D hCD inf_le_left,
      rectangleRowConnecting_naturality F C D hCD inf_le_right]
    rfl
  change (Opens.mayerVietorisSquare A B).δ F 1 2 rfl
    (rectangleRowConnecting F C D hCD (A ⊓ B) (u-w)) = 0
  rw [map_sub, hw, sub_zero, hu]

variable [Subsingleton (F.H' 1 (A ⊓ C))] [Subsingleton (F.H' 1 (A ⊓ D))]
variable [Subsingleton (F.H' 1 (B ⊓ C))] [Subsingleton (F.H' 1 (B ⊓ D))]

/-- The kernel consists exactly of the four original signed face restrictions. -/
theorem rectangleTopConnecting_eq_zero_iff
    (x : F.obj.obj (op ((A ⊓ B) ⊓ (C ⊓ D)))) :
    rectangleTopConnecting F C D hCD A B x = 0 ↔
      ∃ y, rectangleSectionBoundary F C D A B y = x := by
  constructor
  · intro hx
    obtain ⟨u,v,huv⟩ :=
      (mayerVietoris_delta_eq_zero_iff (Opens.mayerVietorisSquare A B) F 1
        (rectangleRowConnecting F C D hCD (A ⊓ B) x)).mp hx
    obtain ⟨s,hs⟩ := rectangleRowConnecting_surjective F C D hCD A u
    obtain ⟨t,ht⟩ := rectangleRowConnecting_surjective F C D hCD B v
    let col := F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_left)).op s -
      F.obj.map (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_right)).op t
    have hcol : rectangleRowConnecting F C D hCD (A ⊓ B) col =
        rectangleRowConnecting F C D hCD (A ⊓ B) x := by
      dsimp only [col]
      rw [map_sub, rectangleRowConnecting_naturality F C D hCD inf_le_left,
        rectangleRowConnecting_naturality F C D hCD inf_le_right, hs, ht]
      exact huv
    have hz : rectangleRowConnecting F C D hCD (A ⊓ B) (x-col) = 0 := by
      rw [map_sub,hcol,sub_self]
    obtain ⟨y,z,hyz⟩ := (rectangleRowConnecting_eq_zero_iff F C D hCD (A ⊓ B) (x-col)).mp hz
    refine ⟨((s,t),(-y,-z)), ?_⟩
    change col - (F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_left)).op (-y) -
      F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_right)).op (-z)) = x
    simp only [map_neg]
    calc
      _ = col + (F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_left)).op y -
          F.obj.map (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_right)).op z) := by abel
      _ = x := by rw [hyz]; abel
  · rintro ⟨y,rfl⟩
    exact rectangleTopConnecting_boundary F C D hCD A B y

/-- The independently defined native rectangular boundary image is the native iterated connecting kernel. -/
theorem rectangleSectionBoundary_range :
    (rectangleSectionBoundary F C D A B).range =
      (rectangleTopConnecting F C D hCD A B).ker := by
  ext x
  exact (rectangleTopConnecting_eq_zero_iff F C D hCD A B x).symm

/-- The actual top rectangular section quotient, defined using native signed restrictions. -/
abbrev RectangleSectionH2 :=
  F.obj.obj (op ((A ⊓ B) ⊓ (C ⊓ D))) ⧸ (rectangleSectionBoundary F C D A B).range

variable [Subsingleton (F.H' 2 A)] [Subsingleton (F.H' 2 B)]
variable [Subsingleton (F.H' 1 ((A ⊓ B) ⊓ C))] [Subsingleton (F.H' 1 ((A ⊓ B) ⊓ D))]

/-- The native two-step connecting map identifies the actual rectangular section quotient with actual H2. -/
noncomputable def rectangleSectionH2Equiv :
    RectangleSectionH2 F C D A B ≃+ F.H' 2 (A ⊔ B) :=
  (QuotientAddGroup.quotientAddEquivOfEq (rectangleSectionBoundary_range F C D hCD A B)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (rectangleTopConnecting F C D hCD A B)
      (rectangleTopConnecting_surjective F C D hCD A B))

/-- Every quotient representative maps to its original iterated connecting class. -/
theorem rectangleSectionH2Equiv_mk (x : F.obj.obj (op ((A ⊓ B) ⊓ (C ⊓ D)))) :
    rectangleSectionH2Equiv F C D hCD A B (QuotientAddGroup.mk x) =
      rectangleTopConnecting F C D hCD A B x := rfl

end BPFixedPoints.SheafTools
