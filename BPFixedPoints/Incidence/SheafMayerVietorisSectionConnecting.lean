import BPFixedPoints.Incidence.SheafMayerVietorisOpenNaturality

/-! # Native section representatives for Mayer--Vietoris connecting classes -/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
variable {T : Type} [TopologicalSpace T]
noncomputable local instance mvSectionConnectingHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (S : (Opens.grothendieckTopology T).MayerVietorisSquare)
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The kernel of the native connecting map is exactly the native restriction difference. -/
theorem mayerVietoris_delta_eq_zero_iff (n : ℕ) (x : F.H' n S.X₁) :
    S.δ F n (n+1) rfl x = 0 ↔
      ∃ (y : F.H' n S.X₂) (z : F.H' n S.X₃),
        (F.cohomologyPresheaf n).map S.f₁₂.op y -
          (F.cohomologyPresheaf n).map S.f₁₃.op z = x := by
  have he := ((S.sequence_exact F n (n+1) rfl).exact 1).ab_range_eq_ker
  change (S.fromBiprod F n).hom.range = (S.δ F n (n+1) rfl).hom.ker at he
  change x ∈ (S.δ F n (n+1) rfl).hom.ker ↔ _
  rw [← he]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨⟨y,z⟩,rfl⟩ := (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective w
    exact ⟨y,z,(S.fromBiprod_biprodIsoProd_inv_apply F y z).symm.trans hw⟩
  · rintro ⟨y,z,h⟩
    exact ⟨(AddCommGrpCat.biprodIsoProd _ _).inv (y,z),
      (S.fromBiprod_biprodIsoProd_inv_apply F y z).trans h⟩

/-- Vanishing on the two members makes the native connecting map surjective. -/
theorem mayerVietorisSquare_delta_surjective (n : ℕ)
    [Subsingleton (F.H' (n+1) S.X₂)] [Subsingleton (F.H' (n+1) S.X₃)] :
    Function.Surjective (S.δ F n (n+1) rfl) := by
  let : Subsingleton ((F.H' (n+1) S.X₂ ⊞ F.H' (n+1) S.X₃ : AddCommGrpCat.{1}) : Type 1) :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective.subsingleton
  have he := ((S.sequence_exact F n (n+1) rfl).exact 2).ab_range_eq_ker
  change (S.δ F n (n+1) rfl).hom.range = (S.toBiprod F (n+1)).hom.ker at he
  intro x
  have hx : x ∈ (S.δ F n (n+1) rfl).hom.range := by
    rw [he]
    exact Subsingleton.elim _ _
  exact hx

/-- The original connecting class of an actual section, through the native degree-zero evaluation. -/
noncomputable def mayerVietorisSectionConnecting : F.obj.obj (op S.X₁) →+ F.H' 1 S.X₄ :=
  (S.δ F 0 1 rfl).hom.comp (localSheafH0Equiv F S.X₁).symm.toAddMonoidHom

/-- A section has zero connecting class exactly when it is a native restriction difference. -/
theorem mayerVietorisSectionConnecting_eq_zero_iff (x : F.obj.obj (op S.X₁)) :
    mayerVietorisSectionConnecting S F x = 0 ↔
      ∃ (y : F.obj.obj (op S.X₂)) (z : F.obj.obj (op S.X₃)),
        F.obj.map S.f₁₂.op y - F.obj.map S.f₁₃.op z = x := by
  change S.δ F 0 1 rfl ((localSheafH0Equiv F S.X₁).symm x) = 0 ↔ _
  rw [mayerVietoris_delta_eq_zero_iff]
  constructor
  · rintro ⟨y,z,h⟩
    refine ⟨localSheafH0Equiv F S.X₂ y, localSheafH0Equiv F S.X₃ z, ?_⟩
    have hh := congrArg (localSheafH0Equiv F S.X₁) h
    simpa only [map_sub, localSheafH0Equiv_naturality, AddEquiv.apply_symm_apply] using hh
  · rintro ⟨y,z,h⟩
    refine ⟨(localSheafH0Equiv F S.X₂).symm y, (localSheafH0Equiv F S.X₃).symm z, ?_⟩
    apply (localSheafH0Equiv F S.X₁).injective
    simpa only [map_sub, localSheafH0Equiv_naturality, AddEquiv.apply_symm_apply] using h

/-- Actual sections represent every degree-one class when both member groups vanish. -/
theorem mayerVietorisSectionConnecting_surjective
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Function.Surjective (mayerVietorisSectionConnecting S F) :=
  (mayerVietorisSquare_delta_surjective S F 0).comp (localSheafH0Equiv F S.X₁).symm.surjective

/-- Connecting classes of actual sections commute with the original open restrictions. -/
theorem mayerVietorisSectionConnecting_open_naturality
    (Q : (Opens.grothendieckTopology T).MayerVietorisSquare)
    (i₁ : S.X₁ ⟶ Q.X₁) (i₂ : S.X₂ ⟶ Q.X₂)
    (i₃ : S.X₃ ⟶ Q.X₃) (i₄ : S.X₄ ⟶ Q.X₄)
    (x : F.obj.obj (op Q.X₁)) :
    mayerVietorisSectionConnecting S F (F.obj.map i₁.op x) =
      (F.cohomologyPresheaf 1).map i₄.op (mayerVietorisSectionConnecting Q F x) := by
  have he : (localSheafH0Equiv F S.X₁).symm (F.obj.map i₁.op x) =
      (F.cohomologyPresheaf 0).map i₁.op ((localSheafH0Equiv F Q.X₁).symm x) := by
    apply (localSheafH0Equiv F S.X₁).injective
    rw [AddEquiv.apply_symm_apply, localSheafH0Equiv_naturality, AddEquiv.apply_symm_apply]
  change S.δ F 0 1 rfl ((localSheafH0Equiv F S.X₁).symm (F.obj.map i₁.op x)) = _
  rw [he]
  exact mayerVietoris_delta_open_naturality S Q i₁ i₂ i₃ i₄ F 0 _

end BPFixedPoints.SheafTools
