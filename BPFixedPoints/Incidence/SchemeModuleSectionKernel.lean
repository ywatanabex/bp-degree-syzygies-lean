import BPFixedPoints.Incidence.SchemeModuleSectionH1

/-! # Native sections as the original Mayer--Vietoris matching kernel -/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

/-- The original two native restrictions of a section over the original union. -/
noncomputable def schemeBaseSquareSectionPair :
    schemeBaseOpenSectionModule f M S.X₄ →ₗ[R]
      schemeBaseOpenSectionModule f M S.X₂ × schemeBaseOpenSectionModule f M S.X₃ :=
  (schemeBaseOpenRestrictionLinear f M S.f₂₄).prod (schemeBaseOpenRestrictionLinear f M S.f₃₄)

/-- The native pair restrictions satisfy precisely the original matching equation. -/
theorem schemeBaseSquareSectionPair_closed (s : schemeBaseOpenSectionModule f M S.X₄) :
    schemeBaseSquareSectionDifference f M S (schemeBaseSquareSectionPair f M S s) = 0 := by
  change M.presheaf.map S.f₁₂.op (M.presheaf.map S.f₂₄.op s) -
    M.presheaf.map S.f₁₃.op (M.presheaf.map S.f₃₄.op s) = 0
  rw [← M.presheaf.map_comp_apply,← M.presheaf.map_comp_apply]
  exact sub_self _

/-- Native sections equal the original matching kernel, with the inverse supplied by Mathlib sheaf gluing. -/
noncomputable def schemeBaseSquareSectionKernelEquiv :
    schemeBaseOpenSectionModule f M S.X₄ ≃ₗ[R] LinearMap.ker (schemeBaseSquareSectionDifference f M S) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let G := (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj F
  have H := S.sheafCondition_of_sheaf G
  let g := (schemeBaseSquareSectionPair f M S).codRestrict
    (LinearMap.ker (schemeBaseSquareSectionDifference f M S)) (schemeBaseSquareSectionPair_closed f M S)
  apply LinearEquiv.ofBijective g
  constructor
  · intro s t he
    have hp := congrArg Subtype.val he
    exact H.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  · intro x
    have hx : M.presheaf.map S.f₁₂.op x.val.1 = M.presheaf.map S.f₁₃.op x.val.2 :=
      sub_eq_zero.mp x.property
    refine ⟨H.glue x.val.1 x.val.2 hx,Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact H.map_f₂₄_op_glue _ _ hx
    · exact H.map_f₃₄_op_glue _ _ hx

/-- The matching-kernel comparison retains both specified actual restrictions. -/
theorem schemeBaseSquareSectionKernelEquiv_val (s : schemeBaseOpenSectionModule f M S.X₄) :
    (schemeBaseSquareSectionKernelEquiv f M S s).val = schemeBaseSquareSectionPair f M S s := rfl

end BPFixedPoints.SchemeTools
