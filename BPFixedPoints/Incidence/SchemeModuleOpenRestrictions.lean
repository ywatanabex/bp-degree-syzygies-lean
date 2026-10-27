import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars

/-! # Native open restrictions over the original geometric base ring -/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)

/-- Package actual sections with their independently defined geometric base action. -/
noncomputable def schemeBaseOpenSectionModule (U : X.Opens) : ModuleCat R := by
  letI := schemeBaseOpenModuleSections f M U
  exact ModuleCat.of R Γ(M, U)

/-- Native restriction is linear for the original geometric base action. -/
noncomputable def schemeBaseOpenRestrictionLinear {U W : X.Opens} (i : U ⟶ W) :
    schemeBaseOpenSectionModule f M W →ₗ[R] schemeBaseOpenSectionModule f M U := by
  letI := schemeBaseOpenModuleSections f M W
  letI := schemeBaseOpenModuleSections f M U
  change Γ(M, W) →ₗ[R] Γ(M, U)
  refine { toFun := M.presheaf.map i.op, map_add' := map_add _, map_smul' := ?_ }
  intro r x
  change M.presheaf.map i.op (schemeBaseCoefficientAt f W r • x) =
    schemeBaseCoefficientAt f U r • M.presheaf.map i.op x
  have h := M.val.map_smul i.op (schemeBaseCoefficientAt f W r) x
  exact h.trans (congrArg (fun c : Γ(X, U) => c • M.presheaf.map i.op x)
    (schemeBaseCoefficientAt_map f i r))

/-- The linear restriction evaluates to the specified original presheaf restriction. -/
theorem schemeBaseOpenRestrictionLinear_apply {U W : X.Opens} (i : U ⟶ W)
    (x : schemeBaseOpenSectionModule f M W) :
    schemeBaseOpenRestrictionLinear f M i x = M.presheaf.map i.op x := rfl

end BPFixedPoints.SchemeTools
