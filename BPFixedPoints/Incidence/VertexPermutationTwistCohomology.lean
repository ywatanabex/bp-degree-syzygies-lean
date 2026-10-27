import BPFixedPoints.Incidence.VertexPermutationTwistSheaf
import BPFixedPoints.Incidence.EdgeExteriorBundleCohomology

/-!
# The map of multi-twist cohomology induced by a vertex bijection

For `ψ : V ≃ W`, the transport of Ext-defined sheaf cohomology `vertexSheafHPerm R ψ` along the
equivalence of abelian sheaf categories `vertexSheafPerm R ψ` is linear for the geometric base
actions: the image of the multiplication by `r` on a sheaf of modules `M` is the multiplication
by `r` on the pushforward `g_* M` (`vertexSheafPerm_map_scalar`), because `g` lies over the base.
Composing with the transport `vertexTwistPermIso : g_* O(a) ≅ O(b)` (for `b ∘ ψ = a`) gives the
geometric map `vertexTwistHPerm : H^n(O(a)) ≃ₗ[R] H^n(O(b))`.

Not proved here: the effect of this map on the state coordinates of `vertexTwistStateLinearEquiv`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open TopologicalSpace SheafTools SchemeTools ProjectiveLine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] (ψ : V ≃ W)

noncomputable local instance vertexPermTwistHasExt (U : Type) [Fintype U] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R U)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The structure map of the coordinate map of `ψ⁻¹` sends base coefficients to base
coefficients. -/
theorem vertexSchemePerm_symm_app_coefficientAt (U : (vertexScheme R W).Opens) (r : R) :
    (vertexSchemePerm R ψ.symm).app U (schemeBaseCoefficientAt (vertexToBase R W) U r) =
      schemeBaseCoefficientAt (vertexToBase R V) (vertexSchemePerm R ψ.symm ⁻¹ᵁ U) r := by
  have hn := congrArg (fun k => k.hom (schemeBaseCoefficientHom (vertexToBase R W) r))
    ((vertexSchemePerm R ψ.symm).naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  refine hn.trans ?_
  change (vertexScheme R V).presheaf.map _ ((vertexSchemePerm R ψ.symm).appTop
    (schemeBaseCoefficientHom (vertexToBase R W) r)) = _
  have hc : (vertexSchemePerm R ψ.symm).appTop (schemeBaseCoefficientHom (vertexToBase R W) r) =
      schemeBaseCoefficientHom (vertexToBase R V) r := by
    rw [← vertexSchemePerm_toBase R ψ.symm, schemeBaseCoefficientHom_comp]
    rfl
  rw [hc]
  rfl

/-- The image of the base multiplication by `r` on `M` is the base multiplication by `r` on the
pushforward. -/
theorem vertexSheafPerm_map_scalar (M : (vertexScheme R V).Modules) (r : R) :
    (vertexSheafPerm R ψ).functor.map (schemeBaseAbelianScalar (vertexToBase R V) M r) =
      schemeBaseAbelianScalar (vertexToBase R W)
        ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) r := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (M.smul (schemeBaseCoefficientAt (vertexToBase R V) (vertexSchemePerm R ψ.symm ⁻¹ᵁ U.unop) r)).asHom =
    (M.smul ((vertexSchemePerm R ψ.symm).app U.unop
      (schemeBaseCoefficientAt (vertexToBase R W) U.unop r))).asHom
  rw [vertexSchemePerm_symm_app_coefficientAt]

/-- The transport of the cohomology of a sheaf of modules `M` along a vertex bijection, with the
cohomology of the pushforward `g_* M` as target. -/
noncomputable def vertexSheafHPermModule (M : (vertexScheme R V).Modules) (n : ℕ) :
    Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n ≃+
      Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).obj
        ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M)) n :=
  vertexSheafHPerm R ψ _ n

theorem vertexSheafHPermModule_apply (M : (vertexScheme R V).Modules) (n : ℕ)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n) :
    vertexSheafHPermModule R ψ M n x = vertexSheafHPerm R ψ _ n x := rfl

/-- The transport of cohomology along a vertex bijection is linear for the geometric base
actions. -/
theorem vertexSheafHPermModule_smul (M : (vertexScheme R V).Modules) (n : ℕ) (r : R)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n) :
    letI := schemeBaseCohomologyModule (vertexToBase R V) M n
    letI := schemeBaseCohomologyModule (vertexToBase R W)
      ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) n
    vertexSheafHPermModule R ψ M n (r • x) = r • vertexSheafHPermModule R ψ M n x := by
  let _ := schemeBaseCohomologyModule (vertexToBase R V) M n
  let _ := schemeBaseCohomologyModule (vertexToBase R W)
    ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) n
  change vertexSheafHPerm R ψ _ n (Sheaf.H.map (schemeBaseAbelianScalar (vertexToBase R V) M r) n x) =
    Sheaf.H.map (schemeBaseAbelianScalar (vertexToBase R W)
      ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) r) n (vertexSheafHPerm R ψ _ n x)
  rw [vertexSheafHPerm_map, vertexSheafPerm_map_scalar]
  rfl

/-- The transport of the cohomology of a sheaf of modules along a vertex bijection, as a linear
isomorphism for the geometric base actions. -/
noncomputable def vertexSheafHPermLinear (M : (vertexScheme R V).Modules) (n : ℕ) :
    letI := schemeBaseCohomologyModule (vertexToBase R V) M n
    letI := schemeBaseCohomologyModule (vertexToBase R W)
      ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) n
    Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).obj
        ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M)) n :=
  letI := schemeBaseCohomologyModule (vertexToBase R V) M n
  letI := schemeBaseCohomologyModule (vertexToBase R W)
    ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) n
  { vertexSheafHPermModule R ψ M n with map_smul' := vertexSheafHPermModule_smul R ψ M n }

/-- The map induced on cohomology by an isomorphism of sheaves of modules, as a linear
isomorphism for the geometric base actions. -/
noncomputable def schemeBaseHMapLinear {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    letI := schemeBaseExtModule f M ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) n
    letI := schemeBaseExtModule f N ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) n
    Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) n :=
  letI := schemeBaseExtModule f M ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) n
  letI := schemeBaseExtModule f N ((constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))) n
  { toFun := Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n
    invFun := Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n
    left_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
        Sheaf.H.map_id_apply]
    right_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
        Sheaf.H.map_id_apply]
    map_add' := map_add _
    map_smul' := fun r x => by
      change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n
          (Sheaf.H.map (schemeBaseAbelianScalar f M r) n x) =
        Sheaf.H.map (schemeBaseAbelianScalar f N r) n
          (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x)
      rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, schemeBaseAbelianScalar_naturality] }

/-- The linear map of an isomorphism of sheaves of modules is the induced map on cohomology. -/
theorem schemeBaseHMapLinear_apply {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
    {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :
    schemeBaseHMapLinear R f e n x =
      Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x := rfl

variable (a : V → ℤ) (b : W → ℤ) (hb : ∀ v, b (ψ v) = a v)

/-- **The geometric map of multi-twist cohomology** of a vertex bijection: transport of
Ext-defined cohomology along `vertexSheafPerm R ψ`, followed by the transport isomorphism
`g_* O(a) ≅ O(b)`. It is linear for the geometric base actions. -/
noncomputable def vertexTwistHPerm (n : ℕ) :
    letI : Module R ((vertexTwistAbelianSheaf R V a).H n) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) n
    letI : Module R ((vertexTwistAbelianSheaf R W b).H n) :=
      schemeBaseCohomologyModule (vertexToBase R W) (vertexTwistSheaf R W b) n
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n ≃ₗ[R] Sheaf.H.{1} (vertexTwistAbelianSheaf R W b) n :=
  (vertexSheafHPermLinear R ψ (vertexTwistSheaf R V a) n).trans
    (schemeBaseHMapLinear R (vertexToBase R W) (vertexTwistPermIso R ψ a b hb) n)

/-- The geometric map is the transport of cohomology followed by the map of the twist
transport. -/
theorem vertexTwistHPerm_apply (n : ℕ) (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :
    vertexTwistHPerm R ψ a b hb n x =
      Sheaf.H.map (vertexTwistAbelianPermIso R ψ a b hb).hom n (vertexSheafHPerm R ψ _ n x) := rfl

end BPFixedPoints.Multigraph
