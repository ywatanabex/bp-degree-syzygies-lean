import BPFixedPoints.Incidence.VertexProjectiveTwistHigherCohomology

/-!
# Vertex bijections act on the vertex projective products

For a bijection `ψ : V ≃ W` of finite vertex sets, the contravariant coordinate map
`a_ψ : (P¹)^W → (P¹)^V`, `(x_w) ↦ (x_{ψ v})_v`, is the morphism over the coefficient scheme
given by the universal property of the actual indexed product `vertexIsProduct`: its composite
with the projection of the vertex `v` is the projection of the vertex `ψ v`
(`vertexOverBasePerm`, `vertexOverBasePerm_projection`). It is an isomorphism of schemes over the
base (`vertexSchemePermIso`), contravariantly functorial in `ψ`, and it pulls back the coordinate
opens and the rectangular faces of the binary cubical cover of `V` to those of `W` at the image
vertices.

This file only constructs the isomorphism of schemes and its compatibility with projections and
coordinate opens. The transport of twist sheaves, of the exterior bundle and of Ext-defined
cohomology along it is not constructed here.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ProjectiveLine

set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] {V W X : Type} [Fintype V] [Fintype W] [Fintype X]

/-- Morphisms into the vertex projective product over the base agree when all their vertex
coordinates agree. -/
theorem vertexOverBase_hom_ext {T : Over (Spec (CommRingCat.of R))} {f g : T ⟶ vertexOverBase R V}
    (h : ∀ v, f ≫ vertexProjectionOver R V v = g ≫ vertexProjectionOver R V v) : f = g :=
  (vertexIsProduct R V).hom_ext (by rintro ⟨v⟩; exact h v)

/-- **The contravariant coordinate map of a vertex bijection**, `(x_w) ↦ (x_{ψ v})_v`, over the
coefficient scheme. -/
noncomputable def vertexOverBasePerm (ψ : V ≃ W) : vertexOverBase R W ⟶ vertexOverBase R V :=
  (vertexIsProduct R V).lift (Fan.mk (vertexOverBase R W) fun v => vertexProjectionOver R W (ψ v))

/-- The vertex `v` coordinate of the coordinate map is the vertex `ψ v` coordinate. -/
@[reassoc (attr := simp)] theorem vertexOverBasePerm_projection (ψ : V ≃ W) (v : V) :
    vertexOverBasePerm R ψ ≫ vertexProjectionOver R V v = vertexProjectionOver R W (ψ v) :=
  (vertexIsProduct R V).fac _ ⟨v⟩

/-- The coordinate map of the identity is the identity. -/
theorem vertexOverBasePerm_refl : vertexOverBasePerm R (Equiv.refl V) = 𝟙 _ :=
  vertexOverBase_hom_ext R fun v => by simp

/-- The coordinate map is contravariantly functorial. -/
theorem vertexOverBasePerm_trans (ψ : V ≃ W) (χ : W ≃ X) :
    vertexOverBasePerm R (ψ.trans χ) = vertexOverBasePerm R χ ≫ vertexOverBasePerm R ψ :=
  vertexOverBase_hom_ext R fun v => by simp

/-- The coordinate map of a vertex bijection as an isomorphism over the base. -/
noncomputable def vertexOverBasePermIso (ψ : V ≃ W) : vertexOverBase R W ≅ vertexOverBase R V where
  hom := vertexOverBasePerm R ψ
  inv := vertexOverBasePerm R ψ.symm
  hom_inv_id := by
    rw [← vertexOverBasePerm_trans, Equiv.symm_trans_self, vertexOverBasePerm_refl]
  inv_hom_id := by
    rw [← vertexOverBasePerm_trans, Equiv.self_trans_symm, vertexOverBasePerm_refl]

/-- The coordinate map of a vertex bijection on the underlying schemes. -/
noncomputable def vertexSchemePerm (ψ : V ≃ W) : vertexScheme R W ⟶ vertexScheme R V :=
  (vertexOverBasePerm R ψ).left

/-- **The isomorphism of vertex projective products** permuting the factors. -/
noncomputable def vertexSchemePermIso (ψ : V ≃ W) : vertexScheme R W ≅ vertexScheme R V :=
  (Over.forget _).mapIso (vertexOverBasePermIso R ψ)

@[simp] theorem vertexSchemePermIso_hom (ψ : V ≃ W) :
    (vertexSchemePermIso R ψ).hom = vertexSchemePerm R ψ := rfl

@[simp] theorem vertexSchemePermIso_inv (ψ : V ≃ W) :
    (vertexSchemePermIso R ψ).inv = vertexSchemePerm R ψ.symm := rfl

/-- The coordinate map lies over the coefficient scheme. -/
@[reassoc (attr := simp)] theorem vertexSchemePerm_toBase (ψ : V ≃ W) :
    vertexSchemePerm R ψ ≫ vertexToBase R V = vertexToBase R W :=
  Over.w (vertexOverBasePerm R ψ)

/-- On schemes, the vertex `v` coordinate of the coordinate map is the vertex `ψ v` coordinate. -/
@[reassoc (attr := simp)] theorem vertexSchemePerm_projection (ψ : V ≃ W) (v : V) :
    vertexSchemePerm R ψ ≫ (vertexProjectionOver R V v).left =
      (vertexProjectionOver R W (ψ v)).left := by
  rw [vertexSchemePerm, ← Over.comp_left, vertexOverBasePerm_projection]

theorem vertexSchemePerm_refl : vertexSchemePerm R (Equiv.refl V) = 𝟙 _ := by
  rw [vertexSchemePerm, vertexOverBasePerm_refl]
  rfl

theorem vertexSchemePerm_trans (ψ : V ≃ W) (χ : W ≃ X) :
    vertexSchemePerm R (ψ.trans χ) = vertexSchemePerm R χ ≫ vertexSchemePerm R ψ := by
  rw [vertexSchemePerm, vertexOverBasePerm_trans, Over.comp_left]
  rfl

/-- The coordinate map pulls back the coordinate opens of `v` to those of `ψ v`. -/
theorem vertexSchemePerm_preimage_coordinateOpen (ψ : V ≃ W) (v : V) (i : Fin 2) :
    vertexSchemePerm R ψ ⁻¹ᵁ vertexCoordinateOpen R V v i = vertexCoordinateOpen R W (ψ v) i := by
  rw [vertexCoordinateOpen, vertexCoordinateOpen, ← Scheme.Hom.comp_preimage,
    vertexSchemePerm_projection]

/-- The coordinate map pulls back every rectangular face of the binary cubical cover of `V` to the
transported rectangular face of `W`. -/
theorem vertexSchemePerm_preimage_binaryCoverFaceOpen (ψ : V ≃ W) (q : V → Fin 3) :
    vertexSchemePerm R ψ ⁻¹ᵁ SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q =
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R W) (fun w => q (ψ.symm w)) := by
  have hfactor : ∀ v, vertexSchemePerm R ψ ⁻¹ᵁ
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v) =
        SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R W (ψ v)) (q v) := by
    intro v
    unfold SheafTools.binaryCoverFaceFactor
    split_ifs <;> simp only [Scheme.Hom.preimage_inf, vertexSchemePerm_preimage_coordinateOpen]
  ext x
  simp only [SheafTools.binaryCoverFaceOpen, Scheme.Hom.coe_preimage, Opens.coe_iInf,
    Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
  constructor
  · intro h w
    have hv := h (ψ.symm w)
    have hf := congrArg (fun U : (vertexScheme R W).Opens => x ∈ U) (hfactor (ψ.symm w))
    simp only [Scheme.Hom.mem_preimage, Equiv.apply_symm_apply] at hf
    exact hf.mp hv
  · intro h v
    have hw := h (ψ v)
    have hf := congrArg (fun U : (vertexScheme R W).Opens => x ∈ U) (hfactor v)
    simp only [Scheme.Hom.mem_preimage] at hf
    simp only [Equiv.symm_apply_apply] at hw
    exact hf.mpr hw

end BPFixedPoints.Multigraph
