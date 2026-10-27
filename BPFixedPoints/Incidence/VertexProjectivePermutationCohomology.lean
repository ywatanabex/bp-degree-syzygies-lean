import BPFixedPoints.Incidence.VertexProjectivePermutation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Transport of Ext-defined sheaf cohomology along the vertex permutation isomorphism

## Transport along an equivalence of abelian sheaf categories

Let `e : Sheaf J Ab ≌ Sheaf K Ab` be an equivalence of categories of abelian sheaves on two sites,
together with an isomorphism `c` from the image of the constant sheaf `ℤ` to the constant sheaf
`ℤ`. Mathlib's map `Ext.mapExactFunctor` of an exact functor on Ext groups, followed by
precomposition with `c⁻¹`, is a map `Sheaf.H F n → Sheaf.H (e F) n` (`sheafHTransport`). It is
bijective by `Functor.mapExt_bijective_of_preservesInjectiveObjects` (an equivalence is fully
faithful and preserves injective objects, and abelian sheaves have enough injectives), and natural
in `F` for the maps induced by sheaf morphisms.

## The homeomorphism case

A homeomorphism `h : T ≅ T'` of topological spaces induces the equivalence of abelian sheaf
categories given by pushforward (`topSheafEquivOfIso`, from Mathlib's `presheafEquivOfIso`), and
the image of the constant sheaf is the constant sheaf, by uniqueness of left adjoints of the
global section functors (`topSheafEquivOfIsoConstant`).

For a vertex bijection `ψ : V ≃ W`, the inverse of the coordinate map
`a_ψ : (P¹)^W ≅ (P¹)^V` gives the equivalence `vertexSheafPerm`, which is the pullback of abelian
sheaves along `a_ψ`; on sections it reads the sections of the original sheaf on the image open, so
the coordinate open of `ψ v` is sent to the coordinate open of `v`. The resulting additive
isomorphism of actual Ext-defined cohomology is `vertexSheafHPerm`.

The transport of the twist sheaves and of the exterior bundle is in
`VertexPermutationTwistSheaf.lean` and `IncidenceVertexRelabelExterior.lean`; the effect on state
coordinates and the naturality square of `incidenceTorExteriorEquiv` are in
`VertexPermutationTwistStateFormula.lean`.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
  TopologicalSpace Opposite ProjectiveLine

set_option backward.isDefEq.respectTransparency false

/-! ## Transport along an equivalence of abelian sheaf categories -/

section Transport

universe u v w w'

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
  (e : Sheaf J AddCommGrpCat.{w} ≌ Sheaf K AddCommGrpCat.{w}) [e.functor.Additive]
  (c : e.functor.obj ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) ≅
    (constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)))

/-- The map of sheaf cohomology induced by an equivalence of abelian sheaf categories and an
identification of the constant sheaves: Mathlib's map of Ext groups of an exact functor, followed
by the identification of the constant sheaves. -/
noncomputable def sheafHTransportHom (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H.{w'} F n →+ Sheaf.H.{w'} (e.functor.obj F) n where
  toFun x := (Ext.mk₀ c.inv).comp (x.mapExactFunctor e.functor) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.comp_add]

theorem sheafHTransportHom_apply (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : Sheaf.H.{w'} F n) :
    sheafHTransportHom e c F n x = (Ext.mk₀ c.inv).comp (x.mapExactFunctor e.functor) (zero_add n) :=
  rfl

/-- The transport of sheaf cohomology is bijective. -/
theorem sheafHTransportHom_bijective [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : Function.Bijective (sheafHTransportHom e c F n) := by
  have h1 := e.functor.mapExt_bijective_of_preservesInjectiveObjects
    ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) F n
  have h2 : Function.Bijective fun y : Ext.{w'}
      (e.functor.obj ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))))
      (e.functor.obj F) n => (Ext.mk₀ c.inv).comp y (zero_add n) := by
    refine ⟨fun y y' hy => ?_, fun z => ⟨(Ext.mk₀ c.hom).comp z (zero_add n), ?_⟩⟩
    · have h := congrArg (fun t => (Ext.mk₀ c.hom).comp t (zero_add n)) hy
      simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp] using h
    · simp only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]
  exact h2.comp h1

/-- **Transport of sheaf cohomology** along an equivalence of abelian sheaf categories that
preserves the constant sheaf. -/
noncomputable def sheafHTransport [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H.{w'} F n ≃+ Sheaf.H.{w'} (e.functor.obj F) n :=
  AddEquiv.ofBijective _ (sheafHTransportHom_bijective e c F n)

theorem sheafHTransport_apply [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : Sheaf.H.{w'} F n) :
    sheafHTransport e c F n x = (Ext.mk₀ c.inv).comp (x.mapExactFunctor e.functor) (zero_add n) :=
  rfl

/-- The transport of sheaf cohomology is natural for morphisms of sheaves. -/
theorem sheafHTransportHom_map {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{w'} F n) :
    sheafHTransportHom e c G n (Sheaf.H.map f n x) =
      Sheaf.H.map (e.functor.map f) n (sheafHTransportHom e c F n x) := by
  rw [sheafHTransportHom_apply, sheafHTransportHom_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

theorem sheafHTransport_map [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (n : ℕ) (x : Sheaf.H.{w'} F n) :
    sheafHTransport e c G n (Sheaf.H.map f n x) =
      Sheaf.H.map (e.functor.map f) n (sheafHTransport e c F n x) :=
  sheafHTransportHom_map e c f n x

end Transport

/-! ## Pushforward along a homeomorphism -/

section Homeomorphism

variable {T T' : TopCat.{0}}

/-- Sheaf conditions are invariant under isomorphisms of presheaves. -/
theorem isClosedUnderIsomorphisms_isSheaf (S : TopCat.{0}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (Presheaf.IsSheaf (Opens.grothendieckTopology S) (A := AddCommGrpCat.{0})) :=
  ⟨fun e hF => (Presheaf.isSheaf_of_iso_iff e).mp hF⟩

/-- Pushforward along a homeomorphism, as an equivalence of categories of abelian sheaves. -/
noncomputable def topSheafEquivOfIso (h : T ≅ T') :
    TopCat.Sheaf AddCommGrpCat.{0} T ≌ TopCat.Sheaf AddCommGrpCat.{0} T' :=
  haveI := isClosedUnderIsomorphisms_isSheaf T'
  (TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{0} h).congrFullSubcategory (by
    funext F
    apply propext
    constructor
    · intro hF
      exact TopCat.Presheaf.isSheaf_of_iso
        ((TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat.{0} h).unitIso.app F).symm
        (TopCat.Sheaf.pushforward_sheaf_of_sheaf h.inv hF)
    · intro hF
      exact TopCat.Sheaf.pushforward_sheaf_of_sheaf h.hom hF)

/-- The underlying presheaf of a pushed forward sheaf is the presheaf pushforward. -/
theorem topSheafEquivOfIso_functor_obj_obj (h : T ≅ T') (F : TopCat.Sheaf AddCommGrpCat.{0} T) :
    ((topSheafEquivOfIso h).functor.obj F).obj = h.hom _* F.obj := rfl

theorem topSheafEquivOfIso_inverse_obj_obj (h : T ≅ T') (G : TopCat.Sheaf AddCommGrpCat.{0} T') :
    ((topSheafEquivOfIso h).inverse.obj G).obj = h.inv _* G.obj := rfl

/-- Pushforward along a homeomorphism is additive. -/
instance topSheafEquivOfIso_functor_additive (h : T ≅ T') :
    (topSheafEquivOfIso h).functor.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (topSheafEquivOfIso h).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Global sections are unchanged by pushforward along a homeomorphism. -/
noncomputable def topSheafEquivOfIsoSections (h : T ≅ T') :
    (topSheafEquivOfIso h).inverse ⋙
        (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology T') AddCommGrpCat.{0}).obj (op ⊤) :=
  Iso.refl _

/-- **The constant sheaf is preserved** by pushforward along a homeomorphism: both are left
adjoint to global sections. -/
noncomputable def topSheafEquivOfIsoConstant (h : T ≅ T') :
    constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} ⋙
        (topSheafEquivOfIso h).functor ≅
      constantSheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0} :=
  (((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T))).comp (topSheafEquivOfIso h).toAdjunction).ofNatIsoRight
        (topSheafEquivOfIsoSections h)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T')))

end Homeomorphism

/-! ## The vertex permutation of the vertex projective products -/

section Vertex

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W]

/-- The homeomorphism underlying the inverse of the coordinate map `a_ψ`. -/
noncomputable def vertexSchemePermHomeo (ψ : V ≃ W) :
    Scheme.forgetToTop.obj (vertexScheme R V) ≅ Scheme.forgetToTop.obj (vertexScheme R W) :=
  Scheme.forgetToTop.mapIso (vertexSchemePermIso R ψ).symm

/-- **Pullback of abelian sheaves along the coordinate map** `a_ψ : (P¹)^W ≅ (P¹)^V`, as an
equivalence of abelian sheaf categories. -/
noncomputable def vertexSheafPerm (ψ : V ≃ W) :
    Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0} ≌
      Sheaf (Opens.grothendieckTopology (vertexScheme R W)) AddCommGrpCat.{0} :=
  topSheafEquivOfIso (vertexSchemePermHomeo R ψ)

instance vertexSheafPerm_functor_additive (ψ : V ≃ W) : (vertexSheafPerm R ψ).functor.Additive :=
  topSheafEquivOfIso_functor_additive _

/-- The transported sheaf on a coordinate open of `ψ v` has the sections of the original sheaf on
the coordinate open of `v`. -/
theorem vertexSheafPerm_obj_coordinateOpen (ψ : V ≃ W)
    (F : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) (v : V)
    (i : Fin 2) :
    ((vertexSheafPerm R ψ).functor.obj F).obj.obj (op (vertexCoordinateOpen R W (ψ v) i)) =
      F.obj.obj (op (vertexCoordinateOpen R V v i)) := by
  have h := vertexSchemePerm_preimage_coordinateOpen R ψ.symm (ψ v) i
  rw [Equiv.symm_apply_apply] at h
  change F.obj.obj (op (vertexSchemePerm R ψ.symm ⁻¹ᵁ vertexCoordinateOpen R W (ψ v) i)) = _
  rw [h]

noncomputable local instance vertexPermHasExt (U : Type) [Fintype U] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R U)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The identification of the constant sheaves along the vertex permutation. -/
noncomputable def vertexSheafPermConstant (ψ : V ≃ W) :
    (vertexSheafPerm R ψ).functor.obj
        ((constantSheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology (vertexScheme R W)) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (topSheafEquivOfIsoConstant (vertexSchemePermHomeo R ψ)).app (AddCommGrpCat.of (ULift ℤ))

/-- **Transport of actual Ext-defined cohomology** along the vertex permutation isomorphism of
the vertex projective products. -/
noncomputable def vertexSheafHPerm (ψ : V ≃ W)
    (F : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) (n : ℕ) :
    Sheaf.H.{1} F n ≃+ Sheaf.H.{1} ((vertexSheafPerm R ψ).functor.obj F) n :=
  sheafHTransport (vertexSheafPerm R ψ) (vertexSheafPermConstant R ψ) F n

/-- The transport of cohomology along the vertex permutation is natural for sheaf morphisms. -/
theorem vertexSheafHPerm_map (ψ : V ≃ W)
    {F G : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}} (f : F ⟶ G)
    (n : ℕ) (x : Sheaf.H.{1} F n) :
    vertexSheafHPerm R ψ G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((vertexSheafPerm R ψ).functor.map f) n (vertexSheafHPerm R ψ F n x) :=
  sheafHTransport_map _ _ f n x

end Vertex

end BPFixedPoints.Multigraph
