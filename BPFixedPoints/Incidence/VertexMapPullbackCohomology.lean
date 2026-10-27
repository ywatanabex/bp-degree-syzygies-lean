import BPFixedPoints.Incidence.VertexMapPullbackScheme
import BPFixedPoints.Incidence.VertexProjectivePermutationCohomology
import BPFixedPoints.Incidence.EdgeExteriorBundle

/-!
# Pullback of Ext-defined sheaf cohomology along the coordinate map of a vertex map

## Inverse image of abelian sheaves

For a continuous map `f : T → T'` Mathlib's inverse image of abelian sheaves
`TopCat.Sheaf.pullback AddCommGrpCat f` (`topSheafPullback f`) is left adjoint to the pushforward,
so it preserves finite colimits, and it preserves finite limits because `Opens.map f` is
representably flat; it is additive. It sends the constant sheaf `ℤ` to the constant sheaf `ℤ`
(`topSheafPullbackConstant`), by uniqueness of left adjoints of the global-section functors. Hence
Mathlib's map of Ext groups along an exact functor (`Ext.mapExactFunctor`), followed by this
identification, is a map of Ext-defined cohomology `H^n(T', F) → H^n(T, f⁻¹ F)` (`sheafHPullback`),
natural in `F` (`sheafHPullback_map`). No exactness of the pullback of sheaves of modules is used.

## Sheaves of modules

For a morphism of schemes `g : Y → X` and a sheaf of `O_X`-modules `M`, the canonical comparison
`g⁻¹ M → g^* M` of underlying abelian sheaves (`moduleSheafPullbackComparison`) is the adjoint, for
the abelian adjunction `g⁻¹ ⊣ g_*`, of the underlying abelian map of the unit `M → g_* g^* M` of
the module adjunction (the underlying abelian sheaf of a module pushforward is the abelian
pushforward, definitionally). It is natural in `M`
(`moduleSheafPullbackComparison_naturality`). Composing gives the pullback of cohomology of sheaves
of modules `H^n(X, M) → H^n(Y, g^* M)` (`moduleSheafHPullback`), natural in `M`.

## Vertex projective products

For a vertex function `f : V → W` and the coordinate map `a_f : (P¹)^W → (P¹)^V`
(`vertexSchemeMap`), this gives
`vertexModuleHPullback R f M n : H^n((P¹)^V, M) → H^n((P¹)^W, a_f^* M)`
for every sheaf of modules `M` on `(P¹)^V`, in particular for the multi-twists `O(-d)` and for the
exterior bundle of a graph (`exteriorBundleHPullback`).

The identification `a_f^* O(-d) ≅ O(-d')` with `d'_w = Σ_{f v = w} d_v`, and the resulting maps of
multi-twist and exterior cohomology, are in `VertexMapPullbackTwist`.

Not proved here: functoriality of `sheafHPullback` under composition of maps, its agreement with
the transport `vertexSheafHPerm` for vertex bijections, and linearity for the geometric base
actions.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
  TopologicalSpace Opposite ProjectiveLine

set_option backward.isDefEq.respectTransparency false

noncomputable local instance topSheafHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-! ## Inverse image of abelian sheaves along a continuous map -/

section TopPullback

variable {T T' : TopCat.{0}} (f : T ⟶ T')

/-- **The inverse image of abelian sheaves** along a continuous map: Mathlib's
`TopCat.Sheaf.pullback`. -/
noncomputable abbrev topSheafPullback :
    Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0} ⥤
      Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{0} f

/-- The inverse image preserves finite limits (`Opens.map f` is representably flat). -/
instance topSheafPullback_preservesFiniteLimits : PreservesFiniteLimits (topSheafPullback f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) AddCommGrpCat.{0} _ _

/-- The inverse image preserves finite colimits (it is a left adjoint). -/
instance topSheafPullback_preservesFiniteColimits : PreservesFiniteColimits (topSheafPullback f) :=
  have : PreservesColimitsOfSize.{0, 0} (topSheafPullback f) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The inverse image is additive. -/
instance topSheafPullback_additive : (topSheafPullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (topSheafPullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Global sections of a pushforward are the global sections. -/
noncomputable def topSheafPushforwardSections :
    TopCat.Sheaf.pushforward AddCommGrpCat.{0} f ⋙
        (sheafSections (Opens.grothendieckTopology T') AddCommGrpCat.{0}).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj (op ⊤) :=
  Iso.refl _

/-- **The inverse image of the constant sheaf is the constant sheaf**: both are left adjoint to
the global sections. -/
noncomputable def topSheafPullbackConstant :
    constantSheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0} ⋙ topSheafPullback f ≅
      constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  (((constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T'))).comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).ofNatIsoRight
          (topSheafPushforwardSections f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T)))

/-- **The map of Ext-defined sheaf cohomology along a continuous map**: Mathlib's map of Ext groups
along the exact inverse image functor, followed by the identification of the constant sheaves. -/
noncomputable def sheafHPullback (F : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0})
    (n : ℕ) : Sheaf.H.{1} F n →+ Sheaf.H.{1} ((topSheafPullback f).obj F) n where
  toFun x := (Ext.mk₀ ((topSheafPullbackConstant f).app (AddCommGrpCat.of (ULift ℤ))).inv).comp
    (x.mapExactFunctor (topSheafPullback f)) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp [Ext.comp_add]

theorem sheafHPullback_apply (F : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0})
    (n : ℕ) (x : Sheaf.H.{1} F n) :
    sheafHPullback f F n x =
      (Ext.mk₀ ((topSheafPullbackConstant f).app (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (x.mapExactFunctor (topSheafPullback f)) (zero_add n) :=
  rfl

/-- The pullback of cohomology is natural for morphisms of sheaves. -/
theorem sheafHPullback_map {F G : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0}}
    (u : F ⟶ G) (n : ℕ) (x : Sheaf.H.{1} F n) :
    sheafHPullback f G n (Sheaf.H.map u n x) =
      Sheaf.H.map ((topSheafPullback f).map u) n (sheafHPullback f F n x) := by
  rw [sheafHPullback_apply, sheafHPullback_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

end TopPullback

/-! ## Sheaves of modules on schemes -/

section Modules

variable {X Y : Scheme.{0}} (g : Y ⟶ X)

/-- **The canonical comparison `g⁻¹ M → g^* M`** of underlying abelian sheaves: the adjoint, for the
abelian adjunction, of the underlying abelian map of the unit `M → g_* g^* M`. -/
noncomputable def moduleSheafPullbackComparison (M : X.Modules) :
    (topSheafPullback g.base).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ⟶
      (SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback g).obj M) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g.base).homEquiv _ _).symm
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M))

/-- The underlying abelian sheaf of a module pushforward is the abelian pushforward. -/
theorem toSheaf_pushforward (N : Y.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward g).obj N) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) :=
  rfl

/-- The underlying abelian map of a module pushforward is the abelian pushforward. -/
theorem toSheaf_map_pushforward {N N' : Y.Modules} (u : N ⟶ N') :
    (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pushforward g).map u) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).map
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map u) :=
  rfl

/-- The comparison `g⁻¹ M → g^* M` is natural in `M`. -/
theorem moduleSheafPullbackComparison_naturality {M N : X.Modules} (u : M ⟶ N) :
    (topSheafPullback g.base).map ((SheafOfModules.toSheaf X.ringCatSheaf).map u) ≫
        moduleSheafPullbackComparison g N =
      moduleSheafPullbackComparison g M ≫
        (SheafOfModules.toSheaf Y.ringCatSheaf).map ((Scheme.Modules.pullback g).map u) := by
  unfold moduleSheafPullbackComparison
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [← toSheaf_map_pushforward, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality u

/-- **The map of sheaf cohomology of a sheaf of modules along a morphism of schemes**
`H^n(X, M) → H^n(Y, g^* M)`: the pullback of Ext-defined cohomology along the inverse image of
abelian sheaves, followed by the comparison `g⁻¹ M → g^* M`. -/
noncomputable def moduleSheafHPullback (M : X.Modules) (n : ℕ) :
    Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n →+
      Sheaf.H.{1} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pullback g).obj M)) n :=
  (Sheaf.H.map (moduleSheafPullbackComparison g M) n).comp (sheafHPullback g.base _ n)

theorem moduleSheafHPullback_apply (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :
    moduleSheafHPullback g M n x =
      Sheaf.H.map (moduleSheafPullbackComparison g M) n (sheafHPullback g.base _ n x) :=
  rfl

/-- The pullback of cohomology of sheaves of modules is natural in the sheaf. -/
theorem moduleSheafHPullback_map {M N : X.Modules} (u : M ⟶ N) (n : ℕ)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :
    moduleSheafHPullback g N n (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map u) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((Scheme.Modules.pullback g).map u)) n
        (moduleSheafHPullback g M n x) := by
  rw [moduleSheafHPullback_apply, moduleSheafHPullback_apply, sheafHPullback_map,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, moduleSheafPullbackComparison_naturality]

end Modules

/-! ## Vertex projective products -/

section Vertex

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W]

/-- **The pullback of cohomology along the coordinate map** `a_f : (P¹)^W → (P¹)^V` of a vertex
function, for a sheaf of modules `M` on `(P¹)^V`: `H^n((P¹)^V, M) → H^n((P¹)^W, a_f^* M)`. -/
noncomputable def vertexModuleHPullback (f : V → W) (M : (vertexScheme R V).Modules) (n : ℕ) :
    Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n →+
      Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).obj
        ((Scheme.Modules.pullback (vertexSchemeMap R f)).obj M)) n :=
  moduleSheafHPullback (vertexSchemeMap R f) M n

/-- The pullback of cohomology along `a_f` is natural for morphisms of sheaves of modules. -/
theorem vertexModuleHPullback_map (f : V → W) {M N : (vertexScheme R V).Modules} (u : M ⟶ N)
    (n : ℕ) (x : Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) n) :
    vertexModuleHPullback R f N n
        (Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map u) n x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
        ((Scheme.Modules.pullback (vertexSchemeMap R f)).map u)) n
        (vertexModuleHPullback R f M n x) :=
  moduleSheafHPullback_map _ u n x

/-- **The pullback of the cohomology of the exterior bundle** of `G` along the coordinate map
`a_φ` of a vertex map `φ : VertexMap G H`, with values in the pulled-back bundle
`a_φ^* (∧^q F_G^∨)` (its identification with `∧^q F_H^∨` is not constructed). -/
noncomputable def exteriorBundleHPullback {E : Type} [DecidableEq V] [Fintype E]
    {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H) (q n : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) n →+
      Sheaf.H.{1} ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).obj
        ((Scheme.Modules.pullback (φ.schemeMap R)).obj (G.exteriorBundle R q))) n :=
  moduleSheafHPullback (φ.schemeMap R) (G.exteriorBundle R q) n

end Vertex

end BPFixedPoints.Multigraph
