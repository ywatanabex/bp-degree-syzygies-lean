import BPFixedPoints.Incidence.VertexProjectivePermutationCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistTensorAdd
import BPFixedPoints.Incidence.SchemeModuleGeometricCoefficients

/-!
# Rank-one frames transported along an isomorphism of schemes

Let `g : X ⟶ Y` be an isomorphism of schemes and `M` a sheaf of modules on `X`. The pushforward
`g_* M` (Mathlib's `Scheme.Modules.pushforward`) has the sections `Γ(M, g⁻¹ S)` over an open `S`
of `Y`, with `Γ(Y, S)` acting through `g.app S`. A rank-one frame `e : M|_{U'} ≅ O` on the native
over-site of an open `U'` of `X` gives a rank-one frame of `g_* M` on every open `U` of `Y` with
`g⁻¹ U ≤ U'` (`pushforwardOverFrame`): a section `x` over `S ≤ U` goes to `(g.app S)⁻¹ (e x)`.
It is constructed sectionwise, not from any comparison of pushforward with tensor products.

Proved here:
* the section formula of the transported frame (`pushforwardOverFrame_hom_apply`);
* transported frames commute with native over-site restriction on either side
  (`pushforwardOverFrame_restriction`, `pushforwardOverFrame_restrict_source`);
* transported frames have the transported transition: if two frames of `M` differ by the
  multiplication by `r`, their transports differ by the multiplication by any `r'` with
  `g.app U r' = r` on `g⁻¹ U` (`pushforwardOverFrame_transition`);
* the lift formula for global functions of open subschemes, used to compute such `r'`
  (`topIso_appTop_lift`, `app_topIso_appTop_lift`).

Nothing about twist sheaves or cohomology is proved in this file.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

section IsoFrames

variable {X Y : Scheme.{0}} (g : X ⟶ Y)

/-- The over object of `U'` given by the preimage of an over object of `U`. -/
def preimageOver {U : Y.Opens} {U' : X.Opens} (hU : g ⁻¹ᵁ U ≤ U') (S : Over U) : Over U' :=
  Over.mk (homOfLE ((g.preimage_mono S.hom.le).trans hU))

@[simp] theorem preimageOver_left {U : Y.Opens} {U' : X.Opens} (hU : g ⁻¹ᵁ U ≤ U') (S : Over U) :
    (preimageOver g hU S).left = g ⁻¹ᵁ S.left := rfl

variable [IsIso g]

/-- The inverse of the structure map of an isomorphism is multiplicative with respect to the
pulled back factor. -/
theorem inv_app_mul (S : Y.Opens) (a : Γ(Y, S)) (b : Γ(X, g ⁻¹ᵁ S)) :
    inv (g.app S) (g.app S a * b) = a * inv (g.app S) b := by
  rw [map_mul]
  congr 1
  rw [← CommRingCat.comp_apply, IsIso.hom_inv_id]
  rfl

/-- The inverse of the structure map of an isomorphism commutes with restriction. -/
theorem inv_app_restrict {S T : Y.Opens} (h : T ≤ S) (b : Γ(X, g ⁻¹ᵁ S)) :
    inv (g.app T) (X.presheaf.map (homOfLE (g.preimage_mono h)).op b) =
      Y.presheaf.map (homOfLE h).op (inv (g.app S) b) := by
  have hn := g.naturality (homOfLE h).op
  have hm : X.presheaf.map (homOfLE (g.preimage_mono h)).op ≫ inv (g.app T) =
      inv (g.app S) ≫ Y.presheaf.map (homOfLE h).op := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, hn]
    rfl
  exact congrArg (fun k => k.hom b) hm

/-- The structure map of an isomorphism undoes its inverse. -/
theorem app_inv_app (S : Y.Opens) (b : Γ(X, g ⁻¹ᵁ S)) : g.app S (inv (g.app S) b) = b := by
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
  rfl

/-- The inverse structure map undoes the structure map of an isomorphism. -/
theorem inv_app_app (S : Y.Opens) (a : Γ(Y, S)) : inv (g.app S) (g.app S a) = a := by
  rw [← CommRingCat.comp_apply, IsIso.hom_inv_id]
  rfl

/-- The transported frame map: a section over `S` goes to the inverse structure map of its
frame coefficient over `g⁻¹ S`. -/
noncomputable def pushforwardOverFrameHom (M : X.Modules) {U : Y.Opens} {U' : X.Opens}
    (hU : g ⁻¹ᵁ U ≤ U') (e : M.over U' ⟶ SheafOfModules.unit (X.ringCatSheaf.over U')) :
    ((Scheme.Modules.pushforward g).obj M).over U ⟶ SheafOfModules.unit (Y.ringCatSheaf.over U) where
  val :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x => inv (g.app S.unop.left)
            ((e.val.app (op (preimageOver g hU S.unop))).hom x)
          map_add' := fun x y => by simp
          map_smul' := fun r x => by
            have h := (e.val.app (op (preimageOver g hU S.unop))).hom.map_smul
              (g.app S.unop.left r) x
            exact (congrArg (inv (g.app S.unop.left)) h).trans (inv_app_mul g S.unop.left r _) }
      naturality := fun {S T} i => by
        ext x
        have hn := congrArg (fun k => k.hom x) (e.val.naturality
          (show op (preimageOver g hU S.unop) ⟶ op (preimageOver g hU T.unop) from
            (Over.homMk (homOfLE (g.preimage_mono i.unop.left.le)) :
              preimageOver g hU T.unop ⟶ preimageOver g hU S.unop).op))
        refine (congrArg (inv (g.app T.unop.left)) hn).trans ?_
        exact inv_app_restrict g (leOfHom i.unop.left) _ }

/-- The inverse transported frame map: a function over `S` goes to the frame section of its
pullback over `g⁻¹ S`. -/
noncomputable def pushforwardOverFrameInv (M : X.Modules) {U : Y.Opens} {U' : X.Opens}
    (hU : g ⁻¹ᵁ U ≤ U') (e : SheafOfModules.unit (X.ringCatSheaf.over U') ⟶ M.over U') :
    SheafOfModules.unit (Y.ringCatSheaf.over U) ⟶ ((Scheme.Modules.pushforward g).obj M).over U where
  val :=
    { app := fun S => ModuleCat.ofHom
        { toFun := fun y => (e.val.app (op (preimageOver g hU S.unop))).hom
            (g.app S.unop.left y)
          map_add' := fun x y => by simp
          map_smul' := fun r y => by
            have h := (e.val.app (op (preimageOver g hU S.unop))).hom.map_smul
              (g.app S.unop.left r) (g.app S.unop.left y)
            refine (congrArg (e.val.app (op (preimageOver g hU S.unop))).hom ?_).trans h
            exact map_mul (g.app S.unop.left).hom r y }
      naturality := fun {S T} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        have hn := congrArg (fun k => k.hom (g.app S.unop.left y)) (e.val.naturality
          (show op (preimageOver g hU S.unop) ⟶ op (preimageOver g hU T.unop) from
            (Over.homMk (homOfLE (g.preimage_mono i.unop.left.le)) :
              preimageOver g hU T.unop ⟶ preimageOver g hU S.unop).op))
        refine Eq.trans ?_ hn
        exact congrArg (e.val.app (op (preimageOver g hU T.unop))).hom
          (congrArg (fun k => k.hom y) (g.naturality i.unop.left.op)) }

/-- **Transport of a rank-one frame** along the isomorphism `g`, from an open `U'` of `X` to any
open `U` of `Y` whose preimage lies in `U'`. -/
noncomputable def pushforwardOverFrame (M : X.Modules) {U : Y.Opens} {U' : X.Opens}
    (hU : g ⁻¹ᵁ U ≤ U') (e : M.over U' ≅ SheafOfModules.unit (X.ringCatSheaf.over U')) :
    ((Scheme.Modules.pushforward g).obj M).over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) where
  hom := pushforwardOverFrameHom g M hU e.hom
  inv := pushforwardOverFrameInv g M hU e.inv
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext S : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (e.inv.val.app (op (preimageOver g hU S.unop))).hom
      (g.app S.unop.left (inv (g.app S.unop.left)
        ((e.hom.val.app (op (preimageOver g hU S.unop))).hom x))) = x
    rw [app_inv_app]
    exact congrArg (fun k => (k.val.app (op (preimageOver g hU S.unop))).hom x) e.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext S : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change inv (g.app S.unop.left) ((e.hom.val.app (op (preimageOver g hU S.unop))).hom
      ((e.inv.val.app (op (preimageOver g hU S.unop))).hom (g.app S.unop.left y))) = y
    have h := congrArg (fun k => (k.val.app (op (preimageOver g hU S.unop))).hom
      (g.app S.unop.left y)) e.inv_hom_id
    change (e.hom.val.app (op (preimageOver g hU S.unop))).hom
      ((e.inv.val.app (op (preimageOver g hU S.unop))).hom (g.app S.unop.left y)) =
        g.app S.unop.left y at h
    rw [h, inv_app_app]

/-- The section formula of the transported frame. -/
theorem pushforwardOverFrame_hom_apply (M : X.Modules) {U : Y.Opens} {U' : X.Opens}
    (hU : g ⁻¹ᵁ U ≤ U') (e : M.over U' ≅ SheafOfModules.unit (X.ringCatSheaf.over U'))
    (S : Over U) (x : Γ(M, g ⁻¹ᵁ S.left)) :
    (show Γ(Y, S.left) from ((pushforwardOverFrame g M hU e).hom.val.app (op S)).hom x) =
      inv (g.app S.left) (show Γ(X, g ⁻¹ᵁ S.left) from
        (e.hom.val.app (op (preimageOver g hU S))).hom x) := rfl

/-- Restricting a transported frame on the target side is transporting to the smaller open. -/
theorem pushforwardOverFrame_restriction (M : X.Modules) {U U₂ : Y.Opens} {U' : X.Opens}
    (i : U₂ ⟶ U) (hU : g ⁻¹ᵁ U ≤ U')
    (e : M.over U' ≅ SheafOfModules.unit (X.ringCatSheaf.over U')) :
    moduleOverFrameRestriction Y i ((Scheme.Modules.pushforward g).obj M)
        (pushforwardOverFrame g M hU e) =
      pushforwardOverFrame g M ((g.preimage_mono i.le).trans hU) e := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Transporting a frame restricted on the source side is transporting the original frame. -/
theorem pushforwardOverFrame_restrict_source (M : X.Modules) {U : Y.Opens} {U' U'' : X.Opens}
    (j : U'' ⟶ U') (hU : g ⁻¹ᵁ U ≤ U'')
    (e : M.over U' ≅ SheafOfModules.unit (X.ringCatSheaf.over U')) :
    pushforwardOverFrame g M hU (moduleOverFrameRestriction X j M e) =
      pushforwardOverFrame g M (hU.trans j.le) e := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- **Transported transitions.** If two frames of `M` on `U'` differ by the multiplication by
`r`, their transports to `U` differ by the multiplication by `r'`, whenever `g.app U` sends `r'`
to the restriction of `r`. -/
theorem pushforwardOverFrame_transition (M : X.Modules) {U : Y.Opens} {U' : X.Opens}
    (hU : g ⁻¹ᵁ U ≤ U') (e d : M.over U' ≅ SheafOfModules.unit (X.ringCatSheaf.over U'))
    (r : Γ(U'.toScheme, ⊤)) (r' : Γ(U.toScheme, ⊤))
    (h : e.hom = d.hom ≫ moduleOverMultiplication X U' r)
    (hr : g.app U (U.topIso.hom r') = X.presheaf.map (homOfLE hU).op (U'.topIso.hom r)) :
    (pushforwardOverFrame g M hU e).hom =
      (pushforwardOverFrame g M hU d).hom ≫ moduleOverMultiplication Y U r' := by
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have he := congrArg (fun k => (k.val.app (op (preimageOver g hU S.unop))).hom x) h
  have hc : moduleOverMultiplicationCoefficient X U' r (preimageOver g hU S.unop) =
      g.app S.unop.left (moduleOverMultiplicationCoefficient Y U r' S.unop) := by
    rw [moduleOverMultiplicationCoefficient_geometric, moduleOverMultiplicationCoefficient_geometric]
    have hn := congrArg (fun k => k.hom (U.topIso.hom r')) (g.naturality S.unop.hom.op)
    change g.app S.unop.left (Y.presheaf.map S.unop.hom.op (U.topIso.hom r')) =
      X.presheaf.map (homOfLE (g.preimage_mono S.unop.hom.le)).op
        (g.app U (U.topIso.hom r')) at hn
    rw [hn, hr]
    exact congrArg (fun k => k.hom (U'.topIso.hom r))
      (X.presheaf.map_comp (homOfLE hU).op (homOfLE (g.preimage_mono S.unop.hom.le)).op)
  have h1 := he.trans (moduleOverMultiplication_app X U' r (preimageOver g hU S.unop)
    ((d.hom.val.app (op (preimageOver g hU S.unop))).hom x))
  rw [hc] at h1
  refine (congrArg (inv (g.app S.unop.left)) h1).trans ?_
  rw [mul_comm, inv_app_mul, mul_comm]
  exact (moduleOverMultiplication_app Y U r' S.unop _).symm

end IsoFrames

section Lifts

/-- The global function of an open subscheme pulled back along a lift through an open subscheme
is the restriction of the function along the lifted morphism. -/
theorem topIso_appTop_lift {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) (O : Y.Opens)
    (k : U.toScheme ⟶ O.toScheme) (hk : k ≫ O.ι = U.ι ≫ p) (h : U ≤ p ⁻¹ᵁ O)
    (t : Γ(O.toScheme, ⊤)) :
    U.topIso.hom (k.appTop t) = p.appLE O U h (O.topIso.hom t) := by
  have hU : U.topIso.inv = U.ι.appLE U ⊤ (by simp) := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hO : O.topIso.inv = O.ι.appLE O ⊤ (by simp) := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hkt : k.appTop = k.appLE ⊤ ⊤ le_rfl := (Scheme.Hom.appLE_eq_app k).symm
  have hcongr : ∀ (f f' : U.toScheme ⟶ Y) (_ : f = f') (e : ⊤ ≤ f ⁻¹ᵁ O) (e' : ⊤ ≤ f' ⁻¹ᵁ O),
      f.appLE O ⊤ e = f'.appLE O ⊤ e' := by
    intro f f' hf e e'
    subst hf
    rfl
  have key : O.topIso.inv ≫ k.appTop = p.appLE O U h ≫ U.topIso.inv := by
    rw [hU, hO, hkt, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact hcongr _ _ hk _ _
  have key2 : k.appTop ≫ U.topIso.hom = O.topIso.hom ≫ p.appLE O U h := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, key, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact congrArg (fun f => f.hom t) key2

/-- Morphisms that agree have the same restriction maps. -/
theorem appLE_congr_hom {X Y : Scheme.{0}} {f f' : X ⟶ Y} (hf : f = f') (O : Y.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ O) (e' : U ≤ f' ⁻¹ᵁ O) : f.appLE O U e = f'.appLE O U e' := by
  subst hf
  rfl

/-- **Lifted functions along an isomorphism.** Let `g : X ⟶ Y` be an isomorphism and let
`pY : Y ⟶ Z`, `pX : X ⟶ Z` satisfy `g ≫ pY = pX`. For lifts `kY`, `kX` of `pY`, `pX` on opens
`U` of `Y` and `U'` of `X` through an open `O` of `Z`, with `g⁻¹ U ≤ U'`, the structure map of `g`
sends the lifted function of `kY` to the restriction of the lifted function of `kX`. -/
theorem app_topIso_appTop_lift {X Y Z : Scheme.{0}} (g : X ⟶ Y) (pY : Y ⟶ Z) (pX : X ⟶ Z)
    (hg : g ≫ pY = pX) (U : Y.Opens) (U' : X.Opens) (hU : g ⁻¹ᵁ U ≤ U') (O : Z.Opens)
    (kY : U.toScheme ⟶ O.toScheme) (hkY : kY ≫ O.ι = U.ι ≫ pY)
    (kX : U'.toScheme ⟶ O.toScheme) (hkX : kX ≫ O.ι = U'.ι ≫ pX)
    (hY : U ≤ pY ⁻¹ᵁ O) (hX : U' ≤ pX ⁻¹ᵁ O) (t : Γ(O.toScheme, ⊤)) :
    g.app U (U.topIso.hom (kY.appTop t)) =
      X.presheaf.map (homOfLE hU).op (U'.topIso.hom (kX.appTop t)) := by
  rw [topIso_appTop_lift pY U O kY hkY hY, topIso_appTop_lift pX U' O kX hkX hX]
  have h₁ : pY.appLE O U hY ≫ g.app U = pX.appLE O (g ⁻¹ᵁ U) (hU.trans hX) := by
    rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom hg _ _ _ _
  have h₂ : pX.appLE O U' hX ≫ X.presheaf.map (homOfLE hU).op =
      pX.appLE O (g ⁻¹ᵁ U) (hU.trans hX) := Scheme.Hom.appLE_map _ _ _
  exact (congrArg (fun k => k.hom (O.topIso.hom t)) h₁).trans
    (congrArg (fun k => k.hom (O.topIso.hom t)) h₂).symm

end Lifts

end BPFixedPoints.Multigraph
