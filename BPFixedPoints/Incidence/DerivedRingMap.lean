import BPFixedPoints.Incidence.IncidenceTorRelabel

/-!
# Left derived extension of scalars along a ring homomorphism

## Lifting to exact resolutions

Mathlib's `ProjectiveResolution.lift` and `ProjectiveResolution.liftHomotopy` lift a morphism to
a chain map between two projective resolutions; only the projectivity of the source and the
exactness of the target are used. We record the target data in `ExactResolution` (an augmented
`ℕ`-indexed chain complex which is exact in positive degrees, exact at degree zero and whose
augmentation is an epimorphism, with no projectivity) and re-prove the lift
(`ExactResolution.lift`) and the uniqueness up to homotopy (`ExactResolution.liftHomotopy`),
mirroring the Mathlib proofs. Exact resolutions are transported along functors preserving finite
limits and colimits (`ExactResolution.map`); restriction of scalars along any ring homomorphism is
such a functor, so a projective resolution of an `R'`-module restricted along `f : R →+* R'` is an
exact resolution of the restricted module, although in general it is not projective.

## The derived ring map

Let `f : R →+* R'` and augmentations `ε : R →+* k`, `ε' : R' →+* k` with `ε'.comp f = ε`. For an
`R'`-module `N` there is a natural `k`-linear map
`k ⊗_R (restrict N) → k ⊗_{R'} N`, `z ⊗ n ↦ z ⊗ n` (`restrictExtendHom`); it is not an isomorphism
in general. Given an `R`-module `M`, an `R'`-module `M'` and an `R`-linear map
`g : M → restrict M'`, `derivedRingMap` is the map
`(L_n ε^*) M ⟶ (L_n ε'^*) M'` obtained by lifting `g` to a chain map from a projective resolution
of `M` to the restriction of a projective resolution of `M'`, applying `ε^*`, composing with the
termwise comparison maps and taking homology. No flatness of `f` is used.

We prove that it is computed by any projective resolutions and any compatible lift
(`derivedRingMap_eq`), hence does not depend on the choices; the identity law
(`derivedRingMap_id`); the composition law (`derivedRingMap_comp`); and agreement with
`derivedRingChange` when `f` is a ring isomorphism (`derivedRingChange_hom_eq_derivedRingMap`).

Not covered here: naturality of `derivedRingMap` in the module map `g`, compatibility with
products of derived functors, and lifts from source resolutions that are not projective.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe v u v' u'

/-! ## Exact resolutions and lifts into them -/

section ExactResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An exact resolution of `Z`: an `ℕ`-indexed chain complex with an epimorphism from its degree
zero term onto `Z`, exact at degree zero and in all positive degrees. The terms need not be
projective. -/
structure ExactResolution (Z : C) where
  /-- The underlying chain complex. -/
  complex : ChainComplex C ℕ
  /-- The augmentation. -/
  π : complex.X 0 ⟶ Z
  /-- The augmentation kills the boundaries in degree zero. -/
  d_comp_π : complex.d 1 0 ≫ π = 0
  /-- The augmentation is an epimorphism. -/
  [epi_π : Epi π]
  /-- Exactness at degree zero. -/
  exact₀ : (ShortComplex.mk _ _ d_comp_π).Exact
  /-- Exactness in positive degrees. -/
  exact_succ : ∀ n, (ShortComplex.mk _ _ (complex.d_comp_d (n + 2) (n + 1) n)).Exact

attribute [instance] ExactResolution.epi_π

namespace ExactResolution

/-- A projective resolution is an exact resolution. -/
noncomputable def ofProjective {Z : C} (P : ProjectiveResolution Z) : ExactResolution Z where
  complex := P.complex
  π := P.π.f 0
  d_comp_π := P.complex_d_comp_π_f_zero
  exact₀ := P.exact₀
  exact_succ := P.exact_succ

@[simp] theorem ofProjective_complex {Z : C} (P : ProjectiveResolution Z) :
    (ofProjective P).complex = P.complex := rfl

@[simp] theorem ofProjective_π {Z : C} (P : ProjectiveResolution Z) :
    (ofProjective P).π = P.π.f 0 := rfl

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An exact functor carries exact resolutions to exact resolutions. -/
noncomputable def map (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {Z : C} (K : ExactResolution Z) : ExactResolution (F.obj Z) where
  complex := (F.mapHomologicalComplex _).obj K.complex
  π := F.map K.π
  d_comp_π := by
    change F.map (K.complex.d 1 0) ≫ F.map K.π = 0
    rw [← F.map_comp, K.d_comp_π, F.map_zero]
  epi_π := inferInstance
  exact₀ := K.exact₀.map F
  exact_succ n := (K.exact_succ n).map F

@[simp] theorem map_complex (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {Z : C} (K : ExactResolution Z) :
    (K.map F).complex = (F.mapHomologicalComplex _).obj K.complex := rfl

@[simp] theorem map_π (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {Z : C} (K : ExactResolution Z) :
    (K.map F).π = F.map K.π := rfl

variable {X Y : C}

/-- Auxiliary construction for `lift`. -/
noncomputable def liftFZero (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    P.complex.X 0 ⟶ K.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) K.π

/-- The degree zero part of the lift is compatible with the augmentations. -/
theorem liftFZero_comp (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    liftFZero f P K ≫ K.π = P.π.f 0 ≫ f :=
  Projective.factorThru_comp _ _

/-- Auxiliary construction for `lift`. -/
noncomputable def liftFOne (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    P.complex.X 1 ⟶ K.complex.X 1 :=
  K.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P K) (by
    change (P.complex.d 1 0 ≫ liftFZero f P K) ≫ K.π = 0
    rw [Category.assoc, liftFZero_comp, ← Category.assoc, P.complex_d_comp_π_f_zero,
      zero_comp])

/-- The degree one part of the lift commutes with the differentials. -/
theorem liftFOne_zero_comm (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    liftFOne f P K ≫ K.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P K :=
  K.exact₀.liftFromProjective_comp _ _

/-- Auxiliary construction for `lift`. -/
noncomputable def liftFSucc (P : ProjectiveResolution X) (K : ExactResolution Y) (n : ℕ)
    (g : P.complex.X n ⟶ K.complex.X n) (g' : P.complex.X (n + 1) ⟶ K.complex.X (n + 1))
    (w : g' ≫ K.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ K.complex.X (n + 2),
      g'' ≫ K.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(K.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by
      change (P.complex.d (n + 2) (n + 1) ≫ g') ≫ K.complex.d (n + 1) n = 0
      rw [Category.assoc, w, ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]),
      (K.exact_succ n).liftFromProjective_comp _ _⟩

/-- A morphism lifts to a chain map from a projective resolution of its source to an exact
resolution of its target. -/
noncomputable def lift (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    P.complex ⟶ K.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P K)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P K n g g' w).1, (liftFSucc P K n g g' w).2⟩

/-- The lift is compatible with the augmentations. -/
theorem lift_comm_zero (f : X ⟶ Y) (P : ProjectiveResolution X) (K : ExactResolution Y) :
    (lift f P K).f 0 ≫ K.π = P.π.f 0 ≫ f := by
  rw [lift, ChainComplex.mkHom_f_0]
  exact liftFZero_comp f P K

/-- An auxiliary definition for `liftHomotopyZero`. -/
noncomputable def liftHomotopyZeroZero {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (comm : φ.f 0 ≫ K.π = 0) : P.complex.X 0 ⟶ K.complex.X 1 :=
  K.exact₀.liftFromProjective (φ.f 0) comm

/-- The degree zero homotopy condition. -/
theorem liftHomotopyZeroZero_comp {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (comm : φ.f 0 ≫ K.π = 0) :
    liftHomotopyZeroZero φ comm ≫ K.complex.d 1 0 = φ.f 0 :=
  K.exact₀.liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
noncomputable def liftHomotopyZeroOne {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (comm : φ.f 0 ≫ K.π = 0) : P.complex.X 1 ⟶ K.complex.X 2 :=
  (K.exact_succ 0).liftFromProjective (φ.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero φ comm)
    (by
      change (φ.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero φ comm) ≫ K.complex.d 1 0 = 0
      rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.Hom.comm,
        liftHomotopyZeroZero_comp, sub_self])

/-- The degree one homotopy condition. -/
theorem liftHomotopyZeroOne_comp {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (comm : φ.f 0 ≫ K.π = 0) :
    liftHomotopyZeroOne φ comm ≫ K.complex.d 2 1 =
      φ.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero φ comm :=
  (K.exact_succ 0).liftFromProjective_comp _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
noncomputable def liftHomotopyZeroSucc {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (n : ℕ) (g : P.complex.X n ⟶ K.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ K.complex.X (n + 2))
    (w : φ.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ K.complex.d (n + 2) (n + 1)) :
    P.complex.X (n + 2) ⟶ K.complex.X (n + 3) :=
  (K.exact_succ (n + 1)).liftFromProjective (φ.f (n + 2) - P.complex.d _ _ ≫ g') (by
    change (φ.f (n + 2) - P.complex.d _ _ ≫ g') ≫ K.complex.d (n + 2) (n + 1) = 0
    rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.Hom.comm, w,
      Preadditive.comp_add, ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp, zero_add,
      sub_self])

/-- The inductive homotopy condition. -/
theorem liftHomotopyZeroSucc_comp {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (n : ℕ) (g : P.complex.X n ⟶ K.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ K.complex.X (n + 2))
    (w : φ.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ K.complex.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc φ n g g' w ≫ K.complex.d (n + 3) (n + 2) =
      φ.f (n + 2) - P.complex.d _ _ ≫ g' :=
  (K.exact_succ (n + 1)).liftFromProjective_comp _ _

/-- A chain map from a projective resolution to an exact resolution whose degree zero part is
killed by the augmentation is homotopic to zero. -/
noncomputable def liftHomotopyZero {P : ProjectiveResolution X} {K : ExactResolution Y}
    (φ : P.complex ⟶ K.complex) (comm : φ.f 0 ≫ K.π = 0) : Homotopy φ 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero φ comm)
    (liftHomotopyZeroZero_comp φ comm).symm
    (liftHomotopyZeroOne φ comm)
    (by rw [liftHomotopyZeroOne_comp, add_sub_cancel])
    fun n ⟨g, g', w⟩ =>
      ⟨liftHomotopyZeroSucc φ n g g' w, by
        rw [liftHomotopyZeroSucc_comp, add_sub_cancel]⟩

/-- Two lifts of the same morphism from a projective resolution to an exact resolution are
homotopic. -/
noncomputable def liftHomotopy (f : X ⟶ Y) {P : ProjectiveResolution X} {K : ExactResolution Y}
    (g h : P.complex ⟶ K.complex) (g_comm : g.f 0 ≫ K.π = P.π.f 0 ≫ f)
    (h_comm : h.f 0 ≫ K.π = P.π.f 0 ≫ f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero (g - h) (by
    rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, g_comm, h_comm, sub_self]))

/-- Two lifts of the same morphism induce the same maps on homology after any additive
functor. -/
theorem homologyMap_mapHomologicalComplex_lift_eq {E : Type*} [Category E] [Abelian E]
    (F : C ⥤ E) [F.Additive] (f : X ⟶ Y) {P : ProjectiveResolution X} {K : ExactResolution Y}
    (g h : P.complex ⟶ K.complex) (g_comm : g.f 0 ≫ K.π = P.π.f 0 ≫ f)
    (h_comm : h.f 0 ≫ K.π = P.π.f 0 ≫ f) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map h) n :=
  ((F.mapHomotopy (liftHomotopy f g h g_comm h_comm))).homologyMap_eq n

end ExactResolution

end ExactResolution

/-! ## The comparison map of extension of scalars after restriction -/

section RingMap

variable {R R' k : Type} [CommRing R] [CommRing R'] [CommRing k] (f : R →+* R')
  (ε : R →+* k) (ε' : R' →+* k) (hε : ε'.comp f = ε)

include hε

/-- The natural `k`-linear map from the extension along `ε` of an `R'`-module restricted along
`f` to its extension along `ε'`, by `z ⊗ n ↦ z ⊗ n`. -/
noncomputable def restrictExtendLinearMap (N : ModuleCat.{0} R') :
    (ModuleCat.extendScalars ε).obj ((ModuleCat.restrictScalars f).obj N) →ₗ[k]
      (ModuleCat.extendScalars ε').obj N := by
  letI : Algebra R k := ε.toAlgebra
  letI : Algebra R' k := ε'.toAlgebra
  let fwd : (ModuleCat.extendScalars ε).obj ((ModuleCat.restrictScalars f).obj N) →+
      (ModuleCat.extendScalars ε').obj N :=
    TensorProduct.liftAddHom
      { toFun := fun z =>
          { toFun := fun n => (z : k) ⊗ₜ[R'] (n : N)
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := by ext n; exact TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => by ext n; exact TensorProduct.add_tmul _ _ _ }
      (fun r z n => by
        change (ε r * (show k from z) : k) ⊗ₜ[R'] (n : N) = (show k from z) ⊗ₜ[R'] (f r • (n : N))
        rw [← TensorProduct.smul_tmul, ← RingHom.congr_fun hε r]
        rfl)
  exact
    { toFun := fwd
      map_add' := map_add fwd
      map_smul' := fun c t => by
        induction t using TensorProduct.inductionOn with
        | tmul z n =>
          change fwd ((c * (show k from z) : k) ⊗ₜ[R] n) = c • fwd (z ⊗ₜ[R] n)
          rfl
        | add t u ht hu => rw [smul_add, map_add, ht, hu, map_add, smul_add] }

/-- The comparison map on pure tensors. -/
theorem restrictExtendLinearMap_tmul (N : ModuleCat.{0} R') (z : k) (n : N) :
    letI : Algebra R k := ε.toAlgebra
    letI : Algebra R' k := ε'.toAlgebra
    restrictExtendLinearMap f ε ε' hε N
        ((z : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars f).obj N from n)) =
      (z : k) ⊗ₜ[R'] n := rfl

/-- The comparison map `k ⊗_R (restrict N) → k ⊗_{R'} N` as a natural transformation. It is not
an isomorphism in general. -/
noncomputable def restrictExtendHom :
    ModuleCat.restrictScalars.{0} f ⋙ ModuleCat.extendScalars ε ⟶ ModuleCat.extendScalars ε' where
  app N := ModuleCat.ofHom (restrictExtendLinearMap f ε ε' hε N)
  naturality {N N'} g := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    rfl

/-- The comparison natural transformation on pure tensors. -/
theorem restrictExtendHom_app_tmul (N : ModuleCat.{0} R') (z : k) (n : N) :
    letI : Algebra R k := ε.toAlgebra
    letI : Algebra R' k := ε'.toAlgebra
    (restrictExtendHom f ε ε' hε).app N
        ((z : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars f).obj N from n)) =
      (z : k) ⊗ₜ[R'] n := rfl

/-- Termwise comparison of complexes. -/
noncomputable def restrictExtendComplexHom (K : ChainComplex (ModuleCat.{0} R') ℕ) :
    ((ModuleCat.extendScalars ε).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj K) ⟶
      ((ModuleCat.extendScalars ε').mapHomologicalComplex _).obj K where
  f i := (restrictExtendHom f ε ε' hε).app (K.X i)
  comm' i j _ := ((restrictExtendHom f ε ε' hε).naturality (K.d i j)).symm

@[simp] theorem restrictExtendComplexHom_f (K : ChainComplex (ModuleCat.{0} R') ℕ) (i : ℕ) :
    (restrictExtendComplexHom f ε ε' hε K).f i = (restrictExtendHom f ε ε' hε).app (K.X i) := rfl

/-- The termwise comparison is natural for chain maps. -/
@[reassoc]
theorem restrictExtendComplexHom_naturality {K L : ChainComplex (ModuleCat.{0} R') ℕ}
    (c : K ⟶ L) :
    ((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
        (((ModuleCat.restrictScalars f).mapHomologicalComplex _).map c) ≫
      restrictExtendComplexHom f ε ε' hε L =
        restrictExtendComplexHom f ε ε' hε K ≫
          ((ModuleCat.extendScalars ε').mapHomologicalComplex _).map c := by
  ext i : 1
  exact (restrictExtendHom f ε ε' hε).naturality (c.f i)

omit hε in
/-- A projective resolution of an `R'`-module, restricted along `f`, as an exact resolution of the
restricted module. It need not be projective. -/
noncomputable def restrictResolution {M' : ModuleCat.{0} R'} (Q : ProjectiveResolution M') :
    ExactResolution ((ModuleCat.restrictScalars f).obj M') :=
  (ExactResolution.ofProjective Q).map (ModuleCat.restrictScalars f)

omit hε in
@[simp] theorem restrictResolution_complex {M' : ModuleCat.{0} R'} (Q : ProjectiveResolution M') :
    (restrictResolution f Q).complex =
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj Q.complex := rfl

omit hε in
@[simp] theorem restrictResolution_π {M' : ModuleCat.{0} R'} (Q : ProjectiveResolution M') :
    (restrictResolution f Q).π = (ModuleCat.restrictScalars f).map (Q.π.f 0) := rfl

/-! ## The derived ring map -/

variable {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'}
  (g : M ⟶ (ModuleCat.restrictScalars f).obj M')

/-- The map of left derived functors of extension of scalars induced by a ring homomorphism `f`
compatible with the augmentations and an `R`-linear map `g : M → restrict M'`. It is computed with
Mathlib's chosen projective resolutions: lift `g` to the restricted resolution of `M'`, extend
scalars along `ε`, compose with the comparison maps `z ⊗ m ↦ z ⊗ m` and take homology. -/
noncomputable def derivedRingMap (n : ℕ) :
    ((ModuleCat.extendScalars ε).leftDerived n).obj M ⟶
      ((ModuleCat.extendScalars ε').leftDerived n).obj M' :=
  ((projectiveResolution M).isoLeftDerivedObj (ModuleCat.extendScalars ε) n).hom ≫
    HomologicalComplex.homologyMap (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
      (ExactResolution.lift g (projectiveResolution M)
        (restrictResolution f (projectiveResolution M')))) n ≫
      HomologicalComplex.homologyMap
        (restrictExtendComplexHom f ε ε' hε (projectiveResolution M').complex) n ≫
        ((projectiveResolution M').isoLeftDerivedObj (ModuleCat.extendScalars ε') n).inv

/-- Two computations of the derived ring map through different projective resolutions and lifts
agree. -/
theorem derivedRingMap_formula_eq (P P₀ : ProjectiveResolution M)
    (Q Q₀ : ProjectiveResolution M')
    (c : P.complex ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj Q.complex)
    (hc : c.f 0 ≫ (ModuleCat.restrictScalars f).map (Q.π.f 0) = P.π.f 0 ≫ g)
    (c₀ : P₀.complex ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj Q₀.complex)
    (hc₀ : c₀.f 0 ≫ (ModuleCat.restrictScalars f).map (Q₀.π.f 0) = P₀.π.f 0 ≫ g) (n : ℕ) :
    (P₀.isoLeftDerivedObj (ModuleCat.extendScalars ε) n).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map c₀) n ≫
          HomologicalComplex.homologyMap (restrictExtendComplexHom f ε ε' hε Q₀.complex) n ≫
            (Q₀.isoLeftDerivedObj (ModuleCat.extendScalars ε') n).inv =
      (P.isoLeftDerivedObj (ModuleCat.extendScalars ε) n).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map c) n ≫
          HomologicalComplex.homologyMap (restrictExtendComplexHom f ε ε' hε Q.complex) n ≫
            (Q.isoLeftDerivedObj (ModuleCat.extendScalars ε') n).inv := by
  have ha : (ProjectiveResolution.lift (𝟙 M) P P₀).f 0 ≫ P₀.π.f 0 = P.π.f 0 ≫ 𝟙 M :=
    ProjectiveResolution.lift_commutes_zero _ _ _
  have ha' : (ProjectiveResolution.lift (𝟙 M) P P₀).f 0 ≫ P₀.π.f 0 = P.π.f 0 :=
    ha.trans (Category.comp_id _)
  have hd : (ProjectiveResolution.lift (𝟙 M') Q₀ Q).f 0 ≫ Q.π.f 0 = Q₀.π.f 0 ≫ 𝟙 M' :=
    ProjectiveResolution.lift_commutes_zero _ _ _
  have hd' : (ProjectiveResolution.lift (𝟙 M') Q₀ Q).f 0 ≫ Q.π.f 0 = Q₀.π.f 0 :=
    hd.trans (Category.comp_id _)
  have h1 := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 M) P P₀ _ ha
    (ModuleCat.extendScalars ε) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h1
  have h2 := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 M') Q₀ Q _ hd
    (ModuleCat.extendScalars ε') n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h2
  have h3 := restrictExtendComplexHom_naturality f ε ε' hε
    (ProjectiveResolution.lift (𝟙 M') Q₀ Q)
  -- The composite of the comparison maps with the lift `c₀` is another lift of `g`.
  have hlift : HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map c) n =
      HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
          (ProjectiveResolution.lift (𝟙 M) P P₀ ≫ c₀ ≫
            ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map
              (ProjectiveResolution.lift (𝟙 M') Q₀ Q))) n := by
    refine ExactResolution.homologyMap_mapHomologicalComplex_lift_eq
      (ModuleCat.extendScalars ε) g (K := restrictResolution f Q) c _ hc ?_ n
    change ((ProjectiveResolution.lift (𝟙 M) P P₀).f 0 ≫ c₀.f 0 ≫
        (ModuleCat.restrictScalars f).map ((ProjectiveResolution.lift (𝟙 M') Q₀ Q).f 0)) ≫
      (ModuleCat.restrictScalars f).map (Q.π.f 0) = P.π.f 0 ≫ g
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, hd', hc₀, ← Category.assoc, ha']
  rw [h1, hlift, h2]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc,
    Functor.map_comp, HomologicalComplex.homologyMap_comp]
  congr 3
  rw [← HomologicalComplex.homologyMap_comp_assoc, ← HomologicalComplex.homologyMap_comp_assoc,
    h3]

/-- **Computation of the derived ring map.** It is computed by any projective resolutions `P` of
`M` and `Q` of `M'` and any chain map from `P` to the restriction of `Q` lifting `g`; in
particular it does not depend on the chosen resolutions or on the lift. -/
theorem derivedRingMap_eq (P : ProjectiveResolution M) (Q : ProjectiveResolution M')
    (c : P.complex ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj Q.complex)
    (hc : c.f 0 ≫ (ModuleCat.restrictScalars f).map (Q.π.f 0) = P.π.f 0 ≫ g) (n : ℕ) :
    derivedRingMap f ε ε' hε g n =
      (P.isoLeftDerivedObj (ModuleCat.extendScalars ε) n).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map c) n ≫
          HomologicalComplex.homologyMap (restrictExtendComplexHom f ε ε' hε Q.complex) n ≫
            (Q.isoLeftDerivedObj (ModuleCat.extendScalars ε') n).inv :=
  derivedRingMap_formula_eq f ε ε' hε g P _ Q _ c hc _
    (ExactResolution.lift_comm_zero g (projectiveResolution M)
      (restrictResolution f (projectiveResolution M'))) n

/-! ## Identity and composition laws -/

omit hε in
/-- The identification of a complex with its restriction along the identity ring
homomorphism. -/
noncomputable def restrictIdComplexHom (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    K ⟶ ((ModuleCat.restrictScalars (RingHom.id R)).mapHomologicalComplex _).obj K where
  f i := (ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app (K.X i)
  comm' i j _ := ((ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.naturality (K.d i j)).symm

omit hε in
/-- **Identity law.** The derived ring map of the identity ring homomorphism and the identity
module map is the identity. -/
theorem derivedRingMap_id (M : ModuleCat.{0} R) (n : ℕ) :
    derivedRingMap (RingHom.id R) ε ε (RingHom.comp_id ε)
        ((ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app M) n = 𝟙 _ := by
  let P := projectiveResolution M
  rw [derivedRingMap_eq (RingHom.id R) ε ε (RingHom.comp_id ε) _ P P (restrictIdComplexHom P.complex)
    (by
      change (ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app (P.complex.X 0) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (P.π.f 0) = _
      exact ((ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.naturality (P.π.f 0)).symm)]
  have hid : ((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
      (restrictIdComplexHom P.complex) ≫
        restrictExtendComplexHom (RingHom.id R) ε ε (RingHom.comp_id ε) P.complex = 𝟙 _ := by
    ext i : 1
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rfl
  rw [← HomologicalComplex.homologyMap_comp_assoc, hid, HomologicalComplex.homologyMap_id,
    Category.id_comp, Iso.hom_inv_id]
  rfl

variable {R'' : Type} [CommRing R''] (f₂ : R' →+* R'') (ε'' : R'' →+* k) (hε₂ : ε''.comp f₂ = ε')

omit hε in
/-- The identification of a doubly restricted complex with its restriction along the composite
ring homomorphism. -/
noncomputable def restrictCompComplexHom (K : ChainComplex (ModuleCat.{0} R'') ℕ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars f₂).mapHomologicalComplex _).obj K) ⟶
      ((ModuleCat.restrictScalars (f₂.comp f)).mapHomologicalComplex _).obj K where
  f i := (ModuleCat.restrictScalarsComp.{0} f f₂).inv.app (K.X i)
  comm' i j _ := ((ModuleCat.restrictScalarsComp.{0} f f₂).inv.naturality (K.d i j)).symm

include hε₂

/-- The composite of two compatible ring homomorphisms is compatible with the augmentations. -/
theorem comp_augmentation_eq : ε''.comp (f₂.comp f) = ε := by
  rw [← RingHom.comp_assoc, hε₂, hε]

variable {M'' : ModuleCat.{0} R''} (g₂ : M' ⟶ (ModuleCat.restrictScalars f₂).obj M'')

/-- **Composition law.** The derived ring map of a composite is the composite of the derived
ring maps, for the composite module map
`M → restrict M' → restrict (restrict M'') = restrict M''`. -/
theorem derivedRingMap_comp (n : ℕ) :
    derivedRingMap (f₂.comp f) ε ε'' (comp_augmentation_eq f ε ε' hε f₂ ε'' hε₂)
        (g ≫ (ModuleCat.restrictScalars f).map g₂ ≫
          (ModuleCat.restrictScalarsComp.{0} f f₂).inv.app M'') n =
      derivedRingMap f ε ε' hε g n ≫ derivedRingMap f₂ ε' ε'' hε₂ g₂ n := by
  let Ψ := ModuleCat.restrictScalars.{0} f
  let P := projectiveResolution M
  let Q := projectiveResolution M'
  let S := projectiveResolution M''
  let c₁ := ExactResolution.lift g P (restrictResolution f Q)
  have hc₁ : c₁.f 0 ≫ Ψ.map (Q.π.f 0) = P.π.f 0 ≫ g :=
    ExactResolution.lift_comm_zero g P (restrictResolution f Q)
  let c₂ := ExactResolution.lift g₂ Q (restrictResolution f₂ S)
  have hc₂ : c₂.f 0 ≫ (ModuleCat.restrictScalars f₂).map (S.π.f 0) = Q.π.f 0 ≫ g₂ :=
    ExactResolution.lift_comm_zero g₂ Q (restrictResolution f₂ S)
  rw [derivedRingMap_eq f ε ε' hε g P Q c₁ hc₁, derivedRingMap_eq f₂ ε' ε'' hε₂ g₂ Q S c₂ hc₂,
    derivedRingMap_eq (f₂.comp f) ε ε'' (comp_augmentation_eq f ε ε' hε f₂ ε'' hε₂) _ P S
      (c₁ ≫ (Ψ.mapHomologicalComplex _).map c₂ ≫ restrictCompComplexHom f f₂ S.complex) (by
        change (c₁.f 0 ≫ Ψ.map (c₂.f 0) ≫
            (ModuleCat.restrictScalarsComp.{0} f f₂).inv.app (S.complex.X 0)) ≫
          (ModuleCat.restrictScalars (f₂.comp f)).map (S.π.f 0) = _
        rw [Category.assoc, Category.assoc,
          ← (ModuleCat.restrictScalarsComp.{0} f f₂).inv.naturality (S.π.f 0)]
        change c₁.f 0 ≫ Ψ.map (c₂.f 0) ≫
            Ψ.map ((ModuleCat.restrictScalars f₂).map (S.π.f 0)) ≫ _ = _
        rw [← Category.assoc (Ψ.map (c₂.f 0)), ← Ψ.map_comp, hc₂, Ψ.map_comp,
          ← Category.assoc, ← Category.assoc, hc₁, Category.assoc, Category.assoc]
        rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  simp only [← HomologicalComplex.homologyMap_comp_assoc]
  congr 1
  have hcomp : ((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
        (restrictCompComplexHom f f₂ S.complex) ≫
      restrictExtendComplexHom (f₂.comp f) ε ε'' (comp_augmentation_eq f ε ε' hε f₂ ε'' hε₂)
        S.complex =
      restrictExtendComplexHom f ε ε' hε
          (((ModuleCat.restrictScalars f₂).mapHomologicalComplex _).obj S.complex) ≫
        restrictExtendComplexHom f₂ ε' ε'' hε₂ S.complex := by
    ext i : 1
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rfl
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcomp,
    ← restrictExtendComplexHom_naturality_assoc f ε ε' hε c₂]
  rfl

end RingMap

/-! ## Agreement with the derived ring change along a ring isomorphism -/

section RingEquiv

variable {R R' k : Type} [CommRing R] [CommRing R'] [CommRing k] (σ : R ≃+* R')
  (ε : R →+* k) (ε' : R' →+* k) (hε : ∀ r, ε' (σ r) = ε r)

include hε

/-- The compatibility of a ring isomorphism with the augmentations, as an equality of ring
homomorphisms. -/
theorem ringEquiv_augmentation_eq : ε'.comp σ.toRingHom = ε :=
  RingHom.ext hε

/-- The termwise isomorphism of `restrictExtendComplexIso` is the termwise comparison map. -/
theorem restrictExtendComplexIso_hom_eq (K : ChainComplex (ModuleCat.{0} R') ℕ) :
    (restrictExtendComplexIso σ ε ε' hε K).hom =
      restrictExtendComplexHom σ.toRingHom ε ε' (ringEquiv_augmentation_eq σ ε ε' hε) K := by
  ext i : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rfl

/-- **Agreement with the derived ring change.** Along a ring isomorphism, the derived ring map of
the inverse of a module isomorphism `restrict M' ≅ M` is the derived ring change. -/
theorem derivedRingChange_hom_eq_derivedRingMap {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'}
    (e : (ModuleCat.restrictScalars σ.toRingHom).obj M' ≅ M) (n : ℕ) :
    (derivedRingChange σ ε ε' hε e n).hom =
      derivedRingMap σ.toRingHom ε ε' (ringEquiv_augmentation_eq σ ε ε' hε) e.inv n := by
  rw [derivedRingChange_hom_eq σ ε ε' hε e (projectiveResolution M) (projectiveResolution M')
    (ExactResolution.lift e.inv _ (restrictResolution σ.toRingHom _))
    (ExactResolution.lift_comm_zero _ _ _), restrictExtendComplexIso_hom_eq]
  rfl

end RingEquiv

end BPFixedPoints.ResolutionTools
