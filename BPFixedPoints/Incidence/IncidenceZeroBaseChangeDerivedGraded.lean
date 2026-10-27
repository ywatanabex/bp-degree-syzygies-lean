import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cochain complexes of graded submodules, chain maps and homotopies

Generic tools for the derived base change of the Čech–Koszul model
(`IncidenceZeroBaseChangeDerivedComplex`). A module `M` over a commutative ring `R` with an
integer grading by submodules `piece i` and an endomorphism `d` of cohomological degree one with
`d ∘ d = 0` (`ZbdGradedComplex`) gives an actual `CochainComplex (ModuleCat R) ℤ` whose term in
degree `i` is `piece i` (`ZbdGradedComplex.complex`). The differential from `i` to `j` is the
restriction of `d` if `i + 1 = j` and zero otherwise, so no `eqToHom` occurs.

* `ZbdGradedComplex.hom`: a linear map preserving the pieces and commuting with `d` is a chain map;
  `hom_comp`, `hom_id`, `hom_ext'`.
* `ZbdGradedComplex.homotopy`: a linear map `h` of cohomological degree `-1` with
  `f = h d + d h + g` is a homotopy from `f` to `g` in Mathlib's convention
  (`f = dNext + prevD + g`).
* `ZbdGradedComplex.homotopyEquiv`: a strict retraction `g f = 1` together with
  `f g = h d + d h + 1` is a `HomotopyEquiv`.
* `zbd_exists_boundary_of_homologyπ_eq_zero`: in a cochain complex of modules, a cycle with zero
  homology class is a boundary (through Mathlib's explicit kernel-modulo-image homology of short
  complexes of modules); `zbd_liftCycles_apply_eq`: lifts to the cycles only depend on the value
  in the complex.

Nothing here is specific to the incidence model.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory

universe u v

/-- A module with an integer grading by submodules and an endomorphism of cohomological degree
one squaring to zero. -/
structure ZbdGradedComplex (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] where
  /-- The piece of cohomological degree `i`. -/
  piece : ℤ → Submodule R M
  /-- The differential on the whole module. -/
  d : M →ₗ[R] M
  d_mem : ∀ i x, x ∈ piece i → d x ∈ piece (i + 1)
  d_d : ∀ x, d (d x) = 0

namespace ZbdGradedComplex

variable {R : Type u} [CommRing R] {M N P : Type v} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The differential from degree `i` to degree `j`; zero unless `i + 1 = j`. -/
noncomputable def dPiece (A : ZbdGradedComplex R M) (i j : ℤ) : A.piece i →ₗ[R] A.piece j :=
  if h : i + 1 = j then
    (A.d ∘ₗ (A.piece i).subtype).codRestrict (A.piece j) fun x => h ▸ A.d_mem i x x.2
  else 0

theorem dPiece_val (A : ZbdGradedComplex R M) {i j : ℤ} (h : i + 1 = j) (x : A.piece i) :
    (A.dPiece i j x : M) = A.d x := by
  rw [dPiece, dite_eq_left h]
  rfl

theorem dPiece_eq_zero (A : ZbdGradedComplex R M) {i j : ℤ} (h : ¬ i + 1 = j) :
    A.dPiece i j = 0 := dite_eq_right h

/-- The cochain complex of the pieces. -/
noncomputable def complex (A : ZbdGradedComplex R M) : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (A.piece i)
  d i j := ModuleCat.ofHom (A.dPiece i j)
  shape i j h := by
    rw [A.dPiece_eq_zero h]
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : A.piece i)
    apply Subtype.ext
    change (A.dPiece j k (A.dPiece i j x) : M) = 0
    rw [A.dPiece_val hjk, A.dPiece_val hij, A.d_d]

theorem complex_X (A : ZbdGradedComplex R M) (i : ℤ) :
    A.complex.X i = ModuleCat.of R (A.piece i) := rfl

theorem complex_d (A : ZbdGradedComplex R M) (i j : ℤ) :
    A.complex.d i j = ModuleCat.ofHom (A.dPiece i j) := rfl

/-- The differential of the complex on underlying elements. -/
theorem complex_d_val (A : ZbdGradedComplex R M) {i j : ℤ} (h : i + 1 = j) (x : A.complex.X i) :
    Subtype.val (p := (· ∈ A.piece j)) (A.complex.d i j x) =
      A.d (Subtype.val (p := (· ∈ A.piece i)) x) :=
  A.dPiece_val h x

/-- The component of a chain map induced by a linear map preserving the pieces. -/
noncomputable def homPiece (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (i : ℤ) : A.piece i →ₗ[R] B.piece i :=
  (f ∘ₗ (A.piece i).subtype).codRestrict (B.piece i) fun x => hf i x x.2

theorem homPiece_val (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (i : ℤ) (x : A.piece i) :
    (A.homPiece B f hf i x : N) = f x := rfl

/-- The chain map induced by a linear map preserving the pieces and commuting with the
differentials. -/
noncomputable def hom (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hc : ∀ x, B.d (f x) = f (A.d x)) :
    A.complex ⟶ B.complex where
  f i := ModuleCat.ofHom (A.homPiece B f hf i)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : A.piece i)
    apply Subtype.ext
    change (B.dPiece i j (A.homPiece B f hf i x) : N) = f (A.dPiece i j x : M)
    rw [B.dPiece_val hij, A.dPiece_val hij, homPiece_val]
    exact hc x

/-- The chain map on underlying elements. -/
theorem hom_f_val (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hc : ∀ x, B.d (f x) = f (A.d x)) (i : ℤ)
    (x : A.complex.X i) :
    Subtype.val (p := (· ∈ B.piece i)) ((A.hom B f hf hc).f i x) =
      f (Subtype.val (p := (· ∈ A.piece i)) x) := rfl

theorem hom_f (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hc : ∀ x, B.d (f x) = f (A.d x)) (i : ℤ) :
    (A.hom B f hf hc).f i = ModuleCat.ofHom (A.homPiece B f hf i) := rfl

theorem hom_comp (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (C : ZbdGradedComplex R P) (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hfc : ∀ x, B.d (f x) = f (A.d x))
    (g : N →ₗ[R] P) (hg : ∀ i x, x ∈ B.piece i → g x ∈ C.piece i)
    (hgc : ∀ x, C.d (g x) = g (B.d x)) :
    A.hom B f hf hfc ≫ B.hom C g hg hgc =
      A.hom C (g ∘ₗ f) (fun i x hx => hg i _ (hf i x hx))
        (fun x => by rw [LinearMap.comp_apply, hgc, hfc, LinearMap.comp_apply]) := by
  ext i : 1
  rfl

theorem hom_id (A : ZbdGradedComplex R M) :
    A.hom A LinearMap.id (fun _ _ hx => hx) (fun _ => rfl) = 𝟙 A.complex := by
  ext i : 1
  rfl

theorem hom_ext' (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N) (f g : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hfc : ∀ x, B.d (f x) = f (A.d x))
    (hg : ∀ i x, x ∈ A.piece i → g x ∈ B.piece i) (hgc : ∀ x, B.d (g x) = g (A.d x))
    (h : ∀ i x, x ∈ A.piece i → f x = g x) :
    A.hom B f hf hfc = A.hom B g hg hgc := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : A.piece i)
  apply Subtype.ext
  exact h i x.1 x.2

/-- The components of a homotopy induced by a linear map of cohomological degree `-1`. -/
noncomputable def htPiece (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (h : M →ₗ[R] N) (hh : ∀ i x, x ∈ A.piece i → h x ∈ B.piece (i - 1)) (i j : ℤ) :
    A.piece i →ₗ[R] B.piece j :=
  if hji : j + 1 = i then
    (h ∘ₗ (A.piece i).subtype).codRestrict (B.piece j) fun x => by
      have hx := hh i x x.2
      rwa [show i - 1 = j by omega] at hx
  else 0

theorem htPiece_val (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (h : M →ₗ[R] N) (hh : ∀ i x, x ∈ A.piece i → h x ∈ B.piece (i - 1)) {i j : ℤ}
    (hji : j + 1 = i) (x : A.piece i) :
    (A.htPiece B h hh i j x : N) = h x := by
  rw [htPiece, dite_eq_left hji]
  rfl

/-- The components of the homotopy, as morphisms of the complexes' terms. -/
noncomputable def htHom (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (h : M →ₗ[R] N) (hh : ∀ i x, x ∈ A.piece i → h x ∈ B.piece (i - 1)) (i j : ℤ) :
    A.complex.X i ⟶ B.complex.X j :=
  ModuleCat.ofHom (A.htPiece B h hh i j)

/-- The homotopy induced by a linear map `h` of cohomological degree `-1` with
`f = h d + d h + g` (Mathlib's convention `f = dNext + prevD + g`). -/
noncomputable def homotopy (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (f g : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hfc : ∀ x, B.d (f x) = f (A.d x))
    (hg : ∀ i x, x ∈ A.piece i → g x ∈ B.piece i) (hgc : ∀ x, B.d (g x) = g (A.d x))
    (h : M →ₗ[R] N) (hh : ∀ i x, x ∈ A.piece i → h x ∈ B.piece (i - 1))
    (hcomm : ∀ x, f x = h (A.d x) + B.d (h x) + g x) :
    Homotopy (A.hom B f hf hfc) (A.hom B g hg hgc) where
  hom := A.htHom B h hh
  zero i j hji := by
    rw [htHom, htPiece, dite_eq_right (show ¬ j + 1 = i from hji)]
    rfl
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : A.piece i)
    apply Subtype.ext
    change f x = ((A.htPiece B h hh (i + 1) i (A.dPiece i (i + 1) x) +
      B.dPiece (i - 1) i (A.htPiece B h hh i (i - 1) x) + A.homPiece B g hg i x : B.piece i) : N)
    rw [Submodule.coe_add, Submodule.coe_add, htPiece_val _ _ _ _ rfl, A.dPiece_val rfl,
      B.dPiece_val (sub_add_cancel i 1), htPiece_val _ _ _ _ (sub_add_cancel i 1), homPiece_val]
    exact hcomm x

/-- A homotopy equivalence from a strict retraction `g f = 1` and a homotopy `f g ≃ 1`. -/
noncomputable def homotopyEquiv (A : ZbdGradedComplex R M) (B : ZbdGradedComplex R N)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hf : ∀ i x, x ∈ A.piece i → f x ∈ B.piece i) (hfc : ∀ x, B.d (f x) = f (A.d x))
    (hg : ∀ i x, x ∈ B.piece i → g x ∈ A.piece i) (hgc : ∀ x, A.d (g x) = g (B.d x))
    (hgf : ∀ x, g (f x) = x)
    (h : N →ₗ[R] N) (hh : ∀ i x, x ∈ B.piece i → h x ∈ B.piece (i - 1))
    (hcomm : ∀ x, f (g x) = h (B.d x) + B.d (h x) + x) :
    HomotopyEquiv A.complex B.complex where
  hom := A.hom B f hf hfc
  inv := B.hom A g hg hgc
  homotopyHomInvId := Homotopy.ofEq (by
    rw [hom_comp, ← hom_id]
    exact A.hom_ext' A _ _ _ _ _ _ fun _ x _ => hgf x)
  homotopyInvHomId := by
    rw [hom_comp, ← hom_id]
    exact B.homotopy B _ _ _ _ _ _ h hh hcomm

end ZbdGradedComplex

section Homology

variable {R : Type u} [CommRing R]

/-- In a short complex of modules, a cycle whose homology class vanishes is a boundary. -/
theorem zbd_shortComplex_exists_of_homologyπ_eq_zero (S : ShortComplex (ModuleCat.{v} R))
    (c : S.cycles) (hc : S.homologyπ c = 0) : ∃ y : S.X₁, S.f y = S.iCycles c := by
  have h1 : S.moduleCatHomologyIso.hom (S.homologyπ c) = 0 := by
    rw [hc]
    exact map_zero _
  rw [S.π_moduleCatCyclesIso_hom_apply] at h1
  let k : LinearMap.ker S.g.hom := S.moduleCatCyclesIso.hom c
  have h2 : (Submodule.Quotient.mk k : LinearMap.ker S.g.hom ⧸
      LinearMap.range S.moduleCatToCycles) = 0 := h1
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp h2
  refine ⟨y, ?_⟩
  have h3 : S.f y = (k : S.X₂) := congrArg Subtype.val hy
  rw [h3]
  exact S.moduleCatCyclesIso_hom_i_apply c

/-- In a cochain complex of modules, a cycle whose homology class vanishes is a boundary. -/
theorem zbd_exists_boundary_of_homologyπ_eq_zero (K : CochainComplex (ModuleCat.{v} R) ℤ)
    {i : ℤ} (c : K.cycles i) (hc : K.homologyπ i c = 0) :
    ∃ (j : ℤ) (y : K.X j), K.d j i y = K.iCycles i c :=
  ⟨_, zbd_shortComplex_exists_of_homologyπ_eq_zero (K.sc i) c hc⟩

/-- Two lifts to the cycles agree when their values in the complex agree. -/
theorem zbd_liftCycles_apply_eq {K : CochainComplex (ModuleCat.{v} R) ℤ} {i : ℤ}
    {A B : ModuleCat.{v} R} (k : A ⟶ K.X i) (l : B ⟶ K.X i) (j : ℤ)
    (hj : (ComplexShape.up ℤ).next i = j) (hk : k ≫ K.d i j = 0) (hl : l ≫ K.d i j = 0)
    (a : A) (b : B) (h : k a = l b) :
    K.liftCycles k j hj hk a = K.liftCycles l j hj hl b := by
  apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i,
    HomologicalComplex.liftCycles_i]
  exact h

end Homology

end BPFixedPoints.ResolutionTools
