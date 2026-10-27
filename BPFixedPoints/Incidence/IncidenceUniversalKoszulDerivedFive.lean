import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Comparing shifted morphisms along a triangulated functor: the five lemma

This file supplies the homological algebra for computing hypercohomology of a bounded complex
by induction on its length (paper, Theorem `alg:resolution`, obligation (c)).

* **Long exact sequences.** For a distinguished triangle `T` in a pretriangulated category and an
  object `W`, the shifted morphisms out of `W` form a long exact sequence, with connecting map the
  composition with `T.mor₃` (`shiftedHom_exact₁`, `shiftedHom_exact₂`, `shiftedHom_exact₃`, and the
  vanishing of consecutive composites `shiftedHom_comp₁₂`, `shiftedHom_comp₂₃`,
  `shiftedHom_comp₃₁`), from Mathlib's homological functor `preadditiveCoyoneda`.
* **Bijectivity along a triangulated functor.** For a triangulated functor `F`,
  `DerivedMapBijective F W X` says that `F` is bijective from `W ⟶ X⟦n⟧` to `F W ⟶ F (X⟦n⟧)` for
  every `n`. It is invariant under isomorphism (`DerivedMapBijective.of_iso`), holds for zero
  objects (`DerivedMapBijective.of_isZero`), is stable under shifts
  (`DerivedMapBijective.shift`), and satisfies the two-out-of-three property in distinguished
  triangles (`DerivedMapBijective.of_triangle₂`, `DerivedMapBijective.of_triangle₃`) by the five
  lemma.

Nothing specific to sheaves or to the incidence complex is used here.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

set_option linter.unusedSectionVars false

/-! ### Long exact sequences of shifted morphisms out of a fixed object -/

section Exact

variable {K : Type*} [Category K] [HasZeroObject K] [Preadditive K] [HasShift K ℤ]
  [∀ n : ℤ, (shiftFunctor K n).Additive] [Pretriangulated K]

/-- Exactness at the second object of a distinguished triangle, for shifted morphisms out of `W`. -/
theorem shiftedHom_exact₂ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n : ℤ)
    (f : ShiftedHom W T.obj₂ n) (hf : f ≫ T.mor₂⟦n⟧' = 0) :
    ∃ g : ShiftedHom W T.obj₁ n, g ≫ T.mor₁⟦n⟧' = f := by
  have h := (ShortComplex.ab_exact_iff _).mp
    ((preadditiveCoyoneda.obj (op W)).homologySequence_exact₂ T hT n) f hf
  exact h

/-- Exactness at the third object of a distinguished triangle, for shifted morphisms out of `W`. -/
theorem shiftedHom_exact₃ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n₀ n₁ : ℤ)
    (h : 1 + n₀ = n₁) (f : ShiftedHom W T.obj₃ n₀)
    (hf : f.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) h = 0) :
    ∃ g : ShiftedHom W T.obj₂ n₀, g ≫ T.mor₂⟦n₀⟧' = f := by
  have hδ := preadditiveCoyoneda_homologySequenceδ_apply T n₀ n₁ (by omega) (A := op W) f
  have hex := (ShortComplex.ab_exact_iff _).mp
    ((preadditiveCoyoneda.obj (op W)).homologySequence_exact₃ T hT n₀ n₁ (by omega)) f
    (hδ.trans hf)
  exact hex

/-- Exactness at the first object of a distinguished triangle, for shifted morphisms out of `W`. -/
theorem shiftedHom_exact₁ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n₀ n₁ : ℤ)
    (h : 1 + n₀ = n₁) (f : ShiftedHom W T.obj₁ n₁) (hf : f ≫ T.mor₁⟦n₁⟧' = 0) :
    ∃ g : ShiftedHom W T.obj₃ n₀, g.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) h = f := by
  obtain ⟨g, hg⟩ := (ShortComplex.ab_exact_iff _).mp
    ((preadditiveCoyoneda.obj (op W)).homologySequence_exact₁ T hT n₀ n₁ (by omega)) f hf
  refine ⟨g, ?_⟩
  have hδ := preadditiveCoyoneda_homologySequenceδ_apply T n₀ n₁ (by omega) (A := op W) g
  rw [← hg, hδ]
  rfl

/-- Consecutive morphisms of the long exact sequence compose to zero at the second object. -/
theorem shiftedHom_comp₁₂ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n : ℤ)
    (g : ShiftedHom W T.obj₁ n) : (g ≫ T.mor₁⟦n⟧') ≫ T.mor₂⟦n⟧' = 0 := by
  rw [Category.assoc, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero,
    comp_zero]

/-- Consecutive morphisms of the long exact sequence compose to zero at the third object. -/
theorem shiftedHom_comp₂₃ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n₀ n₁ : ℤ)
    (h : 1 + n₀ = n₁) (g : ShiftedHom W T.obj₂ n₀) :
    ShiftedHom.comp (g ≫ T.mor₂⟦n₀⟧' : ShiftedHom W T.obj₃ n₀)
      (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) h = 0 := by
  simp only [ShiftedHom.comp, Category.assoc, ← Functor.map_comp_assoc,
    comp_distTriang_mor_zero₂₃ T hT, Functor.map_zero, zero_comp, comp_zero]

/-- Consecutive morphisms of the long exact sequence compose to zero at the first object. -/
theorem shiftedHom_comp₃₁ (W : K) (T : Triangle K) (hT : T ∈ distTriang K) (n₀ n₁ : ℤ)
    (h : 1 + n₀ = n₁) (g : ShiftedHom W T.obj₃ n₀) :
    g.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) h ≫ T.mor₁⟦n₁⟧' = 0 := by
  dsimp only [ShiftedHom.comp]
  rw [Category.assoc, Category.assoc]
  have hn := (shiftFunctorAdd' K 1 n₀ n₁ h).inv.naturality T.mor₁
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc, comp_distTriang_mor_zero₃₁ T hT,
    Functor.map_zero, zero_comp, comp_zero]

end Exact

/-! ### Functors inducing bijections on shifted morphisms -/

section Bijective

variable {K D : Type*} [Category K] [Category D] [HasZeroObject K] [HasZeroObject D]
  [Preadditive K] [Preadditive D] [HasShift K ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor K n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated K] [Pretriangulated D] (F : K ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- **Bijectivity on shifted morphisms.** The functor `F` induces bijections from the morphisms
`W ⟶ X⟦n⟧` to the morphisms `F W ⟶ F (X⟦n⟧)`, for every shift `n`. -/
def DerivedMapBijective (W X : K) : Prop :=
  ∀ n : ℤ, Function.Bijective (F.map : (W ⟶ X⟦n⟧) → (F.obj W ⟶ F.obj (X⟦n⟧)))

/-- Bijectivity of a functor on morphisms is invariant under isomorphism of the target. -/
theorem map_bijective_of_iso {W X X' : K} (e : X ≅ X')
    (h : Function.Bijective (F.map : (W ⟶ X) → (F.obj W ⟶ F.obj X))) :
    Function.Bijective (F.map : (W ⟶ X') → (F.obj W ⟶ F.obj X')) := by
  constructor
  · intro f₁ f₂ hf
    have h₁ : F.map (f₁ ≫ e.inv) = F.map (f₂ ≫ e.inv) := by
      rw [F.map_comp, F.map_comp, hf]
    have h₂ := h.1 h₁
    simpa using congrArg (fun f => f ≫ e.hom) h₂
  · intro g
    obtain ⟨f, hf⟩ := h.2 (g ≫ F.map e.inv)
    refine ⟨f ≫ e.hom, ?_⟩
    rw [F.map_comp, hf, Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

/-- The action of `F` on shifted morphisms is bijective iff `F` is bijective on the underlying
morphisms. -/
theorem bijective_shiftedHomMap_iff (W X : K) (n : ℤ) :
    Function.Bijective (fun f : ShiftedHom W X n => f.map F) ↔
      Function.Bijective (F.map : (W ⟶ X⟦n⟧) → (F.obj W ⟶ F.obj (X⟦n⟧))) := by
  let e := (F.commShiftIso n).app X
  have hfun : (fun f : ShiftedHom W X n => f.map F) =
      (fun g => g ≫ e.hom) ∘ (F.map : (W ⟶ X⟦n⟧) → (F.obj W ⟶ F.obj (X⟦n⟧))) := rfl
  have hb : Function.Bijective (fun g : F.obj W ⟶ F.obj (X⟦n⟧) => g ≫ e.hom) :=
    ⟨fun g₁ g₂ hg => by simpa using congrArg (fun g => g ≫ e.inv) hg,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  rw [hfun]
  constructor
  · intro hc
    exact ⟨fun a b hab => hc.1 (by simp only [Function.comp_apply, hab]),
      fun g => by
        obtain ⟨f, hf⟩ := hc.2 (g ≫ e.hom)
        exact ⟨f, hb.1 hf⟩⟩
  · intro hm
    exact hb.comp hm

/-- `DerivedMapBijective` is invariant under isomorphism of the target. -/
theorem DerivedMapBijective.of_iso {W X X' : K} (e : X ≅ X') (h : DerivedMapBijective F W X) :
    DerivedMapBijective F W X' :=
  fun n => map_bijective_of_iso F ((shiftFunctor K n).mapIso e) (h n)

/-- `DerivedMapBijective` holds for zero objects. -/
theorem DerivedMapBijective.of_isZero {W X : K} (hX : IsZero X) : DerivedMapBijective F W X := by
  intro n
  have hX' : IsZero (X⟦n⟧) := (shiftFunctor K n).map_isZero hX
  have hFX : IsZero (F.obj (X⟦n⟧)) := F.map_isZero hX'
  exact ⟨fun f₁ f₂ _ => hX'.eq_of_tgt f₁ f₂, fun g => ⟨0, hFX.eq_of_tgt _ _⟩⟩

/-- `DerivedMapBijective` is stable under shifts of the target. -/
theorem DerivedMapBijective.shift {W X : K} (h : DerivedMapBijective F W X) (k : ℤ) :
    DerivedMapBijective F W (X⟦k⟧) :=
  fun n => map_bijective_of_iso F ((shiftFunctorAdd' K k n (k + n) rfl).app X) (h (k + n))

/-- **The two-out-of-three property in a distinguished triangle** (five lemma). If `F` is
bijective on shifted morphisms from `W` into the first and third objects of a distinguished
triangle, it is bijective into the second. -/
theorem DerivedMapBijective.of_triangle₂ {W : K} (T : Triangle K) (hT : T ∈ distTriang K)
    (h₁ : DerivedMapBijective F W T.obj₁) (h₃ : DerivedMapBijective F W T.obj₃) :
    DerivedMapBijective F W T.obj₂ := by
  have hD := F.map_distinguished T hT
  set T' := F.mapTriangle.obj T
  have b₁ : ∀ n, Function.Bijective (fun f : ShiftedHom W T.obj₁ n => f.map F) :=
    fun n => (bijective_shiftedHomMap_iff F _ _ n).mpr (h₁ n)
  have b₃ : ∀ n, Function.Bijective (fun f : ShiftedHom W T.obj₃ n => f.map F) :=
    fun n => (bijective_shiftedHomMap_iff F _ _ n).mpr (h₃ n)
  -- compatibilities of the comparison maps with the maps of the long exact sequences
  have c₁ : ∀ (n : ℤ) (g : ShiftedHom W T.obj₁ n),
      ShiftedHom.map (g ≫ T.mor₁⟦n⟧' : ShiftedHom W T.obj₂ n) F = g.map F ≫ T'.mor₁⟦n⟧' := by
    intro n g
    have e₁ := ShiftedHom.comp_mk₀ g (0 : ℤ) rfl T.mor₁
    have e₂ := ShiftedHom.comp_mk₀ (g.map F) (0 : ℤ) rfl (F.map T.mor₁)
    rw [← e₁, ShiftedHom.map_comp, ShiftedHom.map_mk₀, e₂]
    rfl
  have c₂ : ∀ (n : ℤ) (g : ShiftedHom W T.obj₂ n),
      ShiftedHom.map (g ≫ T.mor₂⟦n⟧' : ShiftedHom W T.obj₃ n) F = g.map F ≫ T'.mor₂⟦n⟧' := by
    intro n g
    have e₁ := ShiftedHom.comp_mk₀ g (0 : ℤ) rfl T.mor₂
    have e₂ := ShiftedHom.comp_mk₀ (g.map F) (0 : ℤ) rfl (F.map T.mor₂)
    rw [← e₁, ShiftedHom.map_comp, ShiftedHom.map_mk₀, e₂]
    rfl
  have c₃ : ∀ (n₀ n₁ : ℤ) (h : 1 + n₀ = n₁) (g : ShiftedHom W T.obj₃ n₀),
      (g.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) h).map F =
        (g.map F).comp (T'.mor₃ : ShiftedHom T'.obj₃ T'.obj₁ (1 : ℤ)) h := by
    intro n₀ n₁ h g
    rw [ShiftedHom.map_comp]
    rfl
  intro n
  rw [← bijective_shiftedHomMap_iff]
  constructor
  · intro f₁ f₂ hf
    have key : ∀ f : ShiftedHom W T.obj₂ n, f.map F = 0 → f = 0 := by
      intro f hf0
      have h3 : ShiftedHom.map (f ≫ T.mor₂⟦n⟧' : ShiftedHom W T.obj₃ n) F = 0 := by
        rw [c₂, hf0, zero_comp]
      have h3' : f ≫ T.mor₂⟦n⟧' = 0 :=
        (b₃ n).1 (h3.trans (ShiftedHom.map_zero (X := W) (Y := T.obj₃) F).symm)
      obtain ⟨g, hg⟩ := shiftedHom_exact₂ W T hT n f h3'
      have hg0 : g.map F ≫ T'.mor₁⟦n⟧' = 0 := by rw [← c₁, hg, hf0]
      obtain ⟨y, hy⟩ := shiftedHom_exact₁ (F.obj W) T' hD (n - 1) n (by omega) (g.map F) hg0
      obtain ⟨x, hx⟩ := (b₃ (n - 1)).2 y
      have hgx : g = x.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) (by omega) := by
        apply (b₁ n).1
        change g.map F = ShiftedHom.map (x.comp _ _) F
        rw [c₃, ← hy]
        simp only at hx
        rw [hx]
      rw [← hg, hgx]
      exact shiftedHom_comp₃₁ W T hT (n - 1) n (by omega) x
    have hsub := key (f₁ - f₂) (by
      simp only [ShiftedHom.map, Functor.map_sub, Preadditive.sub_comp]
      change f₁.map F - f₂.map F = 0
      have hf' : f₁.map F = f₂.map F := hf
      rw [hf', sub_self])
    exact sub_eq_zero.mp hsub
  · intro y
    obtain ⟨x₃, hx₃⟩ := (b₃ n).2 (y ≫ T'.mor₂⟦n⟧')
    have hz : x₃.comp (T.mor₃ : ShiftedHom T.obj₃ T.obj₁ (1 : ℤ)) (show 1 + n = n + 1 by omega) =
        0 := by
      apply (b₁ (n + 1)).1
      change ShiftedHom.map (x₃.comp _ _) F = ShiftedHom.map (0 : ShiftedHom W T.obj₁ (n + 1)) F
      rw [c₃, ShiftedHom.map_zero]
      simp only at hx₃
      rw [hx₃]
      exact shiftedHom_comp₂₃ (F.obj W) T' hD n (n + 1) (by omega) y
    obtain ⟨x₂, hx₂⟩ := shiftedHom_exact₃ W T hT n (n + 1) (by omega) x₃ hz
    have hdiff : (y - x₂.map F) ≫ T'.mor₂⟦n⟧' = 0 := by
      rw [Preadditive.sub_comp, ← c₂, hx₂]
      simp only at hx₃
      rw [hx₃, sub_self]
    obtain ⟨y₁, hy₁⟩ := shiftedHom_exact₂ (F.obj W) T' hD n _ hdiff
    obtain ⟨x₁, hx₁⟩ := (b₁ n).2 y₁
    refine ⟨x₂ + x₁ ≫ T.mor₁⟦n⟧', ?_⟩
    simp only
    rw [ShiftedHom.map_add, c₁]
    simp only at hx₁
    rw [hx₁, hy₁, add_sub_cancel]

/-- The two-out-of-three property for the third object of a distinguished triangle. -/
theorem DerivedMapBijective.of_triangle₃ {W : K} (T : Triangle K) (hT : T ∈ distTriang K)
    (h₁ : DerivedMapBijective F W T.obj₁) (h₂ : DerivedMapBijective F W T.obj₂) :
    DerivedMapBijective F W T.obj₃ :=
  DerivedMapBijective.of_triangle₂ F T.rotate (rot_of_distTriang T hT) h₂ (h₁.shift F 1)

end Bijective

end BPFixedPoints.Multigraph
