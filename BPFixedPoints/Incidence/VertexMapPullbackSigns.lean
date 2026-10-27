import BPFixedPoints.Incidence.CechProductPermutation

/-!
# Koszul signs of arbitrary vertex functions

`vertexPermSign` (in `CechProductPermutation.lean`) is the Koszul sign of reordering the degree-one
factors at a vertex set `A` along a bijection `ψ : V ≃ W`, relative to the enumerations
`Fintype.equivFin V` and `Fintype.equivFin W`. The same count makes sense for an arbitrary function
`f : V → W`: `vertexMapInversions f A` is the number of pairs of `A` whose order in the
enumeration of `V` is reversed by `f` in the enumeration of `W`, and
`vertexMapSign R f A = (-1) ^ vertexMapInversions f A`. For a bijection it is `vertexPermSign`
(`vertexMapSign_equiv`).

When `f` is injective on the relevant sets we prove the two identities used for state formulas:
* **insertion** (`vertexMapSign_insert`): adding one vertex `v` to `A` changes the sign by the
  parity of the vertices of `A` before `v` in `V` plus the parity of those whose images come before
  `f v` in `W`; this is what makes the extension of Čech chains along an injective vertex function
  commute with the product Čech differentials;
* **composition** (`vertexMapSign_comp`): the sign of `g ∘ f` on `A` is the sign of `g` on
  `f(A)` times the sign of `f` on `A`.

Nothing here depends on graphs.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

section Signs

variable {V W X : Type} [Fintype V] [Fintype W] [Fintype X]

/-- The number of pairs of a vertex set whose order in the enumeration of `V` is reversed by `f`
in the enumeration of `W`. -/
noncomputable def vertexMapInversions (f : V → W) (A : Finset V) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if Fintype.equivFin V a < Fintype.equivFin V b ∧
    Fintype.equivFin W (f b) < Fintype.equivFin W (f a) then 1 else 0

/-- The Koszul sign of carrying the degree-one factors at the vertices of `A` along `f`, relative
to the enumerations of `V` and `W`. -/
noncomputable def vertexMapSign (R : Type*) [CommRing R] (f : V → W) (A : Finset V) : R :=
  (-1) ^ vertexMapInversions f A

/-- For a bijection the inversion count is that of `vertexInversions`. -/
theorem vertexMapInversions_equiv (ψ : V ≃ W) (A : Finset V) :
    vertexMapInversions ψ A = vertexInversions ψ A := rfl

/-- For a bijection the sign is `vertexPermSign`. -/
theorem vertexMapSign_equiv (R : Type*) [CommRing R] (ψ : V ≃ W) (A : Finset V) :
    vertexMapSign R ψ A = vertexPermSign R ψ A := rfl

@[simp] theorem vertexMapSign_mul_self (R : Type*) [CommRing R] (f : V → W) (A : Finset V) :
    vertexMapSign R f A * vertexMapSign R f A = 1 := by
  rw [vertexMapSign, ← pow_add, ← two_mul, pow_mul]
  simp

@[simp] theorem map_vertexMapSign {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (g : V → W) (A : Finset V) : f (vertexMapSign R g A) = vertexMapSign R' g A := by
  simp [vertexMapSign]

@[simp] theorem vertexMapSign_empty (R : Type*) [CommRing R] (f : V → W) :
    vertexMapSign R f ∅ = 1 := by
  simp [vertexMapSign, vertexMapInversions]

/-- The sign is a unit: it is nonzero in every nontrivial ring. -/
theorem vertexMapSign_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (f : V → W)
    (A : Finset V) : vertexMapSign R f A ≠ 0 := by
  intro h
  have h1 := vertexMapSign_mul_self R f A
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- The sign is `1` or `-1`. -/
theorem vertexMapSign_eq_one_or (R : Type*) [CommRing R] (f : V → W) (A : Finset V) :
    vertexMapSign R f A = 1 ∨ vertexMapSign R f A = -1 := by
  rw [vertexMapSign]
  rcases Nat.even_or_odd (vertexMapInversions f A) with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- Inversions after inserting a vertex: those of the set, plus the mixed pairs with the new
vertex. -/
theorem vertexMapInversions_insert [DecidableEq V] (f : V → W) {A : Finset V} {v : V}
    (hv : v ∉ A) :
    vertexMapInversions f (insert v A) = vertexMapInversions f A +
      ∑ u ∈ A,
        ((if Fintype.equivFin V v < Fintype.equivFin V u ∧
            Fintype.equivFin W (f u) < Fintype.equivFin W (f v) then 1 else 0) +
          (if Fintype.equivFin V u < Fintype.equivFin V v ∧
            Fintype.equivFin W (f v) < Fintype.equivFin W (f u) then 1 else 0)) := by
  unfold vertexMapInversions
  rw [Finset.sum_insert hv, Finset.sum_insert hv]
  simp only [Finset.sum_insert hv, lt_irrefl, false_and, ite_false, zero_add,
    Finset.sum_add_distrib]
  ring

/-- **Insertion of a vertex.** If `f` is injective on `insert v A` and `v ∉ A`, the sign of
`insert v A` times the parity of the vertices of `A` before `v` in `V` is the parity of the
vertices of `A` whose images come before `f v` in `W` times the sign of `A`. -/
theorem vertexMapSign_insert [DecidableEq V] (R : Type*) [CommRing R] (f : V → W)
    {A : Finset V} {v : V} (hv : v ∉ A) (hf : Set.InjOn f (insert v A : Finset V)) :
    vertexMapSign R f (insert v A) *
        (-1 : R) ^ (∑ u ∈ A, if Fintype.equivFin V u < Fintype.equivFin V v then 1 else 0) =
      (-1 : R) ^ (∑ u ∈ A,
          if Fintype.equivFin W (f u) < Fintype.equivFin W (f v) then 1 else 0) *
        vertexMapSign R f A := by
  unfold vertexMapSign
  rw [← pow_add, ← pow_add]
  apply neg_one_pow_eq_of_even_add
  rw [vertexMapInversions_insert f hv]
  have hpt : ∀ u ∈ A, Even (((if Fintype.equivFin V v < Fintype.equivFin V u ∧
        Fintype.equivFin W (f u) < Fintype.equivFin W (f v) then 1 else 0) +
      (if Fintype.equivFin V u < Fintype.equivFin V v ∧
        Fintype.equivFin W (f v) < Fintype.equivFin W (f u) then 1 else 0)) +
      (if Fintype.equivFin V u < Fintype.equivFin V v then 1 else 0) +
      (if Fintype.equivFin W (f u) < Fintype.equivFin W (f v) then 1 else 0)) := by
    intro u hu
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    have h1 : Fintype.equivFin V u ≠ Fintype.equivFin V v :=
      fun h => huv ((Fintype.equivFin V).injective h)
    have h2 : Fintype.equivFin W (f u) ≠ Fintype.equivFin W (f v) := fun h =>
      huv (hf (by simp [hu]) (by simp) ((Fintype.equivFin W).injective h))
    rcases lt_or_gt_of_ne h1 with h1 | h1 <;> rcases lt_or_gt_of_ne h2 with h2 | h2 <;>
      simp [h1, h2, not_lt_of_gt]
  have hsum := Finset.even_sum _ hpt
  simp only [Finset.sum_add_distrib] at hsum ⊢
  obtain ⟨k, hk⟩ := hsum
  exact ⟨vertexMapInversions f A + k, by omega⟩

/-- Inversions of a composite have the parity of the sum of the inversions, when the functions
are injective on the relevant sets. -/
theorem even_vertexMapInversions_comp [DecidableEq W] (f : V → W) (g : W → X) (A : Finset V)
    (hf : Set.InjOn f A) (hg : Set.InjOn g (A.image f : Finset W)) :
    Even (vertexMapInversions (g ∘ f) A + vertexMapInversions g (A.image f) +
      vertexMapInversions f A) := by
  let rV := Fintype.equivFin V
  let rW := Fintype.equivFin W
  let rX := Fintype.equivFin X
  let F : V → V → ℕ := fun a b =>
    (if rV a < rV b ∧ rX (g (f b)) < rX (g (f a)) then 1 else 0) +
      (if rW (f a) < rW (f b) ∧ rX (g (f b)) < rX (g (f a)) then 1 else 0) +
      (if rV a < rV b ∧ rW (f b) < rW (f a) then 1 else 0)
  have himage : vertexMapInversions g (A.image f) = ∑ a ∈ A, ∑ b ∈ A,
      if rW (f a) < rW (f b) ∧ rX (g (f b)) < rX (g (f a)) then 1 else 0 := by
    unfold vertexMapInversions
    rw [Finset.sum_image hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_image hf]
  have hsum : vertexMapInversions (g ∘ f) A + vertexMapInversions g (A.image f) +
      vertexMapInversions f A = ∑ a ∈ A, ∑ b ∈ A, F a b := by
    rw [himage]
    simp only [F, Finset.sum_add_distrib, vertexMapInversions, Function.comp_apply]
    rfl
  have hdiag : ∀ a, F a a = 0 := by
    intro a
    simp [F]
  have hpair : ∀ a ∈ A, ∀ b ∈ A, Even (F a b + F b a) := by
    intro a ha b hb
    by_cases hab : a = b
    · subst hab
      rw [hdiag]
      exact Even.zero
    have h0 : rV a ≠ rV b := fun h => hab (rV.injective h)
    have hfab : f a ≠ f b := fun h => hab (hf ha hb h)
    have h1 : rW (f a) ≠ rW (f b) := fun h => hfab (rW.injective h)
    have h2 : rX (g (f a)) ≠ rX (g (f b)) := fun h =>
      hfab (hg (Finset.mem_image_of_mem f ha) (Finset.mem_image_of_mem f hb) (rX.injective h))
    rcases lt_or_gt_of_ne h0 with h | h <;> rcases lt_or_gt_of_ne h1 with h' | h' <;>
      rcases lt_or_gt_of_ne h2 with h'' | h'' <;>
      simp [F, h, h', h'', not_lt_of_gt]
  have hsplit : ∑ a ∈ A, ∑ b ∈ A, F a b =
      ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F a b + F b a else 0) := by
    have hswap : ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F b a else 0) =
        ∑ a ∈ A, ∑ b ∈ A, (if rV b < rV a then F a b else 0) := Finset.sum_comm
    have hterm : ∀ a b, F a b = (if rV a < rV b then F a b else 0) +
        (if rV b < rV a then F a b else 0) := by
      intro a b
      rcases lt_trichotomy (rV a) (rV b) with h | h | h
      · simp [h, not_lt_of_gt h]
      · rw [rV.injective h, hdiag]
        simp
      · simp [h, not_lt_of_gt h]
    calc ∑ a ∈ A, ∑ b ∈ A, F a b
        = ∑ a ∈ A, ∑ b ∈ A, ((if rV a < rV b then F a b else 0) +
            (if rV b < rV a then F a b else 0)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F a b else 0) +
          ∑ a ∈ A, ∑ b ∈ A, (if rV b < rV a then F a b else 0) := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F a b else 0) +
          ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F b a else 0) := by rw [hswap]
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then F a b + F b a else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
  rw [hsum, hsplit]
  refine Finset.even_sum _ fun a ha => Finset.even_sum _ fun b hb => ?_
  split_ifs
  · exact hpair a ha b hb
  · exact Even.zero

/-- **Composition of signs.** If `f` is injective on `A` and `g` is injective on `f(A)`, the sign
of `g ∘ f` on `A` is the sign of `g` on `f(A)` times the sign of `f` on `A`. -/
theorem vertexMapSign_comp [DecidableEq W] (R : Type*) [CommRing R] (f : V → W) (g : W → X)
    (A : Finset V) (hf : Set.InjOn f A) (hg : Set.InjOn g (A.image f : Finset W)) :
    vertexMapSign R (g ∘ f) A = vertexMapSign R g (A.image f) * vertexMapSign R f A := by
  unfold vertexMapSign
  rw [← pow_add]
  apply neg_one_pow_eq_of_even_add
  have h := even_vertexMapInversions_comp f g A hf hg
  rw [show vertexMapInversions (g ∘ f) A + (vertexMapInversions g (A.image f) +
    vertexMapInversions f A) = vertexMapInversions (g ∘ f) A +
      vertexMapInversions g (A.image f) + vertexMapInversions f A by ring]
  exact h

/-- The sign only depends on the values of the function on the set. -/
theorem vertexMapSign_congr (R : Type*) [CommRing R] {f f' : V → W} {A : Finset V}
    (h : ∀ v ∈ A, f v = f' v) : vertexMapSign R f A = vertexMapSign R f' A := by
  unfold vertexMapSign vertexMapInversions
  congr 1
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [h a ha, h b hb]

end Signs

end BPFixedPoints.Multigraph
