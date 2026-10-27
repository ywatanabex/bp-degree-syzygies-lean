import BPFixedPoints.Degree.Main
import BPFixedPoints.Examples.Graphs
import BPFixedPoints.Graph.Operations
import BPFixedPoints.StateSum.Families
import BPFixedPoints.Incidence.Betti

/-!
# Generic degree N(G) and examples

`HasGenericDegree G n` asserts that some nonzero P∈ℤ[a,b] gives exactly n
simple admissible BP solutions at every nonzero complex parameter with P≠0.
The number is unique (`HasGenericDegree.unique`): the product of two such
polynomials and the coordinates is nonzero, so has a nonvanishing point.
`exists_generic_degree_eq_Q` gives n=Q(G) for loopless G (`hasGenericDegree_iff`).
This defines the paper's generic admissible complex degree N(G).
Adding a leaf or subdividing an edge preserves N (`hasGenericDegree_addLeaf_iff`,
`hasGenericDegree_subdivide_iff`). Computed Q-values give N(C₃)=2,
N(bowtie)=6 and N(K₄)=48, among other examples, using `decide`.
-/

namespace BPFixedPoints

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- n is the generic degree if some nonzero P ensures exactly n simple admissible BP solutions at every nonzero complex parameter with P≠0. -/
def HasGenericDegree (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
    ∀ (a : E → ℂ) (b : V → ℂ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
      MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 →
        Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = n ∧
        ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y

/-- The generic degree is unique. -/
theorem HasGenericDegree.unique {n m : ℕ} (hn : G.HasGenericDegree n) (hm : G.HasGenericDegree m) :
    n = m := by
  classical
  obtain ⟨P₁, hP₁, h₁⟩ := hn
  obtain ⟨P₂, hP₂, h₂⟩ := hm
  set Pp : MvPolynomial (E ⊕ V) ℤ := P₁ * P₂ * ∏ j, MvPolynomial.X j with hPp
  have hPp0 : Pp ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hP₁ hP₂) (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    exact MvPolynomial.X_ne_zero j
  have hmap0 : MvPolynomial.map (Int.castRingHom ℂ) Pp ≠ 0 := fun h =>
    hPp0 (MvPolynomial.map_injective _ (RingHom.injective_int _) (h.trans (map_zero _).symm))
  obtain ⟨x, hx⟩ : ∃ x : E ⊕ V → ℂ,
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℂ) Pp) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hmap0 (MvPolynomial.funext fun x => by simpa using hall x)
  simp only [hPp, map_mul, map_prod, MvPolynomial.map_X, MvPolynomial.eval_X] at hx
  have hx1 := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hx2 := right_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have hx3 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx)
  have hxe : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := Sum.elim_comp_inl_inr x
  have ha : ∀ e, (x ∘ Sum.inl) e ≠ 0 := fun e => hx3 (Sum.inl e) (Finset.mem_univ _)
  have hb : ∀ i, (x ∘ Sum.inr) i ≠ 0 := fun i => hx3 (Sum.inr i) (Finset.mem_univ _)
  rw [← (h₁ _ _ ha hb (by rwa [hxe])).1, (h₂ _ _ ha hb (by rwa [hxe])).1]

/-- The generic degree of a loopless graph is Q(G). -/
theorem hasGenericDegree_Q (hG : G.Loopless) : G.HasGenericDegree G.Q :=
  G.exists_generic_degree_eq_Q hG

theorem hasGenericDegree_iff (hG : G.Loopless) {n : ℕ} : G.HasGenericDegree n ↔ n = G.Q :=
  ⟨fun h => h.unique _ (G.hasGenericDegree_Q hG), fun h => h ▸ G.hasGenericDegree_Q hG⟩

/-- **Adding a leaf.** Adding a leaf at u to a loopless graph preserves generic degree. -/
theorem hasGenericDegree_addLeaf_iff (hG : G.Loopless) (u : V) {n : ℕ} :
    (G.addLeaf u).HasGenericDegree n ↔ G.HasGenericDegree n := by
  rw [hasGenericDegree_iff _ (G.loopless_addLeaf hG u), hasGenericDegree_iff _ hG, Q_addLeaf]

/-- **Subdivision.** Subdividing an edge e₀ of a loopless graph preserves generic degree. -/
theorem hasGenericDegree_subdivide_iff (hG : G.Loopless) (e₀ : E) {n : ℕ} :
    (G.subdivide e₀).HasGenericDegree n ↔ G.HasGenericDegree n := by
  rw [hasGenericDegree_iff _ (G.loopless_subdivide hG e₀), hasGenericDegree_iff _ hG,
    Q_subdivide]

/-- **Sharp lower bound.** A flower of ν triangles, simple of cycle rank ν, has generic degree (ν−1)2^ν+2. -/
theorem triFlower_hasGenericDegree (ν : ℕ) :
    (triFlower ν).HasGenericDegree (bouquetQ ν) :=
  ((triFlower ν).hasGenericDegree_iff (loopless_triFlower ν)).2 (Q_triFlower ν).symm

/-- **Sharp upper bound.** A ladder of cycle rank k is simple and has generic degree U_k. -/
theorem ladder_hasGenericDegree (k : ℕ) :
    ∃ n : ℕ, (ladder k).HasGenericDegree n ∧ (n : ℤ) = U k :=
  ⟨(ladder k).Q, (ladder k).hasGenericDegree_Q (loopless_ladder k), Q_ladder k⟩

/-- **The total Betti number is the generic degree.** For a loopless graph, the sum of the first-page Betti table is N. -/
theorem hasGenericDegree_sum_betti (hG : G.Loopless) :
    G.HasGenericDegree (∑ i ∈ Finset.range (Fintype.card E + 1),
      ∑ k ∈ Finset.range (Fintype.card E + 1), G.betti i k) := by
  rw [G.sum_betti_eq_Q]
  exact G.hasGenericDegree_Q hG

end Multigraph

namespace Examples

open Multigraph

theorem bowtie_N : bowtie.HasGenericDegree 6 :=
  (bowtie.hasGenericDegree_iff (by unfold Multigraph.Loopless; decide)).2 bowtie_Q.symm

theorem K4_N : K4.HasGenericDegree 48 :=
  (K4.hasGenericDegree_iff (by unfold Multigraph.Loopless; decide)).2 K4_Q.symm

theorem triangle_N : triangle.HasGenericDegree 2 :=
  (triangle.hasGenericDegree_iff (by unfold Multigraph.Loopless; decide)).2 triangle_Q.symm

theorem parallel2_N : parallel2.HasGenericDegree 2 :=
  (parallel2.hasGenericDegree_iff (by unfold Multigraph.Loopless; decide)).2 parallel2_Q.symm

theorem path3_N : path3.HasGenericDegree 1 :=
  (path3.hasGenericDegree_iff (by unfold Multigraph.Loopless; decide)).2 path3_Q.symm

end Examples

end BPFixedPoints
