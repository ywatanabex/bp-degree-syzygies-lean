import BPFixedPoints.StateSum.SharpBounds
import BPFixedPoints.StateSum.Bouquet

/-!
# Simple graph families attaining the bounds

`triFlower ν` joins ν triangles at one vertex. It is simple, has cycle rank ν
and Q=(ν−1)2^ν+2 (`Q_triFlower`), attaining the lower bound. A triangle
contributes only when all or none of its edges are selected, since partial
selection gives a degree-one vertex with φ(1)=0.
`ladder k` is the 2×(k+1) grid with k+1 rungs and 2k rails. It is connected,
simple, subcubic and of cycle rank k, giving Q=U_k (`Q_ladder`), the upper bound.
Both are loopless (`loopless_triFlower`, `loopless_ladder`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

/-! ### Triangle flowers -/

/-- Flower of ν triangles: center none, a_i=some(i,false), b_i=some(i,true); edges (i,0)=center–a_i, (i,1)=a_i–b_i, (i,2)=b_i–center. -/
def triFlower (ν : ℕ) : Multigraph (Option (Fin ν × Bool)) (Fin ν × Fin 3) where
  fst p := ![none, some (p.1, false), some (p.1, true)] p.2
  snd p := ![some (p.1, false), some (p.1, true), none] p.2

theorem loopless_triFlower (ν : ℕ) : (triFlower ν).Loopless := by
  rintro ⟨i, j⟩
  fin_cases j <;> simp [triFlower]

theorem cycleRank_triFlower (ν : ℕ) : (triFlower ν).cycleRank = ν := by
  simp only [cycleRank, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  omega

section TriFlowerDeg

variable {ν : ℕ}

theorem endCount_triFlower_a (e : Fin ν × Fin 3) (i : Fin ν) :
    (triFlower ν).endCount e (some (i, false)) =
      (if e = (i, 0) then 1 else 0) + (if e = (i, 1) then 1 else 0) := by
  obtain ⟨k, j⟩ := e
  by_cases hk : k = i
  · subst hk; fin_cases j <;> simp [endCount, triFlower]
  · fin_cases j <;> simp [endCount, triFlower, hk]

theorem endCount_triFlower_b (e : Fin ν × Fin 3) (i : Fin ν) :
    (triFlower ν).endCount e (some (i, true)) =
      (if e = (i, 1) then 1 else 0) + (if e = (i, 2) then 1 else 0) := by
  obtain ⟨k, j⟩ := e
  by_cases hk : k = i
  · subst hk; fin_cases j <;> simp [endCount, triFlower]
  · fin_cases j <;> simp [endCount, triFlower, hk]

theorem endCount_triFlower_center (e : Fin ν × Fin 3) :
    (triFlower ν).endCount e none = (if e.2 = 0 then 1 else 0) + (if e.2 = 2 then 1 else 0) := by
  obtain ⟨k, j⟩ := e
  fin_cases j <;> simp [endCount, triFlower]

theorem deg_triFlower_a (S : Finset (Fin ν × Fin 3)) (i : Fin ν) :
    (triFlower ν).deg S (some (i, false)) =
      (if (i, 0) ∈ S then 1 else 0) + (if (i, 1) ∈ S then 1 else 0) := by
  simp only [deg, endCount_triFlower_a, Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem deg_triFlower_b (S : Finset (Fin ν × Fin 3)) (i : Fin ν) :
    (triFlower ν).deg S (some (i, true)) =
      (if (i, 1) ∈ S then 1 else 0) + (if (i, 2) ∈ S then 1 else 0) := by
  simp only [deg, endCount_triFlower_b, Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- Weight at the two petal vertices is one if all three edge memberships agree, and zero otherwise. -/
theorem phi_petal (p₀ p₁ p₂ : Prop) [Decidable p₀] [Decidable p₁] [Decidable p₂] :
    phi ((if p₀ then 1 else 0) + (if p₁ then 1 else 0)) *
        phi ((if p₁ then 1 else 0) + (if p₂ then 1 else 0)) =
      if (p₀ ↔ p₁) ∧ (p₁ ↔ p₂) then 1 else 0 := by
  by_cases h₀ : p₀ <;> by_cases h₁ : p₁ <;> by_cases h₂ : p₂ <;> simp [h₀, h₁, h₂, phi]

end TriFlowerDeg

/-- Edge set K×{0,1,2} with consistent petal membership. -/
def petalSet {ν : ℕ} (K : Finset (Fin ν)) : Finset (Fin ν × Fin 3) := K ×ˢ Finset.univ

theorem wt_triFlower {ν : ℕ} (S : Finset (Fin ν × Fin 3)) :
    (triFlower ν).wt phi S = phi ((triFlower ν).deg S none) *
      ∏ i, (if ((i, 0) ∈ S ↔ (i, 1) ∈ S) ∧ ((i, 1) ∈ S ↔ (i, 2) ∈ S) then 1 else 0) := by
  rw [wt, Fintype.prod_option, Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool, deg_triFlower_a, deg_triFlower_b, mul_comm, phi_petal]

theorem wt_triFlower_eq_zero {ν : ℕ} {S : Finset (Fin ν × Fin 3)}
    (hS : S ∉ Finset.univ.image (petalSet (ν := ν))) : (triFlower ν).wt phi S = 0 := by
  rw [wt_triFlower]
  apply mul_eq_zero_of_right
  rw [Finset.prod_eq_zero_iff]
  by_contra hall
  push Not at hall
  apply hS
  refine Finset.mem_image.2 ⟨Finset.univ.filter fun i => (i, 0) ∈ S, Finset.mem_univ _, ?_⟩
  ext ⟨i, j⟩
  have hi := hall i (Finset.mem_univ _)
  rw [ite_ne_right_iff] at hi
  have h1 := hi.1
  simp only [petalSet, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
  fin_cases j
  · rfl
  · exact h1.1
  · exact h1.1.trans h1.2

theorem deg_triFlower_center_petalSet {ν : ℕ} (K : Finset (Fin ν)) :
    (triFlower ν).deg (petalSet K) none = 2 * K.card := by
  rw [deg, petalSet, Finset.sum_product]
  simp only [endCount_triFlower_center]
  simp [Fin.sum_univ_three, Finset.sum_const, mul_comm]

theorem wt_triFlower_petalSet {ν : ℕ} (K : Finset (Fin ν)) :
    (triFlower ν).wt phi (petalSet K) = phi (2 * K.card) := by
  rw [wt_triFlower, deg_triFlower_center_petalSet]
  simp [petalSet]

theorem petalSet_injective {ν : ℕ} : Function.Injective (petalSet (ν := ν)) := by
  intro K L h
  ext i
  have := congrArg (fun S => (i, (0 : Fin 3)) ∈ S) h
  simpa [petalSet] using this

/-- **Sharp lower bound.** A triangle flower has Q=(ν−1)2^ν+2 (`bouquetQ ν`). -/
theorem Q_triFlower (ν : ℕ) : (triFlower ν).Q = bouquetQ ν := by
  classical
  unfold Q QOn
  rw [Finset.powerset_univ, ← Finset.sum_subset (Finset.subset_univ _)
    (fun S _ hS => wt_triFlower_eq_zero hS),
    Finset.sum_image (fun K _ L _ h => petalSet_injective h)]
  simp only [wt_triFlower_petalSet]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => phi (2 * k)),
    Finset.card_univ, Fintype.card_fin, bouquetQ]
  simp

/-! ### Ladders -/

/-- Ladder with vertices (i,s), rungs inl i=(i,false)–(i,true), rails inr(j,s)=(j,s)–(j+1,s). -/
def ladder (k : ℕ) : Multigraph (Fin (k + 1) × Bool) (Fin (k + 1) ⊕ (Fin k × Bool)) where
  fst e := e.elim (fun i => (i, false)) fun js => (js.1.castSucc, js.2)
  snd e := e.elim (fun i => (i, true)) fun js => (js.1.succ, js.2)

theorem loopless_ladder (k : ℕ) : (ladder k).Loopless := by
  rintro (i | ⟨j, s⟩)
  · simp [ladder]
  · simp only [ladder, Sum.elim_inr, ne_eq, Prod.mk.injEq, and_true]
    exact ne_of_lt Fin.castSucc_lt_succ

theorem cycleRank_ladder (k : ℕ) : (ladder k).cycleRank = k := by
  simp only [cycleRank, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

theorem deg_ladder_le (k : ℕ) (v : Fin (k + 1) × Bool) : (ladder k).deg Finset.univ v ≤ 3 := by
  obtain ⟨i, s⟩ := v
  rw [deg, Fintype.sum_sum_type]
  have hr : ∑ i' : Fin (k + 1), (ladder k).endCount (Sum.inl i') (i, s) = 1 := by
    rw [Finset.sum_eq_single i]
    · cases s <;> simp [endCount, ladder]
    · intro i' _ hi'
      simp [endCount, ladder, hi']
    · intro h; exact absurd (Finset.mem_univ _) h
  have hl : ∑ js : Fin k × Bool, (ladder k).endCount (Sum.inr js) (i, s) ≤ 2 := by
    have : ∀ js : Fin k × Bool, (ladder k).endCount (Sum.inr js) (i, s) =
        (if js = (js.1, s) ∧ js.1.castSucc = i then 1 else 0) +
          (if js = (js.1, s) ∧ js.1.succ = i then 1 else 0) := by
      rintro ⟨j, t⟩
      simp only [endCount, ladder, Sum.elim_inr, Prod.mk.injEq]
      by_cases ht : t = s <;> simp [ht, and_comm]
    simp only [this, Finset.sum_add_distrib]
    have h1 : ∑ js : Fin k × Bool, (if js = (js.1, s) ∧ js.1.castSucc = i then 1 else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      apply Finset.card_le_one.2
      rintro ⟨j, t⟩ hj ⟨j', t'⟩ hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hj hj'
      simp only [Prod.mk.injEq]
      exact ⟨Fin.castSucc_injective _ (hj.2.trans hj'.2.symm), hj.1.trans hj'.1.symm⟩
    have h2 : ∑ js : Fin k × Bool, (if js = (js.1, s) ∧ js.1.succ = i then 1 else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      apply Finset.card_le_one.2
      rintro ⟨j, t⟩ hj ⟨j', t'⟩ hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hj hj'
      simp only [Prod.mk.injEq]
      exact ⟨Fin.succ_injective _ (hj.2.trans hj'.2.symm), hj.1.trans hj'.1.symm⟩
    omega
  omega

theorem adj_symm {V E : Type*} (G : Multigraph V E) {A : Finset E} {a b : V} (h : G.Adj A a b) :
    G.Adj A b a := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

theorem reflTransGen_adj_symm {V E : Type*} (G : Multigraph V E) {A : Finset E} {a b : V}
    (h : Relation.ReflTransGen (G.Adj A) a b) : Relation.ReflTransGen (G.Adj A) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (adj_symm _ hbc)).trans ih

theorem ladder_reach (k : ℕ) :
    ∀ (i : ℕ) (hi : i < k + 1) (s : Bool),
      Relation.ReflTransGen ((ladder k).Adj Finset.univ) (⟨i, hi⟩, s) (0, false) := by
  intro i
  induction i with
  | zero =>
    intro hi s
    cases s
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨Sum.inl 0, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
  | succ i ih =>
    intro hi s
    have hstep : (ladder k).Adj Finset.univ (⟨i + 1, hi⟩, s) (⟨i, by omega⟩, s) :=
      ⟨Sum.inr (⟨i, by omega⟩, s), Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
    exact Relation.ReflTransGen.head hstep (ih (by omega) s)

theorem connected_ladder (k : ℕ) : (ladder k).Connected := by
  refine ⟨⟨(0, false), Finset.mem_univ _⟩, fun e _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
    fun a _ b _ => ?_⟩
  have ha := ladder_reach k a.1.1 a.1.2 a.2
  have hb := ladder_reach k b.1.1 b.1.2 b.2
  exact ha.trans (reflTransGen_adj_symm _ hb)

/-- **Sharp upper bound.** A ladder of cycle rank k has Q=U_k. -/
theorem Q_ladder (k : ℕ) : ((ladder k).Q : ℤ) = U k := by
  have h := Q_eq_U_of_connected_of_core (ladder k) (connected_ladder k) fun v =>
    ((ladder k).deg_mono ((ladder k).core_subset _) v).trans (deg_ladder_le k v)
  rwa [cycleRank_ladder] at h

end Multigraph

end BPFixedPoints
