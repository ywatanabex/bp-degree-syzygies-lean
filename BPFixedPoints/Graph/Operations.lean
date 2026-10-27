import BPFixedPoints.StateSum.Basic

/-!
# Adding leaves and subdividing edges: operations on whole graphs

`Invariance.lean` replaces edge sets within fixed types. Here construct new
graph types to connect Q-invariance with generic BP degree N.
`addLeaf u` adds vertex none and edge none=u–none.
`subdivide e₀` replaces u–v by u–w–v, with w=none, some e₀=u–w, none=w–v.
`Q_addLeaf` and `Q_subdivide` preserve Q. Split S'⊆Option E by
T=S'.eraseNone and whether none∈S'; for each T the two terms sum to its old
weight. Degree-one terms vanish since φ(1)=0 and subdivision degree two has
φ(2)=1. Both operations preserve looplessness (`loopless_addLeaf`, `loopless_subdivide`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- Split a sum over Finset (Option E) into sums over Finset E according to membership of none. -/
theorem sum_finset_option {M : Type*} [AddCommMonoid M] (f : Finset (Option E) → M) :
    ∑ S, f S = ∑ T : Finset E, (f (T.map Function.Embedding.some) + f (Finset.insertNone T)) := by
  classical
  let e : Finset (Option E) ≃ Finset E × Bool :=
    { toFun := fun S => (Finset.eraseNone S, decide (none ∈ S))
      invFun := fun p => if p.2 then Finset.insertNone p.1 else p.1.map Function.Embedding.some
      left_inv := fun S => by
        by_cases h : none ∈ S
        · simp only [h, decide_true, ite_true]
          rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem h]
        · simp only [h, decide_false]
          ext (_ | x) <;> simp [h]
      right_inv := fun p => by
        rcases p with ⟨T, _ | _⟩
        · simp only [Bool.false_eq_true, ite_false, Prod.mk.injEq]
          refine ⟨?_, by simp⟩
          ext x; simp
        · simp }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Fintype.sum_bool]
  simp [e, add_comm]

/-! ### Adding a leaf -/

/-- Graph obtained by attaching the leaf none to vertex u. -/
def addLeaf (u : V) : Multigraph (Option V) (Option E) where
  fst e := e.elim (some u) fun e => some (G.fst e)
  snd e := e.elim none fun e => some (G.snd e)

theorem loopless_addLeaf (hG : G.Loopless) (u : V) : (G.addLeaf u).Loopless := by
  rintro (_ | e)
  · simp [addLeaf]
  · simpa [addLeaf] using hG e

theorem deg_addLeaf_map (u : V) (T : Finset E) (x : V) :
    (G.addLeaf u).deg (T.map Function.Embedding.some) (some x) = G.deg T x := by
  simp [deg, endCount, addLeaf]

theorem deg_addLeaf_map_none (u : V) (T : Finset E) :
    (G.addLeaf u).deg (T.map Function.Embedding.some) none = 0 := by
  simp [deg, endCount, addLeaf]

theorem deg_addLeaf_insertNone (u : V) (T : Finset E) (x : Option V) :
    (G.addLeaf u).deg (Finset.insertNone T) x =
      (G.addLeaf u).deg (T.map Function.Embedding.some) x + (G.addLeaf u).endCount none x := by
  rw [Finset.insertNone, OrderEmbedding.coe_ofMapLEIff, deg, Finset.sum_cons, deg, add_comm]

/-- **Adding a leaf preserves Q.** -/
theorem Q_addLeaf (u : V) : (G.addLeaf u).Q = G.Q := by
  unfold Q QOn
  rw [Finset.powerset_univ, Finset.powerset_univ, sum_finset_option]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h1 : (G.addLeaf u).wt phi (T.map Function.Embedding.some) = G.wt phi T := by
    rw [wt, Fintype.prod_option, deg_addLeaf_map_none, phi_zero, one_mul, wt]
    exact Finset.prod_congr rfl fun x _ => by rw [deg_addLeaf_map]
  have h2 : (G.addLeaf u).wt phi (Finset.insertNone T) = 0 := by
    rw [wt, Fintype.prod_option, deg_addLeaf_insertNone, deg_addLeaf_map_none]
    simp [endCount, addLeaf]
  rw [h1, h2, add_zero]

/-! ### Subdivision -/

/-- Subdivide e₀=u–v into u–w–v, where w=none, some e₀=u–w and none=w–v. -/
def subdivide (e₀ : E) : Multigraph (Option V) (Option E) where
  fst e := e.elim none fun e => some (G.fst e)
  snd e := e.elim (some (G.snd e₀)) fun e => if e = e₀ then none else some (G.snd e)

theorem loopless_subdivide (hG : G.Loopless) (e₀ : E) : (G.subdivide e₀).Loopless := by
  rintro (_ | e)
  · simp [subdivide]
  · by_cases he : e = e₀
    · simp [subdivide, he]
    · simpa [subdivide, he] using hG e

theorem endCount_subdivide_some (e₀ e : E) (x : V) :
    (G.subdivide e₀).endCount (some e) (some x) =
      if e = e₀ then (if G.fst e₀ = x then 1 else 0) else G.endCount e x := by
  by_cases he : e = e₀
  · subst he; simp [endCount, subdivide]
  · simp [endCount, subdivide, he]

theorem endCount_subdivide_none_some (e₀ : E) (x : V) :
    (G.subdivide e₀).endCount none (some x) = if G.snd e₀ = x then 1 else 0 := by
  simp [endCount, subdivide]

theorem endCount_subdivide_some_none (e₀ e : E) :
    (G.subdivide e₀).endCount (some e) none = if e = e₀ then 1 else 0 := by
  by_cases he : e = e₀
  · subst he; simp [endCount, subdivide]
  · simp [endCount, subdivide, he]

theorem deg_subdivide_map (e₀ : E) (T : Finset E) (x : Option V) :
    (G.subdivide e₀).deg (T.map Function.Embedding.some) x =
      ∑ e ∈ T, (G.subdivide e₀).endCount (some e) x := by
  simp [deg]

theorem deg_subdivide_insertNone (e₀ : E) (T : Finset E) (x : Option V) :
    (G.subdivide e₀).deg (Finset.insertNone T) x =
      (G.subdivide e₀).deg (T.map Function.Embedding.some) x +
        (G.subdivide e₀).endCount none x := by
  rw [Finset.insertNone, OrderEmbedding.coe_ofMapLEIff, deg, Finset.sum_cons, deg, add_comm]

theorem deg_subdivide_map_none (e₀ : E) (T : Finset E) :
    (G.subdivide e₀).deg (T.map Function.Embedding.some) none = if e₀ ∈ T then 1 else 0 := by
  rw [deg_subdivide_map]
  simp only [endCount_subdivide_some_none]
  rw [Finset.sum_ite_eq']

theorem deg_subdivide_map_some_of_not_mem (e₀ : E) {T : Finset E} (h : e₀ ∉ T) (x : V) :
    (G.subdivide e₀).deg (T.map Function.Embedding.some) (some x) = G.deg T x := by
  rw [deg_subdivide_map, deg]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [endCount_subdivide_some, ite_eq_right (fun h' : e = e₀ => h (h' ▸ he))]

theorem deg_subdivide_insertNone_some_of_mem (e₀ : E) {T : Finset E} (h : e₀ ∈ T) (x : V) :
    (G.subdivide e₀).deg (Finset.insertNone T) (some x) = G.deg T x := by
  rw [deg_subdivide_insertNone, deg_subdivide_map, endCount_subdivide_none_some, deg,
    ← Finset.add_sum_erase _ _ h, ← Finset.add_sum_erase _ _ h, endCount_subdivide_some,
    ite_eq_left rfl]
  have : ∑ e ∈ T.erase e₀, (G.subdivide e₀).endCount (some e) (some x) =
      ∑ e ∈ T.erase e₀, G.endCount e x := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [endCount_subdivide_some, ite_eq_right (Finset.ne_of_mem_erase he)]
  rw [this, endCount]
  ring

/-- **Subdivision preserves Q.** -/
theorem Q_subdivide (e₀ : E) : (G.subdivide e₀).Q = G.Q := by
  unfold Q QOn
  rw [Finset.powerset_univ, Finset.powerset_univ, sum_finset_option]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : e₀ ∈ T
  · have h1 : (G.subdivide e₀).wt phi (T.map Function.Embedding.some) = 0 := by
      rw [wt, Fintype.prod_option, deg_subdivide_map_none, ite_eq_left h]
      simp
    have h2 : (G.subdivide e₀).wt phi (Finset.insertNone T) = G.wt phi T := by
      rw [wt, Fintype.prod_option, deg_subdivide_insertNone, deg_subdivide_map_none, ite_eq_left h,
        show (G.subdivide e₀).endCount none none = 1 by simp [endCount, subdivide], wt]
      simp only [show 1 + 1 = 2 from rfl, show phi 2 = 1 from rfl, one_mul]
      exact Finset.prod_congr rfl fun x _ => by rw [deg_subdivide_insertNone_some_of_mem _ _ h]
    rw [h1, h2, zero_add]
  · have h1 : (G.subdivide e₀).wt phi (T.map Function.Embedding.some) = G.wt phi T := by
      rw [wt, Fintype.prod_option, deg_subdivide_map_none, ite_eq_right h, phi_zero, one_mul, wt]
      exact Finset.prod_congr rfl fun x _ => by rw [deg_subdivide_map_some_of_not_mem _ _ h]
    have h2 : (G.subdivide e₀).wt phi (Finset.insertNone T) = 0 := by
      rw [wt, Fintype.prod_option, deg_subdivide_insertNone, deg_subdivide_map_none, ite_eq_right h,
        show (G.subdivide e₀).endCount none none = 1 by simp [endCount, subdivide]]
      simp
    rw [h1, h2, add_zero]

end Multigraph

end BPFixedPoints
