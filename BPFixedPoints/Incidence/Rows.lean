import BPFixedPoints.Incidence.Betti

/-!
# Betti row range and row zero: numerical parts of `alg:state-cohomology` and `alg:cycle-product`

For nonempty S, |S|+1≤dim ker ∂+v(S)
(`card_add_one_le_finrank_ker_add_card_support`): the restricted incidence image
lies in the coordinate-sum-zero hyperplane of dimension v(S)−1, and extension
by zero embeds its kernel in ker ∂.
For connected ν≥1, contributing states satisfy 0≤|S|−v(S)≤ν−1; hence rows
beyond ν−1 vanish (`betti_eq_zero_of_cycleRank_le`). This is the numerical
shadow of the resolution-length bound.
In row zero, contributing states have degree two at each support vertex and
weight one. `betti_zero_eq_card` counts edge sets of size k with degrees zero
or two, the dimension of the paper's cycle compatibility algebra Tor₀.
If no nonempty Eulerian set exists, Q=1 (`Q_eq_one_of_forest`).
This module treats the numerical statements rather than the incidence algebra,
minimal resolution or Tor product themselves (see `FORMALIZATION.md`).
Loops are allowed and count twice.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- Extension by zero 𝔽₂^S→𝔽₂^E. -/
def extZero (S : Finset E) : ({e // e ∈ S} → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun x e := if h : e ∈ S then x ⟨e, h⟩ else 0
  map_add' x y := by funext e; by_cases h : e ∈ S <;> simp [h]
  map_smul' c x := by funext e; by_cases h : e ∈ S <;> simp [h]

theorem extZero_injective (S : Finset E) : Function.Injective (extZero S) := by
  intro x y h
  funext ⟨e, he⟩
  have := congrFun h e
  simpa [extZero, he] using this

theorem incMap_extZero_of_notMem {S : Finset E} (x : {e // e ∈ S} → ZMod 2) {v : V}
    (hv : v ∉ G.support S) : G.incMap (extZero S x) v = 0 := by
  have hdeg : G.deg S v = 0 := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    omega
  rw [deg_eq_zero_iff] at hdeg
  change ∑ e, extZero S x e * (G.endCount e v : ZMod 2) = 0
  refine Finset.sum_eq_zero fun e _ => ?_
  by_cases he : e ∈ S
  · rw [G.endCount_of_not_incident (hdeg e he)]; simp
  · simp [extZero, he]

/-- **Subgraph cycle-space bound.** For nonempty S, |S|+1≤dim ker ∂+v(S). -/
theorem card_add_one_le_finrank_ker_add_card_support {S : Finset E} (hS : S.Nonempty) :
    S.card + 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) + (G.support S).card := by
  classical
  -- The support is nonempty.
  obtain ⟨e₀, he₀⟩ := hS
  have hsupp : G.fst e₀ ∈ G.support S := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    have : G.endCount e₀ (G.fst e₀) ≥ 1 := by simp [endCount]
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun e => G.endCount e (G.fst e₀))
      (fun _ _ => Nat.zero_le _) he₀)
  have : Nonempty {v // v ∈ G.support S} := ⟨⟨_, hsupp⟩⟩
  set res : (V → ZMod 2) →ₗ[ZMod 2] ({v // v ∈ G.support S} → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) Subtype.val
  set ψ := res ∘ₗ G.incMap ∘ₗ extZero S
  -- The image has coordinate sum zero.
  have hrange : LinearMap.range ψ ≤ LinearMap.ker (sumMap (V := {v // v ∈ G.support S})) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ v : {v // v ∈ G.support S}, G.incMap (extZero S x) v.1 = 0
    have h1 : ∑ v : {v // v ∈ G.support S}, G.incMap (extZero S x) v.1 =
        ∑ v, G.incMap (extZero S x) v := by
      rw [← Finset.sum_subset (Finset.subset_univ (G.support S))
        (fun v _ hv => G.incMap_extZero_of_notMem x hv)]
      exact (Finset.sum_coe_sort (G.support S) _)
    rw [h1]
    have := G.range_incMap_le ⟨extZero S x, rfl⟩
    rw [LinearMap.mem_ker] at this
    exact this
  -- The kernel embeds in ker ∂.
  have hker : (LinearMap.ker ψ).map (extZero S) ≤ LinearMap.ker G.incMap := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
    rw [LinearMap.mem_ker]
    funext v
    by_cases hv : v ∈ G.support S
    · have := congrFun hx ⟨v, hv⟩
      exact this
    · exact G.incMap_extZero_of_notMem x hv
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  have h1 := Submodule.finrank_mono hrange
  rw [finrank_ker_sumMap, Fintype.card_coe] at h1
  have h2 : Module.finrank (ZMod 2) (LinearMap.ker ψ) ≤
      Module.finrank (ZMod 2) (LinearMap.ker G.incMap) := by
    rw [(Submodule.equivMapOfInjective _ (extZero_injective S) _).finrank_eq]
    exact Submodule.finrank_mono hker
  have h3 : 1 ≤ (G.support S).card := Finset.card_pos.2 ⟨_, hsupp⟩
  omega

/-- **Row range.** For connected ν≥1, contributing states satisfy |S|−v(S)≤ν−1. -/
theorem card_sub_card_support_le (hc : G.Connected) (S : Finset E) :
    S.card - (G.support S).card ≤ G.cycleRank - 1 := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simp
  · have := G.card_add_one_le_finrank_ker_add_card_support h
    rw [G.finrank_ker_incMap_of_connected hc] at this
    omega

/-- **The Betti table occupies rows zero through ν−1.** For connected ν≥1, β_{i,k}=0 when i≥ν. -/
theorem betti_eq_zero_of_cycleRank_le (hc : G.Connected) (hν : 1 ≤ G.cycleRank) {i : ℕ}
    (hi : G.cycleRank ≤ i) (k : ℕ) : G.betti i k = 0 := by
  unfold betti
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [Finset.mem_filter] at hS
  have := G.card_sub_card_support_le hc S
  omega

/-- Row-zero states: a contributing S with |S|≤v(S) has degree two at every support vertex. -/
theorem deg_eq_two_of_card_le {S : Finset E} (hS : G.wt phi S ≠ 0)
    (hle : S.card ≤ (G.support S).card) (v : V) : G.deg S v = 0 ∨ G.deg S v = 2 := by
  have hne1 : ∀ w, G.deg S w ≠ 1 := by
    intro w h1
    apply hS
    rw [wt]
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h1]; rfl)
  have h2 : ∀ w ∈ G.support S, 2 ≤ G.deg S w := by
    intro w hw
    have := (Finset.mem_filter.1 hw).2
    have := hne1 w
    omega
  -- Σ_{support}(d−2)=2|S|−2v(S)≤0.
  have hsum : ∑ w ∈ G.support S, G.deg S w = 2 * S.card := by
    rw [← G.sum_deg]
    refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_)
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hw
    omega
  by_contra hv
  push Not at hv
  have hvs : v ∈ G.support S := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h3 : 3 ≤ G.deg S v := by have := h2 v hvs; have := hne1 v; omega
  have : ∑ w ∈ G.support S, 2 < ∑ w ∈ G.support S, G.deg S w :=
    Finset.sum_lt_sum h2 ⟨v, hvs, by omega⟩
  rw [Finset.sum_const, smul_eq_mul, hsum] at this
  omega

/-- An edge set with degrees zero or two has weight one and equally many edges and support vertices. -/
theorem wt_eq_one_of_deg {S : Finset E} (h : ∀ v, G.deg S v = 0 ∨ G.deg S v = 2) :
    G.wt phi S = 1 ∧ S.card = (G.support S).card := by
  constructor
  · rw [wt]
    refine Finset.prod_eq_one fun v _ => ?_
    rcases h v with h0 | h2
    · rw [h0]; rfl
    · rw [h2]; rfl
  · have hsum : ∑ w ∈ G.support S, G.deg S w = 2 * S.card := by
      rw [← G.sum_deg]
      refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_)
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hw
      omega
    have : ∑ w ∈ G.support S, G.deg S w = ∑ w ∈ G.support S, 2 := by
      refine Finset.sum_congr rfl fun w hw => ?_
      have := (Finset.mem_filter.1 hw).2
      rcases h w with h0 | h2 <;> omega
    rw [this, Finset.sum_const, smul_eq_mul] at hsum
    omega

/-- **Row zero (cycle compatibility algebra dimensions).** β_{0,k} counts edge sets of size k with degrees zero or two, equivalently vertex-disjoint cycle unions. -/
theorem betti_zero_eq_card (k : ℕ) :
    G.betti 0 k = (Finset.univ.filter fun S : Finset E =>
      S.card = k ∧ ∀ v, G.deg S v = 0 ∨ G.deg S v = 2).card := by
  classical
  unfold betti
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with h1 h3 h3
  · exact (G.wt_eq_one_of_deg h3.2).1
  · by_contra hw
    exact h3 ⟨h1.1, G.deg_eq_two_of_card_le hw (by omega)⟩
  · exfalso
    exact h1 ⟨h3.1, by have := (G.wt_eq_one_of_deg h3.2).2; omega⟩
  · rfl

/-- **Forests have Q=1.** If there is no nonempty Eulerian set, only the empty state contributes. -/
theorem Q_eq_one_of_forest (hF : ∀ S, G.IsEvenSet S → S = ∅) : G.Q = 1 := by
  classical
  have hr : Module.finrank (ZMod 2) (LinearMap.ker G.incMap) = 0 := by
    have h := G.card_evenSets
    have h1 : (Finset.univ.filter G.IsEvenSet) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hF S, fun h => h ▸ fun v => by simp⟩
    rw [h1, Finset.card_singleton] at h
    have : 2 ^ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) = 2 ^ 0 := by rw [← h]; rfl
    exact Nat.pow_right_injective le_rfl this
  rw [Q, QOn, Finset.powerset_univ, Finset.sum_eq_single (∅ : Finset E)]
  · rw [wt]; simp [phi]
  · intro S _ hS
    by_contra hw
    have h1 := G.card_add_one_le_finrank_ker_add_card_support (Finset.nonempty_iff_ne_empty.2 hS)
    have h2 := G.card_support_le S hw
    omega
  · simp

end Multigraph

end BPFixedPoints
