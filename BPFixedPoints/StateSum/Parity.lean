import BPFixedPoints.StateSum.ConnectedBound

/-!
# Parity of Q: Q is even for ν≥1

φ(d) is odd for even d and even for odd d, so modulo two Q counts even-degree
edge sets (`Q_cast_zmod_two`). They correspond to the kernel of ∂:𝔽₂^E→𝔽₂^V
and number 2^{dim ker ∂}. The image has coordinate sum zero, so for nonempty V,
dim ker ∂≥|E|−|V|+1. Therefore Q is even if |V|≤|E| (`even_Q_of_card_le`),
and in particular for connected ν≥1 (`even_Q_of_connected`). Loops are allowed
and counted twice.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- Edge sets with even degree at every vertex: elements of the 𝔽₂ cycle space. -/
def IsEvenSet (S : Finset E) : Prop := ∀ v, Even (G.deg S v)

instance : DecidablePred G.IsEvenSet := fun S => by unfold IsEvenSet; infer_instance

theorem phi_cast_zmod_two (d : ℕ) : (phi d : ZMod 2) = if Even d then 1 else 0 := by
  rcases d with _ | k
  · simp
  · rw [phi_succ]
    by_cases hk : Even k
    · rw [ite_eq_right (Nat.even_add_one.not.2 (not_not.2 hk)), ZMod.natCast_eq_zero_iff_even.2 hk]
    · rw [ite_eq_left (Nat.even_add_one.2 hk), ← ZMod.natCast_mod,
        Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hk), Nat.cast_one]

/-- **Q modulo two.** Q(G)≡#{edge sets with even degree at every vertex}. -/
theorem Q_cast_zmod_two : (G.Q : ZMod 2) = ((Finset.univ.filter G.IsEvenSet).card : ZMod 2) := by
  rw [Q, QOn, Finset.powerset_univ, Nat.cast_sum, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [wt, Nat.cast_prod]
  simp only [phi_cast_zmod_two]
  rw [Finset.prod_boole]
  simp [IsEvenSet]

/-! ### Incidence map over 𝔽₂ -/

/-- Incidence map ∂:𝔽₂^E→𝔽₂^V: (∂x)_v=Σ_e x_e times the number of endpoints of e equal to v. -/
def incMap : (E → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun x v := ∑ e, x e * (G.endCount e v : ZMod 2)
  map_add' x y := by
    funext v
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext v
    simp [Finset.mul_sum, mul_assoc]

/-- Coordinate sum 𝔽₂^V→𝔽₂. -/
def sumMap : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun y := ∑ v, y v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem sum_endCount (e : E) : ∑ v, G.endCount e v = 2 := by
  simp [endCount, Finset.sum_add_distrib]

theorem range_incMap_le : LinearMap.range G.incMap ≤ LinearMap.ker (sumMap (V := V)) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change ∑ v, ∑ e, x e * (G.endCount e v : ZMod 2) = 0
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.mul_sum, ← Nat.cast_sum, G.sum_endCount]
  have : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [this, mul_zero]

theorem finrank_ker_sumMap [Nonempty V] :
    Module.finrank (ZMod 2) (LinearMap.ker (sumMap (V := V))) = Fintype.card V - 1 := by
  have hsurj : LinearMap.range (sumMap (V := V)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    obtain ⟨v₀⟩ := ‹Nonempty V›
    refine ⟨Pi.single v₀ a, ?_⟩
    change ∑ v, Pi.single v₀ a v = a
    simp
  have h := LinearMap.finrank_range_add_finrank_ker (sumMap (V := V))
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- Identify Finset E≃𝔽₂^E by indicator functions. -/
def finsetEquiv : Finset E ≃ (E → ZMod 2) where
  toFun S e := if e ∈ S then 1 else 0
  invFun x := Finset.univ.filter fun e => x e = 1
  left_inv S := by
    ext e
    by_cases he : e ∈ S <;> simp [he]
  right_inv x := by
    funext e
    have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h2 (x e) with h | h <;> simp [h]

theorem incMap_finsetEquiv (S : Finset E) (v : V) :
    G.incMap (finsetEquiv S) v = (G.deg S v : ZMod 2) := by
  change ∑ e, (if e ∈ S then (1 : ZMod 2) else 0) * (G.endCount e v : ZMod 2) = _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, deg, Nat.cast_sum]

theorem isEvenSet_iff_mem_ker (S : Finset E) :
    G.IsEvenSet S ↔ finsetEquiv S ∈ LinearMap.ker G.incMap := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [incMap_finsetEquiv, Pi.zero_apply, ZMod.natCast_eq_zero_iff_even, IsEvenSet]

/-- There are 2^{dim ker ∂} even-degree edge sets. -/
theorem card_evenSets :
    (Finset.univ.filter G.IsEvenSet).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) := by
  classical
  rw [← Fintype.card_subtype,
    Fintype.card_congr (finsetEquiv.subtypeEquiv fun S => G.isEvenSet_iff_mem_ker S)]
  change Fintype.card (LinearMap.ker G.incMap) = _
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- If V is nonempty, dim ker ∂≥|E|−|V|+1. -/
theorem card_le_finrank_ker [Nonempty V] :
    Fintype.card E + 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) + Fintype.card V := by
  have h := LinearMap.finrank_range_add_finrank_ker G.incMap
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hr := Submodule.finrank_mono G.range_incMap_le
  rw [finrank_ker_sumMap] at hr
  have hV : 0 < Fintype.card V := Fintype.card_pos
  omega

/-- **If |V|≤|E| and V is nonempty, Q(G) is even.** -/
theorem even_Q_of_card_le [Nonempty V] (h : Fintype.card V ≤ Fintype.card E) : Even G.Q := by
  have hk := G.card_le_finrank_ker
  have hpos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) := by omega
  rw [← ZMod.natCast_eq_zero_iff_even, Q_cast_zmod_two, G.card_evenSets,
    ZMod.natCast_eq_zero_iff_even]
  exact Nat.even_pow.2 ⟨even_two, by omega⟩

/-- **For a connected graph with ν≥1, Q(G) is even.** -/
theorem even_Q_of_connected (hc : G.Connected) (hν : 1 ≤ G.cycleRank) : Even G.Q := by
  obtain ⟨v, _⟩ := hc.1
  have : Nonempty V := ⟨v⟩
  apply G.even_Q_of_card_le
  have := G.card_vertex_le_of_connected hc
  unfold cycleRank at hν
  omega

/-! ### Connected graphs: dim ker ∂=ν -/

theorem incMap_single (e : E) :
    G.incMap (Pi.single e 1) = Pi.single (G.fst e) 1 + Pi.single (G.snd e) 1 := by
  funext v
  change ∑ e', (Pi.single e (1 : ZMod 2) : E → ZMod 2) e' * (G.endCount e' v : ZMod 2) = _
  rw [Finset.sum_eq_single e (fun e' _ he' => by simp [he'])
    (fun h => absurd (Finset.mem_univ e) h)]
  simp only [Pi.single_eq_same, one_mul, endCount, Nat.cast_add, Pi.add_apply, Pi.single_apply,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, @eq_comm _ v (G.fst e), @eq_comm _ v (G.snd e)]

/-- In a connected graph, e_a+e_b belongs to the image of ∂. -/
theorem single_add_single_mem_range {a b : V}
    (h : Relation.ReflTransGen (G.Adj Finset.univ) a b) :
    Pi.single a 1 + Pi.single b 1 ∈ LinearMap.range G.incMap := by
  induction h with
  | refl =>
    have : (Pi.single a 1 + Pi.single a 1 : V → ZMod 2) = 0 := by
      funext v; simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [this]; exact Submodule.zero_mem _
  | @tail c b _ hcb ih =>
    obtain ⟨e, -, he⟩ := hcb
    have hedge : Pi.single c 1 + Pi.single b 1 ∈ LinearMap.range G.incMap := by
      refine ⟨Pi.single e 1, ?_⟩
      rw [incMap_single]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, add_comm]
    have e2 : (Pi.single a 1 + Pi.single b 1 : V → ZMod 2) =
        (Pi.single a 1 + Pi.single c 1) + (Pi.single c 1 + Pi.single b 1) := by
      funext v
      simp only [Pi.add_apply]
      have : (Pi.single c (1 : ZMod 2) : V → ZMod 2) v + (Pi.single c 1 : V → ZMod 2) v = 0 :=
        CharTwo.add_self_eq_zero _
      linear_combination -this
    rw [e2]
    exact Submodule.add_mem _ ih hedge

/-- For a connected graph, the image of ∂ is the entire coordinate-sum-zero hyperplane. -/
theorem range_incMap_eq_of_connected (hc : G.Connected) :
    LinearMap.range G.incMap = LinearMap.ker (sumMap (V := V)) := by
  refine le_antisymm G.range_incMap_le fun y hy => ?_
  obtain ⟨v₀, -⟩ := hc.1
  have hsum : ∑ v, y v = 0 := hy
  have hy' : y = ∑ v, y v • (Pi.single v 1 + Pi.single v₀ 1) := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    have h1 : ∑ v, y v * (Pi.single v (1 : ZMod 2) : V → ZMod 2) w = y w := by
      rw [Finset.sum_eq_single w (fun v _ hv => by simp [Ne.symm hv])
        (fun h => absurd (Finset.mem_univ w) h)]
      simp
    rw [h1, ← Finset.sum_mul, hsum, zero_mul, add_zero]
  rw [hy']
  refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
  exact G.single_add_single_mem_range (hc.2.2 v (Finset.mem_univ _) v₀ (Finset.mem_univ _))

/-- **Dimension of the connected cycle space.** dim ker ∂=ν=|E|−|V|+1. -/
theorem finrank_ker_incMap_of_connected (hc : G.Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker G.incMap) = G.cycleRank := by
  obtain ⟨v₀, -⟩ := hc.1
  have : Nonempty V := ⟨v₀⟩
  have h := LinearMap.finrank_range_add_finrank_ker G.incMap
  rw [Module.finrank_fintype_fun_eq_card, G.range_incMap_eq_of_connected hc,
    finrank_ker_sumMap] at h
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hle := G.card_vertex_le_of_connected hc
  unfold cycleRank
  omega

/-- A connected graph has exactly 2^ν even-degree edge sets. -/
theorem card_evenSets_of_connected (hc : G.Connected) :
    (Finset.univ.filter G.IsEvenSet).card = 2 ^ G.cycleRank := by
  rw [card_evenSets, finrank_ker_incMap_of_connected G hc]

/-- **For a connected graph, Q is odd iff it is a tree (ν=0).** -/
theorem odd_Q_iff_of_connected (hc : G.Connected) : Odd G.Q ↔ G.cycleRank = 0 := by
  constructor
  · intro hodd
    by_contra hν
    exact (Nat.not_even_iff_odd.2 hodd) (G.even_Q_of_connected hc (Nat.one_le_iff_ne_zero.2 hν))
  · intro hν
    rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, Q_cast_zmod_two,
      card_evenSets_of_connected G hc, hν]
    decide

end Multigraph

end BPFixedPoints
