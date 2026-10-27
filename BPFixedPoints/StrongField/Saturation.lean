import BPFixedPoints.StrongField.ChartSolution
import BPFixedPoints.StrongField.Density
import BPFixedPoints.Degree.Limit.VertexRoots

/-!
# Complete strong-field complex count (`thm:real` (i), `sf:exhaustion`)

For fixed a_e≠0,a_e²≠1, some ε>0 gives exactly Q(G) admissible complex BP
solutions when all inverse fields p_i=b_i⁻¹ have norm strictly between zero
and ε (`card_strong_field_eq_Q`).
For the lower bound (`sf:normal-form`), evaluate the state/root branches
`exists_chart_branch` at π^S with π_i^{r_i}=(−1)^{k_i}p_i. They are admissible
by `isAdmissibleSolution_chartBP`. As p→0, chart coordinates approach (q⁰,ω)
and messages approach zero on S and q⁰≠0 off S, distinguishing all indices.
There are Σ_S∏_i r_i=Q indices (`card_stIdx`).
For the upper bound (`sf:degree-saturation`), generic auxiliary parameters
with g(s,β)≠0 have exactly Q solutions (`exists_generic_aux_degree_eq_Q`).
The Q distinct branches near (s⁰,β⁰), together with generic-point density
`exists_aux_near_generic`, exclude extra solutions (`card_eq_of_saturation`).
Rational auxiliary coordinates and the one-variable identity theorem replace
the paper's density argument via the generic étale locus of an irreducible total space.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

section Saturation

/-- **Abstract saturation lemma.** Generic parameters Gd have exactly Q solutions. If Q branches are continuous near p₀ and distinct there, and every p₀-solution is approximated by generic solutions, then p₀ also has exactly Q solutions. -/
theorem card_eq_of_saturation {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    (Sol : P → Set X) (Gd : Set P) (Q : ℕ) (hGd : ∀ p ∈ Gd, Nat.card (Sol p) = Q ∧ (Sol p).Finite)
    (p₀ : P) {ι : Type*} [Finite ι] (hι : Nat.card ι = Q) (σ : ι → P → X)
    (hσ : ∀ᶠ p in 𝓝 p₀, ∀ k, σ k p ∈ Sol p) (hσc : ∀ k, ContinuousAt (σ k) p₀)
    (hσinj : Function.Injective fun k => σ k p₀)
    (hdense : ∀ z ∈ Sol p₀, ∀ U ∈ 𝓝 p₀, ∀ W ∈ 𝓝 z, ∃ p ∈ U, p ∈ Gd ∧ ∃ z' ∈ W, z' ∈ Sol p) :
    Nat.card (Sol p₀) = Q := by
  classical
  have hrange : Sol p₀ = Set.range fun k => σ k p₀ := by
    apply Set.Subset.antisymm
    · intro z hz
      by_contra hzr
      have hfin : (insert z (Set.range fun k => σ k p₀)).Finite :=
        (Set.finite_range _).insert z
      obtain ⟨O, hO, hdisj⟩ := hfin.t2_separation
      have hU : ∀ᶠ p in 𝓝 p₀, (∀ k, σ k p ∈ Sol p) ∧ ∀ k, σ k p ∈ O (σ k p₀) := by
        refine hσ.and (Filter.eventually_all.2 fun k => ?_)
        exact (hσc k).eventually ((hO _).2.mem_nhds (hO _).1)
      obtain ⟨p, hp, hpG, z', hz'O, hz'⟩ := hdense z hz _ hU _ ((hO z).2.mem_nhds (hO z).1)
      obtain ⟨hcard, hfinp⟩ := hGd p hpG
      have : Finite (Sol p) := hfinp.to_subtype
      -- Injection from Option ι into Sol p.
      let g : Option ι → Sol p := fun o => match o with
        | none => ⟨z', hz'⟩
        | some k => ⟨σ k p, hp.1 k⟩
      have hg : Function.Injective g := by
        have hmem : ∀ k, σ k p₀ ∈ insert z (Set.range fun k => σ k p₀) := fun k =>
          Set.mem_insert_of_mem _ ⟨k, rfl⟩
        have hz_mem : z ∈ insert z (Set.range fun k => σ k p₀) := Set.mem_insert _ _
        have hne : ∀ k, z ≠ σ k p₀ := fun k h => hzr ⟨k, h.symm⟩
        rintro (_ | k) (_ | k') h
        · rfl
        · exfalso
          have h1 : z' = σ k' p := congrArg Subtype.val h
          have := Set.disjoint_left.1 (hdisj hz_mem (hmem k') (hne k')) hz'O
          exact this (h1 ▸ hp.2 k')
        · exfalso
          have h1 : σ k p = z' := congrArg Subtype.val h
          have := Set.disjoint_left.1 (hdisj hz_mem (hmem k) (hne k)) hz'O
          exact this (h1 ▸ hp.2 k)
        · have h1 : σ k p = σ k' p := congrArg Subtype.val h
          by_contra hkk
          have hkk' : k ≠ k' := fun h => hkk (congrArg some h)
          have hne' : σ k p₀ ≠ σ k' p₀ := fun h => hkk' (hσinj h)
          have := Set.disjoint_left.1 (hdisj (hmem k) (hmem k') hne') (hp.2 k)
          exact this (h1 ▸ hp.2 k')
      have hle := Nat.card_le_card_of_injective g hg
      have _ : Fintype ι := Fintype.ofFinite ι
      rw [Nat.card_eq_fintype_card (α := Option ι), Fintype.card_option,
        ← Nat.card_eq_fintype_card, hι, hcard] at hle
      omega
    · rintro _ ⟨k, rfl⟩
      exact hσ.self_of_nhds k
  rw [hrange, Nat.card_range_of_injective hσinj, hι]

end Saturation

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Roots

/-- If c≠0 and r>0, the equation ω^r=c has exactly r roots. -/
theorem card_pow_eq (r : ℕ) (hr : 0 < r) (c : ℂ) (hc : c ≠ 0) :
    Nat.card {ω : ℂ // ω ^ r = c} = r := by
  classical
  have h := card_roots_X_pow_sub_C ℂ r hr c hc
  calc Nat.card {ω : ℂ // ω ^ r = c}
      = Nat.card ((Polynomial.X ^ r - Polynomial.C c : Polynomial ℂ).roots.toFinset) := by
        apply Nat.card_congr
        refine Equiv.subtypeEquivRight fun ω => ?_
        rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hr c)]
        simp [sub_eq_zero]
    _ = r := by rw [Nat.card_eq_finsetCard, h]

theorem rS_pos (S : Finset E) (hS : IsState G S) (i : V) : 0 < G.rS S i := by
  have := hS i
  unfold rS; split_ifs <;> omega

theorem rS_eq_phi (S : Finset E) (hS : IsState G S) (i : V) : G.rS S i = phi (G.deg S i) := by
  have := hS i
  unfold rS
  split_ifs with h
  · rw [h]; rfl
  · rw [phi_of_pos (Nat.pos_of_ne_zero h)]

variable (a : E → ℂ)

/-- Type of root tuples. -/
def RootSet (S : Finset E) := {ω : V → ℂ // ∀ i, ω i ^ G.rS S i = G.C0 S a i}

/-- Index of a state and a root tuple. -/
def StIdx := Σ S : {S : Finset E // IsState G S}, G.RootSet a S.1

theorem card_rootSet (ha : ∀ e, a e ≠ 0) (S : Finset E) (hS : IsState G S) :
    Nat.card (G.RootSet a S) = ∏ i, G.rS S i := by
  unfold RootSet
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (x : ℂ) => x ^ G.rS S i = G.C0 S a i)),
    Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ =>
    card_pow_eq _ (G.rS_pos S hS i) _ (C0_ne_zero ha i)

theorem finite_rootSet (ha : ∀ e, a e ≠ 0) (S : {S : Finset E // IsState G S}) :
    Finite (G.RootSet a S.1) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_rootSet G a ha S.1 S.2]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (G.rS_pos S.1 S.2 i).ne')

/-- **There are Q indices.** Σ_{states S}∏_i r_i=Σ_S∏_iφ(d_S(i))=Q. -/
theorem card_stIdx (ha : ∀ e, a e ≠ 0) : Nat.card (G.StIdx a) = G.Q := by
  classical
  have : ∀ S : {S : Finset E // IsState G S}, Finite (G.RootSet a S.1) :=
    fun S => G.finite_rootSet a ha S
  unfold StIdx
  rw [Nat.card_sigma, Q, QOn, Finset.powerset_univ]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun S => IsState G S)) (by simp)
    (fun S => Nat.card (G.RootSet a S))]
  · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => IsState G S) (G.wt phi)]
    have h0 : ∑ S ∈ Finset.univ.filter (fun S => ¬ IsState G S), G.wt phi S = 0 := by
      refine Finset.sum_eq_zero fun S hS => ?_
      have hS' := (Finset.mem_filter.1 hS).2
      simp only [IsState, not_forall, not_not] at hS'
      obtain ⟨i, hi⟩ := hS'
      rw [wt]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS' := (Finset.mem_filter.1 hS).2
    rw [card_rootSet G a ha S hS', wt]
    exact Finset.prod_congr rfl fun i _ => G.rS_eq_phi S hS' i

end Roots

end Multigraph

end BPFixedPoints
