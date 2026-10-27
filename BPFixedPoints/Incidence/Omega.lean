import BPFixedPoints.Incidence.StateCohomology

/-!
# ω_G and the tree-component correction ω̃_G=ω_G/(1−t)^τ

Treat the paper's normalization ω_G(t)=(1−t)^{n−m}θ_G(t,2i) for general
multigraphs, including tree components (`alg:omega-definition`, `alg:omega-reduced`).
`thetaTwoI_eq_prod_comp` factors θ over components. Tree components have θ=1
(`thetaTwoI_compGraph_of_isTreeComp`), as do forests (`thetaTwoI_eq_one_of_forest`).
For a cyclic component C, θ_C=(1−t)^{m_C−n_C}ω_C (`compOmega`, `exists_omega`).
Define ω̃_G as the product of cyclic-component ω_C (`omegaTilde`) and
ω_G=(1−t)^τ ω̃_G (`omega`). Then θ_G=(1−t)^ρ ω̃_G (`thetaTwoI_eq_omegaTilde`)
and (1−t)^n θ_G=(1−t)^m ω_G (`one_sub_pow_mul_thetaTwoI`).
For connected cyclic graphs this agrees with the quotient `exists_omega`.
For trees that natural-exponent quotient is one, while the paper's `omega` is 1−X.
Realization by Hilbert series and Artin sections (`alg:hilbert`) is not formalized here.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open Polynomial

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-! ### Forests have θ=1 -/

/-- **If no nonempty Eulerian edge set exists, θ_G(t,2i)=1.** Only the empty state contributes. -/
theorem thetaTwoI_eq_one_of_forest (hF : ∀ S, G.IsEvenSet S → S = ∅) : G.thetaTwoI = 1 := by
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
  rw [thetaTwoI, Finset.sum_eq_single (∅ : Finset E)]
  · simp
  · intro S _ hS
    rw [G.prod_one_sub_deg S]
    by_cases hw : G.wt phi S = 0
    · simp [hw]
    · exfalso
      have h1 := G.card_add_one_le_finrank_ker_add_card_support
        (Finset.nonempty_iff_ne_empty.2 hS)
      have h2 := G.card_support_le S hw
      omega
  · simp

/-! ### Component decomposition -/

/-- Bijection between edge sets and families of componentwise edge sets. -/
noncomputable def compSplit :
    Finset E ≃ ((K : G.Comp) → Finset {e // e ∈ G.compEdges K}) where
  toFun S K := S.subtype (· ∈ G.compEdges K)
  invFun x := Finset.univ.biUnion fun K => (x K).map (Function.Embedding.subtype _)
  left_inv S := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_subtype, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨K, ⟨e', he', rfl⟩⟩; exact he'
    · intro he
      exact ⟨G.compOf (G.fst e), ⟨e, mem_compEdges.2 rfl⟩, he, rfl⟩
  right_inv x := by
    funext K
    ext ⟨e, he⟩
    simp only [Finset.mem_subtype, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨L, ⟨e', he', rfl⟩⟩
      have : L = K := by
        rw [← mem_compEdges.1 e'.2, ← mem_compEdges.1 he]
      subst this
      exact he'
    · intro h
      exact ⟨K, ⟨⟨e, he⟩, h, rfl⟩⟩

theorem map_compSplit (S : Finset E) (K : G.Comp) :
    (G.compSplit S K).map (Function.Embedding.subtype _) = G.compPart S K := by
  ext e
  simp [compSplit, compPart]

theorem card_compSplit (S : Finset E) (K : G.Comp) :
    (G.compSplit S K).card = (G.compPart S K).card := by
  rw [← map_compSplit, Finset.card_map]

theorem compGraph_deg_compSplit (S : Finset E) (K : G.Comp) (v : {v // v ∈ G.compVerts K}) :
    (G.compGraph K).deg (G.compSplit S K) v = G.deg S v.1 := by
  rw [compGraph_deg, map_compSplit, deg_compPart, ite_cond_eq_true _ _ (eq_true (mem_compVerts.1 v.2))]

/-- Split a product over vertices into products over components. -/
theorem prod_eq_prod_comp {M : Type*} [CommMonoid M] (f : V → M) :
    ∏ v, f v = ∏ K : G.Comp, ∏ v : {v // v ∈ G.compVerts K}, f v.1 := by
  rw [← Finset.prod_fiberwise Finset.univ G.compOf f]
  refine Finset.prod_congr rfl fun K _ => ?_
  rw [← Finset.prod_coe_sort]
  rfl

/-- **θ_G(t,2i) is multiplicative over connected components.** -/
theorem thetaTwoI_eq_prod_comp :
    G.thetaTwoI = ∏ K : G.Comp, (G.compGraph K).thetaTwoI := by
  simp only [thetaTwoI]
  rw [Finset.prod_univ_sum]
  rw [← Fintype.sum_equiv G.compSplit.symm _ _ (fun _ => rfl)]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  set S := G.compSplit.symm x with hS
  have hx : x = G.compSplit S := by rw [hS, Equiv.apply_symm_apply]
  rw [hx]
  rw [Finset.prod_mul_distrib, ← map_prod]
  congr 1
  · rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [G.card_eq_sum_compPart S]
    exact Finset.sum_congr rfl fun K _ => (G.card_compSplit S K).symm
  · congr 1
    rw [G.prod_eq_prod_comp]
    refine Finset.prod_congr rfl fun K _ => Finset.prod_congr rfl fun v _ => ?_
    rw [compGraph_deg_compSplit]

/-! ### Tree and cyclic components -/

theorem cycleRank_compGraph (K : G.Comp) :
    (G.compGraph K).cycleRank = (G.compEdges K).card + 1 - (G.compVerts K).card := by
  simp [cycleRank, Fintype.card_coe]

/-- A tree component has θ_T(t,2i)=1. -/
theorem thetaTwoI_compGraph_of_isTreeComp {K : G.Comp} (hK : G.IsTreeComp K) :
    (G.compGraph K).thetaTwoI = 1 := by
  refine (G.compGraph K).thetaTwoI_eq_one_of_forest fun S hS => ?_
  have hc := G.compGraph_connected K
  have h := (G.compGraph K).card_evenSets_of_connected hc
  rw [cycleRank_compGraph] at h
  unfold IsTreeComp at hK
  rw [show (G.compEdges K).card + 1 - (G.compVerts K).card = 0 by omega, pow_zero] at h
  obtain ⟨T, hT⟩ := Finset.card_eq_one.1 h
  have h1 : S ∈ Finset.univ.filter (G.compGraph K).IsEvenSet := by simp [hS]
  have h2 : (∅ : Finset {e // e ∈ G.compEdges K}) ∈
      Finset.univ.filter (G.compGraph K).IsEvenSet := by simp [IsEvenSet]
  rw [hT, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

/-- Quotient by each component's natural exponent ν(C)−1: the paper's ω_C for cyclic components and one for tree components. -/
noncomputable def compOmega (K : G.Comp) : ℤ[X] :=
  Classical.choose ((G.compGraph K).exists_omega (G.compGraph_connected K))

theorem thetaTwoI_compGraph (K : G.Comp) :
    (G.compGraph K).thetaTwoI =
      (1 - X) ^ ((G.compGraph K).cycleRank - 1) * G.compOmega K :=
  Classical.choose_spec ((G.compGraph K).exists_omega (G.compGraph_connected K))

/-- ω̃_G=∏_{cyclic components C}ω_C, omitting tree components. -/
noncomputable def omegaTilde : ℤ[X] :=
  ∏ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K), G.compOmega K

/-- ω_G=(1−t)^τ ω̃_G, the paper's normalization (1−t)^{n−m}θ_G(t,2i). -/
noncomputable def omega : ℤ[X] := (1 - X) ^ G.tau * G.omegaTilde

/-- Natural-number form of ρ=Σ_{cyclic components}(m_K−n_K). -/
theorem rho_eq_sum_nat :
    G.rho = ∑ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K),
      ((G.compEdges K).card - (G.compVerts K).card) := by
  have h := G.rho_eq_sum
  have hcast : ((∑ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K),
      ((G.compEdges K).card - (G.compVerts K).card) : ℕ) : ℤ) =
      ∑ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K),
        ((G.compEdges K).card - (G.compVerts K).card : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun K hK => ?_
    have h1 := (Finset.mem_filter.1 hK).2
    have h2 := G.card_compVerts_le K
    unfold IsTreeComp at h1
    rw [Nat.cast_sub (by omega)]
  exact_mod_cast h.trans hcast.symm

/-- **θ_G(t,2i) = (1−t)^ρ ω̃_G。** -/
theorem thetaTwoI_eq_omegaTilde : G.thetaTwoI = (1 - X) ^ G.rho * G.omegaTilde := by
  rw [thetaTwoI_eq_prod_comp, ← Finset.prod_filter_mul_prod_filter_not Finset.univ G.IsTreeComp]
  rw [Finset.prod_eq_one fun K hK =>
    G.thetaTwoI_compGraph_of_isTreeComp (Finset.mem_filter.1 hK).2, one_mul]
  rw [omegaTilde, rho_eq_sum_nat, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun K _ => ?_
  rw [thetaTwoI_compGraph, cycleRank_compGraph]
  congr 2
  omega

/-- **ω_G = (1−t)^{n−m} θ_G(t,2i)**：(1−t)^n θ_G = (1−t)^m ω_G。 -/
theorem one_sub_pow_mul_thetaTwoI :
    (1 - X : ℤ[X]) ^ Fintype.card V * G.thetaTwoI = (1 - X) ^ Fintype.card E * G.omega := by
  rw [thetaTwoI_eq_omegaTilde, omega, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add,
    add_comm (Fintype.card V), G.rho_add_card]

/-- ω̃ is uniquely determined by θ=(1−t)^ρ ω̃. -/
theorem omegaTilde_unique {ω : ℤ[X]} (h : G.thetaTwoI = (1 - X) ^ G.rho * ω) :
    ω = G.omegaTilde :=
  G.omega_unique h G.thetaTwoI_eq_omegaTilde

/-- If there are no tree components, ω̃=ω. -/
theorem omega_eq_omegaTilde_of_tau_eq_zero (h : G.tau = 0) : G.omega = G.omegaTilde := by
  rw [omega, h, pow_zero, one_mul]

end Multigraph

end BPFixedPoints
