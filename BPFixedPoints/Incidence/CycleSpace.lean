import BPFixedPoints.Incidence.Rows

/-!
# Binary cycle space and components for arbitrary graphs

Define n=|V|, m=|E|, c=c(G), including isolated vertices, and ν=m−n+c as in
`alg:edge-bundles` at the start of §3. Prove that the binary cycle space
H₁(G;𝔽₂), equivalently even-degree Eulerian edge sets, has size 2^ν even for
disconnected multigraphs. `StateSum/Parity.lean` treats only connected graphs.
`compSetoid A` is reachability via A; `numComp A` counts the components of
(V,A), and `numComponents=numComp univ` is c(G).
`range_incMap_eq_ker_compSum` identifies the image of ∂ with vectors summing
to zero on each component, giving dim ker ∂+n=m+c (`finrank_ker_incMap_add_card`).
Define ν=m+c−n and prove `card_evenSets_eq_two_pow_nu`; connected ν equals
`cycleRank` (`nu_eq_cycleRank_of_connected`). `edgeRestrict A` retains all
vertices; `card_evenSubsets` counts the cycle space on A by 2^{dim ker ∂_A}
and its dimension is monotone in A.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-! ### Reachability and components -/

theorem adj_comm {A : Finset E} {a b : V} (h : G.Adj A a b) : G.Adj A b a := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

/-- Reachability using only edges in A. -/
def Reach (A : Finset E) (a b : V) : Prop := Relation.ReflTransGen (G.Adj A) a b

theorem reach_symm {A : Finset E} {a b : V} (h : G.Reach A a b) : G.Reach A b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (G.adj_comm hbc) ih

theorem reach_of_adj {A : Finset E} {a b : V} (h : G.Adj A a b) : G.Reach A a b :=
  Relation.ReflTransGen.single h

/-- The endpoints of an edge are reachable in any edge set containing it. -/
theorem reach_fst_snd {A : Finset E} {e : E} (he : e ∈ A) : G.Reach A (G.fst e) (G.snd e) :=
  G.reach_of_adj ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- Component equivalence for edge set A; each isolated vertex is its own component. -/
def compSetoid (A : Finset E) : Setoid V where
  r := G.Reach A
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl, fun h => G.reach_symm h,
    fun h₁ h₂ => Relation.ReflTransGen.trans h₁ h₂⟩

/-- Number of components of the spanning subgraph (V,A), including isolated vertices. -/
noncomputable def numComp (A : Finset E) : ℕ := Nat.card (Quotient (G.compSetoid A))

/-- c(G): number of connected components, including isolated vertices. -/
noncomputable def numComponents : ℕ := G.numComp Finset.univ

/-! ### Component sums and the image of ∂ -/

/-- Componentwise coordinate sum 𝔽₂^V→𝔽₂^{components}. -/
noncomputable def compSum (A : Finset E) :
    (V → ZMod 2) →ₗ[ZMod 2] (Quotient (G.compSetoid A) → ZMod 2) := by
  classical
  exact
    { toFun := fun x K => ∑ v, if Quotient.mk (G.compSetoid A) v = K then x v else 0
      map_add' := fun x y => by
        funext K
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      map_smul' := fun c x => by
        funext K
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp }

theorem compSum_apply [DecidableEq (Quotient (G.compSetoid Finset.univ))]
    (x : V → ZMod 2) (K : Quotient (G.compSetoid Finset.univ)) :
    G.compSum Finset.univ x K =
      ∑ v, if Quotient.mk (G.compSetoid Finset.univ) v = K then x v else 0 := by
  unfold compSum
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1

theorem compSum_surjective : Function.Surjective (G.compSum Finset.univ) := by
  classical
  intro y
  refine ⟨fun v => if v = (Quotient.mk (G.compSetoid Finset.univ) v).out then
    y (Quotient.mk (G.compSetoid Finset.univ) v) else 0, ?_⟩
  funext K
  rw [compSum_apply]
  rw [Finset.sum_eq_single K.out]
  · rw [Quotient.out_eq]; simp
  · intro v _ hv
    split_ifs with h1 h2
    · exfalso; apply hv; rw [h2, h1]
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- c(G) ≤ n。 -/
theorem numComponents_le : G.numComponents ≤ Fintype.card V := by
  classical
  unfold numComponents numComp
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_quotient_le _

/-- The kernel of componentwise coordinate sum has dimension n−c. -/
theorem finrank_ker_compSum :
    Module.finrank (ZMod 2) (LinearMap.ker (G.compSum Finset.univ)) + G.numComponents =
      Fintype.card V := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (G.compSum Finset.univ)
  rw [LinearMap.range_eq_top.2 G.compSum_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  unfold numComponents numComp
  rw [Nat.card_eq_fintype_card]
  omega

theorem range_incMap_le_ker_compSum :
    LinearMap.range G.incMap ≤ LinearMap.ker (G.compSum Finset.univ) := by
  classical
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  funext K
  rw [compSum_apply, Pi.zero_apply]
  change ∑ v, (if Quotient.mk _ v = K then ∑ e, x e * (G.endCount e v : ZMod 2) else 0) = 0
  simp_rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.mul_sum]
  have hfs : Quotient.mk (G.compSetoid Finset.univ) (G.fst e) =
      Quotient.mk (G.compSetoid Finset.univ) (G.snd e) :=
    Quotient.sound (G.reach_fst_snd (Finset.mem_univ e))
  have hsum : ∑ v ∈ Finset.univ.filter (fun v => Quotient.mk (G.compSetoid Finset.univ) v = K),
      (G.endCount e v : ZMod 2) =
      ((if Quotient.mk (G.compSetoid Finset.univ) (G.fst e) = K then 1 else 0 : ℕ) +
        (if Quotient.mk (G.compSetoid Finset.univ) (G.snd e) = K then 1 else 0 : ℕ) : ℕ) := by
    rw [← Nat.cast_sum, Finset.sum_filter]
    congr 1
    have hsplit : ∀ a, (if Quotient.mk (G.compSetoid Finset.univ) a = K then G.endCount e a
        else 0) = (if G.fst e = a ∧ Quotient.mk (G.compSetoid Finset.univ) a = K then 1 else 0) +
          (if G.snd e = a ∧ Quotient.mk (G.compSetoid Finset.univ) a = K then 1 else 0) := by
      intro a
      unfold endCount
      split_ifs <;> simp_all
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (G.fst e) (fun a _ ha => by simp [Ne.symm ha]) (by simp),
      Finset.sum_eq_single (G.snd e) (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  rw [hsum, hfs]
  split_ifs
  · have : ((1 + 1 : ℕ) : ZMod 2) = 0 := by decide
    rw [this, mul_zero]
  · simp

/-- If a and b are reachable, e_a+e_b lies in the image of ∂. -/
theorem single_add_single_mem_range_of_reach {a b : V} (h : G.Reach Finset.univ a b) :
    Pi.single a 1 + Pi.single b 1 ∈ LinearMap.range G.incMap :=
  G.single_add_single_mem_range h

/-- **The image of ∂ consists of vectors with zero sum on each component.** -/
theorem range_incMap_eq_ker_compSum :
    LinearMap.range G.incMap = LinearMap.ker (G.compSum Finset.univ) := by
  classical
  refine le_antisymm G.range_incMap_le_ker_compSum fun y hy => ?_
  obtain ⟨rep, hrep_def⟩ : ∃ rep : V → V,
      ∀ v, rep v = (Quotient.mk (G.compSetoid Finset.univ) v).out := ⟨_, fun _ => rfl⟩
  have hrep : ∀ v, G.Reach Finset.univ v (rep v) := fun v => by
    rw [hrep_def]
    exact G.reach_symm (Quotient.exact (Quotient.out_eq (Quotient.mk (G.compSetoid _) v)))
  have hcls : ∀ v, Quotient.mk (G.compSetoid Finset.univ) (rep v) =
      Quotient.mk (G.compSetoid Finset.univ) v := fun v => by
    rw [hrep_def, Quotient.out_eq]
  rw [LinearMap.mem_ker] at hy
  -- Σ_v y_v e_{rep v} = 0
  have hzero : ∑ v, y v • (Pi.single (rep v) (1 : ZMod 2) : V → ZMod 2) = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hK := congrFun hy (Quotient.mk (G.compSetoid Finset.univ) w)
    rw [compSum_apply, Pi.zero_apply] at hK
    by_cases hw : w = rep w
    · rw [← hK]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : Quotient.mk (G.compSetoid Finset.univ) v =
          Quotient.mk (G.compSetoid Finset.univ) w
      · have : rep v = w := by rw [hw, hrep_def, hrep_def, hv]
        simp only [hv, ↓reduceIte, this, Pi.single_eq_same, mul_one]
      · have : rep v ≠ w := by
          intro h
          apply hv
          rw [← hcls v, h]
        simp only [hv, ↓reduceIte, Pi.single_eq_of_ne (Ne.symm this), mul_zero]
    · refine Finset.sum_eq_zero fun v _ => ?_
      have : rep v ≠ w := by
        intro h
        apply hw
        rw [← h, hrep_def (rep v), hcls v, ← hrep_def v]
      rw [Pi.single_eq_of_ne (Ne.symm this), mul_zero]
  have hy' : y = ∑ v, y v • (Pi.single v 1 + Pi.single (rep v) 1 : V → ZMod 2) := by
    simp only [smul_add, Finset.sum_add_distrib, hzero, add_zero]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single w (fun v _ hv => by simp [Ne.symm hv])
      (fun h => absurd (Finset.mem_univ w) h)]
    simp
  rw [hy']
  exact Submodule.sum_mem _ fun v _ =>
    Submodule.smul_mem _ _ (G.single_add_single_mem_range_of_reach (hrep v))

/-- **Cycle-space dimension for arbitrary graphs.** dim ker ∂+n=m+c. -/
theorem finrank_ker_incMap_add_card :
    Module.finrank (ZMod 2) (LinearMap.ker G.incMap) + Fintype.card V =
      Fintype.card E + G.numComponents := by
  have h := LinearMap.finrank_range_add_finrank_ker G.incMap
  rw [Module.finrank_fintype_fun_eq_card, G.range_incMap_eq_ker_compSum] at h
  have h2 := G.finrank_ker_compSum
  omega

/-! ### Cycle rank ν=m−n+c -/

/-- Cycle rank of a general multigraph: ν(G)=m−n+c(G). -/
noncomputable def nu : ℕ := Fintype.card E + G.numComponents - Fintype.card V

theorem card_le_card_add_numComponents :
    Fintype.card V ≤ Fintype.card E + G.numComponents := by
  have := G.finrank_ker_incMap_add_card
  omega

/-- dim H₁(G;𝔽₂) = ν(G)。 -/
theorem finrank_ker_incMap_eq_nu :
    Module.finrank (ZMod 2) (LinearMap.ker G.incMap) = G.nu := by
  have := G.finrank_ker_incMap_add_card
  unfold nu
  omega

/-- **There are exactly 2^ν Eulerian edge sets, the elements of the binary cycle space.** -/
theorem card_evenSets_eq_two_pow_nu :
    (Finset.univ.filter G.IsEvenSet).card = 2 ^ G.nu := by
  rw [card_evenSets, finrank_ker_incMap_eq_nu]

/-- A connected graph has one component. -/
theorem numComponents_eq_one_of_connected (hc : G.Connected) : G.numComponents = 1 := by
  classical
  obtain ⟨v₀, -⟩ := hc.1
  unfold numComponents numComp
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun K L => ?_⟩, ⟨Quotient.mk _ v₀⟩⟩
  induction K using Quotient.inductionOn
  induction L using Quotient.inductionOn
  exact Quotient.sound (hc.2.2 _ (Finset.mem_univ _) _ (Finset.mem_univ _))

/-- For a connected graph, ν equals `cycleRank`=m+1−n. -/
theorem nu_eq_cycleRank_of_connected (hc : G.Connected) : G.nu = G.cycleRank := by
  rw [nu, cycleRank, G.numComponents_eq_one_of_connected hc]

/-! ### Restriction to an edge set -/

/-- Restrict to edges in A while retaining all vertices. -/
def edgeRestrict (A : Finset E) : Multigraph V {e // e ∈ A} where
  fst e := G.fst e.1
  snd e := G.snd e.1

@[simp] theorem edgeRestrict_endCount (A : Finset E) (e : {e // e ∈ A}) (v : V) :
    (G.edgeRestrict A).endCount e v = G.endCount e.1 v := rfl

theorem edgeRestrict_deg (A : Finset E) (T : Finset {e // e ∈ A}) (v : V) :
    (G.edgeRestrict A).deg T v = G.deg (T.map (Function.Embedding.subtype _)) v := by
  simp [deg, Finset.sum_map]

theorem edgeRestrict_deg_univ (A : Finset E) (v : V) :
    (G.edgeRestrict A).deg Finset.univ v = G.deg A v := by
  rw [edgeRestrict_deg]
  congr 1
  ext e
  simp

theorem edgeRestrict_support_univ (A : Finset E) :
    (G.edgeRestrict A).support Finset.univ = G.support A := by
  ext v
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, edgeRestrict_deg_univ]

theorem edgeRestrict_isEvenSet_iff (A : Finset E) (T : Finset {e // e ∈ A}) :
    (G.edgeRestrict A).IsEvenSet T ↔ G.IsEvenSet (T.map (Function.Embedding.subtype _)) := by
  simp only [IsEvenSet, edgeRestrict_deg]

/-- Eulerian edge sets contained in A: its cycle space. -/
def evenSubsets (A : Finset E) : Finset (Finset E) := A.powerset.filter G.IsEvenSet

theorem mem_evenSubsets {A S : Finset E} : S ∈ G.evenSubsets A ↔ S ⊆ A ∧ G.IsEvenSet S := by
  simp [evenSubsets]

theorem card_evenSubsets_eq (A : Finset E) :
    (G.evenSubsets A).card = (Finset.univ.filter (G.edgeRestrict A).IsEvenSet).card := by
  symm
  refine Finset.card_bij (fun T _ => T.map (Function.Embedding.subtype _)) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    rw [mem_evenSubsets]
    refine ⟨fun e he => ?_, (G.edgeRestrict_isEvenSet_iff A T).1 hT.2⟩
    obtain ⟨e', -, rfl⟩ := Finset.mem_map.1 he
    exact e'.2
  · intro T₁ _ T₂ _ h
    exact Finset.map_injective _ h
  · intro S hS
    rw [mem_evenSubsets] at hS
    refine ⟨S.subtype (· ∈ A), ?_, ?_⟩
    · rw [Finset.mem_filter, edgeRestrict_isEvenSet_iff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.subtype_map_of_mem fun e he => hS.1 he]
      exact hS.2
    · exact Finset.subtype_map_of_mem fun e he => hS.1 he

/-- The cycle space on A has size 2^{dim ker ∂_A}, with ∂_A the restricted incidence map. -/
theorem card_evenSubsets (A : Finset E) :
    (G.evenSubsets A).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict A).incMap) := by
  rw [card_evenSubsets_eq, card_evenSets]

/-- Cycle-space dimension is monotone in the edge set. -/
theorem finrank_ker_restrict_mono {A B : Finset E} (h : A ⊆ B) :
    Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict A).incMap) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict B).incMap) := by
  have hle : (G.evenSubsets A).card ≤ (G.evenSubsets B).card := by
    refine Finset.card_le_card fun S hS => ?_
    rw [mem_evenSubsets] at hS ⊢
    exact ⟨hS.1.trans h, hS.2⟩
  rw [card_evenSubsets, card_evenSubsets] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle

/-- For nonempty S, |S|+1≤dim ker ∂_S+v(S). -/
theorem card_add_one_le_finrank_restrict {S : Finset E} (hS : S.Nonempty) :
    S.card + 1 ≤
      Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict S).incMap) + (G.support S).card := by
  obtain ⟨e₀, he₀⟩ := hS
  have h := (G.edgeRestrict S).card_add_one_le_finrank_ker_add_card_support
    (S := Finset.univ) ⟨⟨e₀, he₀⟩, Finset.mem_univ _⟩
  rw [edgeRestrict_support_univ, Finset.card_univ, Fintype.card_coe] at h
  exact h

/-- Contributing state: an edge set with no degree-one vertex, equivalently nonzero weight ∏φ(d_S(v)). -/
def IsContributing (S : Finset E) : Prop := ∀ v, G.deg S v ≠ 1

instance : DecidablePred G.IsContributing := fun S => by unfold IsContributing; infer_instance

theorem wt_phi_ne_zero_iff (S : Finset E) : G.wt phi S ≠ 0 ↔ G.IsContributing S := by
  rw [wt, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies, IsContributing]
  refine forall_congr' fun v => ?_
  constructor
  · intro h h1; rw [h1] at h; exact h rfl
  · intro h; exact (phi_pos_of_ne_one h).ne'

/-- A contributing state satisfies v(S)≤|S| by the handshake identity. -/
theorem card_support_le_of_isContributing {S : Finset E} (hS : G.IsContributing S) :
    (G.support S).card ≤ S.card :=
  G.card_support_le S ((G.wt_phi_ne_zero_iff S).2 hS)

/-- Eulerian edge sets are contributing states. -/
theorem isContributing_of_isEvenSet {S : Finset E} (h : G.IsEvenSet S) : G.IsContributing S := by
  intro v h1
  have := h v
  rw [h1] at this
  exact Nat.not_even_one this

end Multigraph

end BPFixedPoints
