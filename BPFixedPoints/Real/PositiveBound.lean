import BPFixedPoints.Real.Count
import BPFixedPoints.Real.Parity

/-!
# Positive-root bound at generic physical parameters (`real:positive-bound`)

For a_e>0, a_e≠1 and b_i>0 satisfying the nonzero polynomial condition of N=Q,
there are Q(G) complex solutions. Real solutions embed by ℝ→ℂ. Every Eulerian
sector has a real solution (`exists_real_solution`); nonempty sectors give
nonpositive solutions. Hence #H₁≤R≤Q, 1≤N₊ and N₊+#H₁≤Q+1
(`real_positive_budget`). If connected, #H₁=2^ν and N₊≤Q−2^ν+1
(`real_positive_budget_of_connected`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Admissible real solutions inject into admissible complex solutions. -/
theorem real_to_complex_injective (a : E → ℝ) (b : V → ℝ) :
    Function.Injective fun y : {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} =>
      (⟨Complex.ofRealHom ∘ y.1, (G.isAdmissibleSolution_map_iff Complex.ofRealHom a b y.1).2 y.2⟩ :
        {z : Dart E → ℂ // G.IsAdmissibleSolution (Complex.ofRealHom ∘ a) (Complex.ofRealHom ∘ b) z}) := by
  intro y y' h
  apply Subtype.ext
  funext α
  have := congrFun (congrArg Subtype.val h) α
  simpa using this

/-- **Positive-root bound (`real:positive-bound`).** -/
theorem real_positive_budget (hG : G.Loopless) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℝ) (b : V → ℝ), (∀ e, 0 < a e) → (∀ e, a e ≠ 1) → (∀ i, 0 < b i) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℝ) P) ≠ 0 →
          (Finset.univ.filter G.IsEvenSet).card ≤
              Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
            Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ≤ G.Q ∧
            1 ≤ Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} ∧
            Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} +
                (Finset.univ.filter G.IsEvenSet).card ≤ G.Q + 1 := by
  obtain ⟨P, hP0, hP⟩ := G.exists_generic_count_eq_Q_complex hG
  refine ⟨P, hP0, fun a b ha ha1 hb hPab => ?_⟩
  let ι : ℝ →+* ℂ := Complex.ofRealHom
  have hPc : MvPolynomial.eval (Sum.elim (ι ∘ a) (ι ∘ b))
      (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 := by
    have e1 : ι (MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℝ) P)) =
        MvPolynomial.eval (Sum.elim (ι ∘ a) (ι ∘ b)) (MvPolynomial.map (Int.castRingHom ℂ) P) := by
      rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left,
        Sum.comp_elim]
      congr 1
    rw [← e1]
    exact (map_ne_zero ι).2 hPab
  have hcard := hP (ι ∘ a) (ι ∘ b) (fun e => by simpa [ι] using (ha e).ne')
    (fun i => by simpa [ι] using (hb i).ne') hPc
  set Sol := {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}
  set CSol := {z : Dart E → ℂ // G.IsAdmissibleSolution (ι ∘ a) (ι ∘ b) z}
  have hCfin : Finite CSol := Nat.finite_of_card_ne_zero (by rw [hcard]; exact G.Q_pos.ne')
  have hinj := G.real_to_complex_injective a b
  have hfin : Finite Sol := Finite.of_injective _ hinj
  have hRQ : Nat.card Sol ≤ G.Q := hcard ▸ Nat.card_le_card_of_injective _ hinj
  -- Lower bound.
  have hlow : (Finset.univ.filter G.IsEvenSet).card ≤ Nat.card Sol := by
    have := card_evenSets_le_real ha ha1 hG hb
    rw [ENat.card_eq_coe_natCard] at this
    exact_mod_cast this
  -- A solution in each sector.
  have hsol : ∀ S : {S : Finset E // G.IsEvenSet S},
      ∃ y, G.IsAdmissibleSolution a b y ∧ negSupport y = S.1 :=
    fun S => exists_real_solution ha ha1 hG S.2 hb
  choose f hf using hsol
  have hempty : G.IsEvenSet ∅ := fun v => by simp
  have hpos₀ : ∀ α, 0 < f ⟨∅, hempty⟩ α := by
    intro α
    have hy := (hf ⟨∅, hempty⟩).1
    have h1 : ¬ f ⟨∅, hempty⟩ α < 0 := by
      intro h
      have := (msg_neg_iff_mem_negSupport ha hb hy α).1 h
      rw [(hf ⟨∅, hempty⟩).2] at this
      exact Finset.notMem_empty _ this
    exact lt_of_le_of_ne (not_lt.1 h1) (hy.2.1 α).symm
  set Pos := {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α}
  have hPosfin : Finite Pos :=
    Finite.of_injective (fun y : Pos => (⟨y.1, y.2.1⟩ : Sol)) fun y y' h =>
      Subtype.ext (congrArg (fun w : Sol => w.1) h)
  have hPos1 : 1 ≤ Nat.card Pos := by
    have : Nonempty Pos := ⟨⟨f ⟨∅, hempty⟩, (hf _).1, hpos₀⟩⟩
    exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨this, hPosfin⟩)
  -- Solutions in nonempty sectors are distinct from positive solutions.
  set NE := {S : {S : Finset E // G.IsEvenSet S} // S.1 ≠ ∅}
  let g : NE ⊕ Pos → Sol := fun x => match x with
    | Sum.inl S => ⟨f S.1, (hf S.1).1⟩
    | Sum.inr y => ⟨y.1, y.2.1⟩
  have hg : Function.Injective g := by
    have hnp : ∀ (S : NE) (y : Pos), (⟨f S.1, (hf S.1).1⟩ : Sol) ≠ ⟨y.1, y.2.1⟩ := by
      intro S y h
      have h1 := congrArg (fun z : Sol => negSupport z.1) h
      simp only [(hf S.1).2] at h1
      apply S.2
      rw [h1]
      ext e
      simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_lt]
      exact (y.2.2 (e, true)).le
    rintro (S | y) (T | z) h
    · have := congrArg (fun w : Sol => negSupport w.1) h
      simp only [g, (hf S.1).2, (hf T.1).2] at this
      exact congrArg Sum.inl (Subtype.ext (Subtype.ext this))
    · exact absurd h (hnp S z)
    · exact absurd h.symm (hnp T y)
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun w : Sol => w.1) h))
  have hNE : Nat.card NE + 1 = (Finset.univ.filter G.IsEvenSet).card := by
    have hT : Nat.card {S : Finset E // G.IsEvenSet S} = (Finset.univ.filter G.IsEvenSet).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1 : Nat.card {S : {S : Finset E // G.IsEvenSet S} // S.1 = ∅} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨⟨∅, hempty⟩, rfl⟩, fun z => Subtype.ext (Subtype.ext z.2)⟩
    have h2 := Nat.card_congr (Equiv.sumCompl fun S : {S : Finset E // G.IsEvenSet S} => S.1 = ∅)
    rw [Nat.card_sum, h1] at h2
    rw [← hT, ← h2, add_comm]
  have hsum : Nat.card NE + Nat.card Pos ≤ Nat.card Sol := by
    rw [← Nat.card_sum]
    exact Nat.card_le_card_of_injective g hg
  refine ⟨hlow, hRQ, hPos1, ?_⟩
  omega

/-- For connected G at generic physical parameters, 2^ν≤R≤Q and 1≤N₊≤Q−2^ν+1. -/
theorem real_positive_budget_of_connected (hG : G.Loopless) (hc : G.Connected) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℝ) (b : V → ℝ), (∀ e, 0 < a e) → (∀ e, a e ≠ 1) → (∀ i, 0 < b i) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℝ) P) ≠ 0 →
          2 ^ G.cycleRank ≤ Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
            Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ≤ G.Q ∧
            1 ≤ Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} ∧
            Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} +
                2 ^ G.cycleRank ≤ G.Q + 1 := by
  rw [← G.card_evenSets_of_connected hc]
  exact G.real_positive_budget hG

end Multigraph

end BPFixedPoints
