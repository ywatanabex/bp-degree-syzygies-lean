import BPFixedPoints.Degree.Main
import BPFixedPoints.StateSum.Parity

/-!
# Parity of real-root counts: R≡Q mod 2

At real parameters, complex conjugation preserves admissible complex BP
solutions and fixes exactly the real ones. An involution's fixed-point count
has the parity of its total cardinality. With generic N=Q this proves
`card_real_admissible_modEq_Q` at generic nonzero real parameters. For connected
ν≥1, `even_Q_of_connected` makes both Q and R even.
Injective field maps preserve and reflect admissible BP solutions
(`isAdmissibleSolution_map_iff`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Map

variable {K L : Type*} [Field K] [Field L] (σ : K →+* L) (a : E → K) (b : V → K) (y : Dart E → K)

theorem cavity_map (α : Dart E) : G.cavity (σ ∘ b) (σ ∘ y) α = σ (G.cavity b y α) := by
  simp [cavity, map_prod]

theorem bpPoly_map (α : Dart E) :
    G.bpPoly (σ ∘ a) (σ ∘ b) (σ ∘ y) α = σ (G.bpPoly a b y α) := by
  simp [bpPoly, cavity_map]

theorem totalField_map (i : V) : G.totalField (σ ∘ b) (σ ∘ y) i = σ (G.totalField b y i) := by
  simp [totalField, map_prod]

/-- A field homomorphism, hence injective, preserves and reflects admissible BP solutions. -/
theorem isAdmissibleSolution_map_iff :
    G.IsAdmissibleSolution (σ ∘ a) (σ ∘ b) (σ ∘ y) ↔ G.IsAdmissibleSolution a b y := by
  have h0 : ∀ x : K, σ x = 0 ↔ x = 0 := fun x => map_eq_zero σ
  simp only [IsAdmissibleSolution, IsFixedPoint, Admissible, bpPoly_map, cavity_map,
    totalField_map, Function.comp_apply, ← map_add, ← map_one σ, ne_eq, h0]

end Map

/-- **Real-root parity.** For loopless G, some nonzero P∈ℤ[a,b] ensures that every nonzero real parameter with P≠0 has admissible real-root count congruent to Q(G) modulo two. -/
theorem card_real_admissible_modEq_Q (hG : G.Loopless) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℝ) (b : V → ℝ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℝ) P) ≠ 0 →
          Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ≡ G.Q [MOD 2] := by
  classical
  obtain ⟨P, hP0, hP⟩ := G.exists_generic_count_eq_Q hG
  refine ⟨P, hP0, fun a b ha hb hPab => ?_⟩
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
  obtain ⟨hcard, -⟩ := hP ℂ (ι ∘ a) (ι ∘ b) (fun e => by simpa [ι] using ha e)
    (fun i => by simpa [ι] using hb i) hPc
  set Sol := {y : Dart E → ℂ // G.IsAdmissibleSolution (ι ∘ a) (ι ∘ b) y}
  have hfin : Finite Sol := Nat.finite_of_card_ne_zero (by rw [hcard]; exact G.Q_pos.ne')
  have : Fintype Sol := Fintype.ofFinite Sol
  -- Complex conjugation.
  let σ : ℂ →+* ℂ := starRingEnd ℂ
  have hσa : σ ∘ (ι ∘ a) = ι ∘ a := funext fun e => Complex.conj_ofReal (a e)
  have hσb : σ ∘ (ι ∘ b) = ι ∘ b := funext fun i => Complex.conj_ofReal (b i)
  let f : Function.End Sol := fun y => ⟨σ ∘ y.1, by
    have := (G.isAdmissibleSolution_map_iff σ (ι ∘ a) (ι ∘ b) y.1).2 y.2
    rwa [hσa, hσb] at this⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    funext α
    change σ (σ (y.1 α)) = y.1 α
    exact Complex.conj_conj _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf2
  -- Fixed points are equivalent to real solutions.
  have hfix : Function.fixedPoints f ≃ {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} :=
    { toFun := fun y => ⟨fun α => (y.1.1 α).re, by
        have hy : ι ∘ (fun α => (y.1.1 α).re) = y.1.1 := by
          funext α
          have h1 := congrArg (fun z : Sol => z.1 α) y.2
          exact Complex.conj_eq_iff_re.1 h1
        have := y.1.2
        rw [← hy] at this
        exact (G.isAdmissibleSolution_map_iff ι a b _).1 this⟩
      invFun := fun r => ⟨⟨ι ∘ r.1, (G.isAdmissibleSolution_map_iff ι a b r.1).2 r.2⟩, by
        apply Subtype.ext
        funext α
        exact Complex.conj_ofReal (r.1 α)⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        funext α
        have h1 := congrArg (fun z : Sol => z.1 α) y.2
        exact Complex.conj_eq_iff_re.1 h1
      right_inv := fun r => by
        apply Subtype.ext
        funext α
        simp [ι] }
  rw [← Nat.card_congr hfix, Nat.card_eq_fintype_card, ← hcard, Nat.card_eq_fintype_card]
  exact hmod.symm

/-- For connected ν≥1, the generic nonzero real parameter has an even number of admissible real solutions. -/
theorem even_card_real_admissible (hG : G.Loopless) (hc : G.Connected) (hν : 1 ≤ G.cycleRank) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℝ) (b : V → ℝ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℝ) P) ≠ 0 →
          Even (Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) := by
  obtain ⟨P, hP0, hP⟩ := G.card_real_admissible_modEq_Q hG
  refine ⟨P, hP0, fun a b ha hb hPab => ?_⟩
  have hmod := hP a b ha hb hPab
  have hQ := G.even_Q_of_connected hc hν
  rw [Nat.even_iff] at hQ ⊢
  rw [Nat.ModEq] at hmod
  omega

end Multigraph

end BPFixedPoints
