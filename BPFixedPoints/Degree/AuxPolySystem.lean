import BPFixedPoints.Degree.Lift.LimitSystem
import BPFixedPoints.Degree.AuxSystem

/-!
# Polynomial auxiliary system over an arbitrary coefficient ring

Write `IsAuxSolution` over R using edge polynomials
A_α(1+s_e A_ᾱ)−F_{t(α)}(1+A_ᾱ) (`auxEdgePoly`), vertex polynomials
F_i∏_{α∈in(i)}A_ᾱ−β_i F_i^{d_i} (`vertexPoly`, `Degree/Lift/LimitSystem.lean`),
and denominator ∏_α A_α(A_α+1)∏_i F_i(F_i+1) (`auxDen`).
Over a field κ, zeros with nonzero denominator are exactly auxiliary solutions
(`isAuxSolution_iff`, `auxSolEquiv`). The one-parameter `weakSystem` specializes
s_e=1+t c_e and β_i=C β_i (`weakSystem_eq_auxSystem`). Simplicity means the
Jacobian determinant is nonzero (`IsSimpleAuxSolution`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace BP

open MvPolynomial

variable (V E : Type*) [Fintype V] [Fintype E]

/-- Admissibility denominator product_α A_α(A_α+1) product_i F_i(F_i+1). -/
noncomputable def auxDen {R : Type*} [CommRing R] : MvPolynomial (Multigraph.Var V E) R :=
  (∏ α : Dart E, X (Sum.inl α) * (X (Sum.inl α) + 1)) *
    ∏ i : V, X (Sum.inr i) * (X (Sum.inr i) + 1)

variable {V E}

theorem map_auxDen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    map φ (auxDen V E : MvPolynomial (Multigraph.Var V E) R) = auxDen V E := by
  simp [auxDen, map_prod]

theorem eval_auxDen {κ : Type*} [CommRing κ] (x : Multigraph.Var V E → κ) :
    eval x (auxDen V E) =
      (∏ α : Dart E, x (Sum.inl α) * (x (Sum.inl α) + 1)) *
        ∏ i : V, x (Sum.inr i) * (x (Sum.inr i) + 1) := by
  simp [auxDen, eval_prod]

theorem eval_auxDen_ne_zero_iff {κ : Type*} [Field κ] (x : Multigraph.Var V E → κ) :
    eval x (auxDen V E) ≠ 0 ↔
      (∀ α, x (Sum.inl α) ≠ 0) ∧ (∀ α, x (Sum.inl α) ≠ -1) ∧
        (∀ i, x (Sum.inr i) ≠ 0) ∧ (∀ i, x (Sum.inr i) ≠ -1) := by
  rw [eval_auxDen, mul_ne_zero_iff, Finset.prod_ne_zero_iff, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies, mul_ne_zero_iff, ne_eq, add_eq_zero_iff_eq_neg,
    forall_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

end BP

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Ring

variable {R : Type*} [CommRing R]

/-- Edge equation A_α(1+s_e A_revα) - F_tailα(1+A_revα). -/
noncomputable def auxEdgePoly (s : E → R) (α : Dart E) : MvPolynomial (Var V E) R :=
  X (Sum.inl α) * (1 + C (s α.1) * X (Sum.inl (rev α))) -
    X (Sum.inr (G.tail α)) * (1 + X (Sum.inl (rev α)))

/-- Polynomial auxiliary system over R with parameters s and β. -/
noncomputable def auxSystem (s : E → R) (β : V → R) : Var V E → MvPolynomial (Var V E) R
  | Sum.inl α => G.auxEdgePoly s α
  | Sum.inr i => G.vertexPoly β i

theorem map_auxEdgePoly {S : Type*} [CommRing S] (φ : R →+* S) (s : E → R) (α : Dart E) :
    map φ (G.auxEdgePoly s α) = G.auxEdgePoly (φ ∘ s) α := by
  simp [auxEdgePoly]

theorem map_vertexPoly {S : Type*} [CommRing S] (φ : R →+* S) (β : V → R) (i : V) :
    map φ (G.vertexPoly β i) = G.vertexPoly (φ ∘ β) i := by
  simp [vertexPoly, map_prod]

theorem map_auxSystem {S : Type*} [CommRing S] (φ : R →+* S) (s : E → R) (β : V → R)
    (v : Var V E) : map φ (G.auxSystem s β v) = G.auxSystem (φ ∘ s) (φ ∘ β) v := by
  cases v with
  | inl α => simp [auxSystem, map_auxEdgePoly]
  | inr i => simp [auxSystem, map_vertexPoly]

/-- Jacobian matrix of the auxiliary system at x. -/
noncomputable def auxJacobian (s : E → R) (β : V → R) (x : Var V E → R) :
    Matrix (Var V E) (Var V E) R :=
  Matrix.of fun i j => eval x (pderiv j (G.auxSystem s β i))

end Ring

/-- `weakSystem` specializes the auxiliary system to s_e=1+t c_e and β_i=C β_i. -/
theorem weakSystem_eq_auxSystem {K : Type*} [Field K] [DecidableEq K] (c : E → K) (β : V → K)
    (v : Var V E) :
    G.weakSystem c β v =
      G.auxSystem (fun e => 1 + PowerSeries.X * PowerSeries.C (c e))
        (fun i => PowerSeries.C (β i)) v := by
  cases v with
  | inl α =>
    simp only [weakSystem, auxSystem, edgePoly, auxEdgePoly, map_add, map_mul, map_one]
    ring
  | inr i => rfl

section Field

variable {κ : Type*} [Field κ]

/-- Simplicity of an auxiliary solution: the Jacobian determinant is nonzero. -/
def IsSimpleAuxSolution (s : E → κ) (β : V → κ) (A : Dart E → κ) (F : V → κ) : Prop :=
  (G.auxJacobian s β (Sum.elim A F)).det ≠ 0

theorem eval_auxEdgePoly (s : E → κ) (x : Var V E → κ) (α : Dart E) :
    eval x (G.auxEdgePoly s α) =
      x (Sum.inl α) * (1 + s α.1 * x (Sum.inl (rev α))) -
        x (Sum.inr (G.tail α)) * (1 + x (Sum.inl (rev α))) := by
  simp [auxEdgePoly]

theorem eval_vertexPoly (β : V → κ) (x : Var V E → κ) (i : V) :
    eval x (G.vertexPoly β i) =
      x (Sum.inr i) * ∏ α ∈ G.inDarts i, x (Sum.inl (rev α)) -
        β i * x (Sum.inr i) ^ G.degree i := by
  simp [vertexPoly, eval_prod]

/-- Over a field, admissible polynomial zeros are exactly auxiliary solutions. -/
theorem isAuxSolution_iff (s : E → κ) (β : V → κ) (x : Var V E → κ) :
    ((∀ v, eval x (G.auxSystem s β v) = 0) ∧ eval x (auxDen V E) ≠ 0) ↔
      G.IsAuxSolution s β (fun α => x (Sum.inl α)) (fun i => x (Sum.inr i)) := by
  rw [eval_auxDen_ne_zero_iff]
  constructor
  · rintro ⟨hsol, hA0, hA1, hF0, hF1⟩
    refine ⟨hA0, hA1, hF0, hF1, ?_, ?_⟩
    · intro α
      have h := hsol (Sum.inl α)
      rw [auxSystem, eval_auxEdgePoly, sub_eq_zero] at h
      exact h.symm
    · intro i
      have h := hsol (Sum.inr i)
      rw [auxSystem, eval_vertexPoly, sub_eq_zero] at h
      have hF : x (Sum.inr i) ≠ 0 := hF0 i
      rw [zpow_sub₀ hF, zpow_one, zpow_natCast, div_mul_eq_mul_div, h, mul_div_assoc,
        div_self (pow_ne_zero _ hF), mul_one]
  · intro h
    refine ⟨?_, h.A_ne_zero, h.A_ne_neg_one, h.F_ne_zero, h.F_ne_neg_one⟩
    intro v
    cases v with
    | inl α =>
      rw [auxSystem, eval_auxEdgePoly, sub_eq_zero]
      exact (h.edge α).symm
    | inr i =>
      rw [auxSystem, eval_vertexPoly, sub_eq_zero]
      have hv := h.vertex i
      have hF : x (Sum.inr i) ≠ 0 := h.F_ne_zero i
      rw [hv, zpow_sub₀ hF, zpow_one, zpow_natCast]
      field_simp

/-- Equivalence between polynomial zeros with nonzero denominator and auxiliary solutions. -/
noncomputable def auxSolEquiv (s : E → κ) (β : V → κ) :
    {x : Var V E → κ // (∀ v, eval x (G.auxSystem s β v) = 0) ∧ eval x (auxDen V E) ≠ 0} ≃
      {p : (Dart E → κ) × (V → κ) // G.IsAuxSolution s β p.1 p.2} where
  toFun x := ⟨(fun α => x.1 (Sum.inl α), fun i => x.1 (Sum.inr i)),
    (G.isAuxSolution_iff s β x.1).1 x.2⟩
  invFun p := ⟨Sum.elim p.1.1 p.1.2, (G.isAuxSolution_iff s β _).2 p.2⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    cases v <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

end Field

end Multigraph

end BPFixedPoints
