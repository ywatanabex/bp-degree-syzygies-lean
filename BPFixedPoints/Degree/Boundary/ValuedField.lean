import BPFixedPoints.Degree.Boundary.Exclusion

/-!
# Puiseux-type valued fields

The paper uses the Puiseux field ⋃_r K((t^{1/r})) over algebraically closed K
of characteristic zero. Only valued-field properties are needed; collect them
in `PuiseuxField K`. Existence is `newtonPuiseux_exists` in
`Degree/Boundary/ValuedFieldExists.lean`, obtained from a valuation ring of an
algebraic closure of K((t)) dominating K⟦t⟧, without the Newton–Puiseux theorem.

Required properties: L is algebraically closed of characteristic zero, K embeds
in L with trivial valuation, t≠0 has v(t)<1, and every integral element has a
residue in K. The valuation form of `boundary_exclusion` applies immediately.
-/

universe u

namespace BPFixedPoints.BP

/--
Puiseux-type valued field over algebraically closed characteristic-zero K,
with embedding of K[[t]], constant-coefficient valuation criterion, and residue field K.
-/
structure PuiseuxField (K : Type u) [Field K] where
  /-- Field playing the role of the algebraic closure of K((t)). -/
  L : Type u
  [field : Field L]
  [algClosed : IsAlgClosed L]
  [charZero : CharZero L]
  /-- Value group: a linearly ordered commutative group with zero. -/
  Γ₀ : Type u
  [ord : LinearOrderedCommGroupWithZero Γ₀]
  /-- Valuation. -/
  v : Valuation L Γ₀
  /-- Embedding of K. -/
  ofK : K →+* L
  /-- The valuation is trivial on K. -/
  val_ofK : ∀ c : K, c ≠ 0 → v (ofK c) = 1
  /-- Embedding of the formal power-series ring K[[t]]. -/
  ofPS : PowerSeries K →+* L
  ofPS_injective : Function.Injective ofPS
  /-- Embedding constants agrees with the embedding of K. -/
  ofPS_C : ∀ c : K, ofPS (PowerSeries.C c) = ofK c
  /-- Uniformizing parameter t. -/
  t : L
  ofPS_X : ofPS PowerSeries.X = t
  /-- Images of power series are integral. -/
  val_ofPS_le_one : ∀ f : PowerSeries K, v (ofPS f) ≤ 1
  /-- The image of a power series has valuation below 1 exactly when its constant coefficient is zero. -/
  val_ofPS_lt_one_iff : ∀ f : PowerSeries K, v (ofPS f) < 1 ↔ PowerSeries.constantCoeff f = 0
  /-- Residue field K: every integral element is congruent to an element of K. -/
  residue : ∀ x : L, v x ≤ 1 → ∃ c : K, v (x - ofK c) < 1

attribute [instance] PuiseuxField.field PuiseuxField.algClosed PuiseuxField.charZero
  PuiseuxField.ord

namespace PuiseuxField

variable {K : Type u} [Field K] (P : PuiseuxField K)

theorem val_t_lt_one : P.v P.t < 1 := by
  rw [← P.ofPS_X, P.val_ofPS_lt_one_iff]; simp

theorem t_ne_zero : P.t ≠ 0 := by
  rw [← P.ofPS_X]
  intro h
  have := P.ofPS_injective (h.trans (map_zero _).symm)
  exact PowerSeries.X_ne_zero this

/-- Residues are unique: distinct elements of K are not congruent. -/
theorem eq_of_val_ofK_sub_lt {c c' : K} (h : P.v (P.ofK c - P.ofK c') < 1) : c = c' := by
  by_contra hne
  rw [← map_sub, P.val_ofK _ (sub_ne_zero.2 hne)] at h
  exact lt_irrefl _ h

end PuiseuxField

end BPFixedPoints.BP

namespace BPFixedPoints.Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] {G : Multigraph V E}
variable {K : Type u} [Field K] (P : PuiseuxField K)

/-- Boundary exclusion for a Puiseux-type field: if s̄_e=1, β_i are units and β̄_i≠−1, every admissible L-solution has unit F_i,A_{e,i} and F̄_i≠−1. -/
theorem boundary_exclusion_puiseux {s : E → P.L} {β : V → P.L} {A : Dart E → P.L} {F : V → P.L}
    (hs : ∀ e, P.v (s e - 1) < 1) (hβ : ∀ i, P.v (β i) = 1) (hβ1 : ∀ i, P.v (β i + 1) = 1)
    (h : G.IsAuxSolution s β A F) :
    (∀ i, P.v (F i) = 1) ∧ (∀ α, P.v (A α) = 1) ∧ (∀ i, P.v (F i + 1) = 1) :=
  boundary_exclusion P.v hs hβ hβ1 h

end BPFixedPoints.Multigraph
