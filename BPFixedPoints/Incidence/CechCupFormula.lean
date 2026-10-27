import BPFixedPoints.Incidence.CechCupNaturality

/-! # Monomial product formula for arbitrary finite vertex sets -/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.CechProduct

open Finsupp

theorem finCupBasis_some_iff (n : ℕ) (e : Fin n → ℕ) (x y z : Fin n → Basis) :
    finCupBasis n e x y = some z ↔ ∀ v, lineCupBasis (e v) (x v) (y v) = some (z v) := by
  induction n with
  | zero => simp [finCupBasis, Subsingleton.elim (fun i : Fin 0 => Fin.elim0 i) z]
  | succ n ih =>
    constructor
    · intro h
      simp only [finCupBasis, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      intro v
      refine Fin.cases ha (fun j => ?_) v
      exact (ih _ _ _ _).mp hb j
    · intro h
      have ht := (ih (Fin.tail e) (Fin.tail x) (Fin.tail y) (Fin.tail z)).mpr
        (fun v => h v.succ)
      simp only [finCupBasis, h 0, ht, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Fin.cons_self_tail]

variable {V : Type*} [Fintype V]

noncomputable def cupBasis (e : V → ℕ) (x y : V → Basis) : Option (V → Basis) :=
  (finCupBasis (Fintype.card V) (e ∘ (Fintype.equivFin V).symm)
    (x ∘ (Fintype.equivFin V).symm) (y ∘ (Fintype.equivFin V).symm)).map
      (fun z => z ∘ Fintype.equivFin V)

noncomputable def cupCross (x y : V → Basis) : ℕ :=
  finCupCross (Fintype.card V) (x ∘ (Fintype.equivFin V).symm)
    (y ∘ (Fintype.equivFin V).symm)

theorem cupBasis_some_iff (e : V → ℕ) (x y z : V → Basis) :
    cupBasis e x y = some z ↔ ∀ v, lineCupBasis (e v) (x v) (y v) = some (z v) := by
  unfold cupBasis
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ v
    have h := (finCupBasis_some_iff _ _ _ _ _).mp ha ((Fintype.equivFin V) v)
    simpa using h
  · intro h
    refine ⟨z ∘ (Fintype.equivFin V).symm, ?_, ?_⟩
    · apply (finCupBasis_some_iff _ _ _ _ _).mpr
      intro v
      exact h ((Fintype.equivFin V).symm v)
    · funext v; simp

variable (R : Type*) [CommRing R]

theorem chainCup_single (d e : V → ℕ) (x y : V → Basis) (r s : R) :
    chainCup R d e (single x r) (single y s) =
      (cupBasis e x y).elim 0 (fun z => single z ((-1 : R) ^ cupCross x y * (r * s))) := by
  have hsingle (z : V → Basis) (t : R) :
      single z t = vertexReindex R (single (z ∘ (Fintype.equivFin V).symm) t) := by
    change single z t = mapDomain ((Fintype.equivFin V).symm.arrowCongr (Equiv.refl Basis))
      (single (z ∘ (Fintype.equivFin V).symm) t)
    rw [mapDomain_single]
    congr 1
    funext v
    simp
  rw [hsingle x r, hsingle y s, chainCup_reindex, finChainPairing_mul_single]
  unfold cupBasis cupCross
  cases finCupBasis (Fintype.card V) (e ∘ (Fintype.equivFin V).symm)
      (x ∘ (Fintype.equivFin V).symm) (y ∘ (Fintype.equivFin V).symm) with
  | none => simp
  | some z =>
    simp only [Option.map_some, Option.elim, vertexReindex, mapDomain.coe_linearEquiv,
      mapDomain_single]
    congr 1

end BPFixedPoints.CechProduct
