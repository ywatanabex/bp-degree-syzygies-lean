import BPFixedPoints.Incidence.FiniteFiltration

/-!
# Finite perturbation preserves ground-field subspaces

The maps are linear over `R`; the subspaces may be over a smaller ring `k`.
This distinction is necessary for the coefficient grading of a polynomial
module. The finite inverse is expanded explicitly; no preservation property
of an abstract inverse is assumed.
-/

namespace BPFixedPoints.IncidencePerturbation

variable {R k M H : Type*} [CommRing R] [CommRing k]
  [AddCommGroup M] [Module R M] [Module k M]
  [AddCommGroup H] [Module R H] [Module k H]

/-- The finite correction preserves a subspace whenever both input maps do. -/
theorem correction_mem_of_preserves (δ h : Module.End R M)
    (P : Submodule k M)
    (hδ : ∀ x ∈ P, δ x ∈ P) (hh : ∀ x ∈ P, h x ∈ P)
    (hn : IsNilpotent (δ * h)) {x : M} (hx : x ∈ P) :
    correction δ h x ∈ P := by
  obtain ⟨N, hN⟩ := hn
  have hp : ∀ n : ℕ, ∀ y ∈ P, ((-(δ * h)) ^ n) y ∈ P := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ, Module.End.mul_apply]
      apply ih
      exact P.neg_mem (hδ _ (hh _ hy))
  rw [correction, inverse_one_add_eq_sum (δ * h) N hN,
    Module.End.mul_apply, LinearMap.sum_apply]
  exact P.sum_mem fun n hn => hp n _ (hδ _ hx)

namespace Contraction

variable (C : Contraction R M H) (δ : Module.End R M)
  (P : Submodule k M) (Q : Submodule k H)
  (hδ : ∀ x ∈ P, δ x ∈ P) (hh : ∀ x ∈ P, C.h x ∈ P)
  (hi : ∀ x ∈ Q, C.i x ∈ P) (hp : ∀ x ∈ P, C.p x ∈ Q)
  (hn : IsNilpotent (δ * C.h))

include hδ hh hi hp hn in
/-- The actual transferred differential preserves the prescribed subspace. -/
theorem transfer_mem_of_preserves {x : H} (hx : x ∈ Q) : C.transfer δ x ∈ Q := by
  change C.p (correction δ C.h (C.i x)) ∈ Q
  exact hp _ (correction_mem_of_preserves δ C.h P hδ hh hn (hi _ hx))

include hδ hh hi hn in
theorem inclusion_mem_of_preserves {x : H} (hx : x ∈ Q) : C.inclusion δ x ∈ P := by
  change C.i x - C.h (correction δ C.h (C.i x)) ∈ P
  exact P.sub_mem (hi _ hx)
    (hh _ (correction_mem_of_preserves δ C.h P hδ hh hn (hi _ hx)))

include hδ hh hp hn in
theorem projection_mem_of_preserves {x : M} (hx : x ∈ P) : C.projection δ x ∈ Q := by
  change C.p (x - correction δ C.h (C.h x)) ∈ Q
  exact hp _ (P.sub_mem hx (correction_mem_of_preserves δ C.h P hδ hh hn (hh _ hx)))

include hδ hh hn in
theorem contractingHomotopy_mem_of_preserves {x : M} (hx : x ∈ P) :
    C.contractingHomotopy δ x ∈ P := by
  change C.h x - C.h (correction δ C.h (C.h x)) ∈ P
  exact P.sub_mem (hh _ hx)
    (hh _ (correction_mem_of_preserves δ C.h P hδ hh hn (hh _ hx)))

end Contraction

end BPFixedPoints.IncidencePerturbation
