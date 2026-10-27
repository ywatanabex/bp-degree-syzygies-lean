import BPFixedPoints.Incidence.FiniteFiltration

/-!
# Finite perturbation for families of graded submodules

Compute degrees of perturbed differentials, chain maps and homotopy directly
on integer-indexed submodule families, without flattening the total module's basis.
-/

namespace BPFixedPoints.ResolutionTools

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def Shifts (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (k : ℤ)
    (f : M →ₗ[R] N) : Prop := ∀ n x, x ∈ F n → f x ∈ G (n + k)

namespace Shifts

variable {F : ℤ → Submodule R M} {G : ℤ → Submodule R N} {H : ℤ → Submodule R P}
  {k l : ℤ} {f f' : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem zero : Shifts F G k (0 : M →ₗ[R] N) := by
  intro n x hx
  exact (G (n + k)).zero_mem

theorem id : Shifts F F 0 LinearMap.id := by
  intro n x hx
  simpa only [LinearMap.id_apply, add_zero] using hx

theorem add (hf : Shifts F G k f) (hf' : Shifts F G k f') : Shifts F G k (f + f') := by
  intro n x hx
  exact (G (n + k)).add_mem (hf n x hx) (hf' n x hx)

theorem neg (hf : Shifts F G k f) : Shifts F G k (-f) := by
  intro n x hx
  exact (G (n + k)).neg_mem (hf n x hx)

theorem sub (hf : Shifts F G k f) (hf' : Shifts F G k f') : Shifts F G k (f - f') := by
  intro n x hx
  exact (G (n + k)).sub_mem (hf n x hx) (hf' n x hx)

theorem comp (hg : Shifts G H l g) (hf : Shifts F G k f) : Shifts F H (k + l) (g.comp f) := by
  intro n x hx
  simpa only [LinearMap.comp_apply, add_assoc] using hg (n + k) (f x) (hf n x hx)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → M →ₗ[R] N)
    (hf : ∀ i ∈ s, Shifts F G k (f i)) : Shifts F G k (∑ i ∈ s, f i) := by
  intro n x hx
  rw [LinearMap.sum_apply]
  exact (G (n + k)).sum_mem fun i hi => hf i hi n x hx

theorem pow_zero {f : Module.End R M} (hf : Shifts F F 0 f) (n : ℕ) :
    Shifts F F 0 (f ^ n) := by
  induction n with
  | zero => exact Shifts.id
  | succ n ih => rw [pow_succ]; exact ih.comp hf

/-- Repeated composition adds degree shifts. -/
theorem pow {f : Module.End R M} (hf : Shifts F F k f) (n : ℕ) :
    Shifts F F ((n : ℤ) * k) (f ^ n) := by
  induction n with
  | zero => simpa only [_root_.pow_zero, Module.End.one_eq_id, Nat.cast_zero, zero_mul] using (Shifts.id (F := F))
  | succ n ih =>
    rw [pow_succ]
    have h := ih.comp hf
    have hk : k + (n : ℤ) * k = ((n + 1 : ℕ) : ℤ) * k := by push_cast; ring
    rw [hk] at h
    exact h

theorem inverse_one_add {f : Module.End R M} (hf : Shifts F F 0 f)
    (hn : IsNilpotent f) : Shifts F F 0 (Ring.inverse (1 + f)) := by
  obtain ⟨n, hn⟩ := hn
  rw [IncidencePerturbation.inverse_one_add_eq_sum f n hn]
  exact Shifts.sum _ _ fun k _ => hf.neg.pow_zero k

/-- If the graded piece containing a homogeneous image is zero, the image is zero. -/
theorem eq_zero_of_eq_bot (hf : Shifts F G k f) {n : ℤ} {x : M}
    (hx : x ∈ F n) (hG : G (n + k) = ⊥) : f x = 0 := by
  have h := hf n x hx
  rw [hG] at h
  exact h

/-- Restriction of scalars preserves underlying sets of graded pieces. -/
theorem restrictScalars {K : Type*} [CommRing K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module K N] [IsScalarTower K R N]
    (hf : Shifts F G k f) :
    Shifts (fun n => (F n).restrictScalars K) (fun n => (G n).restrictScalars K)
      k (f.restrictScalars K) := by
  intro n x hx
  exact hf n x hx

end Shifts

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.IncidencePerturbation

open ResolutionTools

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

theorem correction_shifts (F : ℤ → Submodule R M) (δ h : Module.End R M)
    (hδ : Shifts F F (-1) δ) (hh : Shifts F F 1 h)
    (hn : IsNilpotent (δ * h)) : Shifts F F (-1) (correction δ h) := by
  have hδh : Shifts F F 0 (δ * h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using hδ.comp hh
  simpa only [correction, Module.End.mul_eq_comp, add_zero] using
    (hδh.inverse_one_add hn).comp hδ

namespace Contraction

variable (C : Contraction R M H) (δ : Module.End R M)
  (F : ℤ → Submodule R M) (G : ℤ → Submodule R H)
  (hδ : Shifts F F (-1) δ) (hh : Shifts F F 1 C.h)
  (hi : Shifts G F 0 C.i) (hp : Shifts F G 0 C.p)
  (hn : IsNilpotent (δ * C.h))

include hδ hh hi hp hn in
theorem transfer_shifts : Shifts G G (-1) (C.transfer δ) := by
  simpa only [transfer, zero_add, add_zero] using
    hp.comp ((correction_shifts F δ C.h hδ hh hn).comp hi)

include hδ hh hi hn in
theorem inclusion_shifts : Shifts G F 0 (C.inclusion δ) := by
  have ha := correction_shifts F δ C.h hδ hh hn
  have hha : Shifts F F 0 (C.h * correction δ C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using hh.comp ha
  simpa only [inclusion, add_zero, Module.End.one_eq_id] using (Shifts.id.sub hha).comp hi

include hδ hh hp hn in
theorem projection_shifts : Shifts F G 0 (C.projection δ) := by
  have ha := correction_shifts F δ C.h hδ hh hn
  have hah : Shifts F F 0 (correction δ C.h * C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using ha.comp hh
  simpa only [projection, add_zero, Module.End.one_eq_id] using hp.comp (Shifts.id.sub hah)

include hδ hh hn in
theorem contractingHomotopy_shifts : Shifts F F 1 (C.contractingHomotopy δ) := by
  have ha := correction_shifts F δ C.h hδ hh hn
  have hhh : Shifts F F 1 (C.h * correction δ C.h * C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using (hh.comp ha).comp hh
  exact hh.sub hhh

end Contraction

end BPFixedPoints.IncidencePerturbation
