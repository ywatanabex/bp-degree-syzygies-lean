import BPFixedPoints.Incidence.ResolutionHomogeneous
import BPFixedPoints.Incidence.FiniteFiltration

/-!
# Integer degrees preserved by finite homological perturbation

Express the corrected inverse as a finite geometric series to derive degrees
of the transferred differential, chain equivalences and homotopy.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp

variable {R A B : Type*} [CommRing R]

namespace HasDegree

theorem inverse_one_add {da : A → ℤ} {f : Module.End R (A →₀ R)}
    (hf : HasDegree da da 0 f) (hn : IsNilpotent f) :
    HasDegree da da 0 (Ring.inverse (1 + f)) := by
  obtain ⟨n, hn⟩ := hn
  rw [IncidencePerturbation.inverse_one_add_eq_sum f n hn]
  exact HasDegree.sum _ _ (fun k _ => hf.neg.pow_zero k)

end HasDegree

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.IncidencePerturbation

open ResolutionTools

variable {R A B : Type*} [CommRing R]

theorem correction_hasDegree {degree : A → ℤ} (δ h : Module.End R (A →₀ R))
    (hδ : HasDegree degree degree (-1) δ) (hh : HasDegree degree degree 1 h)
    (hn : IsNilpotent (δ * h)) : HasDegree degree degree (-1) (correction δ h) := by
  have hδh : HasDegree degree degree 0 (δ * h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using hδ.comp hh
  simpa only [correction, Module.End.mul_eq_comp, add_zero] using
    (hδh.inverse_one_add hn).comp hδ

namespace Contraction

variable (C : Contraction R (A →₀ R) (B →₀ R))
  (δ : Module.End R (A →₀ R)) (da : A → ℤ) (db : B → ℤ)
  (hδ : HasDegree da da (-1) δ) (hh : HasDegree da da 1 C.h)
  (hi : HasDegree db da 0 C.i) (hp : HasDegree da db 0 C.p)
  (hn : IsNilpotent (δ * C.h))

include hδ hh hi hp hn in
theorem transfer_hasDegree : HasDegree db db (-1) (C.transfer δ) := by
  simpa only [transfer, zero_add, add_zero] using
    hp.comp ((correction_hasDegree δ C.h hδ hh hn).comp hi)

include hδ hh hi hn in
theorem inclusion_hasDegree : HasDegree db da 0 (C.inclusion δ) := by
  have ha := correction_hasDegree δ C.h hδ hh hn
  have hha : HasDegree da da 0 (C.h * correction δ C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using hh.comp ha
  simpa only [inclusion, add_zero, Module.End.one_eq_id] using ((HasDegree.id da).sub hha).comp hi

include hδ hh hp hn in
theorem projection_hasDegree : HasDegree da db 0 (C.projection δ) := by
  have ha := correction_hasDegree δ C.h hδ hh hn
  have hah : HasDegree da da 0 (correction δ C.h * C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using ha.comp hh
  simpa only [projection, add_zero, Module.End.one_eq_id] using hp.comp ((HasDegree.id da).sub hah)

include hδ hh hn in
theorem contractingHomotopy_hasDegree :
    HasDegree da da 1 (C.contractingHomotopy δ) := by
  have ha := correction_hasDegree δ C.h hδ hh hn
  have hhh : HasDegree da da 1 (C.h * correction δ C.h * C.h) := by
    simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using (hh.comp ha).comp hh
  exact hh.sub hhh

end Contraction

end BPFixedPoints.IncidencePerturbation
