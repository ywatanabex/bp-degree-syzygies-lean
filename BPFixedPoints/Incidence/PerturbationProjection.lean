import BPFixedPoints.Incidence.Perturbation

/-! # Simplification when perturbation vanishes between projection and homotopy -/

namespace BPFixedPoints.IncidencePerturbation.Contraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : Contraction R M H) (δ : Module.End R M)
  (hu : IsUnit (1 + δ * C.h))
  (hpδh : C.p.comp (δ.comp C.h) = 0)

include hu hpδh in
theorem projection_correction_eq : C.p.comp (correction δ C.h) = C.p.comp δ := by
  have hz : C.p.comp (δ * C.h * correction δ C.h) = 0 := by
    change (C.p.comp (δ.comp C.h)).comp (correction δ C.h) = 0
    rw [hpδh, LinearMap.zero_comp]
  have he := congrArg (fun f : Module.End R M => C.p.comp f)
    (correction_eq_add_left δ C.h hu)
  simpa only [LinearMap.comp_add, hz, add_zero] using he

include hu hpδh in
theorem projection_eq_of_perturbation_homotopy_zero : C.projection δ = C.p := by
  unfold projection
  rw [LinearMap.comp_sub]
  change C.p - C.p.comp ((correction δ C.h).comp C.h) = C.p
  rw [← LinearMap.comp_assoc, C.projection_correction_eq δ hu hpδh,
    LinearMap.comp_assoc, hpδh, sub_zero]

include hu hpδh in
theorem transfer_eq_of_perturbation_homotopy_zero :
    C.transfer δ = C.p.comp (δ.comp C.i) := by
  unfold transfer
  rw [← LinearMap.comp_assoc, C.projection_correction_eq δ hu hpδh,
    LinearMap.comp_assoc]

end BPFixedPoints.IncidencePerturbation.Contraction
