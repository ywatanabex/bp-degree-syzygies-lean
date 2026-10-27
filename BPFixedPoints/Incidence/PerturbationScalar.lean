import BPFixedPoints.Incidence.Perturbation

/-! # Simultaneous sign change of differential and homotopy -/

namespace BPFixedPoints.IncidencePerturbation.Contraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

/-- Multiply both differential and homotopy by a scalar of square one. -/
noncomputable def smulInvolution (C : Contraction R M H) (a : R) (ha : a * a = 1) :
    Contraction R M H where
  d := a • C.d
  i := C.i
  p := C.p
  h := a • C.h
  d_sq := by
    apply LinearMap.ext
    intro x
    change a • C.d (a • C.d x) = 0
    rw [map_smul, smul_smul, ha, one_smul]
    exact LinearMap.congr_fun C.d_sq x
  d_i := by
    apply LinearMap.ext
    intro x
    change a • C.d (C.i x) = 0
    have hh := LinearMap.congr_fun C.d_i x
    change C.d (C.i x) = 0 at hh
    rw [hh, smul_zero]
  p_d := by
    apply LinearMap.ext
    intro x
    change C.p (a • C.d x) = 0
    rw [map_smul]
    have hh := LinearMap.congr_fun C.p_d x
    change C.p (C.d x) = 0 at hh
    rw [hh, smul_zero]
  p_i := C.p_i
  homotopy := by
    apply LinearMap.ext
    intro x
    change a • C.d (a • C.h x) + a • C.h (a • C.d x) + C.i (C.p x) = x
    simp only [map_smul, smul_smul, ha, one_smul]
    exact LinearMap.congr_fun C.homotopy x
  h_sq := by
    apply LinearMap.ext
    intro x
    change a • C.h (a • C.h x) = 0
    rw [map_smul, smul_smul, ha, one_smul]
    exact LinearMap.congr_fun C.h_sq x
  h_i := by
    apply LinearMap.ext
    intro x
    change a • C.h (C.i x) = 0
    have hh := LinearMap.congr_fun C.h_i x
    change C.h (C.i x) = 0 at hh
    rw [hh, smul_zero]
  p_h := by
    apply LinearMap.ext
    intro x
    change C.p (a • C.h x) = 0
    rw [map_smul]
    have hh := LinearMap.congr_fun C.p_h x
    change C.p (C.h x) = 0 at hh
    rw [hh, smul_zero]

end BPFixedPoints.IncidencePerturbation.Contraction
