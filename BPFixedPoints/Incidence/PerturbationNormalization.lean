import BPFixedPoints.Incidence.Perturbation

/-!
# Normalize contraction homotopies

Replace the homotopy of a weak deformation retract by qhq and then
(qhq)d(qhq) to obtain the three side conditions required for finite perturbation.
-/

namespace BPFixedPoints.IncidencePerturbation

section Ring

variable {A : Type*} [Ring A]

theorem projected_homotopy (d h q : A)
    (hqd : q * d = d) (hdq : d * q = d) (hqq : q * q = q)
    (hc : d * h + h * d = q) :
    d * (q * h * q) + (q * h * q) * d = q := by
  calc
    d * (q * h * q) + (q * h * q) * d = q * (d * h + h * d) * q := by
      linear_combination (norm := noncomm_ring)
        (hdq - hqd) * h * q + q * h * (hqd - hdq)
    _ = q := by rw [hc, hqq, hqq]

theorem normalized_homotopy (d h q : A)
    (hd : d * d = 0) (hqd : q * d = d)
    (hc : d * h + h * d = q) :
    d * (h * d * h) + (h * d * h) * d = q := by
  have hdh : d * h * d = d := by
    linear_combination (norm := noncomm_ring) hc * d - h * hd + hqd
  calc
    d * (h * d * h) + (h * d * h) * d =
        (d * h * d) * h + h * (d * h * d) := by noncomm_ring
    _ = q := by rw [hdh, hc]

theorem normalized_homotopy_square (d h q : A)
    (hd : d * d = 0) (hqh : q * h = h) (hhq : h * q = h)
    (hc : d * h + h * d = q) :
    (h * d * h) * (h * d * h) = 0 := by
  have hcomm : d * h * h = h * h * d := by
    linear_combination (norm := noncomm_ring) hc * h - h * hc + hqh - hhq
  calc
    (h * d * h) * (h * d * h) = h * (d * h * h) * d * h := by noncomm_ring
    _ = h * (h * h * d) * d * h := by rw [hcomm]
    _ = h * h * h * (d * d) * h := by noncomm_ring
    _ = 0 := by rw [hd]; simp

end Ring

namespace Contraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

/-- Normalize a weak deformation retract to a strong contraction satisfying the side conditions. -/
noncomputable def ofHomotopy
    (d : Module.End R M) (i : H →ₗ[R] M) (p : M →ₗ[R] H)
    (h : Module.End R M)
    (hd : d * d = 0) (hdi : d.comp i = 0) (hpd : p.comp d = 0)
    (hpi : p.comp i = LinearMap.id)
    (hc : d * h + h * d + i.comp p = 1) : Contraction R M H := by
  let e : Module.End R M := i.comp p
  let q : Module.End R M := 1 - e
  let h₀ : Module.End R M := q * h * q
  have hee : e * e = e := by
    dsimp [e]
    rw [Module.End.mul_eq_comp, LinearMap.comp_assoc,
      ← LinearMap.comp_assoc p i, hpi, LinearMap.id_comp]
  have hde : d * e = 0 := by
    dsimp [e]
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hdi, LinearMap.zero_comp]
  have hed : e * d = 0 := by
    dsimp [e]
    rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, hpd, LinearMap.comp_zero]
  have hqd : q * d = d := by simp [q, sub_mul, hed]
  have hdq : d * q = d := by simp [q, mul_sub, hde]
  have hqq : q * q = q := by
    dsimp [q]
    linear_combination (norm := noncomm_ring) hee
  have hch : d * h + h * d = q := by
    dsimp [q, e]
    exact eq_sub_of_add_eq hc
  have hc₀ : d * h₀ + h₀ * d = q :=
    projected_homotopy d h q hqd hdq hqq hch
  have hqh : q * h₀ = h₀ := by
    dsimp [h₀]
    calc
      q * (q * h * q) = (q * q) * h * q := by noncomm_ring
      _ = q * h * q := by rw [hqq]
  have hhq : h₀ * q = h₀ := by
    dsimp [h₀]
    rw [mul_assoc, hqq]
  have hqi : q.comp i = 0 := by
    simp only [q, e, Module.End.one_eq_id, LinearMap.sub_comp, LinearMap.id_comp,
      LinearMap.comp_assoc, hpi, LinearMap.comp_id, sub_self]
  have hpq : p.comp q = 0 := by
    simp only [q, e, Module.End.one_eq_id, LinearMap.comp_sub, LinearMap.comp_id,
      ← LinearMap.comp_assoc, hpi, LinearMap.id_comp, sub_self]
  have hh₀i : h₀.comp i = 0 := by
    dsimp [h₀]
    rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, hqi, LinearMap.comp_zero]
  have hph₀ : p.comp h₀ = 0 := by
    dsimp [h₀]
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hpq, LinearMap.zero_comp,
      LinearMap.zero_comp]
  exact
    { d := d
      i := i
      p := p
      h := h₀ * d * h₀
      d_sq := hd
      d_i := hdi
      p_d := hpd
      p_i := hpi
      homotopy := by
        rw [normalized_homotopy d h₀ q hd hqd hc₀]
        simp [q, e]
      h_sq := normalized_homotopy_square d h₀ q hd hqh hhq hc₀
      h_i := by
        rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, hh₀i, LinearMap.comp_zero]
      p_h := by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
          Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hph₀, LinearMap.zero_comp,
          LinearMap.zero_comp] }

variable (d : Module.End R M) (i : H →ₗ[R] M) (p : M →ₗ[R] H)
  (h : Module.End R M)
  (hd : d * d = 0) (hdi : d.comp i = 0) (hpd : p.comp d = 0)
  (hpi : p.comp i = LinearMap.id)
  (hc : d * h + h * d + i.comp p = 1)

@[simp] theorem ofHomotopy_d : (ofHomotopy d i p h hd hdi hpd hpi hc).d = d := rfl

@[simp] theorem ofHomotopy_i : (ofHomotopy d i p h hd hdi hpd hpi hc).i = i := rfl

@[simp] theorem ofHomotopy_p : (ofHomotopy d i p h hd hdi hpd hpi hc).p = p := rfl

theorem ofHomotopy_h :
    (ofHomotopy d i p h hd hdi hpd hpi hc).h =
      ((1 - i.comp p) * h * (1 - i.comp p)) * d *
        ((1 - i.comp p) * h * (1 - i.comp p)) := rfl

end Contraction

end BPFixedPoints.IncidencePerturbation
