import BPFixedPoints.Incidence.DimensionTools
import Mathlib.RingTheory.KrullDimension.Module

/-! # Support dimension of a finite algebra as a coefficient module -/

namespace BPFixedPoints.ResolutionTools
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]

/-- The support dimension of a finite algebra equals the algebra's own Krull dimension. -/
theorem supportDim_finite_algebra : Module.supportDim R A = ringKrullDim A := by
  let f := algebraMap R A
  have hann : Module.annihilator R A = RingHom.ker f := by
    ext r
    rw [Module.mem_annihilator, RingHom.mem_ker]
    constructor
    · intro h
      simpa only [Algebra.smul_def, mul_one] using h 1
    · intro h x
      simp only [Algebra.smul_def, show algebraMap R A r = 0 from h, zero_mul]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, hann]
  let Q := R ⧸ RingHom.ker f
  letI : Algebra Q A := (RingHom.kerLift f).toAlgebra
  haveI : IsScalarTower R Q A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral Q A := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  exact (ringKrullDim_eq_of_integral_injective (RingHom.kerLift_injective f)).symm

end BPFixedPoints.ResolutionTools
