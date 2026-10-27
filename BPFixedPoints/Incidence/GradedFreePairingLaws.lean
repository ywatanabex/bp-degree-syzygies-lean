import BPFixedPoints.Incidence.GradedFreePairing
import BPFixedPoints.Incidence.GradedParityLaws

namespace BPFixedPoints.ResolutionTools
open Finsupp
universe u
variable {R A : Type u} [CommRing R] {degree : A → ℕ} {D : Module.End R (A →₀ R)}
namespace GradedFreePairing
variable (μ : GradedFreePairing degree D)

noncomputable def rightMul (y : A →₀ R) : Module.End R (A →₀ R) := μ.mul.flip y

@[simp] theorem rightMul_apply (x y : A →₀ R) : μ.rightMul y x = μ.mul x y := rfl

end GradedFreePairing
end BPFixedPoints.ResolutionTools
