import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The Zariski topology on coefficient tuples -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial
open scoped Topology

variable {k σ : Type*} [Field k]

/-- A coefficient tuple determines the prime ideal of polynomials vanishing there. -/
noncomputable def parameterPrime (a : σ → k) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨RingHom.ker (eval a), RingHom.ker_isPrime (eval a)⟩

/-- Pull back the spectrum topology to rational points of affine coefficient space.
The topology is explicit to avoid replacing any existing topology on the base field. -/
@[instance_reducible]
noncomputable def parameterZariskiTopology : TopologicalSpace (σ → k) :=
  TopologicalSpace.induced parameterPrime inferInstance

theorem isOpen_parameter_nonvanishing (P : MvPolynomial σ k) :
    IsOpen[parameterZariskiTopology] {a : σ → k | eval a P ≠ 0} := by
  exact isOpen_induced (PrimeSpectrum.basicOpen P).isOpen

end BPFixedPoints.ResolutionTools
