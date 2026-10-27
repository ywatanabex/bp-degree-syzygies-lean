import Mathlib.RingTheory.Depth.Basic

/-! # Ideal depth depends only on the radical -/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Rees' support criterion identifies the depths of ideals with the same radical. -/
theorem depth_eq_of_radical_eq (I J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) < ⊤) (hJ : J • (⊤ : Submodule R M) < ⊤)
    (h : I.radical = J.radical) : I.depth M = J.depth M := by
  have hne : I ≠ ⊤ := by
    intro ht
    simp [ht] at hI
  haveI : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hne
  let N := ModuleCat.of R (R ⧸ I)
  have hs : Module.support R N = PrimeSpectrum.zeroLocus I := by
    change Module.support R (R ⧸ I) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hs' : Module.support R N = PrimeSpectrum.zeroLocus J :=
    hs.trans (PrimeSpectrum.zeroLocus_eq_iff.mpr h)
  exact (ModuleCat.depth_eq_depth_of_support_eq I N M hI hs).symm.trans
    (ModuleCat.depth_eq_depth_of_support_eq J N M hJ hs')

end BPFixedPoints.ResolutionTools
