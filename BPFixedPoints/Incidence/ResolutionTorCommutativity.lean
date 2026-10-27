import BPFixedPoints.Incidence.GradedOppositeProduct
import BPFixedPoints.Incidence.TorProductCoordinates

/-!
# Graded commutativity of the standard Tor product

The signed opposite product lifts the same multiplication in the original
commutative ring, so the two specialize equally at the origin.
-/
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph
open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)
noncomputable local instance torCommutativityOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

namespace IncResolutionMultiplication
variable {G} (μ : G.IncResolutionMultiplication)

noncomputable def opposite : G.IncResolutionMultiplication where
  toGradedFreePairing := μ.toGradedFreePairing.opposite G.incResolutionDifferential_hasDegree
  augmentation x y hx hy := by
    change G.incResolutionTorusAugmentation (μ.toGradedFreePairing.oppositeMul x y) = _
    rw [μ.toGradedFreePairing.oppositeMul_zero x y hx]
    rw [μ.augmentation _ _ hy hx, mul_comm]

theorem comm_atOrigin (p q : ℕ) (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul x.val y.val =
      (-1 : ℂ) ^ (p * q) • ((1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul y.val x.val) := by
  have h := congrArg (fun f => G.incidenceTorToFull (p + q)
    (f (G.incFreeTermToTor p x) (G.incFreeTermToTor q y))) (μ.torProduct_eq μ.opposite p q)
  simp only [torProduct_on_classes, G.incidenceTorToFull_class] at h
  change (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul x.val y.val =
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.toGradedFreePairing.oppositeMul x.val y.val at h
  exact h.trans (μ.toGradedFreePairing.oppositeMul_baseChange p q x.property y.property)

end IncResolutionMultiplication

theorem incidenceTorProduct_graded_comm (p q : ℕ)
    (x : G.incidenceTor p) (y : G.incidenceTor q) :
    G.incidenceTorCast (Nat.add_comm p q) (G.incidenceTorProduct p q x y) =
      (-1 : ℂ) ^ (p * q) • G.incidenceTorProduct q p y x := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  obtain ⟨y, rfl⟩ := G.incFreeTermToTor_surjective q y
  apply G.incidenceTorToFull_injective (q + p)
  rw [G.incidenceTorToFull_cast, map_smul]
  simp only [G.incidenceTorProduct_eq_transferred, G.incidenceTorToFull_class]
  exact G.incResolutionMultiplication.comm_atOrigin p q x y

end BPFixedPoints.Multigraph
