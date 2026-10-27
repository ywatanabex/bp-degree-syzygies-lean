import BPFixedPoints.Incidence.ResolutionEndomorphismComparison
import BPFixedPoints.Incidence.GradedFreePairingLaws

/-!
# Unit of the actual Tor product

Lift 1 from the original incidence ring. Homotopy comparison of augmentation-preserving
chain maps with the identity yields both unit laws.
-/

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph
open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance resolutionTorUnitOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

noncomputable def incResolutionUnit : G.IncFreeTerm 0 :=
  Classical.choose (G.incResolutionAugmentation_surjective 1)

theorem incResolutionUnit_augmentation :
    G.incResolutionTorusAugmentation G.incResolutionUnit.val = 1 :=
  congrArg Subtype.val (Classical.choose_spec (G.incResolutionAugmentation_surjective 1))

noncomputable def incidenceTorOne : G.incidenceTor 0 :=
  G.incFreeTermToTor 0 G.incResolutionUnit

namespace IncResolutionMultiplication
variable {G} (μ : G.IncResolutionMultiplication)

theorem unit_left_atOrigin (p : ℕ) (x : G.IncFreeTerm p) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul G.incResolutionUnit.val x.val =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] x.val := by
  refine G.incResolutionEndomorphism_atOrigin (μ.mul G.incResolutionUnit.val) ?_ ?_ ?_ p x
  · intro n y hy
    simpa only [zero_add] using μ.homogeneous 0 n G.incResolutionUnit.property hy
  · intro y
    rw [μ.leibniz, G.incResolutionDifferential_zero_degree _ G.incResolutionUnit.property,
      gradedParity_zero G.incResolutionDegree G.incResolutionUnit.property]
    simp only [pow_zero, one_smul, map_zero, LinearMap.zero_apply, zero_add, add_zero]
  · intro y
    rw [μ.augmentation _ _ G.incResolutionUnit.property y.property,
      G.incResolutionUnit_augmentation, one_mul]

theorem unit_right_atOrigin (p : ℕ) (x : G.IncFreeTerm p) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul x.val G.incResolutionUnit.val =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] x.val := by
  refine G.incResolutionEndomorphism_atOrigin (μ.toGradedFreePairing.rightMul G.incResolutionUnit.val) ?_ ?_ ?_ p x
  · intro n y hy
    exact μ.homogeneous n 0 hy G.incResolutionUnit.property
  · intro y
    change G.incResolutionDifferential (μ.mul y G.incResolutionUnit.val) = _
    rw [μ.leibniz, G.incResolutionDifferential_zero_degree _ G.incResolutionUnit.property]
    simp only [pow_zero, one_smul, map_zero, LinearMap.zero_apply, zero_add, add_zero]
    rfl
  · intro y
    change G.incResolutionTorusAugmentation (μ.mul y.val G.incResolutionUnit.val) = _
    rw [μ.augmentation _ _ y.property G.incResolutionUnit.property,
      G.incResolutionUnit_augmentation, mul_one]

end IncResolutionMultiplication

theorem incidenceTorOne_mul (p : ℕ) (x : G.incidenceTor p) :
    G.incidenceTorCast (Nat.zero_add p) (G.incidenceTorProduct 0 p G.incidenceTorOne x) = x := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  apply G.incidenceTorToFull_injective p
  rw [G.incidenceTorToFull_cast]
  change G.incidenceTorToFull (0 + p)
    (G.incidenceTorProduct 0 p (G.incFreeTermToTor 0 G.incResolutionUnit)
      (G.incFreeTermToTor p x)) = _
  rw [G.incidenceTorProduct_eq_transferred, G.incidenceTorToFull_class,
    G.incidenceTorToFull_class]
  exact G.incResolutionMultiplication.unit_left_atOrigin p x

theorem incidenceTor_mul_one (p : ℕ) (x : G.incidenceTor p) :
    G.incidenceTorProduct p 0 x G.incidenceTorOne = x := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  apply G.incidenceTorToFull_injective p
  change G.incidenceTorToFull (p + 0)
    (G.incidenceTorProduct p 0 (G.incFreeTermToTor p x)
      (G.incFreeTermToTor 0 G.incResolutionUnit)) = _
  rw [G.incidenceTorProduct_eq_transferred, G.incidenceTorToFull_class,
    G.incidenceTorToFull_class]
  exact G.incResolutionMultiplication.unit_right_atOrigin p x

end BPFixedPoints.Multigraph
