import BPFixedPoints.Incidence.ResolutionMapComparison
import BPFixedPoints.Incidence.GradedTripleProduct
import BPFixedPoints.Incidence.TorProductCoordinates

/-!
# Associativity of the standard Tor product

Both parenthesizations on the triple tensor complex lift the same triple
multiplication in the original ring. Homotopy comparison for projective terms
and minimality make them agree after specialization.
-/
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph
open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance resolutionTorAssociativityOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

noncomputable abbrev incTripleDifferential :=
  tripleD G.incResolutionDegree G.incResolutionDifferential

theorem incTripleDifferential_degree :
    HasDegree (fun a => (tripleDegree G.incResolutionDegree a : ℤ))
      (fun a => (tripleDegree G.incResolutionDegree a : ℤ)) (-1) G.incTripleDifferential :=
  mixedTensorD_degree _ _ _ _
    (gradedTensorD_degree _ _ G.incResolutionDifferential_hasDegree)
    G.incResolutionDifferential_hasDegree

theorem incTripleDifferential_sq : G.incTripleDifferential * G.incTripleDifferential = 0 :=
  mixedTensorD_sq _ _ _ (gradedTensorD_degree _ _ G.incResolutionDifferential_hasDegree)
    (gradedTensorD_sq _ _ G.incResolutionDifferential_hasDegree G.incResolutionDifferential_sq)
    G.incResolutionDifferential_sq

theorem incTripleDifferential_minimal (x) :
    G.incTripleDifferential x ∈ incCoeffAugmentationIdeal E •
      (⊤ : Submodule (IncCoeffRing E) ((G.IncResolutionBasis × G.IncResolutionBasis) ×
        G.IncResolutionBasis →₀ IncCoeffRing E)) :=
  mixedTensorD_minimal _ _ _ (incCoeffAugmentationIdeal E)
    (gradedTensorD_minimal _ _ (incCoeffAugmentationIdeal E) G.incResolutionDifferential_minimal)
    G.incResolutionDifferential_minimal x

namespace IncResolutionMultiplication
variable {G} (μ : G.IncResolutionMultiplication)

theorem triple_augmentation_eq
    (x : gradedPiece (IncCoeffRing E) (tripleDegree G.incResolutionDegree) 0) :
    G.incResolutionTorusAugmentation (μ.toGradedFreePairing.tripleLeft x.val) =
      G.incResolutionTorusAugmentation (μ.toGradedFreePairing.tripleRight x.val) := by
  rw [← x.val.sum_single]
  simp only [map_finsuppSum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨⟨a,b⟩,c⟩ habc
  rw [← freeTriple_single a b c _, GradedFreePairing.tripleLeft_triple,
    GradedFreePairing.tripleRight_triple]
  have hdeg := (mem_supported (IncCoeffRing E) x.val).mp x.property habc
  change G.incResolutionDegree a + G.incResolutionDegree b + G.incResolutionDegree c = 0 at hdeg
  have ha : G.incResolutionDegree a = 0 := by omega
  have hb : G.incResolutionDegree b = 0 := by omega
  have hc : G.incResolutionDegree c = 0 := by omega
  have hA : single a (1 : IncCoeffRing E) ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 := single_mem_supported _ _ ha
  have hB : single b (1 : IncCoeffRing E) ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 := single_mem_supported _ _ hb
  have hC : single c (x.val ((a,b),c)) ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 := single_mem_supported _ _ hc
  rw [μ.augmentation _ _ (μ.homogeneous 0 0 hA hB) hC,
    μ.augmentation _ _ hA (μ.homogeneous 0 0 hB hC),
    μ.augmentation _ _ hA hB, μ.augmentation _ _ hB hC, mul_assoc]

theorem assoc_atOrigin (p q r : ℕ)
    (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) (z : G.IncFreeTerm r) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul (μ.mul x.val y.val) z.val =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] μ.mul x.val (μ.mul y.val z.val) := by
  have h := G.incResolutionMap_atOrigin (tripleDegree G.incResolutionDegree)
    G.incTripleDifferential G.incTripleDifferential_degree G.incTripleDifferential_sq
    μ.toGradedFreePairing.tripleLeft μ.toGradedFreePairing.tripleRight
    μ.toGradedFreePairing.tripleLeft_degree μ.toGradedFreePairing.tripleRight_degree
    μ.toGradedFreePairing.tripleLeft_chain μ.toGradedFreePairing.tripleRight_chain
    G.incTripleDifferential_minimal μ.triple_augmentation_eq
    (p + q + r) ⟨freeTriple x.val y.val z.val,
      freeTriple_degree G.incResolutionDegree p q r x.property y.property z.property⟩
  simpa only [GradedFreePairing.tripleLeft_triple, GradedFreePairing.tripleRight_triple] using h

end IncResolutionMultiplication

theorem incidenceTorProduct_assoc (p q r : ℕ)
    (x : G.incidenceTor p) (y : G.incidenceTor q) (z : G.incidenceTor r) :
    G.incidenceTorCast (Nat.add_assoc p q r)
      (G.incidenceTorProduct (p + q) r (G.incidenceTorProduct p q x y) z) =
    G.incidenceTorProduct p (q + r) x (G.incidenceTorProduct q r y z) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  obtain ⟨y, rfl⟩ := G.incFreeTermToTor_surjective q y
  obtain ⟨z, rfl⟩ := G.incFreeTermToTor_surjective r z
  apply G.incidenceTorToFull_injective (p + (q + r))
  rw [G.incidenceTorToFull_cast]
  simp only [G.incidenceTorProduct_eq_transferred, G.incidenceTorToFull_class]
  exact G.incResolutionMultiplication.assoc_atOrigin p q r x y z

end BPFixedPoints.Multigraph
