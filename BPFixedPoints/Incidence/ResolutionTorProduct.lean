import BPFixedPoints.Incidence.ResolutionMultiplication
import BPFixedPoints.Incidence.GradedTensorSpecialization
import BPFixedPoints.Incidence.ResolutionTorGrading
import BPFixedPoints.Incidence.PerturbationProductSpecialization

/-!
# Identify the standard Tor product with the exterior Čech product

Specialize chain maps on the resolution lifting multiplication in the original
incidence ring, then transfer to Mathlib's actual left derived functor.
All lifts of the same multiplication give the same result.
-/

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

namespace IncResolutionMultiplication

variable {G} (μ : G.IncResolutionMultiplication)

/-- Action of a multiplication lift through the derived-specialization comparison. -/
noncomputable def torProduct (p q : ℕ) :
    G.incidenceTor p →ₗ[ℂ] G.incidenceTor q →ₗ[ℂ] G.incidenceTor (p + q) :=
  ((specializedGradedPair (k := ℂ) G.incResolutionDegree p q).compl₁₂
    (G.incidenceTorIsoFreeTerm p).hom.hom (G.incidenceTorIsoFreeTerm q).hom.hom).compr₂
      ((G.incidenceTorIsoFreeTerm (p + q)).inv.hom.comp
        (((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
          (μ.chainMap.f (p + q))).hom))

/-- Standard Tor product independent of the multiplication lift. -/
theorem torProduct_eq (ν : G.IncResolutionMultiplication) (p q : ℕ) :
    μ.torProduct p q = ν.torProduct p q := by
  unfold torProduct
  rw [μ.specialized_chainMap_eq ν (p + q)]

theorem torProduct_on_classes (p q : ℕ) (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    μ.torProduct p q (G.incFreeTermToTor p x) (G.incFreeTermToTor q y) =
      G.incFreeTermToTor (p + q)
        ⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩ := by
  apply (G.incidenceTorIsoFreeTerm (p + q)).toLinearEquiv.injective
  change (G.incidenceTorIsoFreeTerm (p + q)).hom
    ((G.incidenceTorIsoFreeTerm (p + q)).inv
      (((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
        (μ.chainMap.f (p + q)))
        (specializedGradedPair (R := IncCoeffRing E) (k := ℂ) G.incResolutionDegree p q
          ((G.incidenceTorIsoFreeTerm p).hom (G.incFreeTermToTor p x))
          ((G.incidenceTorIsoFreeTerm q).hom (G.incFreeTermToTor q y))))) = _
  rw [G.incFreeTermToTor_eq_tmul, G.incFreeTermToTor_eq_tmul,
    specializedGradedPair_tmul, one_mul]
  change (G.incidenceTorIsoFreeTerm (p + q)).toLinearEquiv
      ((G.incidenceTorIsoFreeTerm (p + q)).toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change (1 : ℂ) ⊗ₜ[IncCoeffRing E]
    μ.toGradedFreePairing.component (p + q)
      ⟨freePair x.val y.val, freePair_degree _ p q x.property y.property⟩ =
    (G.incidenceTorIsoFreeTerm (p + q)).hom (G.incFreeTermToTor (p + q)
      ⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩)
  rw [G.incFreeTermToTor_eq_tmul]
  congr 1
  apply Subtype.ext
  exact μ.toGradedFreePairing.linearize_tmul x.val y.val

end IncResolutionMultiplication

/-- Choose any multiplication lift; later theorems show the choice does not affect the product. -/
noncomputable def incidenceStandardMultiplication : G.IncResolutionMultiplication :=
  Classical.choice ⟨G.incResolutionMultiplication⟩

/-- Standard product on actual derived specialization determined by original ring multiplication. -/
noncomputable def incidenceTorProduct (p q : ℕ) :
    G.incidenceTor p →ₗ[ℂ] G.incidenceTor q →ₗ[ℂ] G.incidenceTor (p + q) :=
  G.incidenceStandardMultiplication.torProduct p q

theorem incidenceTorProduct_eq_of_lift (μ : G.IncResolutionMultiplication) (p q : ℕ) :
    G.incidenceTorProduct p q = μ.torProduct p q :=
  G.incidenceStandardMultiplication.torProduct_eq μ p q

/-- The concrete transferred exterior Čech product equals the standard Tor product. -/
theorem incidenceTorProduct_eq_transferred (p q : ℕ)
    (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    G.incidenceTorProduct p q (G.incFreeTermToTor p x) (G.incFreeTermToTor q y) =
      G.incFreeTermToTor (p + q)
        ⟨G.incResolutionCup x.val y.val, G.incResolutionCup_degree p q x.property y.property⟩ := by
  rw [G.incidenceTorProduct_eq_of_lift G.incResolutionMultiplication]
  exact G.incResolutionMultiplication.torProduct_on_classes p q x y

/-- Canonical inclusion into the resolution's full free module, used for product comparison. -/
noncomputable def incidenceTorToFull (p : ℕ) :
    G.incidenceTor p →ₗ[ℂ] ℂ ⊗[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  ((gradedPiece (IncCoeffRing E) G.incResolutionDegree p).subtype.baseChange ℂ).comp
    (G.incidenceTorIsoFreeTerm p).hom.hom

theorem incidenceTorToFull_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceTorToFull p (G.incFreeTermToTor p x) = (1 : ℂ) ⊗ₜ[IncCoeffRing E] x.val := by
  change ((gradedPiece (IncCoeffRing E) G.incResolutionDegree p).subtype.baseChange ℂ)
    ((G.incidenceTorIsoFreeTerm p).hom (G.incFreeTermToTor p x)) = _
  rw [G.incFreeTermToTor_eq_tmul, LinearMap.baseChange_tmul]
  rfl

theorem incidenceTorToFull_injective (p : ℕ) : Function.Injective (G.incidenceTorToFull p) := by
  let j := (gradedPiece (IncCoeffRing E) G.incResolutionDegree p).subtype.baseChange ℂ
  let r := (Finsupp.restrictDom (IncCoeffRing E) (IncCoeffRing E)
    {b | G.incResolutionDegree b = p}).baseChange ℂ
  have hr : r.comp j = LinearMap.id := by
    have hbase : (Finsupp.restrictDom (IncCoeffRing E) (IncCoeffRing E)
        {b | G.incResolutionDegree b = p}).comp
          (gradedPiece (IncCoeffRing E) G.incResolutionDegree p).subtype = LinearMap.id :=
      Finsupp.restrictDom_comp_subtype _
    rw [show r.comp j = ((Finsupp.restrictDom (IncCoeffRing E) (IncCoeffRing E)
      {b | G.incResolutionDegree b = p}).comp
        (gradedPiece (IncCoeffRing E) G.incResolutionDegree p).subtype).baseChange ℂ from
          (LinearMap.baseChange_comp _ _).symm,
      hbase, LinearMap.baseChange_id]
  have hj : Function.Injective j :=
    Function.LeftInverse.injective (fun z => LinearMap.congr_fun hr z)
  exact hj.comp (G.incidenceTorIsoFreeTerm p).toLinearEquiv.injective

/-- At the origin, standard Tor multiplication equals projection of the uncorrected exterior Čech product. Injectivity of `incidenceTorToFull_injective` makes this formula determine the original Tor class uniquely. -/
theorem incidenceTorProduct_cech_formula (p q : ℕ)
    (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    G.incidenceTorToFull (p + q)
        (G.incidenceTorProduct p q (G.incFreeTermToTor p x) (G.incFreeTermToTor q y)) =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] G.incCechContraction.p
        (G.incTotalCup (G.incCechContraction.i x.val) (G.incCechContraction.i y.val)) := by
  rw [G.incidenceTorProduct_eq_transferred, G.incidenceTorToFull_class]
  exact G.incTransferredPairing_atOrigin G.incTotalCup x.val y.val

end BPFixedPoints.Multigraph
