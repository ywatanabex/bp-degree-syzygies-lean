import BPFixedPoints.Incidence.ResolutionTorRanks
import BPFixedPoints.Incidence.GradedSpecialization
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Minimal number of generators of the actual incidence module

The zeroth term of the previously constructed *actual* free resolution
surjects onto the incidence module. Minimality of the differential at the
coefficient origin makes the residue vectors of this term descend through
that augmentation. This proves a lower bound for the cardinality of *any*
finite generating family, not merely for a particular state-indexed family.

Together with the obvious generating family supplied by the augmentation,
this identifies the intrinsic minimal generator count with the zeroth row
of the state-sum Betti table.
-/

namespace BPFixedPoints.ResolutionTools

/-- A linear map is constant on each fiber of a map whose kernel it kills. -/
theorem linearMap_eq_of_ker_le
    {R M N P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : M →ₗ[R] P) (h : LinearMap.ker f ≤ LinearMap.ker g)
    (x y : M) (hxy : f x = f y) : g x = g y := by
  apply sub_eq_zero.mp
  rw [← g.map_sub]
  apply LinearMap.mem_ker.mp
  apply h
  change f (x - y) = 0
  rw [f.map_sub, hxy, sub_self]

/-- A surjection from an R-module to a finite-dimensional residue vector
space bounds below the size of any R-generating family. This uses the actual
ring action on the residue vector space, not an assumed dimension formula. -/
theorem card_le_of_generating_family_and_residue_surjection
    {R k M I J : Type*} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup M] [Module R M] [Fintype I] [Fintype J]
    (ψ : M →ₗ[R] (I →₀ k)) (hψ : Function.Surjective ψ)
    (g : J → M) (hg : Submodule.span R (Set.range g) = ⊤) :
    Fintype.card I ≤ Fintype.card J := by
  classical
  let c : (J →₀ k) →ₗ[k] (I →₀ k) :=
    Finsupp.linearCombination k (fun j => ψ (g j))
  have hspan : Submodule.span R (Set.range g) ≤
      Submodule.comap ψ ((LinearMap.range c).restrictScalars R) := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    change ψ (g j) ∈ LinearMap.range c
    refine ⟨Finsupp.single j 1, ?_⟩
    simp [c]
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨m, rfl⟩ := hψ y
    have hm : m ∈ Submodule.span R (Set.range g) := by
      rw [hg]
      trivial
    exact hspan hm
  have hdim := c.finrank_le_finrank_of_surjective hc
  simpa only [Module.finrank_finsupp_self] using hdim

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open ResolutionTools
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance minimalGeneratorsCoefficientAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

noncomputable local instance minimalGeneratorsOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

/-- The images of the zeroth free basis in the actual incidence module. -/
noncomputable def incidenceResolutionGenerators
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) :
    G.IncidenceRing :=
  G.incResolutionAugmentation ((G.incFreeTermBasis 0) b)

/-- These elements actually generate the incidence module over its coefficient ring. -/
theorem incidenceResolutionGenerators_span :
    Submodule.span (IncCoeffRing E) (Set.range G.incidenceResolutionGenerators) = ⊤ := by
  let b := G.incFreeTermBasis 0
  change Submodule.span (IncCoeffRing E)
    (Set.range (fun i => G.incResolutionAugmentation (b i))) = ⊤
  calc
    Submodule.span (IncCoeffRing E)
      (Set.range (fun i => G.incResolutionAugmentation (b i))) =
        (Submodule.span (IncCoeffRing E) (Set.range b)).map
          G.incResolutionAugmentation := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
    _ = ⊤ := by
      rw [b.span_eq, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr G.incResolutionAugmentation_surjective

/-- Evaluation of the zeroth free term at the coefficient origin. -/
noncomputable def incidenceFreeOriginMap :
    G.IncFreeTerm 0 →ₗ[IncCoeffRing E]
      ({b : G.IncResolutionBasis // G.incResolutionDegree b = 0} →₀ ℂ) :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap (IncCoeffRing E) ℂ)).comp
    (G.incFreeTermBasis 0).repr.toLinearMap

/-- The origin evaluation of a free term is surjective, by constant lifts. -/
theorem incidenceFreeOriginMap_surjective :
    Function.Surjective G.incidenceFreeOriginMap := by
  intro y
  refine ⟨(G.incFreeTermBasis 0).repr.symm
    (freeConstantLift (σ := IncCoeffIdx E) y), ?_⟩
  ext i
  simp [incidenceFreeOriginMap, freeConstantLift_apply]
  change MvPolynomial.constantCoeff (MvPolynomial.C (y i)) = y i
  simp

/-- Minimality makes evaluation descend through the zeroth augmentation. -/
theorem incidenceFreeOriginMap_ker :
    LinearMap.ker G.incResolutionAugmentation ≤ LinearMap.ker G.incidenceFreeOriginMap := by
  have hmin : LinearMap.range (G.incFreeTermDifferential 0) ≤
      RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) •
        (⊤ : Submodule (IncCoeffRing E) (G.IncFreeTerm 0)) := by
    exact gradedDifferential_minimal (incCoeffAugmentationIdeal E)
      G.incResolutionDegree G.incResolutionDifferential G.incResolutionDifferential_degree
      G.incResolutionDifferential_minimal 0
  have hzero : RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) •
        (⊤ : Submodule (IncCoeffRing E) (G.IncFreeTerm 0)) ≤
          LinearMap.ker G.incidenceFreeOriginMap := by
    apply Submodule.smul_le.mpr
    intro r hr x _
    change G.incidenceFreeOriginMap (r • x) = 0
    rw [map_smul]
    ext i
    change (MvPolynomial.constantCoeff r) * (G.incidenceFreeOriginMap x i) = 0
    simp [RingHom.mem_ker.mp hr]
  rw [← G.incFreeTermDifferential_augmentation_exact]
  exact hmin.trans hzero

/-- The residue specialization only depends on the image in the actual
incidence module. This is the kernel condition proved above, in equality form. -/
theorem incidenceFreeOriginMap_eq_of_augmentation_eq
    (x y : G.IncFreeTerm 0)
    (hxy : G.incResolutionAugmentation x = G.incResolutionAugmentation y) :
    G.incidenceFreeOriginMap x = G.incidenceFreeOriginMap y := by
  have h := linearMap_eq_of_ker_le (R := IncCoeffRing E) (M := G.IncFreeTerm 0)
    (N := G.IncidenceRing)
    (P := {b : G.IncResolutionBasis // G.incResolutionDegree b = 0} →₀ ℂ)
    G.incResolutionAugmentation G.incidenceFreeOriginMap G.incidenceFreeOriginMap_ker x y hxy
  exact h

/-- The residue quotient map is constructed directly from a section of the
surjective augmentation. Independence of the chosen preimage supplies the
additive and scalar-linear laws. -/
noncomputable def incidenceGeneratorResidueMap :
    G.IncidenceRing →ₗ[IncCoeffRing E]
      ({b : G.IncResolutionBasis // G.incResolutionDegree b = 0} →₀ ℂ) := by
  let s (u : G.IncidenceRing) : G.IncFreeTerm 0 :=
    Classical.choose (G.incResolutionAugmentation_surjective u)
  have hs (u : G.IncidenceRing) : G.incResolutionAugmentation (s u) = u :=
    Classical.choose_spec (G.incResolutionAugmentation_surjective u)
  refine {
    toFun := fun u => G.incidenceFreeOriginMap (s u)
    map_add' := ?_
    map_smul' := ?_
  }
  · intro u v
    calc
      G.incidenceFreeOriginMap (s (u + v)) =
          G.incidenceFreeOriginMap (s u + s v) :=
        G.incidenceFreeOriginMap_eq_of_augmentation_eq _ _ (by
          rw [map_add, hs, hs, hs])
      _ = G.incidenceFreeOriginMap (s u) + G.incidenceFreeOriginMap (s v) :=
        map_add _ _ _
  · intro r u
    calc
      G.incidenceFreeOriginMap (s (r • u)) =
          G.incidenceFreeOriginMap (r • s u) :=
        G.incidenceFreeOriginMap_eq_of_augmentation_eq _ _ (by
          rw [map_smul, hs, hs])
      _ = r • G.incidenceFreeOriginMap (s u) := G.incidenceFreeOriginMap.map_smul r (s u)

theorem incidenceGeneratorResidueMap_surjective :
    Function.Surjective G.incidenceGeneratorResidueMap := by
  intro y
  obtain ⟨x, hx⟩ := G.incidenceFreeOriginMap_surjective y
  refine ⟨G.incResolutionAugmentation x, ?_⟩
  change G.incidenceFreeOriginMap
      (Classical.choose (G.incResolutionAugmentation_surjective
        (G.incResolutionAugmentation x))) = y
  have hε : G.incResolutionAugmentation
      (Classical.choose (G.incResolutionAugmentation_surjective
        (G.incResolutionAugmentation x))) = G.incResolutionAugmentation x :=
    Classical.choose_spec (G.incResolutionAugmentation_surjective
      (G.incResolutionAugmentation x))
  exact (G.incidenceFreeOriginMap_eq_of_augmentation_eq _ _ hε).trans hx

/-- No finite generating family can be smaller than the actual zeroth
Betti row. This is a statement about the original incidence module. -/
theorem incidence_generators_card_lower_bound
    {J : Type*} [Fintype J] (g : J → G.IncidenceRing)
    (hg : Submodule.span (IncCoeffRing E) (Set.range g) = ⊤) :
    (∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q) ≤ Fintype.card J := by
  rw [← G.card_incHomologicalBasis 0]
  exact card_le_of_generating_family_and_residue_surjection
    G.incidenceGeneratorResidueMap G.incidenceGeneratorResidueMap_surjective g hg

/-- The state-indexed family is cardinality-minimal among all finite
coefficient-module generating families, not just among homogeneous ones. -/
theorem incidenceResolutionGenerators_minimal :
    Submodule.span (IncCoeffRing E) (Set.range G.incidenceResolutionGenerators) = ⊤ ∧
    ∀ {J : Type*} [Fintype J] (g : J → G.IncidenceRing),
      Submodule.span (IncCoeffRing E) (Set.range g) = ⊤ →
        Fintype.card {b : G.IncResolutionBasis // G.incResolutionDegree b = 0} ≤
          Fintype.card J := by
  refine ⟨G.incidenceResolutionGenerators_span, ?_⟩
  intro J _ g hg
  rw [G.card_incHomologicalBasis 0]
  exact G.incidence_generators_card_lower_bound g hg

end BPFixedPoints.Multigraph
