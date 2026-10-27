import BPFixedPoints.Incidence.IncidenceMinimalGenerators
import BPFixedPoints.Incidence.Generators
import BPFixedPoints.Incidence.NaturalGradedResolution
import Mathlib.Algebra.Module.SpanRank

/-! # The intrinsic module generator number and the graph cycle criterion -/

namespace BPFixedPoints.ResolutionTools

universe u

/-- A spanning family whose residues form a full vector space realizes Mathlib's
minimum cardinality of module generators. -/
theorem spanFinrank_eq_card_of_residue_surjection
    {R k M I : Type u} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup M] [Module R M] [Fintype I]
    (ψ : M →ₗ[R] (I →₀ k)) (hψ : Function.Surjective ψ)
    (g : I → M) (hg : Submodule.span R (Set.range g) = ⊤) :
    (⊤ : Submodule R M).spanFinrank = Fintype.card I := by
  classical
  have hfg : (⊤ : Submodule R M).FG :=
    Submodule.fg_def.mpr ⟨Set.range g, Set.finite_range g, hg⟩
  apply Nat.le_antisymm
  · apply (hfg.spanRank_le_iff (Fintype.card I)).mp
    rw [← hg]
    have h := (Submodule.spanRank_span_le_card (R := R) (Set.range g)).trans
      (Cardinal.mk_range_le (f := g))
    simpa only [Cardinal.mk_fintype] using h
  · obtain ⟨s, hs, hspan⟩ := hfg.exists_span_finset_card_eq_spanFinrank
    have hs' : Submodule.span R (Set.range (Subtype.val : s → M)) = ⊤ := by
      simpa using hspan
    have h := card_le_of_generating_family_and_residue_surjection ψ hψ
      (Subtype.val : s → M) hs'
    rw [← hs]
    simpa only [Fintype.card_coe] using h

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open ResolutionTools
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance generatorCountCoefficientAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

noncomputable local instance generatorCountOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

/-- The intrinsic minimum for the original coefficient module, using Mathlib's definition. -/
noncomputable def incidenceModuleGeneratorNumber : ℕ :=
  (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing).spanFinrank

/-- The actual minimum among all module generating sets is the zeroth Betti row. -/
theorem incidenceModuleGeneratorNumber_eq :
    G.incidenceModuleGeneratorNumber =
      ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q := by
  rw [← G.card_incHomologicalBasis 0]
  have h := spanFinrank_eq_card_of_residue_surjection
    G.incidenceGeneratorResidueMap G.incidenceGeneratorResidueMap_surjective
    G.incidenceResolutionGenerators G.incidenceResolutionGenerators_span
  exact h

/-- The cardinality-minimal generating family is homogeneous for the natural ring grading. -/
theorem incidenceResolutionGenerators_homogeneous
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) :
    G.incidenceResolutionGenerators b ∈ G.incidenceCoefficientPiece (G.incResolutionInternalDegree b.val) := by
  apply G.incResolutionAugmentation_coefficient_degree
  apply (G.mem_incFreeTermInternalPiece_iff 0 _ _).mp
  change (G.incFreeTermBasis 0).repr ((G.incFreeTermBasis 0) b) ∈ weightedFreePiece _ _
  rw [Module.Basis.repr_self]
  apply weightedFreePiece_single
  simpa only [sub_self, map_one] using homogeneousCoeffPiece_C
    (σ := IncCoeffIdx E) (1 : ℂ)

/-- Counting the homogeneous generators in each natural degree recovers beta_{0,q}. -/
theorem card_incidenceResolutionGenerators_degree (q : ℕ) :
    Fintype.card {b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0} //
      G.incResolutionInternalDegree b.val = q} = G.betti 0 q := by
  rw [← G.card_incBigradedBasis 0 q]
  apply Fintype.card_congr
  exact
    { toFun := fun b => ⟨b.val.val, b.val.property, b.property⟩
      invFun := fun b => ⟨⟨b.val, b.property.1⟩, b.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The intrinsic minimum counts vertex-disjoint simple-cycle collections, including the empty one. -/
theorem incidenceModuleGeneratorNumber_eq_cycleCollections [DecidablePred G.IsCycleCollection] :
    G.incidenceModuleGeneratorNumber = (Finset.univ.filter G.IsCycleCollection).card :=
  G.incidenceModuleGeneratorNumber_eq.trans G.sum_betti_zero_eq_card_cycleCollections

/-- The minimum module generator number is bounded by the binary cycle-space cardinality. -/
theorem incidenceModuleGeneratorNumber_le : G.incidenceModuleGeneratorNumber ≤ 2 ^ G.nu := by
  rw [G.incidenceModuleGeneratorNumber_eq]
  exact G.sum_betti_zero_le

/-- The sharpness criterion is now a statement about the original module. -/
theorem incidenceModuleGeneratorNumber_eq_iff :
    G.incidenceModuleGeneratorNumber = 2 ^ G.nu ↔
      ∀ C D, G.IsSimpleCycle C → G.IsSimpleCycle D → Disjoint C D →
        Disjoint (G.support C) (G.support D) := by
  rw [G.incidenceModuleGeneratorNumber_eq]
  exact G.sum_betti_zero_eq_iff

/-- Graphs of maximum degree at most three attain the bound. -/
theorem incidenceModuleGeneratorNumber_eq_of_deg_le_three
    (h : ∀ v, G.deg Finset.univ v ≤ 3) : G.incidenceModuleGeneratorNumber = 2 ^ G.nu := by
  rw [G.incidenceModuleGeneratorNumber_eq]
  exact G.sum_betti_zero_eq_of_deg_le_three h

end BPFixedPoints.Multigraph
