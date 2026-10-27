import BPFixedPoints.Incidence.RingCoefficientGrading
import BPFixedPoints.Incidence.ResolutionTorGrading
import BPFixedPoints.Incidence.GradedLinearExactness

/-!
# Homogeneous free resolution for the natural ring grading

Prove that natural ring pieces form a direct sum and the augmentation is
surjective in each degree.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial ResolutionTools Finsupp

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

theorem iSup_incFreeTermInternalPiece (p : ℕ) :
    (⨆ q, G.incFreeTermInternalPiece p q) = ⊤ := by
  let e := (G.incFreeTermBasis p).repr.restrictScalars ℂ
  change (⨆ q : ℕ, (weightedFreePiece _ (q : ℤ)).comap e.toLinearMap) = ⊤
  simp_rw [Submodule.comap_equiv_eq_map_symm]
  rw [← Submodule.map_iSup, iSup_weightedFreePiece_nat]
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.surjective]

/-- Finite internal-degree decomposition of each free term. -/
theorem exists_incFreeTermInternal_decomposition (p : ℕ) (x : G.IncFreeTerm p) :
    ∃ f : ℕ →₀ G.IncFreeTerm p, (∀ q, f q ∈ G.incFreeTermInternalPiece p q) ∧
      f.sum (fun _ y => y) = x := by
  apply (Submodule.mem_iSup_iff_exists_finsupp _ _).mp
  rw [G.iSup_incFreeTermInternalPiece]
  trivial

theorem iSupIndep_incFreeTermInternalPiece (p : ℕ) :
    iSupIndep (G.incFreeTermInternalPiece p) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (R := ℂ) (N := G.IncFreeTerm p) (G.incFreeTermInternalPiece p)).mpr
  intro s x hx hs q hq
  apply Subtype.val_injective
  change (x q).val = 0
  apply weightedFreePiece_sum_unique (σ := IncCoeffIdx E) (k := ℂ)
    G.incResolutionInternalDegree s (fun n => (x n).val)
    (fun n hn => (G.mem_incFreeTermInternalPiece_iff p n _).mp (hx n hn)) _ q hq
  simpa only [Submodule.coe_sum, Submodule.coe_zero] using congrArg Subtype.val hs

/-- Uniqueness of natural ring components through the injection into a chart. -/
theorem incidenceCoefficientPiece_sum_unique (s : Finset ℕ) (x : ℕ → G.IncidenceRing)
    (hx : ∀ n ∈ s, x n ∈ G.incidenceCoefficientPiece n)
    (hs : ∑ n ∈ s, x n = 0) (q : ℕ) (hq : q ∈ s) : x q = 0 := by
  classical
  let f := G.incidenceChartPolynomial (fun _ => false)
  apply G.incidenceChartPolynomial_injective (fun _ => false)
  have h := congrArg (fun z => homogeneousComponent q (f z)) hs
  simp only [map_sum, map_zero] at h ⊢
  have hc (n) (hn : n ∈ s) : homogeneousComponent q (f (x n)) =
      if q = n then f (x n) else 0 :=
    homogeneousComponent_of_mem ((G.mem_incidenceCoefficientPiece n _).mp (hx n hn) _)
  rw [Finset.sum_congr rfl hc] at h
  simpa [hq] using h

theorem iSupIndep_incidenceCoefficientPiece : iSupIndep G.incidenceCoefficientPiece :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr G.incidenceCoefficientPiece_sum_unique

theorem iSup_incidenceCoefficientPiece : (⨆ n, G.incidenceCoefficientPiece n) = ⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
  obtain ⟨f, hf, he⟩ := G.exists_incFreeTermInternal_decomposition 0 x
  rw [← he, map_finsuppSum]
  apply Submodule.sum_mem
  intro n _
  apply le_iSup G.incidenceCoefficientPiece n
  exact G.incResolutionAugmentation_coefficient_degree n (f n)
    ((G.mem_incFreeTermInternalPiece_iff 0 n _).mp (hf n))

/-- Natural coefficient degree gives an actual graded algebra structure on the incidence ring. -/
@[instance_reducible]
noncomputable def incidenceCoefficientGradedAlgebra : GradedAlgebra G.incidenceCoefficientPiece where
  one_mem := G.one_mem_incidenceCoefficientPiece
  mul_mem := fun _ _ _ _ hx hy => G.mul_mem_incidenceCoefficientPiece hx hy
  __ := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    G.iSupIndep_incidenceCoefficientPiece G.iSup_incidenceCoefficientPiece).chooseDecomposition

/-- The augmentation to the original incidence ring is surjective in each degree. -/
theorem incResolutionAugmentation_graded_surjective (q : ℕ) (u : G.IncidenceRing)
    (hu : u ∈ G.incidenceCoefficientPiece q) :
    ∃ x : G.IncFreeTerm 0, x ∈ G.incFreeTermInternalPiece 0 q ∧
      G.incResolutionAugmentation x = u := by
  classical
  obtain ⟨x, hx⟩ := G.incResolutionAugmentation_surjective u
  obtain ⟨f, hf, he⟩ := G.exists_incFreeTermInternal_decomposition 0 x
  refine ⟨f q, hf q, ?_⟩
  apply G.incidenceChartPolynomial_injective (fun _ => false)
  let a := G.incidenceChartPolynomial (fun _ => false)
  have h := congrArg (fun z => homogeneousComponent q (a z)) hx
  rw [← he, map_finsuppSum, Finsupp.sum, map_sum, map_sum] at h
  have hc (n : ℕ) : homogeneousComponent q (a (G.incResolutionAugmentation (f n))) =
      if q = n then a (G.incResolutionAugmentation (f n)) else 0 := by
    apply homogeneousComponent_of_mem
    exact (G.mem_incidenceCoefficientPiece n _).mp
      (G.incResolutionAugmentation_coefficient_degree n (f n)
        ((G.mem_incFreeTermInternalPiece_iff 0 n _).mp (hf n))) _
  simp_rw [hc] at h
  rw [homogeneousComponent_eq_self ((G.mem_incidenceCoefficientPiece q u).mp hu _)] at h
  by_cases hq : q ∈ f.support
  · simpa [hq] using h
  · have hzero : f q = 0 := Finsupp.notMem_support_iff.mp hq
    simpa [hq, hzero] using h

/-- Positive homological exactness holds at each fixed internal degree. -/
theorem incFreeTermDifferential_graded_exact (p q : ℕ) (x : G.IncFreeTerm (p + 1))
    (hx : x ∈ G.incFreeTermInternalPiece (p + 1) q)
    (hdx : G.incFreeTermDifferential p x = 0) :
    ∃ y : G.IncFreeTerm (p + 2), y ∈ G.incFreeTermInternalPiece (p + 2) q ∧
      G.incFreeTermDifferential (p + 1) y = x := by
  have hr : x ∈ LinearMap.range (G.incFreeTermDifferential (p + 1)) := by
    rw [G.incFreeTermDifferential_exact, LinearMap.mem_ker]
    exact hdx
  exact exists_homogeneous_preimage (k := ℂ) (M := G.IncFreeTerm (p + 2))
    (N := G.IncFreeTerm (p + 1)) (G.incFreeTermInternalPiece (p + 2))
    (G.incFreeTermInternalPiece (p + 1)) (G.iSup_incFreeTermInternalPiece (p + 2))
    (G.iSupIndep_incFreeTermInternalPiece (p + 1))
    ((G.incFreeTermDifferential (p + 1)).restrictScalars ℂ)
    (fun n _ hx => G.incFreeTermDifferential_internal_degree (p + 1) n hx) q hx hr

/-- In each internal degree, the augmentation kernel equals the first boundaries. -/
theorem incResolutionAugmentation_graded_exact (q : ℕ) (x : G.IncFreeTerm 0)
    (hx : x ∈ G.incFreeTermInternalPiece 0 q) (hεx : G.incResolutionAugmentation x = 0) :
    ∃ y : G.IncFreeTerm 1, y ∈ G.incFreeTermInternalPiece 1 q ∧
      G.incFreeTermDifferential 0 y = x := by
  have hr : x ∈ LinearMap.range (G.incFreeTermDifferential 0) := by
    rw [G.incFreeTermDifferential_augmentation_exact, LinearMap.mem_ker]
    exact hεx
  exact exists_homogeneous_preimage (k := ℂ) (M := G.IncFreeTerm 1)
    (N := G.IncFreeTerm 0) (G.incFreeTermInternalPiece 1)
    (G.incFreeTermInternalPiece 0) (G.iSup_incFreeTermInternalPiece 1)
    (G.iSupIndep_incFreeTermInternalPiece 0)
    ((G.incFreeTermDifferential 0).restrictScalars ℂ)
    (fun n _ hx => G.incFreeTermDifferential_internal_degree 0 n hx) q hx hr

end BPFixedPoints.Multigraph
