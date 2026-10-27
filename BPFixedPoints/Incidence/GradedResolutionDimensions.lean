import BPFixedPoints.Incidence.NaturalGradedResolution
import BPFixedPoints.Incidence.HomogeneousDimensions
import BPFixedPoints.Incidence.FiniteExactEuler

/-! # Natural graded exact free resolutions and the Euler dimension formula -/

namespace BPFixedPoints.Multigraph
open ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance gradedResolutionDimensionsRingAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

noncomputable def incFreeTermInternalEquivWeighted (p q : ℕ) :
    G.incFreeTermInternalPiece p q ≃ₗ[ℂ]
      weightedFreePiece (σ := IncCoeffIdx E) (k := ℂ)
        (fun b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p} =>
          G.incResolutionInternalDegree b.val) q := by
  let e := (G.incFreeTermBasis p).repr.restrictScalars ℂ
  exact LinearEquiv.ofBijective (e.toLinearMap.submoduleComap _) ⟨
    fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)),
    e.toLinearMap.submoduleComap_surjective_of_surjective _ e.surjective⟩

noncomputable instance incFreeTermInternalPiece_finite (p q : ℕ) :
    Module.Finite ℂ (G.incFreeTermInternalPiece p q) :=
  Module.Finite.of_surjective (G.incFreeTermInternalEquivWeighted p q).symm.toLinearMap
    (G.incFreeTermInternalEquivWeighted p q).symm.surjective

theorem finrank_incFreeTermInternalPiece (p q : ℕ) :
    Module.finrank ℂ (G.incFreeTermInternalPiece p q) =
      ∑ b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p},
        if G.incResolutionInternalDegree b.val ≤ q then
          Nat.multichoose (4 * Fintype.card E) (q - G.incResolutionInternalDegree b.val) else 0 := by
  rw [(G.incFreeTermInternalEquivWeighted p q).finrank_eq, finrank_weightedFreePiece]
  have hcard : Fintype.card (IncCoeffIdx E) = 4 * Fintype.card E := by
    simp only [IncCoeffIdx, Fintype.card_prod, Fintype.card_fin]
    omega
  rw [hcard]
  apply Finset.sum_congr rfl
  intro b _
  have he : ((G.incResolutionInternalDegree b.val : ℤ) ≤ (q : ℤ)) ↔
      G.incResolutionInternalDegree b.val ≤ q := by omega
  have hn : ((q : ℤ) - (G.incResolutionInternalDegree b.val : ℤ)).toNat =
      q - G.incResolutionInternalDegree b.val := by omega
  simp only [he, hn]

/-- Restrict the actual differential to one internal degree. -/
noncomputable def incInternalDifferential (p q : ℕ) :
    G.incFreeTermInternalPiece (p + 1) q →ₗ[ℂ] G.incFreeTermInternalPiece p q :=
  (((G.incFreeTermDifferential p).restrictScalars ℂ).comp
    (G.incFreeTermInternalPiece (p + 1) q).subtype).codRestrict _
      (fun x => G.incFreeTermDifferential_internal_degree p q x.property)

noncomputable def incInternalAugmentation (q : ℕ) :
    G.incFreeTermInternalPiece 0 q →ₗ[ℂ] G.incidenceCoefficientPiece q :=
  ((G.incResolutionAugmentation.restrictScalars ℂ).comp
    (G.incFreeTermInternalPiece 0 q).subtype).codRestrict _
      (fun x => G.incResolutionAugmentation_coefficient_degree q x.val
        ((G.mem_incFreeTermInternalPiece_iff 0 q x.val).mp x.property))

theorem incInternalAugmentation_surjective (q : ℕ) :
    Function.Surjective (G.incInternalAugmentation q) := by
  intro x
  obtain ⟨y, hy, he⟩ := G.incResolutionAugmentation_graded_surjective q x.val x.property
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

noncomputable instance incidenceCoefficientPiece_finite (q : ℕ) :
    Module.Finite ℂ (G.incidenceCoefficientPiece q) :=
  Module.Finite.of_surjective (G.incInternalAugmentation q) (G.incInternalAugmentation_surjective q)

theorem incInternalDifferential_exact (p q : ℕ) :
    LinearMap.range (G.incInternalDifferential (p + 1) q) =
      LinearMap.ker (G.incInternalDifferential p q) := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change G.incFreeTermDifferential p (G.incFreeTermDifferential (p + 1) y.val) = 0
    apply LinearMap.mem_ker.mp
    rw [← G.incFreeTermDifferential_exact p]
    exact ⟨y.val, rfl⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := G.incFreeTermDifferential_graded_exact p q x.val x.property
      (congrArg Subtype.val hx)
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

theorem incInternalAugmentation_exact (q : ℕ) :
    LinearMap.range (G.incInternalDifferential 0 q) =
      LinearMap.ker (G.incInternalAugmentation q) := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change G.incResolutionAugmentation (G.incFreeTermDifferential 0 y.val) = 0
    apply LinearMap.mem_ker.mp
    rw [← G.incFreeTermDifferential_augmentation_exact]
    exact ⟨y.val, rfl⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := G.incResolutionAugmentation_graded_exact q x.val x.property
      (congrArg Subtype.val hx)
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

theorem finrank_incFreeTermInternalPiece_above (p q : ℕ) (hp : G.rho < p) :
    Module.finrank ℂ (G.incFreeTermInternalPiece p q) = 0 := by
  classical
  haveI : IsEmpty {b : G.IncResolutionBasis // G.incResolutionDegree b = p} :=
    ⟨fun b => by have := G.incResolutionDegree_le b.val; have := b.property; omega⟩
  rw [G.finrank_incFreeTermInternalPiece]
  exact Finset.sum_eq_zero fun b _ => isEmptyElim b

/-- The dimension of the actual ring component of natural degree q is the alternating sum from the exact free resolution. -/
theorem incidenceCoefficientPiece_euler (q : ℕ) :
    (Module.finrank ℂ (G.incidenceCoefficientPiece q) : ℤ) =
      ∑ p ∈ Finset.range (G.rho + 1), (-1 : ℤ) ^ p *
        Module.finrank ℂ (G.incFreeTermInternalPiece p q) := by
  letI : ∀ p, AddCommMonoid (G.incFreeTermInternalPiece p q) :=
    fun p => inferInstance
  letI : ∀ p, Module ℂ (G.incFreeTermInternalPiece p q) :=
    fun p => inferInstance
  letI : ∀ p, Module.Finite ℂ (G.incFreeTermInternalPiece p q) :=
    fun p => G.incFreeTermInternalPiece_finite p q
  have h := alternating_finrank_exact (k := ℂ) (N := G.incidenceCoefficientPiece q)
    (fun p => G.incFreeTermInternalPiece p q)
    (fun p => G.incInternalDifferential p q) (G.incInternalAugmentation q)
    (fun p => G.incInternalDifferential_exact p q) (G.incInternalAugmentation_exact q)
    (G.incInternalAugmentation_surjective q) G.rho
    (G.finrank_incFreeTermInternalPiece_above (G.rho + 1) q (Nat.lt_succ_self _))
  exact h

end BPFixedPoints.Multigraph
