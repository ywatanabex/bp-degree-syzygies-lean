import BPFixedPoints.Incidence.ResolutionTorRanks
import BPFixedPoints.Incidence.GradedSpecialization

/-!
# Internal degrees on actual Tor from the free resolution

`incidenceTorInternalPiece` is the image of homogeneous free terms under actual
origin specialization, a subspace of the derived functor `incidenceTor`.
Identify its basis with `IncBigradedBasis`. `NaturalGradedResolution` compares
with the incidence ring's natural grading; compatibility with derived products
is a separate assertion.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Internal-degree-q subspace of free-resolution term p. -/
noncomputable def incFreeTermInternalPiece (p q : ℕ) : Submodule ℂ (G.IncFreeTerm p) :=
  (weightedFreePiece
    (fun b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p} =>
      G.incResolutionInternalDegree b.val) q).comap
    ((G.incFreeTermBasis p).repr.toLinearMap.restrictScalars ℂ)

@[simp] theorem incFreeTermBasis_repr_apply (p : ℕ) (x : G.IncFreeTerm p)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    (G.incFreeTermBasis p).repr x b = x.val b.val := by
  rfl

/-- This is the free-term grading for which differential homogeneity was already proved. -/
theorem mem_incFreeTermInternalPiece_iff (p q : ℕ) (x : G.IncFreeTerm p) :
    x ∈ G.incFreeTermInternalPiece p q ↔ x.val ∈ G.incResolutionInternalPiece q := by
  constructor
  · intro hx b
    by_cases hb : G.incResolutionDegree b = p
    · exact hx ⟨b, hb⟩
    · have hx0 : x.val b = 0 := (Finsupp.mem_supported' _ x.val).mp x.property b hb
      rw [hx0]
      exact (homogeneousCoeffPiece _).zero_mem
  · intro hx b
    exact hx b.val

theorem incFreeTermDifferential_internal_degree (p q : ℕ) {x : G.IncFreeTerm (p + 1)}
    (hx : x ∈ G.incFreeTermInternalPiece (p + 1) q) :
    G.incFreeTermDifferential p x ∈ G.incFreeTermInternalPiece p q := by
  apply (G.mem_incFreeTermInternalPiece_iff p q _).mpr
  exact G.incResolutionDifferential_internal_degree q
    ((G.mem_incFreeTermInternalPiece_iff (p + 1) q x).mp hx)

/-- Map origin specialization into Tor through the existing derived-specialization isomorphism. -/
noncomputable def incFreeTermToTor (p : ℕ) : G.IncFreeTerm p →ₗ[ℂ] G.incidenceTor p :=
  (G.incidenceTorEquivState p).symm.toLinearMap.comp
    (freeAtOrigin.comp ((G.incFreeTermBasis p).repr.toLinearMap.restrictScalars ℂ))

/-- This map is the actual tensor map x↦1⊗x. -/
theorem incFreeTermToTor_eq_tmul (p : ℕ) (x : G.IncFreeTerm p) :
    letI : Algebra (IncCoeffRing E) ℂ :=
      (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
    (G.incidenceTorIsoFreeTerm p).hom (G.incFreeTermToTor p x) =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] x := by
  letI : Algebra (IncCoeffRing E) ℂ :=
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
  apply (G.incSpecializedFreeTermEquiv p).injective
  change (G.incidenceTorEquivState p) (G.incFreeTermToTor p x) = _
  simp only [incFreeTermToTor, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext b
  rw [freeAtOrigin_apply]
  change MvPolynomial.constantCoeff ((G.incFreeTermBasis p).repr x b) =
    ((G.incFreeTermBasis p).baseChange ℂ).repr ((1 : ℂ) ⊗ₜ[IncCoeffRing E] x) b
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- Define internal Tor pieces as images of homogeneous free terms under actual origin specialization. -/
noncomputable def incidenceTorInternalPiece (p q : ℕ) : Submodule ℂ (G.incidenceTor p) :=
  (G.incFreeTermInternalPiece p q).map (G.incFreeTermToTor p)

theorem mem_incidenceTorInternalPiece_iff (p q : ℕ) (x : G.incidenceTor p) :
    x ∈ G.incidenceTorInternalPiece p q ↔
      G.incidenceTorEquivState p x ∈ Finsupp.supported ℂ ℂ
        {b | G.incResolutionInternalDegree b.val = q} := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [incFreeTermToTor, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    exact freeAtOrigin_mem_supported _ q hy
  · intro hx
    let y := (G.incFreeTermBasis p).repr.symm
      (freeConstantLift (σ := IncCoeffIdx E) (G.incidenceTorEquivState p x))
    have hy : y ∈ G.incFreeTermInternalPiece p q := by
      change (G.incFreeTermBasis p).repr y ∈ weightedFreePiece _ q
      rw [LinearEquiv.apply_symm_apply]
      exact freeConstantLift_mem_weightedFreePiece _ q hx
    refine ⟨y, hy, ?_⟩
    apply (G.incidenceTorEquivState p).injective
    simp [incFreeTermToTor, y]

/-- Isomorphism between actual Tor in a fixed internal degree and the corresponding bigraded state basis. -/
noncomputable def incidenceTorInternalEquivState (p q : ℕ) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] (G.IncBigradedBasis p q →₀ ℂ) := by
  let e := (G.incidenceTorEquivState p).submoduleMap (G.incidenceTorInternalPiece p q)
  have he : (G.incidenceTorInternalPiece p q).map (G.incidenceTorEquivState p).toLinearMap =
      Finsupp.supported ℂ ℂ {b | G.incResolutionInternalDegree b.val = q} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (G.mem_incidenceTorInternalPiece_iff p q y).mp hy
    · intro hx
      refine ⟨(G.incidenceTorEquivState p).symm x, ?_, by simp⟩
      apply (G.mem_incidenceTorInternalPiece_iff p q _).mpr
      simpa using hx
  let f := Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
    {b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p} |
      G.incResolutionInternalDegree b.val = q}
  let r : {b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p} //
      G.incResolutionInternalDegree b.val = q} ≃ G.IncBigradedBasis p q :=
    { toFun := fun b => ⟨b.val.val, b.val.property, b.property⟩
      invFun := fun b => ⟨⟨b.val, b.property.1⟩, b.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans ((LinearEquiv.ofEq _ _ he).trans
    (f.trans (Finsupp.domLCongr r)))

/-- Each bigraded Tor dimension is the paper's Betti state sum. -/
theorem finrank_incidenceTorInternalPiece (p q : ℕ) :
    Module.finrank ℂ (G.incidenceTorInternalPiece p q) = G.betti p q := by
  rw [← G.card_incBigradedBasis p q]
  exact (G.incidenceTorInternalEquivState p q).finrank_eq.trans
    (Module.finrank_eq_card_basis Finsupp.basisSingleOne)

/-- Projection to one internal-degree component after origin specialization. -/
noncomputable def incidenceTorComponent (p q : ℕ) :
    G.incidenceTor p →ₗ[ℂ] G.incidenceTor p := by
  classical
  let f : ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) →ₗ[ℂ]
      ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) :=
    { toFun := Finsupp.filter (fun b => G.incResolutionInternalDegree b.val = q)
      map_add' := fun _ _ => Finsupp.filter_add
      map_smul' := fun _ _ => Finsupp.filter_smul }
  exact (G.incidenceTorEquivState p).symm.toLinearMap.comp
    (f.comp (G.incidenceTorEquivState p).toLinearMap)

@[simp] theorem incidenceTorComponent_state (p q : ℕ) (x : G.incidenceTor p)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    G.incidenceTorEquivState p (G.incidenceTorComponent p q x) b =
      if G.incResolutionInternalDegree b.val = q then G.incidenceTorEquivState p x b
      else 0 := by
  classical
  simp [incidenceTorComponent, Finsupp.filter_apply]

theorem incidenceTorComponent_mem (p q : ℕ) (x : G.incidenceTor p) :
    G.incidenceTorComponent p q x ∈ G.incidenceTorInternalPiece p q := by
  rw [G.mem_incidenceTorInternalPiece_iff, Finsupp.mem_supported']
  intro b hb
  change G.incResolutionInternalDegree b.val ≠ q at hb
  simp [hb]

/-- Projection kills components of different internal degrees and preserves the matching degree. -/
theorem incidenceTorComponent_of_mem (p q r : ℕ) {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p r) :
    G.incidenceTorComponent p q x = if q = r then x else 0 := by
  classical
  have hs := (Finsupp.mem_supported' ℂ _).mp
    ((G.mem_incidenceTorInternalPiece_iff p r x).mp hx)
  apply (G.incidenceTorEquivState p).injective
  ext b
  by_cases hq : q = r
  · subst r
    by_cases hb : G.incResolutionInternalDegree b.val = q
    · simp [hb]
    · simp [hb, hs b hb]
  · by_cases hb : G.incResolutionInternalDegree b.val = q
    · have hr : G.incResolutionInternalDegree b.val ≠ r := by omega
      simp [hq, hb, hs b hr]
    · simp [hq, hb]

/-- Every Tor element is a finite sum of internal-degree components. -/
theorem sum_incidenceTorComponent (p : ℕ) (x : G.incidenceTor p) :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.incidenceTorComponent p q x = x := by
  apply (G.incidenceTorEquivState p).injective
  ext b
  simp only [map_sum]
  have hb := G.incResolutionInternalDegree_le b.val
  simp [Finset.mem_range, Nat.lt_succ_of_le hb]

/-- If a finite homogeneous sum is zero, each component is zero. -/
theorem incidenceTorInternalPiece_sum_unique (p : ℕ) (s : Finset ℕ)
    (x : ℕ → G.incidenceTor p)
    (hx : ∀ q ∈ s, x q ∈ G.incidenceTorInternalPiece p q)
    (hs : ∑ q ∈ s, x q = 0) {r : ℕ} (hr : r ∈ s) : x r = 0 := by
  have h := congrArg (G.incidenceTorComponent p r) hs
  rw [map_sum, map_zero] at h
  rw [Finset.sum_congr rfl (fun q hq =>
    G.incidenceTorComponent_of_mem p r q (hx q hq))] at h
  simpa [hr] using h

/-- Internal-degree components above the edge count vanish. -/
theorem incidenceTorInternalPiece_eq_bot (p q : ℕ) (hq : Fintype.card E < q) :
    G.incidenceTorInternalPiece p q = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (G.incidenceTorEquivState p).injective
  ext b
  have hs := (Finsupp.mem_supported' ℂ _).mp
    ((G.mem_incidenceTorInternalPiece_iff p q x).mp hx)
  have hb := G.incResolutionInternalDegree_le b.val
  simpa using hs b (by change G.incResolutionInternalDegree b.val ≠ q; omega)

end BPFixedPoints.Multigraph
