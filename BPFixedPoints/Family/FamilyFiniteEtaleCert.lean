import BPFixedPoints.Degree.Generic.FiberConstancy
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot

/-!
# Shape certificates over a principal localization, and monogenic étale algebras

Two general facts used for finite étaleness of the admissible BP family.

* `exists_shapeCert_away`: if an injective θ₀:R→Ω into an algebraically closed
  field of characteristic zero has exactly Q solutions of a square system
  (f,D), all simple, then some nonzero g∈R carries a shape certificate
  (`ShapeCert`) over the localization R[1/g]. This is the certificate built
  inside the proof of `generic_fiber_constancy`; here it is returned itself
  (as `Nonempty`) instead of being specialized to fibers.
* `adjoinRoot_etale_of_bezout`, `adjoinRoot_free`, `adjoinRoot_finite`,
  `finrank_adjoinRoot`: for a monic χ∈S[Y] with a Bezout identity
  s_a χ+s_b χ'=1, the algebra S[Y]/(χ) is étale over S (Mathlib's
  `Algebra.Etale`, through the standard étale pair (χ,1)) and free of rank
  deg χ.

Nothing about the BP equations is used here.
-/

namespace BPFixedPoints.BP

set_option linter.unusedSectionVars false

open MvPolynomial

section CertAway

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Certificate over a principal localization.** An injective θ₀ to an algebraically closed characteristic-zero field with exactly Q solutions, all simple, gives a nonzero g∈R and a shape certificate of degree Q over R[1/g]. -/
theorem exists_shapeCert_away {R : Type*} [CommRing R]
    (f : ι → MvPolynomial ι R) (D : MvPolynomial ι R) (Q : ℕ)
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (θ₀ : R →+* Ω)
    (hθ₀ : Function.Injective θ₀) (hfin : Finite (SystemSolutions f D θ₀))
    (hcard : Nat.card (SystemSolutions f D θ₀) = Q)
    (hsimple : ∀ y : SystemSolutions f D θ₀, IsSimpleAt f θ₀ y.1) :
    ∃ g : R, g ≠ 0 ∧ Nonempty (ShapeCert (fun i => map (algebraMap R (Localization.Away g)) (f i))
      (map (algebraMap R (Localization.Away g)) D) Q) := by
  classical
  have : IsDomain R := hθ₀.isDomain θ₀
  let φ : (FractionRing R) →+* Ω := IsFractionRing.lift hθ₀
  let _ : Algebra (FractionRing R) Ω := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R (FractionRing R) r) = θ₀ r :=
    IsFractionRing.lift_algebraMap hθ₀
  have hmapF : ∀ p : MvPolynomial ι R,
      map (algebraMap (FractionRing R) Ω) (map (algebraMap R (FractionRing R)) p) = map θ₀ p := by
    intro p
    rw [map_map, show (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) = θ₀ from
      RingHom.ext hφ]
  let fF : ι → MvPolynomial ι (FractionRing R) := fun i => map (algebraMap R (FractionRing R)) (f i)
  let DF : MvPolynomial ι (FractionRing R) := map (algebraMap R (FractionRing R)) D
  have hpred : ∀ y : ι → Ω, ((∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0) ↔
      ((∀ i, eval y (map θ₀ (f i)) = 0) ∧ eval y (map θ₀ D) ≠ 0) := by
    intro y
    simp only [fF, DF, hmapF]
  let eqv := Equiv.subtypeEquivRight hpred
  have : Finite {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0} := Finite.of_equiv _ eqv.symm
  have hcardF : Nat.card {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0} = Q := (Nat.card_congr eqv).trans hcard
  have hsimpleF : ∀ y : {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0},
      (Matrix.of fun i j => eval y.1 (pderiv j (map (algebraMap (FractionRing R) Ω) (fF i)))).det ≠ 0 := by
    intro y
    have := hsimple ⟨y.1, (hpred y.1).1 y.2⟩
    simpa only [IsSimpleAt, fF, hmapF] using this
  obtain ⟨cF⟩ := exists_shapeCert fF DF hsimpleF
  rw [hcardF] at cF
  obtain ⟨⟨g, hg⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    cF.coeffSet
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  let Rg := Localization.Away g
  have hgu : IsUnit (algebraMap R (FractionRing R) g) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hg0)
  let ψ : Rg →+* (FractionRing R) := IsLocalization.Away.lift g hgu
  have hψ_alg : ∀ r : R, ψ (algebraMap R Rg r) = algebraMap R (FractionRing R) r :=
    IsLocalization.Away.lift_eq g hgu
  have hψ_inv : ψ (IsLocalization.Away.invSelf g) = (algebraMap R (FractionRing R) g)⁻¹ := by
    have h1 := congrArg ψ (IsLocalization.Away.mul_invSelf (S := Rg) g)
    rw [map_mul, map_one, hψ_alg] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers g) a
    have hr : algebraMap R (FractionRing R) r = 0 := by
      rw [← hψ_alg, ← hrm, map_mul, ha, zero_mul]
    have hr0 : r = 0 := (map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))).1 hr
    rw [hr0, map_zero] at hrm
    exact (IsLocalization.map_units Rg m).mul_left_eq_zero.1 hrm
  have hrange : ↑cF.coeffSet ⊆ Set.range ψ := by
    intro a ha
    obtain ⟨r, hr⟩ := hint a ha
    refine ⟨algebraMap R Rg r * IsLocalization.Away.invSelf g, ?_⟩
    rw [map_mul, hψ_alg, hψ_inv, hr, Algebra.smul_def]
    field_simp [hgu.ne_zero]
  let fg : ι → MvPolynomial ι Rg := fun i => map (algebraMap R Rg) (f i)
  let Dg : MvPolynomial ι Rg := map (algebraMap R Rg) D
  have hψcomp : ψ.comp (algebraMap R Rg) = algebraMap R (FractionRing R) :=
    IsLocalization.Away.lift_comp g hgu
  have hfg : (fun i => map ψ (fg i)) = fF := by
    funext i
    simp only [fg, fF, map_map, hψcomp]
  have hDg : map ψ Dg = DF := by simp only [Dg, DF, map_map, hψcomp]
  exact ⟨g, hg0, ShapeCert.lift ψ hψ_inj fg Dg hfg hDg cF hrange⟩

end CertAway

/-! ### Monogenic algebras with a Bezout identity -/

section Monogenic

open Polynomial

variable {S : Type*} [CommRing S]

/-- The standard étale pair (χ,1) of a monic χ with a Bezout identity s_a χ+s_b χ'=1. -/
noncomputable def bezoutEtalePair (χ : S[X]) (hχ : χ.Monic) (sa sb : S[X])
    (h : sa * χ + sb * derivative χ = 1) : StandardEtalePair S where
  f := χ
  monic_f := hχ
  g := 1
  cond := ⟨sb, sa, 0, by rw [pow_zero]; linear_combination h⟩

/-- S[Y]/(χ) is the standard étale algebra of the pair (χ,1). -/
noncomputable def adjoinRootEquivBezoutEtalePair (χ : S[X]) (hχ : χ.Monic) (sa sb : S[X])
    (h : sa * χ + sb * derivative χ = 1) :
    AdjoinRoot χ ≃ₐ[S] (bezoutEtalePair χ hχ sa sb h).Ring := by
  let P := bezoutEtalePair χ hχ sa sb h
  have hP : P.HasMap (AdjoinRoot.root χ) := by
    refine ⟨?_, ?_⟩
    · change aeval (AdjoinRoot.root χ) χ = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · change IsUnit (aeval (AdjoinRoot.root χ) (1 : S[X]))
      rw [map_one]
      exact isUnit_one
  have hX : eval₂ (↑(Algebra.ofId S P.Ring)) P.X χ = 0 := by
    have := (StandardEtalePair.hasMap_X (P := P)).1
    rwa [Polynomial.aeval_def] at this
  refine AlgEquiv.ofAlgHom (AdjoinRoot.liftAlgHom χ (Algebra.ofId S P.Ring) P.X hX)
    (P.lift (AdjoinRoot.root χ) hP) ?_ ?_
  · apply StandardEtalePair.hom_ext
    rw [AlgHom.comp_apply, StandardEtalePair.lift_X]
    simp only [AdjoinRoot.liftAlgHom_root]
    rfl
  · apply AdjoinRoot.algHom_ext
    simp

/-- **Monogenic étale algebra.** S[Y]/(χ) is étale over S when χ is monic with s_a χ+s_b χ'=1. -/
theorem adjoinRoot_etale_of_bezout (χ : S[X]) (hχ : χ.Monic) (sa sb : S[X])
    (h : sa * χ + sb * derivative χ = 1) : Algebra.Etale S (AdjoinRoot χ) :=
  Algebra.Etale.of_equiv (adjoinRootEquivBezoutEtalePair χ hχ sa sb h).symm

/-- S[Y]/(χ) is a free S-module for monic χ. -/
theorem adjoinRoot_free {χ : S[X]} (hχ : χ.Monic) : Module.Free S (AdjoinRoot χ) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' hχ).basis

/-- S[Y]/(χ) is a finite S-module for monic χ. -/
theorem adjoinRoot_finite {χ : S[X]} (hχ : χ.Monic) : Module.Finite S (AdjoinRoot χ) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' hχ).basis

/-- S[Y]/(χ) has rank deg χ over a nontrivial S for monic χ. -/
theorem finrank_adjoinRoot [Nontrivial S] {χ : S[X]} (hχ : χ.Monic) :
    Module.finrank S (AdjoinRoot χ) = χ.natDegree := by
  rw [(AdjoinRoot.powerBasis' hχ).finrank, AdjoinRoot.powerBasis'_dim]

end Monogenic

end BPFixedPoints.BP
