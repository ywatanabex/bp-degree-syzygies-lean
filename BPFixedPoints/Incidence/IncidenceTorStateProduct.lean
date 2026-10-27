import BPFixedPoints.Incidence.StateExteriorCup
import BPFixedPoints.Incidence.ResolutionTorProductGrading
import BPFixedPoints.Incidence.ResolutionTorUnit
import BPFixedPoints.Incidence.TorProductCoordinates
import BPFixedPoints.Incidence.CechProductCupStatePieces
import BPFixedPoints.Incidence.CechProjectionMonomials

/-!
# The actual Tor algebra of the incidence ring in the shared state algebra

Extend the state coordinates `incidenceTorEquivState p` of the actual Tor space by zero
to all resolution states (`incidenceTorFullState`). Under these coordinates the standard
Tor product is the state product `incStateCup ℂ` and the unit of Tor is `incStateUnit ℂ`:
specialize `incidenceTorProduct_cech_formula` from `IncCoeffRing E` to `ℂ` at the
coefficient origin through `incStateCup_mapRange`. The same statements hold for the
internal state equivalences `incidenceTorInternalEquivState` of the bigraded pieces.

Bigraded state coordinates of bidegree `(p, q)` with `p ≤ q` are the states of the
`q`-element edge sets lying in cohomological degree `q - p`
(`incBigradedStateEquiv`). The twist-zero state space is spanned by `cohomologyUnit`,
which is the basis vector with coefficient one (`cohomologyUnit_eq_single`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type) [CommRing R] {V : Type} [Fintype V]

/-- The twist-zero state module has a single basis vector. -/
instance hBasisZeroSubsingleton : Subsingleton (HBasis (0 : V → ℕ)) := by
  constructor
  intro a b
  funext v
  apply Fin.ext
  have ha := (a v).isLt
  have hb := (b v).isLt
  simp only [Pi.zero_apply, phi_zero] at ha hb
  omega

/-- The twist-zero cohomology unit is the basis state with coefficient one. -/
theorem cohomologyUnit_eq_single (κ : HBasis (0 : V → ℕ)) :
    cohomologyUnit (V := V) R = single κ 1 := by
  classical
  ext κ'
  rw [Subsingleton.elim κ' κ, single_eq_same, cohomologyUnit, contraction_p_coefficient]
  have hm : stateProjectionMonomial (0 : V → ℕ) κ = fun _ => unitBasis false := by
    funext v
    exact lineProjectionMonomial_zero (κ v)
  rw [hm, chainUnit, Finset.sum_apply' (s := Finset.univ)]
  rw [Finset.sum_eq_single (fun _ : V => false)]
  · exact single_eq_same
  · intro s _ hs
    apply single_eq_of_ne
    intro h
    apply hs
    funext v
    have hv := congrFun h v
    cases hsv : s v
    · rfl
    · rw [hsv] at hv
      exact absurd hv (by decide)
  · intro h
    exact absurd (Finset.mem_univ _) h

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools CechProduct
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incidenceTorStateOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

/-! ## Full state coordinates of actual Tor -/

/-- State coordinates of actual Tor extended by zero to all resolution states. -/
noncomputable def incidenceTorFullState (p : ℕ) :
    G.incidenceTor p →ₗ[ℂ] (G.IncResolutionBasis →₀ ℂ) :=
  (Finsupp.lmapDomain ℂ ℂ Subtype.val).comp (G.incidenceTorEquivState p).toLinearMap

/-- Full state coordinates at a state of the given homological degree. -/
theorem incidenceTorFullState_apply (p : ℕ) (x : G.incidenceTor p)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    G.incidenceTorFullState p x b.val = G.incidenceTorEquivState p x b :=
  mapDomain_apply_of_injective Subtype.val_injective _ b

/-- Full state coordinates vanish at states of another homological degree. -/
theorem incidenceTorFullState_apply_of_ne (p : ℕ) (x : G.incidenceTor p)
    (b : G.IncResolutionBasis) (hb : G.incResolutionDegree b ≠ p) :
    G.incidenceTorFullState p x b = 0 := by
  apply mapDomain_of_notMem_range
  rintro ⟨c, rfl⟩
  exact hb c.property

/-- Full state coordinates determine the Tor class. -/
theorem incidenceTorFullState_injective (p : ℕ) :
    Function.Injective (G.incidenceTorFullState p) :=
  (mapDomain_injective Subtype.val_injective).comp (G.incidenceTorEquivState p).injective

/-- Full state coordinates are compatible with transport of the homological degree. -/
@[simp] theorem incidenceTorFullState_cast {p q : ℕ} (h : p = q) (x : G.incidenceTor p) :
    G.incidenceTorFullState q (G.incidenceTorCast h x) = G.incidenceTorFullState p x := by
  subst q
  rfl

/-- Every state vector supported in homological degree `p` is the full state of a Tor class. -/
theorem exists_incidenceTorFullState_eq (p : ℕ) (z : G.IncResolutionBasis →₀ ℂ)
    (hz : ∀ b, G.incResolutionDegree b ≠ p → z b = 0) :
    ∃ x : G.incidenceTor p, G.incidenceTorFullState p x = z := by
  refine ⟨(G.incidenceTorEquivState p).symm
    (Finsupp.subtypeDomain (fun b => G.incResolutionDegree b = p) z), ?_⟩
  ext b
  by_cases hb : G.incResolutionDegree b = p
  · rw [show b = (⟨b, hb⟩ : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}).val
      from rfl, incidenceTorFullState_apply, LinearEquiv.apply_symm_apply, subtypeDomain_apply]
  · rw [incidenceTorFullState_apply_of_ne G p _ b hb, hz b hb]

/-- The full state of the specialization of a free-resolution element is its coefficientwise
value at the coefficient origin. -/
theorem incidenceTorFullState_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceTorFullState p (G.incFreeTermToTor p x) =
      mapRange (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x.val := by
  ext b
  rw [mapRange_apply]
  by_cases hb : G.incResolutionDegree b = p
  · rw [show b = (⟨b, hb⟩ : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}).val
      from rfl, incidenceTorFullState_apply]
    simp only [incFreeTermToTor, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [freeAtOrigin_apply]
    rfl
  · rw [incidenceTorFullState_apply_of_ne G p _ b hb]
    have hx : x.val b = 0 := (mem_supported' _ _).mp x.property b hb
    rw [hx, map_zero]

/-- Coordinates at the coefficient origin of the scalar extension of the full free module. -/
noncomputable def incOriginStateEquiv :
    (ℂ ⊗[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E)) ≃ₗ[ℂ]
      (G.IncResolutionBasis →₀ ℂ) :=
  (Finsupp.basisSingleOne.baseChange ℂ).repr

/-- Origin coordinates of `1 ⊗ z` are the coefficientwise constant coefficients of `z`. -/
theorem incOriginStateEquiv_tmul (z : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incOriginStateEquiv ((1 : ℂ) ⊗ₜ[IncCoeffRing E] z) =
      mapRange (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) z := by
  ext b
  rw [incOriginStateEquiv, Module.Basis.baseChange_repr_tmul, mapRange_apply,
    Finsupp.basisSingleOne_repr]
  simp only [LinearEquiv.refl_apply, Algebra.smul_def, mul_one]
  rfl

/-- Full state coordinates are origin coordinates of the inclusion into the full free module. -/
theorem incidenceTorFullState_eq_origin (p : ℕ) (x : G.incidenceTor p) :
    G.incidenceTorFullState p x = G.incOriginStateEquiv (G.incidenceTorToFull p x) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  rw [incidenceTorFullState_class, incidenceTorToFull_class, incOriginStateEquiv_tmul]

/-! ## Product and unit -/

/-- Under full state coordinates the standard Tor product is the complex state product. -/
theorem incidenceTorFullState_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    G.incidenceTorFullState (p + q) (G.incidenceTorProduct p q x y) =
      G.incStateCup ℂ (G.incidenceTorFullState p x) (G.incidenceTorFullState q y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p x
  obtain ⟨y, rfl⟩ := G.incFreeTermToTor_surjective q y
  rw [incidenceTorFullState_eq_origin, incidenceTorProduct_cech_formula, incOriginStateEquiv_tmul,
    incidenceTorFullState_class, incidenceTorFullState_class, ← incStateCup_incCoeffRing,
    incStateCup_mapRange]

/-- The unit state lies in homological degree zero. -/
theorem incStateUnit_apply_of_ne (R : Type) [CommRing R] (b : G.IncResolutionBasis)
    (hb : G.incResolutionDegree b ≠ 0) : G.incStateUnit R b = 0 := by
  obtain ⟨S, κ⟩ := b
  have hS : (∅ : Finset E) ≠ S := by
    rintro rfl
    exact hb (by simp [incResolutionDegree])
  exact G.incStateEmbed_apply_of_ne R hS _ κ

/-- The unit state is the empty edge state with its unique twist-zero basis state. -/
theorem incStateUnit_eq_single (R : Type) [CommRing R] (κ : HBasis (G.deg (∅ : Finset E))) :
    G.incStateUnit R = single ⟨∅, κ⟩ 1 := by
  rw [incStateUnit, cohomologyUnit_eq_single R (cast (congrArg HBasis G.deg_empty_eq_zero) κ),
    castH_single, incStateEmbed_single, cast_cast, cast_eq]

/-- Under full state coordinates the unit of Tor is the unit state. -/
theorem incidenceTorFullState_one :
    G.incidenceTorFullState 0 G.incidenceTorOne = G.incStateUnit ℂ := by
  obtain ⟨x, hx⟩ := G.exists_incidenceTorFullState_eq 0 (G.incStateUnit ℂ)
    (G.incStateUnit_apply_of_ne ℂ)
  have h := congrArg (G.incidenceTorFullState 0) (G.incidenceTorOne_mul 0 x)
  rw [incidenceTorFullState_cast, incidenceTorFullState_product, hx,
    incStateCup_unit_right] at h
  exact h

/-- The state coordinates of the unit of Tor, extended by zero, are the unit state. -/
theorem incidenceTorEquivState_one :
    Finsupp.lmapDomain ℂ ℂ Subtype.val (G.incidenceTorEquivState 0 G.incidenceTorOne) =
      G.incStateUnit ℂ :=
  G.incidenceTorFullState_one

/-! ## Bigraded state coordinates -/

/-- Inclusion of bigraded state coordinates into all resolution states. -/
noncomputable def incBigradedEmbed (R : Type) [CommRing R] (p q : ℕ) :
    (G.IncBigradedBasis p q →₀ R) →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  Finsupp.lmapDomain R R Subtype.val

/-- The bigraded inclusion at a state of the given bidegree. -/
theorem incBigradedEmbed_apply (R : Type) [CommRing R] (p q : ℕ)
    (z : G.IncBigradedBasis p q →₀ R) (b : G.IncBigradedBasis p q) :
    G.incBigradedEmbed R p q z b.val = z b :=
  mapDomain_apply_of_injective Subtype.val_injective _ b

/-- The bigraded inclusion vanishes at states of another bidegree. -/
theorem incBigradedEmbed_apply_of_not (R : Type) [CommRing R] (p q : ℕ)
    (z : G.IncBigradedBasis p q →₀ R) (b : G.IncResolutionBasis)
    (hb : ¬ (G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q)) :
    G.incBigradedEmbed R p q z b = 0 := by
  apply mapDomain_of_notMem_range
  rintro ⟨c, rfl⟩
  exact hb c.property

/-- The bigraded inclusion is injective. -/
theorem incBigradedEmbed_injective (R : Type) [CommRing R] (p q : ℕ) :
    Function.Injective (G.incBigradedEmbed R p q) :=
  mapDomain_injective Subtype.val_injective

/-- Restriction of a bigraded inclusion back to the bigraded states is the identity. -/
theorem subtypeDomain_incBigradedEmbed (R : Type) [CommRing R] (p q : ℕ)
    (z : G.IncBigradedBasis p q →₀ R) :
    Finsupp.subtypeDomain
        (fun b => G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q)
        (G.incBigradedEmbed R p q z) = z := by
  ext b
  rw [subtypeDomain_apply]
  exact G.incBigradedEmbed_apply R p q z b

/-- The internal state equivalence is the full state coordinate map restricted to a
bigraded piece. -/
theorem incBigradedEmbed_internalEquivState (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    G.incBigradedEmbed ℂ p q (G.incidenceTorInternalEquivState p q x) =
      G.incidenceTorFullState p x.val := by
  ext b
  by_cases hb : G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q
  · calc G.incBigradedEmbed ℂ p q (G.incidenceTorInternalEquivState p q x) b
        = G.incidenceTorInternalEquivState p q x ⟨b, hb⟩ :=
          G.incBigradedEmbed_apply ℂ p q _ ⟨b, hb⟩
      _ = G.incidenceTorEquivState p x.val ⟨b, hb.1⟩ := rfl
      _ = G.incidenceTorFullState p x.val b :=
          (G.incidenceTorFullState_apply p x.val ⟨b, hb.1⟩).symm
  · rw [incBigradedEmbed_apply_of_not G ℂ p q _ b hb]
    by_cases hp : G.incResolutionDegree b = p
    · have hq : G.incResolutionInternalDegree b ≠ q := fun hq => hb ⟨hp, hq⟩
      rw [show b = (⟨b, hp⟩ : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}).val
        from rfl, incidenceTorFullState_apply]
      exact ((mem_supported' ℂ _).mp
        ((G.mem_incidenceTorInternalPiece_iff p q x.val).mp x.property) ⟨b, hp⟩ hq).symm
    · exact (G.incidenceTorFullState_apply_of_ne p _ b hp).symm

/-- Under the internal state equivalences the standard Tor product of bigraded pieces is the
complex state product of the included bigraded states. -/
theorem incidenceTorInternalEquivState_product (p q a b : ℕ)
    (x : G.incidenceTorInternalPiece p a) (y : G.incidenceTorInternalPiece q b) :
    G.incBigradedEmbed ℂ (p + q) (a + b)
        (G.incidenceTorInternalEquivState (p + q) (a + b)
          ⟨G.incidenceTorProduct p q x y,
            G.incidenceTorProduct_internal_degree p q a b x.property y.property⟩) =
      G.incStateCup ℂ (G.incBigradedEmbed ℂ p a (G.incidenceTorInternalEquivState p a x))
        (G.incBigradedEmbed ℂ q b (G.incidenceTorInternalEquivState q b y)) := by
  rw [incBigradedEmbed_internalEquivState, incBigradedEmbed_internalEquivState,
    incBigradedEmbed_internalEquivState]
  exact G.incidenceTorFullState_product p q x y

/-- The internal state equivalence of a product of bigraded pieces is the restriction of the
complex state product of the included bigraded states. -/
theorem incidenceTorInternalEquivState_product_eq (p q a b : ℕ)
    (x : G.incidenceTorInternalPiece p a) (y : G.incidenceTorInternalPiece q b) :
    G.incidenceTorInternalEquivState (p + q) (a + b)
        ⟨G.incidenceTorProduct p q x y,
          G.incidenceTorProduct_internal_degree p q a b x.property y.property⟩ =
      Finsupp.subtypeDomain
        (fun c => G.incResolutionDegree c = p + q ∧ G.incResolutionInternalDegree c = a + b)
        (G.incStateCup ℂ (G.incBigradedEmbed ℂ p a (G.incidenceTorInternalEquivState p a x))
          (G.incBigradedEmbed ℂ q b (G.incidenceTorInternalEquivState q b y))) := by
  rw [← incidenceTorInternalEquivState_product, subtypeDomain_incBigradedEmbed]

/-- Under the internal state equivalence of bidegree `(0, 0)` the unit of Tor is the unit
state. -/
theorem incidenceTorInternalEquivState_one :
    G.incBigradedEmbed ℂ 0 0
        (G.incidenceTorInternalEquivState 0 0
          ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩) =
      G.incStateUnit ℂ := by
  rw [incBigradedEmbed_internalEquivState]
  exact G.incidenceTorFullState_one

/-! ## Bigraded states as states of edge sets in one cohomological degree -/

/-- The cohomological degree of the twist of an edge set is the number of vertices it touches. -/
theorem cohomologyDegree_deg (S : Finset E) :
    cohomologyDegree (G.deg S) = (G.support S).card :=
  cohomologyDegree_eq_card _

/-- A resolution state of homological degree `p` and internal degree `q` lies in cohomological
degree `q - p`. -/
theorem incBigraded_cohomologyDegree {p q : ℕ} (b : G.IncBigradedBasis p q) :
    cohomologyDegree (G.deg b.val.1) = q - p := by
  have hp := b.property.1
  have hq := b.property.2
  have hle := G.incResolutionBasis_card_support_le b.val
  rw [cohomologyDegree_deg]
  simp only [incResolutionDegree, incResolutionInternalDegree] at hp hq
  omega

/-- Resolution states of bidegree `(p, q)` with `p ≤ q` are pairs of a `q`-element edge set and a
state of its twist lying in cohomological degree `q - p`. -/
def incBigradedIndexEquiv {p q : ℕ} (h : p ≤ q) :
    G.IncBigradedBasis p q ≃
      Σ S : Set.powersetCard E q,
        ({_κ : HBasis (G.deg (S : Finset E)) |
          (cohomologyDegree (G.deg (S : Finset E)) : ℤ) = ((q - p : ℕ) : ℤ)} : Set _) where
  toFun b := ⟨⟨b.val.1, b.property.2⟩, ⟨b.val.2, by
    change (cohomologyDegree (G.deg b.val.1) : ℤ) = ((q - p : ℕ) : ℤ)
    rw [G.incBigraded_cohomologyDegree b]⟩⟩
  invFun s := ⟨⟨s.1.val, s.2.val⟩, by
    have hc : (cohomologyDegree (G.deg (s.1 : Finset E)) : ℤ) = ((q - p : ℕ) : ℤ) :=
      s.2.property
    have hc' : (G.support (s.1 : Finset E)).card = q - p := by
      rw [← cohomologyDegree_deg]
      exact_mod_cast hc
    have hcard := Set.powersetCard.card_eq s.1
    refine ⟨?_, hcard⟩
    change (s.1 : Finset E).card - (G.support (s.1 : Finset E)).card = p
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bigraded state coordinates of bidegree `(p, q)` with `p ≤ q`, as the family over
`q`-element edge sets of states of cohomological degree `q - p`. -/
noncomputable def incBigradedStateEquiv (R : Type) [CommRing R] {p q : ℕ} (h : p ≤ q) :
    (G.IncBigradedBasis p q →₀ R) ≃ₗ[R]
      ((S : Set.powersetCard E q) → stateDegreePiece R (G.deg (S : Finset E)) (q - p)) :=
  (Finsupp.domLCongr (G.incBigradedIndexEquiv h)).trans
    ((Finsupp.sigmaFinsuppLEquivPiFinsupp R).trans
      (LinearEquiv.piCongrRight fun _ => (Finsupp.supportedEquivFinsupp _).symm))

/-- Each state coordinate of the bigraded state equivalence is the corresponding coefficient of
the included bigraded state vector. -/
theorem incBigradedStateEquiv_apply (R : Type) [CommRing R] {p q : ℕ} (h : p ≤ q)
    (z : G.IncBigradedBasis p q →₀ R) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) :
    (G.incBigradedStateEquiv R h z S : CechProduct.H R (G.deg (S : Finset E))) κ =
      G.incBigradedEmbed R p q z ⟨S, κ⟩ := by
  classical
  by_cases hκ : (cohomologyDegree (G.deg (S : Finset E)) : ℤ) = ((q - p : ℕ) : ℤ)
  · have hb :
        G.incResolutionDegree ⟨S, κ⟩ = p ∧ G.incResolutionInternalDegree ⟨S, κ⟩ = q :=
      ((G.incBigradedIndexEquiv h).symm ⟨S, ⟨κ, hκ⟩⟩).property
    calc (G.incBigradedStateEquiv R h z S : CechProduct.H R (G.deg (S : Finset E))) κ
        = z ⟨⟨S, κ⟩, hb⟩ := by
          simp only [incBigradedStateEquiv, LinearEquiv.trans_apply,
            LinearEquiv.piCongrRight_apply, supportedEquivFinsupp_symm_apply_coe,
            extendDomain_apply, sigmaFinsuppLEquivPiFinsupp_apply, domLCongr_apply]
          split_ifs with hκ'
          · rfl
          · exact absurd hκ hκ'
      _ = G.incBigradedEmbed R p q z ⟨S, κ⟩ :=
          (G.incBigradedEmbed_apply R p q z ⟨⟨S, κ⟩, hb⟩).symm
  · have hz := (mem_supported' R _).mp (G.incBigradedStateEquiv R h z S).property κ hκ
    rw [hz, incBigradedEmbed_apply_of_not]
    intro hb
    apply hκ
    rw [G.incBigraded_cohomologyDegree ⟨⟨S, κ⟩, hb⟩]

/-- The included bigraded state vector of a family of edge-set states is the sum of the
embedded edge-set states. -/
theorem incBigradedEmbed_incBigradedStateEquiv_symm (R : Type) [CommRing R] {p q : ℕ}
    (h : p ≤ q)
    (f : (S : Set.powersetCard E q) → stateDegreePiece R (G.deg (S : Finset E)) (q - p)) :
    G.incBigradedEmbed R p q ((G.incBigradedStateEquiv R h).symm f) =
      ∑ S : Set.powersetCard E q, G.incStateEmbed R S (f S) := by
  ext ⟨T, κ⟩
  rw [Finsupp.finsetSum_apply]
  by_cases hT : T.card = q
  · let T' : Set.powersetCard E q := ⟨T, hT⟩
    have hT' := G.incBigradedStateEquiv_apply R h ((G.incBigradedStateEquiv R h).symm f) T' κ
    rw [LinearEquiv.apply_symm_apply] at hT'
    rw [← hT', Finset.sum_eq_single T']
    · exact (G.incStateEmbed_apply_same R T _ κ).symm
    · intro S _ hS
      exact G.incStateEmbed_apply_of_ne R (fun hST => hS (Subtype.ext hST)) _ κ
    · intro hT''
      exact absurd (Finset.mem_univ _) hT''
  · rw [incBigradedEmbed_apply_of_not G R p q _ ⟨T, κ⟩ (fun hb => hT hb.2)]
    symm
    apply Finset.sum_eq_zero
    intro S _
    refine G.incStateEmbed_apply_of_ne R (fun hST => hT ?_) _ κ
    rw [← hST]
    exact Set.powersetCard.card_eq S

/-- The bigraded state equivalence sends the state of one edge set to its embedded state. -/
theorem incBigradedEmbed_incBigradedStateEquiv_symm_single (R : Type) [CommRing R] {p q : ℕ}
    (h : p ≤ q) (S : Set.powersetCard E q)
    (x : stateDegreePiece R (G.deg (S : Finset E)) (q - p)) :
    G.incBigradedEmbed R p q ((G.incBigradedStateEquiv R h).symm (Pi.single S x)) =
      G.incStateEmbed R S x := by
  rw [incBigradedEmbed_incBigradedStateEquiv_symm, Finset.sum_eq_single S]
  · rw [Pi.single_eq_same]
  · intro T _ hT
    rw [Pi.single_eq_of_ne hT, Submodule.coe_zero, map_zero]
  · intro hS
    exact absurd (Finset.mem_univ _) hS

/-- The included bigraded state vector is the sum of the embedded edge-set states of its
bigraded state coordinates. -/
theorem incBigradedEmbed_eq_sum (R : Type) [CommRing R] {p q : ℕ} (h : p ≤ q)
    (z : G.IncBigradedBasis p q →₀ R) :
    G.incBigradedEmbed R p q z =
      ∑ S : Set.powersetCard E q, G.incStateEmbed R S (G.incBigradedStateEquiv R h z S) := by
  conv_lhs => rw [← (G.incBigradedStateEquiv R h).symm_apply_apply z]
  exact G.incBigradedEmbed_incBigradedStateEquiv_symm R h _

/-! ## Actual Tor in edge-set state coordinates -/

/-- Actual Tor of bidegree `(p, q)` with `p ≤ q`, as the family over `q`-element edge sets of
complex states of cohomological degree `q - p`. -/
noncomputable def incidenceTorBigradedStateEquiv {p q : ℕ} (h : p ≤ q) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ]
      ((S : Set.powersetCard E q) → stateDegreePiece ℂ (G.deg (S : Finset E)) (q - p)) :=
  (G.incidenceTorInternalEquivState p q).trans (G.incBigradedStateEquiv ℂ h)

/-- The edge-set state coordinates of a bigraded Tor class are its full state coefficients. -/
theorem incidenceTorBigradedStateEquiv_apply {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) :
    (G.incidenceTorBigradedStateEquiv h x S : CechProduct.H ℂ (G.deg (S : Finset E))) κ =
      G.incidenceTorFullState p x.val ⟨S, κ⟩ := by
  rw [incidenceTorBigradedStateEquiv, LinearEquiv.trans_apply, incBigradedStateEquiv_apply,
    incBigradedEmbed_internalEquivState]

/-- The full state of a bigraded Tor class is the sum of the embedded edge-set states of its
edge-set state coordinates. -/
theorem incidenceTorFullState_eq_sum {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    G.incidenceTorFullState p x.val =
      ∑ S : Set.powersetCard E q,
        G.incStateEmbed ℂ S (G.incidenceTorBigradedStateEquiv h x S) := by
  rw [← incBigradedEmbed_internalEquivState, G.incBigradedEmbed_eq_sum ℂ h]
  rfl

/-- In edge-set state coordinates the unit of Tor has coefficient one at the unique state of the
empty edge set. -/
theorem incidenceTorBigradedStateEquiv_one (S : Set.powersetCard E 0)
    (κ : HBasis (G.deg (S : Finset E))) :
    (G.incidenceTorBigradedStateEquiv (le_refl 0)
        ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩ S :
          CechProduct.H ℂ (G.deg (S : Finset E))) κ = 1 := by
  rw [incidenceTorBigradedStateEquiv_apply]
  change G.incidenceTorFullState 0 G.incidenceTorOne ⟨S, κ⟩ = 1
  rw [incidenceTorFullState_one]
  obtain ⟨S, hS⟩ := S
  obtain rfl : S = ∅ := Finset.card_eq_zero.mp hS
  rw [G.incStateUnit_eq_single ℂ κ, single_eq_same]

/-- The standard Tor product of bigraded classes in edge-set state coordinates: the full state
of the product is the double sum of state products of the embedded edge-set states. -/
theorem incidenceTorFullState_product_eq_sum {p q a b : ℕ} (hp : p ≤ a) (hq : q ≤ b)
    (x : G.incidenceTorInternalPiece p a) (y : G.incidenceTorInternalPiece q b) :
    G.incidenceTorFullState (p + q) (G.incidenceTorProduct p q x y) =
      ∑ S : Set.powersetCard E a, ∑ T : Set.powersetCard E b,
        G.incStateCup ℂ (G.incStateEmbed ℂ S (G.incidenceTorBigradedStateEquiv hp x S))
          (G.incStateEmbed ℂ T (G.incidenceTorBigradedStateEquiv hq y T)) := by
  rw [incidenceTorFullState_product, G.incidenceTorFullState_eq_sum hp x,
    G.incidenceTorFullState_eq_sum hq y, map_sum]
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]

end BPFixedPoints.Multigraph
