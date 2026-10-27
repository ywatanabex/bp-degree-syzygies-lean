import BPFixedPoints.Incidence.IncidenceCycleAlgebra

/-!
# The cycle-compatibility algebra as `U_G/(S_G)_+U_G`

The paper states `alg:cycle-algebra` for the quotient of the incidence ring `U_G` by the
coefficient augmentation ideal `(S_G)_+U_G`, the extension of the kernel of the constant
coefficient `S_G → ℂ` (`incidenceAugmentationIdeal`). Send an element of `U_G` to the origin
specialization of any degree-zero lift through the augmentation of the free resolution
(`incidenceRingToTor`): lifts with equal augmentation have equal classes, sums of lifts lift
sums, the resolution cup of two lifts lifts the product
(`incResolutionTorusAugmentation_cup`) and computes the standard Tor product
(`incidenceTorProduct_eq_transferred`), and the chosen lift of one defines `incidenceTorOne`.
This is a surjective complex algebra map onto degree-zero Tor. A coefficient `s` acts on Tor
through its constant coefficient, so `(S_G)_+U_G` lies in the kernel; conversely a lift with
zero class has all its coordinates in the kernel of the constant coefficient, so its
augmentation lies in `(S_G)_+U_G` (`ker_incidenceRingToTor`). Hence
`incidenceQuotientEquivTor : U_G/(S_G)_+U_G ≃ₐ[ℂ] incidenceTor 0`, which matches the natural
degree `q` of `U_G` with internal degree `q` of Tor. Composing with `cycleAlgebraEquivTor`
gives the paper's isomorphism `incidenceQuotientEquivCycleAlgebra`, graded for
`deg z_C = |C|`.
-/

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incidenceQuotientCoeffAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

/-- The coefficient augmentation ideal `(S_G)_+ U_G`: the extension to the incidence ring of the
ideal of coefficient polynomials vanishing at the coefficient origin. -/
noncomputable def incidenceAugmentationIdeal : Ideal G.IncidenceRing :=
  Ideal.map G.coeffHom (RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ))

/-- Origin specialization of free terms is semilinear over the constant coefficient. -/
theorem incFreeTermToTor_smul (p : ℕ) (s : IncCoeffRing E) (x : G.IncFreeTerm p) :
    G.incFreeTermToTor p (s • x) =
      MvPolynomial.constantCoeff s • G.incFreeTermToTor p x := by
  apply G.incidenceTorFullState_injective p
  rw [incidenceTorFullState_class, LinearMap.map_smul, incidenceTorFullState_class]
  ext b
  simp only [Submodule.coe_smul, mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

/-- The augmentation of a coefficient multiple is the product with the coefficient image. -/
theorem incResolutionAugmentation_smul_eq_mul (s : IncCoeffRing E) (x : G.IncFreeTerm 0) :
    G.incResolutionAugmentation (s • x) = G.coeffHom s * G.incResolutionAugmentation x := by
  rw [map_smul, Algebra.smul_def]
  rfl

/-- The augmentation of the chosen unit lift is one. -/
theorem incResolutionAugmentation_unit : G.incResolutionAugmentation G.incResolutionUnit = 1 :=
  Classical.choose_spec (G.incResolutionAugmentation_surjective 1)

/-- The class in degree-zero Tor of an element of the incidence ring: the origin specialization
of a degree-zero lift through the augmentation. -/
noncomputable def incidenceRingToTorFun (u : G.IncidenceRing) : G.incidenceTor 0 :=
  G.incFreeTermToTor 0 (Classical.choose (G.incResolutionAugmentation_surjective u))

/-- Every degree-zero lift of an element gives its class. -/
theorem incidenceRingToTorFun_augmentation (x : G.IncFreeTerm 0) :
    G.incidenceRingToTorFun (G.incResolutionAugmentation x) = G.incFreeTermToTor 0 x :=
  G.incFreeTermToTor_eq_of_augmentation_eq _ _
    (Classical.choose_spec (G.incResolutionAugmentation_surjective _))

/-- **Degree-zero Tor as a quotient of the incidence ring.** The class of a lift defines a
complex algebra map from the incidence ring to degree-zero Tor with its standard product. -/
noncomputable def incidenceRingToTor : G.IncidenceRing →ₐ[ℂ] G.incidenceTor 0 where
  toFun := G.incidenceRingToTorFun
  map_one' := rfl
  map_mul' u v := by
    obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
    obtain ⟨y, rfl⟩ := G.incResolutionAugmentation_surjective v
    have h : G.incResolutionAugmentation x * G.incResolutionAugmentation y =
        G.incResolutionAugmentation ⟨G.incResolutionCup x.val y.val,
          G.incResolutionCup_degree 0 0 x.property y.property⟩ := by
      apply Subtype.ext
      exact (G.incResolutionTorusAugmentation_cup x.val y.val x.property y.property).symm
    rw [h, incidenceRingToTorFun_augmentation, incidenceRingToTorFun_augmentation,
      incidenceRingToTorFun_augmentation, incidenceTorZero_mul_def,
      incidenceTorProduct_eq_transferred]
  map_zero' := by
    change G.incidenceRingToTorFun 0 = 0
    rw [← map_zero G.incResolutionAugmentation, incidenceRingToTorFun_augmentation, map_zero]
  map_add' u v := by
    obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
    obtain ⟨y, rfl⟩ := G.incResolutionAugmentation_surjective v
    rw [← map_add, incidenceRingToTorFun_augmentation, incidenceRingToTorFun_augmentation,
      incidenceRingToTorFun_augmentation, map_add]
  commutes' c := by
    have h : algebraMap ℂ G.IncidenceRing c =
        G.incResolutionAugmentation
          ((MvPolynomial.C c : IncCoeffRing E) • G.incResolutionUnit) := by
      rw [incResolutionAugmentation_smul_eq_mul, incResolutionAugmentation_unit, mul_one]
      exact (G.coeffHom.commutes c).symm
    change G.incidenceRingToTorFun (algebraMap ℂ G.IncidenceRing c) = _
    rw [h, incidenceRingToTorFun_augmentation, incFreeTermToTor_smul,
      MvPolynomial.constantCoeff_C, Algebra.algebraMap_eq_smul_one]
    rfl

/-- The map from the incidence ring on the augmentation of a degree-zero lift. -/
theorem incidenceRingToTor_augmentation (x : G.IncFreeTerm 0) :
    G.incidenceRingToTor (G.incResolutionAugmentation x) = G.incFreeTermToTor 0 x :=
  G.incidenceRingToTorFun_augmentation x

/-- The map from the incidence ring to degree-zero Tor is surjective. -/
theorem incidenceRingToTor_surjective : Function.Surjective G.incidenceRingToTor := by
  intro t
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective 0 t
  exact ⟨_, G.incidenceRingToTor_augmentation x⟩

/-- Coefficients act through their value at the coefficient origin. -/
theorem incidenceRingToTor_coeffHom (s : IncCoeffRing E) :
    G.incidenceRingToTor (G.coeffHom s) = MvPolynomial.constantCoeff s • 1 := by
  have h : G.coeffHom s = G.incResolutionAugmentation (s • G.incResolutionUnit) := by
    rw [incResolutionAugmentation_smul_eq_mul, incResolutionAugmentation_unit, mul_one]
  rw [h, incidenceRingToTor_augmentation, incFreeTermToTor_smul]
  rfl

/-- **The kernel is `(S_G)_+ U_G`.** -/
theorem ker_incidenceRingToTor :
    RingHom.ker G.incidenceRingToTor = G.incidenceAugmentationIdeal := by
  classical
  apply le_antisymm
  · intro u hu
    rw [RingHom.mem_ker] at hu
    obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
    rw [incidenceRingToTor_augmentation] at hu
    have hc : ∀ b, MvPolynomial.constantCoeff ((G.incFreeTermBasis 0).repr x b) = 0 := by
      intro b
      have h := congrArg (fun z => G.incidenceTorFullState 0 z b.val) hu
      simp only [incidenceTorFullState_class, map_zero, Finsupp.zero_apply, mapRange_apply] at h
      rw [incFreeTermBasis_repr_apply]
      exact h
    rw [← (G.incFreeTermBasis 0).sum_repr x, map_sum]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [incResolutionAugmentation_smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr (hc b)))
  · apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker, incidenceRingToTor_coeffHom,
      RingHom.mem_ker.mp hs, zero_smul]

/-- The quotient of the incidence ring by `(S_G)_+ U_G`. -/
abbrev IncidenceAugmentationQuotient : Type :=
  G.IncidenceRing ⧸ G.incidenceAugmentationIdeal

/-- The algebra map from `U_G/(S_G)_+U_G` to degree-zero Tor. -/
noncomputable def incidenceQuotientToTor : G.IncidenceAugmentationQuotient →ₐ[ℂ] G.incidenceTor 0 :=
  Ideal.Quotient.liftₐ G.incidenceAugmentationIdeal G.incidenceRingToTor
    (fun u hu => by
      rw [← G.ker_incidenceRingToTor] at hu
      exact RingHom.mem_ker.mp hu)

/-- The map from `U_G/(S_G)_+U_G` on the class of an element. -/
theorem incidenceQuotientToTor_mk (u : G.IncidenceRing) :
    G.incidenceQuotientToTor (Ideal.Quotient.mk G.incidenceAugmentationIdeal u) =
      G.incidenceRingToTor u :=
  rfl

/-- The map from `U_G/(S_G)_+U_G` to degree-zero Tor is bijective. -/
theorem incidenceQuotientToTor_bijective : Function.Bijective G.incidenceQuotientToTor := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [incidenceQuotientToTor_mk, ← RingHom.mem_ker, G.ker_incidenceRingToTor] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  · intro t
    obtain ⟨u, rfl⟩ := G.incidenceRingToTor_surjective t
    exact ⟨_, G.incidenceQuotientToTor_mk u⟩

/-- **`U_G/(S_G)_+U_G ≅ Tor_0`.** The quotient of the incidence ring by the coefficient
augmentation ideal is isomorphic, as a complex algebra, to degree-zero Tor with its standard
product. -/
noncomputable def incidenceQuotientEquivTor :
    G.IncidenceAugmentationQuotient ≃ₐ[ℂ] G.incidenceTor 0 :=
  AlgEquiv.ofBijective G.incidenceQuotientToTor G.incidenceQuotientToTor_bijective

/-- The isomorphism on the class of an element. -/
theorem incidenceQuotientEquivTor_mk (u : G.IncidenceRing) :
    G.incidenceQuotientEquivTor (Ideal.Quotient.mk G.incidenceAugmentationIdeal u) =
      G.incidenceRingToTor u :=
  rfl

/-- The natural degree-`q` piece of the incidence ring goes to internal degree `q` of
degree-zero Tor. -/
theorem incidenceRingToTor_mem_internalPiece {q : ℕ} {u : G.IncidenceRing}
    (hu : u ∈ G.incidenceCoefficientPiece q) :
    G.incidenceRingToTor u ∈ G.incidenceTorInternalPiece 0 q := by
  obtain ⟨x, hx, rfl⟩ := G.incResolutionAugmentation_graded_surjective q u hu
  rw [incidenceRingToTor_augmentation]
  exact ⟨x, hx, rfl⟩

/-- Every degree-zero Tor class of internal degree `q` comes from the natural degree-`q` piece
of the incidence ring. -/
theorem exists_incidenceRingToTor_eq_of_mem_internalPiece {q : ℕ} {t : G.incidenceTor 0}
    (ht : t ∈ G.incidenceTorInternalPiece 0 q) :
    ∃ u ∈ G.incidenceCoefficientPiece q, G.incidenceRingToTor u = t := by
  obtain ⟨x, hx, rfl⟩ := ht
  exact ⟨_, G.incResolutionAugmentation_coefficient_degree q x
    ((G.mem_incFreeTermInternalPiece_iff 0 q x).mp hx), G.incidenceRingToTor_augmentation x⟩

/-- **The cycle-compatibility algebra as `U_G/(S_G)_+U_G` (`alg:cycle-algebra`).** The
quotient of the incidence ring by the coefficient augmentation ideal is isomorphic to
`ℂ[z_C : C simple cycle] / (z_C z_D : V(C) ∩ V(D) ≠ ∅)`. -/
noncomputable def incidenceQuotientEquivCycleAlgebra :
    G.IncidenceAugmentationQuotient ≃ₐ[ℂ] G.CycleAlgebra :=
  G.incidenceQuotientEquivTor.trans G.cycleAlgebraEquivTor.symm

/-- The image of `z_C` in `U_G/(S_G)_+U_G` is the class of any element of the incidence ring
whose degree-zero Tor class is the class of the cycle `C`. -/
theorem incidenceQuotientEquivCycleAlgebra_symm_X (C : G.SimpleCycle) (u : G.IncidenceRing)
    (hu : G.incidenceRingToTor u = G.cycleClass C) :
    G.incidenceQuotientEquivCycleAlgebra.symm
        (Ideal.Quotient.mk G.cycleCompatibilityIdeal (MvPolynomial.X C)) =
      Ideal.Quotient.mk G.incidenceAugmentationIdeal u := by
  apply G.incidenceQuotientEquivCycleAlgebra.injective
  rw [AlgEquiv.apply_symm_apply]
  apply G.cycleAlgebraEquivTor.injective
  change _ = G.cycleAlgebraEquivTor (G.cycleAlgebraEquivTor.symm
    (G.incidenceQuotientEquivTor (Ideal.Quotient.mk G.incidenceAugmentationIdeal u)))
  rw [AlgEquiv.apply_symm_apply, incidenceQuotientEquivTor_mk, hu, cycleAlgebraEquivTor_X]

/-- **The isomorphism `U_G/(S_G)_+U_G ≅ ℂ[z_C]/(z_C z_D)` is graded.** The class of an
element of natural degree `q` has weight `q` (with `deg z_C = |C|`). -/
theorem incidenceQuotientEquivCycleAlgebra_mem_piece {q : ℕ} {u : G.IncidenceRing}
    (hu : u ∈ G.incidenceCoefficientPiece q) :
    G.incidenceQuotientEquivCycleAlgebra (Ideal.Quotient.mk G.incidenceAugmentationIdeal u) ∈
      G.cycleAlgebraPiece q := by
  rw [← G.cycleAlgebraEquivTor_mem_internalPiece_iff]
  change G.cycleAlgebraEquivTor (G.cycleAlgebraEquivTor.symm
    (G.incidenceQuotientEquivTor (Ideal.Quotient.mk G.incidenceAugmentationIdeal u))) ∈ _
  rw [AlgEquiv.apply_symm_apply, incidenceQuotientEquivTor_mk]
  exact G.incidenceRingToTor_mem_internalPiece hu

/-- Every element of weight `q` of the cycle-compatibility algebra is the image of the class of
an element of natural degree `q` of the incidence ring. -/
theorem exists_incidenceQuotientEquivCycleAlgebra_eq {q : ℕ} {a : G.CycleAlgebra}
    (ha : a ∈ G.cycleAlgebraPiece q) :
    ∃ u ∈ G.incidenceCoefficientPiece q,
      G.incidenceQuotientEquivCycleAlgebra (Ideal.Quotient.mk G.incidenceAugmentationIdeal u) =
        a := by
  rw [← G.cycleAlgebraEquivTor_mem_internalPiece_iff] at ha
  obtain ⟨u, hu, hut⟩ := G.exists_incidenceRingToTor_eq_of_mem_internalPiece ha
  refine ⟨u, hu, G.cycleAlgebraEquivTor.injective ?_⟩
  change G.cycleAlgebraEquivTor (G.cycleAlgebraEquivTor.symm
    (G.incidenceQuotientEquivTor (Ideal.Quotient.mk G.incidenceAugmentationIdeal u))) = _
  rw [AlgEquiv.apply_symm_apply, incidenceQuotientEquivTor_mk, hut]

end BPFixedPoints.Multigraph
