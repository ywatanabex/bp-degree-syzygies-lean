import BPFixedPoints.Incidence.IncidenceEdgeSignResolution
import BPFixedPoints.Incidence.IncidenceEdgeSignExterior
import BPFixedPoints.Incidence.IncidenceEdgeSignTransport

/-!
# The Tor automorphism of an edge sign and its naturality

For an edge sign `ε`, the coefficient sign change `edgeSignCoeff ε` and the incidence ring
automorphism `edgeSignIncidence ε` give, by the derived ring change of `IncidenceTorRelabel.lean`,
an automorphism of actual Tor (`incidenceTorSignIso`, defined exactly as the Tor map of an edge
relabeling, through `incidenceTorTransportIso`).

It is computed by the explicit sign-change chain map `edgeSignChainMap` of the actual free
resolution, which comes from the total Koszul–Čech complex (Koszul generator `e ↦ ε_e e`,
coefficients through the coefficient sign change) by inclusion, total map and projection
(`incidenceTorSignIso_hom_eq`). At the coefficient origin this chain map is the edge-sign scaling
of states, so the full state vector of the image of a Tor class is its full state vector with the
`S`-components multiplied by `∏_{e ∈ S} ε_e` (`incidenceTorFullState_sign`,
`incidenceTorFullState_sign_apply`). Consequently the Tor automorphism preserves internal degrees,
the standard Tor product and the unit; the trivial sign gives the identity, products of signs give
composites, and since every edge sign squares to one it is an involution. Together with the
exterior side (`IncidenceEdgeSignExterior.lean`) this gives the naturality square of
`incidenceTorExteriorEquiv` (`incidenceTorExteriorEquiv_sign`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (ε : EdgeSign E)

/-- The automorphism of actual Tor induced by an edge sign: the derived ring change along the
coefficient sign change and the incidence ring automorphism. -/
noncomputable def incidenceTorSignIso (p : ℕ) : G.incidenceTor p ≅ G.incidenceTor p :=
  incidenceTorTransportIso (edgeSignCoeff ε) (constantCoeff_edgeSignCoeff ε)
    (G.edgeSignIncidence ε) (G.edgeSignIncidence_coeffHom ε) p

/-- The Tor automorphism of an edge sign, as a linear isomorphism. -/
noncomputable def incidenceTorSign (p : ℕ) : G.incidenceTor p ≃ₗ[ℂ] G.incidenceTor p :=
  (G.incidenceTorSignIso ε p).toLinearEquiv

/-- The Tor automorphism of an edge sign is the transported Tor map of its ring automorphisms. -/
theorem incidenceTorSign_eq_transport (p : ℕ) (y : G.incidenceTor p) :
    G.incidenceTorSign ε p y =
      incidenceTorTransport (edgeSignCoeff ε) (constantCoeff_edgeSignCoeff ε)
        (G.edgeSignIncidence ε) (G.edgeSignIncidence_coeffHom ε) p y := rfl

/-- The sign-change chain map of the actual free resolution, as a chain map of complexes of
coefficient modules. -/
noncomputable def edgeSignChainMap :
    G.incFreeResolution.complex ⟶
      ((ModuleCat.restrictScalars (edgeSignCoeff ε).toRingEquiv.toRingHom).mapHomologicalComplex
        _).obj G.incFreeResolution.complex :=
  freeTermChainMap (edgeSignCoeff ε) (G.edgeSignFreeTerm ε) (G.edgeSignFreeTerm_differential ε)

theorem edgeSignChainMap_f_apply (n : ℕ) (x : G.IncFreeTerm n) :
    ((G.edgeSignChainMap ε).f n) x = G.edgeSignFreeTerm ε n x := rfl

/-- The Tor automorphism of an edge sign is computed by the sign-change chain map of the actual
free resolution. -/
theorem incidenceTorSignIso_hom_eq (p : ℕ) :
    (G.incidenceTorSignIso ε p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map (G.edgeSignChainMap ε)) p ≫
          HomologicalComplex.homologyMap
            (restrictExtendComplexIso (edgeSignCoeff ε).toRingEquiv constantCoeff constantCoeff
              (constantCoeff_edgeSignCoeff ε) G.incFreeResolution.complex).hom p ≫
            (G.incFreeResolution.isoLeftDerivedObj
              (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).inv :=
  incidenceTorTransportIso_hom_eq (edgeSignCoeff ε) (constantCoeff_edgeSignCoeff ε)
    (G.edgeSignIncidence ε) (G.edgeSignIncidence_coeffHom ε) (G.edgeSignFreeTerm ε)
    (G.edgeSignFreeTerm_differential ε) (G.edgeSignFreeTerm_augmentation ε) p

/-- The Tor automorphism of an edge sign sends the specialization of a free-resolution element to
the specialization of its sign change. -/
theorem incidenceTorSign_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceTorSign ε p (G.incFreeTermToTor p x) =
      G.incFreeTermToTor p (G.edgeSignFreeTerm ε p x) :=
  incidenceTorTransport_class (edgeSignCoeff ε) (constantCoeff_edgeSignCoeff ε)
    (G.edgeSignIncidence ε) (G.edgeSignIncidence_coeffHom ε) (G.edgeSignFreeTerm ε)
    (G.edgeSignFreeTerm_differential ε) (G.edgeSignFreeTerm_augmentation ε) p x

/-- **State formula.** The full state vector of the image of a Tor class under the Tor
automorphism of an edge sign is the edge-sign scaling of its full state vector. -/
theorem incidenceTorFullState_sign (p : ℕ) (y : G.incidenceTor p) :
    G.incidenceTorFullState p (G.incidenceTorSign ε p y) =
      G.edgeSignState ε ℂ (G.incidenceTorFullState p y) :=
  incidenceTorFullState_transport (edgeSignCoeff ε) (constantCoeff_edgeSignCoeff ε)
    (G.edgeSignIncidence ε) (G.edgeSignIncidence_coeffHom ε) (G.edgeSignFreeTerm ε)
    (G.edgeSignFreeTerm_differential ε) (G.edgeSignFreeTerm_augmentation ε) p
    (G.edgeSignState ε ℂ) (fun x => G.mapRange_edgeSignResolution ε x.val) y

/-- **State formula in coordinates.** The coefficient of the image of a Tor class at a state of
the edge set `S` is `∏_{e ∈ S} ε_e` times the coefficient of the class. -/
theorem incidenceTorFullState_sign_apply (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) :
    G.incidenceTorFullState p (G.incidenceTorSign ε p y) b =
      ε.setSign ℂ b.1 * G.incidenceTorFullState p y b := by
  rw [incidenceTorFullState_sign, edgeSignState_apply]

/-- The Tor automorphism of an edge sign preserves the standard Tor product. -/
theorem incidenceTorSign_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    G.incidenceTorSign ε (p + q) (G.incidenceTorProduct p q x y) =
      G.incidenceTorProduct p q (G.incidenceTorSign ε p x) (G.incidenceTorSign ε q y) := by
  apply G.incidenceTorFullState_injective (p + q)
  rw [incidenceTorFullState_sign, incidenceTorFullState_product, incidenceTorFullState_product,
    incidenceTorFullState_sign, incidenceTorFullState_sign, edgeSignState_incStateCup]

/-- The Tor automorphism of an edge sign fixes the unit of Tor. -/
theorem incidenceTorSign_one : G.incidenceTorSign ε 0 G.incidenceTorOne = G.incidenceTorOne := by
  apply G.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_sign, incidenceTorFullState_one, edgeSignState_incStateUnit]

/-! ## Identity, composition and involution -/

/-- The Tor automorphism of the trivial edge sign is the identity. -/
theorem incidenceTorSign_trivial (p : ℕ) (y : G.incidenceTor p) :
    G.incidenceTorSign (1 : EdgeSign E) p y = y :=
  G.incidenceTorFullState_injective p (by rw [incidenceTorFullState_sign, edgeSignState_one])

/-- The Tor automorphism of a product of edge signs is the composite of the Tor automorphisms. -/
theorem incidenceTorSign_mul (ε' : EdgeSign E) (p : ℕ) (y : G.incidenceTor p) :
    G.incidenceTorSign (ε * ε') p y = G.incidenceTorSign ε p (G.incidenceTorSign ε' p y) :=
  G.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_sign, incidenceTorFullState_sign, incidenceTorFullState_sign,
      edgeSignState_mul])

/-- The Tor automorphism of an edge sign is an involution, since every edge sign squares to the
trivial sign. -/
@[simp] theorem incidenceTorSign_incidenceTorSign (p : ℕ) (y : G.incidenceTor p) :
    G.incidenceTorSign ε p (G.incidenceTorSign ε p y) = y := by
  rw [← incidenceTorSign_mul, EdgeSign.mul_self, incidenceTorSign_trivial]

/-- The inverse of the Tor automorphism of an edge sign is itself. -/
theorem incidenceTorSign_symm_apply (p : ℕ) (y : G.incidenceTor p) :
    (G.incidenceTorSign ε p).symm y = G.incidenceTorSign ε p y := by
  rw [LinearEquiv.symm_apply_eq, incidenceTorSign_incidenceTorSign]

/-! ## Internal degrees and the naturality square -/

/-- The Tor automorphism of an edge sign preserves internal degrees. -/
theorem incidenceTorSign_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    G.incidenceTorSign ε p x ∈ G.incidenceTorInternalPiece p q := by
  rw [EdgeRelabel.mem_incidenceTorInternalPiece_iff_fullState] at hx ⊢
  intro b hb
  rw [incidenceTorFullState_sign_apply, hx b hb, mul_zero]

theorem map_incidenceTorInternalPiece_sign (p q : ℕ) :
    (G.incidenceTorInternalPiece p q).map (G.incidenceTorSign ε p : G.incidenceTor p →ₗ[ℂ] _) =
      G.incidenceTorInternalPiece p q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact G.incidenceTorSign_mem_internalPiece ε hx
  · intro y hy
    exact ⟨_, G.incidenceTorSign_mem_internalPiece ε hy, G.incidenceTorSign_incidenceTorSign ε p y⟩

/-- The Tor automorphism of an edge sign on bigraded pieces. -/
noncomputable def incidenceTorInternalSign (p q : ℕ) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] G.incidenceTorInternalPiece p q :=
  (G.incidenceTorSign ε p).ofSubmodules _ _ (G.map_incidenceTorInternalPiece_sign ε p q)

@[simp] theorem incidenceTorInternalSign_val (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    (G.incidenceTorInternalSign ε p q x : G.incidenceTor p) = G.incidenceTorSign ε p x.val :=
  rfl

/-- **Naturality of the bigraded Tor isomorphism under edge signs.** The isomorphism
`incidenceTorExteriorEquiv` intertwines the Tor automorphism of an edge sign with its exterior
cohomology automorphism. -/
theorem incidenceTorExteriorEquiv_sign {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    G.incidenceTorExteriorEquiv h (G.incidenceTorInternalSign ε p q x) =
      G.exteriorCohomologySignLinear ε ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  apply G.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, exteriorCohomologySignLinear_apply,
    exteriorCohomologyState_sign, exteriorCohomologyState_incidenceTorExteriorEquiv,
    incidenceTorInternalSign_val, incidenceTorFullState_sign]

end BPFixedPoints.Multigraph
