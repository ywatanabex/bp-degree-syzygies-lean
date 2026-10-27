import BPFixedPoints.Incidence.IncidenceEdgeSignTor

/-!
# Signed edge relabelings and the functoriality of Tor and exterior cohomology

A signed edge relabeling `φ : SignedEdgeRelabel G H` is an edge relabeling together with an edge
sign `ε = φ.edgeSign` on the source edges: the orientation-line signs `ε_φ(e)` of the
functoriality proposition of the paper. Its coefficient map is
`c_{e,α,β} ↦ ε_e c_{φ e,α,β}` (with the endpoint indices exchanged when `e` is reversed), the
composite of the coefficient sign change of `G` and the unsigned coefficient relabeling
(`signedCoeffEquiv`). It carries the chart equation of `e` to `ε_e` times the chart equation of
`φ e` (`rename_varSignHom_incChartEq`), the Lean counterpart of the paper's
`a_φ^* b_e = ε_φ(e) b_{φ(e)}`.

**Order convention.** Every map of a signed relabeling is the sign change on the source graph `G`
followed by the unsigned relabeling `G → H`: the Tor map is
`φ.incidenceTorSignedRelabel p = (G.incidenceTorSign ε p).trans (φ.incidenceTorRelabel p)`, and the
exterior map is `(G.exteriorCohomologySign ε R q j).trans (φ.exteriorCohomologyRelabel R q j)`.

The Tor map is also the derived ring change along the signed coefficient isomorphism and the signed
incidence ring isomorphism (`incidenceTorSignedRelabel_eq_transport`), computed by the composite
chain map. Its state formula multiplies the coefficient of a state of the edge set `S` by the total
sign `φ.sign S * ∏_{e ∈ S} ε_e` and moves it to the relabeled state
(`incidenceTorFullState_signedRelabel_stateIndex`). Tor and exterior maps preserve products and
units, they form a naturality square with `incidenceTorExteriorEquiv`
(`incidenceTorExteriorEquiv_signedRelabel`), the identity signed relabeling acts trivially, and
the composite of signed relabelings, with signs `e ↦ ε_φ(e) · ε_ψ(φ e)`, acts by the composite
maps. Unsigned relabelings (`ofEdgeRelabel`, sign one) and pure sign changes (`ofEdgeSign`, the
identity relabeling) are special cases.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial TopologicalSpace AlgebraicGeometry

/-- A signed edge relabeling: an edge relabeling together with the orientation-line sign
`ε_φ(e) ∈ {±1}` of every source edge. -/
structure SignedEdgeRelabel {V E E' : Type} (G : Multigraph V E) (H : Multigraph V E') extends
    EdgeRelabel G H where
  /-- The orientation-line sign of each source edge. -/
  edgeSign : EdgeSign E

namespace SignedEdgeRelabel

/-! ## Identity, composition and special cases -/

/-- The identity signed relabeling: the identity relabeling with trivial signs. -/
def refl {V E : Type} (G : Multigraph V E) : SignedEdgeRelabel G G where
  toEdgeRelabel := EdgeRelabel.refl G
  edgeSign := 1

/-- The composite of signed relabelings: the composite relabeling with signs
`e ↦ ε_φ(e) · ε_ψ(φ e)`. -/
def trans {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'} {K : Multigraph V E''}
    (φ : SignedEdgeRelabel G H) (ψ : SignedEdgeRelabel H K) : SignedEdgeRelabel G K where
  toEdgeRelabel := φ.toEdgeRelabel.trans ψ.toEdgeRelabel
  edgeSign e := φ.edgeSign e * ψ.edgeSign (φ.edge e)

@[simp] theorem refl_toEdgeRelabel {V E : Type} (G : Multigraph V E) :
    (refl G).toEdgeRelabel = EdgeRelabel.refl G := rfl

@[simp] theorem refl_edgeSign {V E : Type} (G : Multigraph V E) : (refl G).edgeSign = 1 := rfl

@[simp] theorem trans_toEdgeRelabel {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : SignedEdgeRelabel G H) (ψ : SignedEdgeRelabel H K) :
    (φ.trans ψ).toEdgeRelabel = φ.toEdgeRelabel.trans ψ.toEdgeRelabel := rfl

theorem trans_edgeSign {V E E' E'' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    {K : Multigraph V E''} (φ : SignedEdgeRelabel G H) (ψ : SignedEdgeRelabel H K) :
    (φ.trans ψ).edgeSign = φ.edgeSign * φ.pullSign ψ.edgeSign := rfl

/-- An unsigned relabeling, as a signed relabeling with trivial signs. -/
def ofEdgeRelabel {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    (φ : EdgeRelabel G H) : SignedEdgeRelabel G H where
  toEdgeRelabel := φ
  edgeSign := 1

/-- A pure sign change, as a signed relabeling with the identity relabeling. -/
def ofEdgeSign {V E : Type} (G : Multigraph V E) (ε : EdgeSign E) : SignedEdgeRelabel G G where
  toEdgeRelabel := EdgeRelabel.refl G
  edgeSign := ε

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}
  (φ : SignedEdgeRelabel G H)

/-! ## Rings -/

/-- The signed coefficient isomorphism: the coefficient sign change of `G` followed by the
coefficient relabeling, `c_{e,α,β} ↦ ε_e c_{φ e,α,β}` (endpoint indices exchanged for a reversed
edge). -/
noncomputable def signedCoeffEquiv : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E' :=
  (edgeSignCoeff φ.edgeSign).trans φ.coeffEquiv

theorem signedCoeffEquiv_apply (r : IncCoeffRing E) :
    φ.signedCoeffEquiv r = φ.coeffEquiv (edgeSignCoeff φ.edgeSign r) := rfl

@[simp] theorem signedCoeffEquiv_X (e : E) (ab : Fin 2 × Fin 2) :
    φ.signedCoeffEquiv (X (e, ab)) =
      ((φ.edgeSign e : ℤ) : IncCoeffRing E') * X (φ.edge e, φ.endpointIndex e ab) := by
  rw [signedCoeffEquiv_apply, edgeSignCoeff_X, map_mul, map_intCast, EdgeRelabel.coeffEquiv_X,
    EdgeRelabel.coeffIdxEquiv_apply]

/-- The signed coefficient isomorphism preserves the coefficient origin. -/
@[simp] theorem constantCoeff_signedCoeffEquiv (r : IncCoeffRing E) :
    constantCoeff (φ.signedCoeffEquiv r) = constantCoeff r := by
  rw [signedCoeffEquiv_apply, EdgeRelabel.constantCoeff_coeffEquiv, constantCoeff_edgeSignCoeff]

/-- The signed relabeling carries the chart equation of `e` to `ε_e` times the chart equation of
the image edge, the counterpart of `a_φ^* b_e = ε_φ(e) b_{φ(e)}`. -/
theorem rename_varSignHom_incChartEq (σ : V → Bool) (e : E) :
    rename φ.chartVarEquiv (varSignHom φ.edgeSign.chartVarSign (G.incChartEq σ e)) =
      ((φ.edgeSign e : ℤ) : MvPolynomial (IncChartVar V E') ℂ) * H.incChartEq σ (φ.edge e) := by
  rw [varSignHom_incChartEq, map_mul, map_intCast, EdgeRelabel.rename_incChartEq]

/-- The signed incidence ring isomorphism: the incidence sign change of `G` followed by the
incidence relabeling. -/
noncomputable def signedIncidenceEquiv : G.IncidenceRing ≃ₐ[ℂ] H.IncidenceRing :=
  (G.edgeSignIncidence φ.edgeSign).trans φ.incidenceEquiv

theorem signedIncidenceEquiv_apply (x : G.IncidenceRing) :
    φ.signedIncidenceEquiv x = φ.incidenceEquiv (G.edgeSignIncidence φ.edgeSign x) := rfl

/-- The signed incidence ring isomorphism intertwines the coefficient maps through the signed
coefficient isomorphism. -/
theorem signedIncidenceEquiv_coeffHom (r : IncCoeffRing E) :
    φ.signedIncidenceEquiv (G.coeffHom r) = H.coeffHom (φ.signedCoeffEquiv r) := by
  rw [signedIncidenceEquiv_apply, edgeSignIncidence_coeffHom, EdgeRelabel.incidenceEquiv_coeffHom]
  rfl

/-! ## States -/

/-- The signed relabeling of states: the edge-sign scaling of `G` followed by the relabeling of
states. -/
noncomputable def signedStateRelabel (R : Type) [CommRing R] :
    (G.IncResolutionBasis →₀ R) ≃ₗ[R] (H.IncResolutionBasis →₀ R) :=
  (G.edgeSignState φ.edgeSign R).trans (φ.stateRelabel R)

theorem signedStateRelabel_apply (R : Type) [CommRing R] (z : G.IncResolutionBasis →₀ R) :
    φ.signedStateRelabel R z = φ.stateRelabel R (G.edgeSignState φ.edgeSign R z) := rfl

/-- Coefficients of a signed relabeled state vector: the total sign `φ.sign S * ∏_{e ∈ S} ε_e`
times the original coefficient. -/
theorem signedStateRelabel_apply_stateIndex (R : Type) [CommRing R]
    (z : G.IncResolutionBasis →₀ R) (b : G.IncResolutionBasis) :
    φ.signedStateRelabel R z (φ.stateIndex b) =
      φ.sign R b.1 * φ.edgeSign.setSign R b.1 * z b := by
  rw [signedStateRelabel_apply, EdgeRelabel.stateRelabel_apply_stateIndex, edgeSignState_apply,
    mul_assoc]

/-- The signed relabeling of states preserves the state product. -/
theorem signedStateRelabel_incStateCup (R : Type) [CommRing R] (x y : G.IncResolutionBasis →₀ R) :
    φ.signedStateRelabel R (G.incStateCup R x y) =
      H.incStateCup R (φ.signedStateRelabel R x) (φ.signedStateRelabel R y) := by
  rw [signedStateRelabel_apply, edgeSignState_incStateCup, EdgeRelabel.stateRelabel_incStateCup]
  rfl

/-- The signed relabeling of states preserves the unit state. -/
theorem signedStateRelabel_incStateUnit (R : Type) [CommRing R] :
    φ.signedStateRelabel R (G.incStateUnit R) = H.incStateUnit R := by
  rw [signedStateRelabel_apply, edgeSignState_incStateUnit, EdgeRelabel.stateRelabel_incStateUnit]

/-! ## Tor -/

/-- The termwise chain map of a signed relabeling: the sign change of `G` followed by the
relabeling of the actual free resolutions. -/
noncomputable def signedFreeTermRelabel (n : ℕ) :
    G.IncFreeTerm n →ₛₗ[φ.signedCoeffEquiv.toAlgHom.toRingHom] H.IncFreeTerm n where
  toFun x := φ.freeTermRelabel n (G.edgeSignFreeTerm φ.edgeSign n x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    rfl

theorem signedFreeTermRelabel_apply (n : ℕ) (x : G.IncFreeTerm n) :
    φ.signedFreeTermRelabel n x = φ.freeTermRelabel n (G.edgeSignFreeTerm φ.edgeSign n x) := rfl

theorem signedFreeTermRelabel_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.signedFreeTermRelabel (n + 1) x) =
      φ.signedFreeTermRelabel n (G.incFreeTermDifferential n x) := by
  rw [signedFreeTermRelabel_apply, signedFreeTermRelabel_apply,
    EdgeRelabel.freeTermRelabel_differential, edgeSignFreeTerm_differential]

theorem signedFreeTermRelabel_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.signedFreeTermRelabel 0 x) =
      φ.signedIncidenceEquiv (G.incResolutionAugmentation x) := by
  rw [signedFreeTermRelabel_apply, EdgeRelabel.freeTermRelabel_augmentation,
    edgeSignFreeTerm_augmentation]
  rfl

/-- The Tor map of a signed relabeling: the Tor automorphism of the edge sign on `G` followed by
the Tor map of the unsigned relabeling. -/
noncomputable def incidenceTorSignedRelabel (p : ℕ) : G.incidenceTor p ≃ₗ[ℂ] H.incidenceTor p :=
  (G.incidenceTorSign φ.edgeSign p).trans (φ.incidenceTorRelabel p)

theorem incidenceTorSignedRelabel_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorSignedRelabel p y = φ.incidenceTorRelabel p (G.incidenceTorSign φ.edgeSign p y) :=
  rfl

/-- The Tor map of a signed relabeling sends the specialization of a free-resolution element to
the specialization of its image under the composite chain map. -/
theorem incidenceTorSignedRelabel_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorSignedRelabel p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.signedFreeTermRelabel p x) := by
  rw [incidenceTorSignedRelabel_apply, incidenceTorSign_class,
    EdgeRelabel.incidenceTorRelabel_class]
  rfl

/-- The Tor map of a signed relabeling is the derived ring change along the signed coefficient
isomorphism and the signed incidence ring isomorphism. -/
theorem incidenceTorSignedRelabel_eq_transport (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorSignedRelabel p y =
      incidenceTorTransport φ.signedCoeffEquiv φ.constantCoeff_signedCoeffEquiv
        φ.signedIncidenceEquiv φ.signedIncidenceEquiv_coeffHom p y := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [incidenceTorSignedRelabel_class,
    incidenceTorTransport_class φ.signedCoeffEquiv φ.constantCoeff_signedCoeffEquiv
      φ.signedIncidenceEquiv φ.signedIncidenceEquiv_coeffHom φ.signedFreeTermRelabel
      φ.signedFreeTermRelabel_differential φ.signedFreeTermRelabel_augmentation]

/-- **State formula.** The full state vector of the image of a Tor class under a signed
relabeling is the signed relabeling of its full state vector. -/
theorem incidenceTorFullState_signedRelabel (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorSignedRelabel p y) =
      φ.signedStateRelabel ℂ (G.incidenceTorFullState p y) := by
  rw [incidenceTorSignedRelabel_apply, EdgeRelabel.incidenceTorFullState_relabel,
    incidenceTorFullState_sign]
  rfl

/-- **State formula in coordinates.** The coefficient of the image of a Tor class at the relabeled
state of a state of the edge set `S` is the total sign `φ.sign S * ∏_{e ∈ S} ε_e` times the
coefficient of the class. -/
theorem incidenceTorFullState_signedRelabel_stateIndex (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) :
    H.incidenceTorFullState p (φ.incidenceTorSignedRelabel p y) (φ.stateIndex b) =
      φ.sign ℂ b.1 * φ.edgeSign.setSign ℂ b.1 * G.incidenceTorFullState p y b := by
  rw [incidenceTorFullState_signedRelabel, signedStateRelabel_apply_stateIndex]

/-- The Tor map of a signed relabeling preserves the standard Tor product. -/
theorem incidenceTorSignedRelabel_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorSignedRelabel (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorSignedRelabel p x)
        (φ.incidenceTorSignedRelabel q y) := by
  rw [incidenceTorSignedRelabel_apply, incidenceTorSign_product,
    EdgeRelabel.incidenceTorRelabel_product]
  rfl

/-- The Tor map of a signed relabeling sends the unit of Tor to the unit. -/
theorem incidenceTorSignedRelabel_one :
    φ.incidenceTorSignedRelabel 0 G.incidenceTorOne = H.incidenceTorOne := by
  rw [incidenceTorSignedRelabel_apply, incidenceTorSign_one, EdgeRelabel.incidenceTorRelabel_one]

/-- The Tor map of a signed relabeling on bigraded pieces. -/
noncomputable def incidenceTorInternalSignedRelabel (p q : ℕ) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (G.incidenceTorInternalSign φ.edgeSign p q).trans (φ.incidenceTorInternalRelabel p q)

@[simp] theorem incidenceTorInternalSignedRelabel_val (p q : ℕ)
    (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalSignedRelabel p q x : H.incidenceTor p) =
      φ.incidenceTorSignedRelabel p x.val := rfl

/-! ## Exterior cohomology -/

section Exterior

attribute [local instance] exteriorProductHasExt

variable (R : Type) [CommRing R]

/-- The exterior cohomology map of a signed relabeling: the exterior sign change of `G` followed
by the exterior relabeling. -/
noncomputable def exteriorCohomologySignedRelabel (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  (G.exteriorCohomologySign φ.edgeSign R q j).trans (φ.exteriorCohomologyRelabel R q j)

theorem exteriorCohomologySignedRelabel_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologySignedRelabel R q j x =
      φ.exteriorCohomologyRelabel R q j (G.exteriorCohomologySign φ.edgeSign R q j x) := rfl

variable [IsNoetherianRing R]

/-- The state vector of the image of an exterior class under a signed relabeling is the signed
relabeling of its state vector. -/
theorem exteriorCohomologyState_signedRelabel (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologySignedRelabel R q j x) =
      φ.signedStateRelabel R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologySignedRelabel_apply, EdgeRelabel.exteriorCohomologyState_relabel,
    exteriorCohomologyState_sign]
  rfl

/-- The exterior cohomology map of a signed relabeling, as a linear isomorphism for the original
geometric base actions. -/
noncomputable def exteriorCohomologySignedRelabelLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R] Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := H.exteriorBundleCohomologyModule R q j
  (G.exteriorCohomologySignLinear φ.edgeSign R q j).trans (φ.exteriorCohomologyRelabelLinear R q j)

theorem exteriorCohomologySignedRelabelLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologySignedRelabelLinear R q j x = φ.exteriorCohomologySignedRelabel R q j x :=
  rfl

/-- Signed relabelings preserve the exterior cohomology products. -/
theorem exteriorCohomologySignedRelabel_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologySignedRelabel R (q + q') (i + j)
        (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologySignedRelabel R q i x)
        (φ.exteriorCohomologySignedRelabel R q' j y) := by
  rw [exteriorCohomologySignedRelabel_apply, exteriorCohomologySign_product,
    EdgeRelabel.exteriorCohomologyRelabel_product]
  rfl

/-- Signed relabelings send the exterior cohomology unit to the unit. -/
theorem exteriorCohomologySignedRelabel_unit :
    φ.exteriorCohomologySignedRelabel R 0 0 (G.exteriorCohomologyUnit R) =
      H.exteriorCohomologyUnit R := by
  rw [exteriorCohomologySignedRelabel_apply, exteriorCohomologySign_unit,
    EdgeRelabel.exteriorCohomologyRelabel_unit]

end Exterior

/-- **Naturality of the bigraded Tor isomorphism under signed relabelings.** The isomorphism
`incidenceTorExteriorEquiv` intertwines the Tor map of a signed relabeling with its exterior
cohomology map: the composite of the naturality squares of the sign change and of the unsigned
relabeling. -/
theorem incidenceTorExteriorEquiv_signedRelabel {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalSignedRelabel p q x) =
      φ.exteriorCohomologySignedRelabelLinear ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  rw [incidenceTorInternalSignedRelabel, LinearEquiv.trans_apply,
    EdgeRelabel.incidenceTorExteriorEquiv_natural, incidenceTorExteriorEquiv_sign]
  rfl

/-! ## Functoriality -/

/-- An unsigned relabeling, regarded as a signed relabeling, has its unsigned Tor map. -/
theorem incidenceTorSignedRelabel_ofEdgeRelabel (ψ : EdgeRelabel G H) (p : ℕ)
    (y : G.incidenceTor p) :
    (ofEdgeRelabel ψ).incidenceTorSignedRelabel p y = ψ.incidenceTorRelabel p y := by
  rw [incidenceTorSignedRelabel_apply]
  exact congrArg (ψ.incidenceTorRelabel p) (G.incidenceTorSign_trivial p y)

/-- A pure sign change, regarded as a signed relabeling, has the Tor map of the edge sign. -/
theorem incidenceTorSignedRelabel_ofEdgeSign (ε : EdgeSign E) (p : ℕ) (y : G.incidenceTor p) :
    (ofEdgeSign G ε).incidenceTorSignedRelabel p y = G.incidenceTorSign ε p y := by
  rw [incidenceTorSignedRelabel_apply]
  exact EdgeRelabel.incidenceTorRelabel_refl G p _

/-- The identity signed relabeling acts trivially on Tor. -/
theorem incidenceTorSignedRelabel_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorSignedRelabel p y = y := by
  rw [incidenceTorSignedRelabel_apply]
  exact (EdgeRelabel.incidenceTorRelabel_refl G p _).trans (G.incidenceTorSign_trivial p y)

/-- The signed relabeling of states of a composite is the composite of the signed relabelings. -/
theorem signedStateRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : SignedEdgeRelabel H K) (R : Type) [CommRing R]
    (z : G.IncResolutionBasis →₀ R) :
    (φ.trans ψ).signedStateRelabel R z = ψ.signedStateRelabel R (φ.signedStateRelabel R z) := by
  rw [signedStateRelabel_apply, signedStateRelabel_apply, signedStateRelabel_apply,
    ← EdgeRelabel.stateRelabel_edgeSignState, ← edgeSignState_mul, ← EdgeRelabel.stateRelabel_trans,
    trans_edgeSign, mul_comm]
  rfl

/-- The Tor map of a composite of signed relabelings is the composite of the Tor maps. -/
theorem incidenceTorSignedRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : SignedEdgeRelabel H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans ψ).incidenceTorSignedRelabel p y =
      ψ.incidenceTorSignedRelabel p (φ.incidenceTorSignedRelabel p y) :=
  K.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_signedRelabel, incidenceTorFullState_signedRelabel,
      incidenceTorFullState_signedRelabel, signedStateRelabel_trans])

section ExteriorFunctoriality

attribute [local instance] exteriorProductHasExt

/-- The identity signed relabeling acts trivially on exterior cohomology. -/
theorem exteriorCohomologySignedRelabel_refl (G : Multigraph V E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (refl G).exteriorCohomologySignedRelabel ℂ q j x = x := by
  rw [exteriorCohomologySignedRelabel_apply]
  exact (EdgeRelabel.exteriorCohomologyRelabel_refl G q j _).trans
    (G.exteriorCohomologySign_one ℂ q j x)

/-- The exterior cohomology map of a composite of signed relabelings is the composite of the
maps. -/
theorem exteriorCohomologySignedRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : SignedEdgeRelabel H K) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (φ.trans ψ).exteriorCohomologySignedRelabel ℂ q j x =
      ψ.exteriorCohomologySignedRelabel ℂ q j (φ.exteriorCohomologySignedRelabel ℂ q j x) :=
  K.exteriorCohomologyState_injective ℂ q j (by
    rw [exteriorCohomologyState_signedRelabel, exteriorCohomologyState_signedRelabel,
      exteriorCohomologyState_signedRelabel, signedStateRelabel_trans])

end ExteriorFunctoriality

end SignedEdgeRelabel

end BPFixedPoints.Multigraph
