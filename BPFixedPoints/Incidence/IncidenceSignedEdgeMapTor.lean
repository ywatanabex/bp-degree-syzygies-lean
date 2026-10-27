import BPFixedPoints.Incidence.IncidenceSignedEdgeMapStates
import BPFixedPoints.Incidence.IncidenceEdgeMapTor
import BPFixedPoints.Incidence.IncidenceEdgeSignRelabel

/-!
# The Tor map of a signed edge map

For a signed edge map `φ : SignedEdgeMap G H` with edge sign `ε`, the signed coefficient ring
homomorphism `ρ = φ.signedCoeffRingHom` and the signed incidence ring homomorphism, which is
`ρ`-linear on coefficient modules (`signedIncidenceModuleMap`), give the map of actual Tor spaces
`incidenceTorSignedEdgeMap p : Tor_p^{S_G}(𝒰_G, ℂ) → Tor_p^{S_H}(𝒰_H, ℂ)`. It is defined as the
derived ring map `derivedRingMap` along `ρ`; no flatness of `ρ` is used and nothing about states
enters the definition.

**Two descriptions agree.** The derived ring map along the composite ring map is the composite of
the Tor automorphism of the edge sign on `G` and the Tor map of the unsigned edge map
(`incidenceTorSignedEdgeMapHom_eq_comp`): the sign automorphism, defined by `derivedRingChange`,
is rewritten as a derived ring map by `derivedRingChange_hom_eq_derivedRingMap`, and the two derived
ring maps are composed by `derivedRingMap_comp`, in the form `derivedRingMap_comp_of_apply` for a
module map along the composite ring homomorphism agreeing elementwise with the composite module map
(here `signedIncidenceModuleMap`, elementwise the incidence sign change followed by the incidence
homomorphism of the edge map).

Consequently the full state vector of the image of a Tor class is the signed state map of its full
state vector (`incidenceTorFullState_signedEdgeMap`): a state of an edge set `S` goes to
`wedgeSign S · ∏_{e ∈ S} ε_e` times the same state of `φ S` when `φ` is injective on `S`, and to zero
otherwise (`incidenceTorFullState_signedEdgeMap_of_single`,
`incidenceTorSignedEdgeMap_eq_zero_of_single`). The Tor map preserves the standard Tor product, the
unit and internal degrees; the identity signed edge map acts trivially; the composite of signed
edge maps, with signs `e ↦ ε_φ(e) · ε_ψ(φ e)`, acts by the composite; and for a signed relabeling
the Tor map is `incidenceTorSignedRelabel` (`SignedEdgeRelabel.incidenceTorSignedEdgeMap_toSignedEdgeMap`).
Unsigned edge maps and pure sign changes are special cases.

The identity and composition laws are proved through the injective full state vectors, not
through `derivedRingMap_id` and `derivedRingMap_comp`. The Tor map is not an isomorphism in
general.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

/-- The composition law `derivedRingMap_comp` for any module map along the composite ring
homomorphism which agrees elementwise with the composite of the two module maps. -/
theorem derivedRingMap_comp_of_apply {R R' R'' k : Type} [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing k] (f : R →+* R') (ε : R →+* k) (ε' : R' →+* k) (hε : ε'.comp f = ε)
    (f₂ : R' →+* R'') (ε'' : R'' →+* k) (hε₂ : ε''.comp f₂ = ε')
    (hε₁₂ : ε''.comp (f₂.comp f) = ε)
    {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'} {M'' : ModuleCat.{0} R''}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj M')
    (g₂ : M' ⟶ (ModuleCat.restrictScalars f₂).obj M'')
    (h : M ⟶ (ModuleCat.restrictScalars (f₂.comp f)).obj M'') (hh : ∀ x, h x = g₂ (g x)) (n : ℕ) :
    derivedRingMap (f₂.comp f) ε ε'' hε₁₂ h n =
      derivedRingMap f ε ε' hε g n ≫ derivedRingMap f₂ ε' ε'' hε₂ g₂ n := by
  have hh' : h = g ≫ (ModuleCat.restrictScalars f).map g₂ ≫
      (ModuleCat.restrictScalarsComp.{0} f f₂).inv.app M'' := by
    ext x
    exact hh x
  subst hh'
  exact derivedRingMap_comp f ε ε' hε g f₂ ε'' hε₂ g₂ n

namespace SignedEdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : SignedEdgeMap G H)

/-! ## The Tor map and its two descriptions -/

/-- The signed incidence ring homomorphism as a linear map from the incidence module of `G` to the
incidence module of `H` restricted along the signed coefficient ring homomorphism. -/
noncomputable def signedIncidenceModuleMap :
    EdgeRelabel.incidenceModule G ⟶
      (ModuleCat.restrictScalars φ.signedCoeffRingHom).obj (EdgeRelabel.incidenceModule H) :=
  ModuleCat.ofHom (X := EdgeRelabel.incidenceModule G)
    (Y := (ModuleCat.restrictScalars φ.signedCoeffRingHom).obj (EdgeRelabel.incidenceModule H))
    { toFun := fun x => φ.signedIncidenceHom x
      map_add' := fun x y => map_add φ.signedIncidenceHom x y
      map_smul' := fun r x => φ.signedIncidenceHom_coeff_mul r x }

theorem signedIncidenceModuleMap_apply (x : G.IncidenceRing) :
    φ.signedIncidenceModuleMap x = φ.signedIncidenceHom x := rfl

/-- **The Tor map of a signed edge map**, as a morphism: the derived ring map along the signed
coefficient ring homomorphism of the signed incidence module map. -/
noncomputable def incidenceTorSignedEdgeMapHom (p : ℕ) : G.incidenceTor p ⟶ H.incidenceTor p :=
  derivedRingMap φ.signedCoeffRingHom constantCoeff constantCoeff
    φ.constantCoeff_comp_signedCoeffRingHom φ.signedIncidenceModuleMap p

/-- **The Tor map of a signed edge map**, as a linear map. -/
noncomputable def incidenceTorSignedEdgeMap (p : ℕ) : G.incidenceTor p →ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorSignedEdgeMapHom p).hom

/-- **The two descriptions agree.** The derived ring map along the composite of the coefficient
sign change and the coefficient renaming is the Tor automorphism of the edge sign on `G` followed by
the Tor map of the unsigned edge map. -/
theorem incidenceTorSignedEdgeMapHom_eq_comp (p : ℕ) :
    φ.incidenceTorSignedEdgeMapHom p =
      (G.incidenceTorSignIso φ.edgeSign p).hom ≫ φ.toEdgeMap.incidenceTorEdgeMapHom p := by
  rw [incidenceTorSignIso, incidenceTorTransportIso, derivedRingChange_hom_eq_derivedRingMap,
    EdgeMap.incidenceTorEdgeMapHom]
  exact derivedRingMap_comp_of_apply _ _ _ _ _ _ _ _ _ _ φ.signedIncidenceModuleMap
    (fun _ => rfl) p

/-- The Tor map of a signed edge map is the Tor automorphism of the edge sign followed by the Tor
map of the edge map. -/
theorem incidenceTorSignedEdgeMap_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorSignedEdgeMap p y =
      φ.toEdgeMap.incidenceTorEdgeMap p (G.incidenceTorSign φ.edgeSign p y) := by
  rw [incidenceTorSignedEdgeMap, incidenceTorSignedEdgeMapHom_eq_comp]
  rfl

/-- The Tor map of a signed edge map, as a composite of linear maps. -/
theorem incidenceTorSignedEdgeMap_eq_comp (p : ℕ) :
    φ.incidenceTorSignedEdgeMap p =
      φ.toEdgeMap.incidenceTorEdgeMap p ∘ₗ (G.incidenceTorSign φ.edgeSign p).toLinearMap :=
  LinearMap.ext (φ.incidenceTorSignedEdgeMap_apply p)

/-- The Tor map sends the specialization of a free-resolution element to the specialization of its
image under the composite chain map: the sign change of `G` followed by `F_φ`. -/
theorem incidenceTorSignedEdgeMap_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorSignedEdgeMap p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.toEdgeMap.freeTermMap p (G.edgeSignFreeTerm φ.edgeSign p x)) := by
  rw [incidenceTorSignedEdgeMap_apply, incidenceTorSign_class, EdgeMap.incidenceTorEdgeMap_class]

/-! ## The state formula -/

/-- **State formula.** The full state vector of the image of a Tor class is the signed state map
of its full state vector. -/
theorem incidenceTorFullState_signedEdgeMap (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorSignedEdgeMap p y) =
      φ.signedStateMap ℂ (G.incidenceTorFullState p y) := by
  rw [incidenceTorSignedEdgeMap_apply, EdgeMap.incidenceTorFullState_edgeMap,
    incidenceTorFullState_sign]
  rfl

/-- **State formula on basis states, injective case.** If the full state of a Tor class is
`r` times the basis state `b` of an edge set `S` on which the edge function is injective, the full
state of its image is `wedgeSign S · ∏_{e ∈ S} ε_e · r` times the same state of `φ S`. -/
theorem incidenceTorFullState_signedEdgeMap_of_single (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) (r : ℂ) (hy : G.incidenceTorFullState p y = single b r)
    (h : Set.InjOn φ.edge b.1) :
    H.incidenceTorFullState p (φ.incidenceTorSignedEdgeMap p y) =
      single (φ.toEdgeMap.stateIndex b h)
        ((φ.toEdgeMap.wedgeSign b.1 : ℂ) * φ.edgeSign.setSign ℂ b.1 * r) := by
  rw [incidenceTorFullState_signedEdgeMap, hy, signedStateMap_single_of_injOn _ ℂ _ h]

/-- **State formula on basis states, non-injective case.** The Tor map kills a class whose full
state is a basis state of an edge set on which the edge function is not injective. -/
theorem incidenceTorSignedEdgeMap_eq_zero_of_single (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) (r : ℂ) (hy : G.incidenceTorFullState p y = single b r)
    (h : ¬ Set.InjOn φ.edge b.1) : φ.incidenceTorSignedEdgeMap p y = 0 := by
  apply H.incidenceTorFullState_injective p
  rw [incidenceTorFullState_signedEdgeMap, hy, signedStateMap_single_of_not_injOn _ ℂ _ h,
    map_zero]

/-! ## Products, units and internal degrees -/

/-- The Tor map of a signed edge map preserves the standard Tor product. -/
theorem incidenceTorSignedEdgeMap_product (p q : ℕ) (x : G.incidenceTor p)
    (y : G.incidenceTor q) :
    φ.incidenceTorSignedEdgeMap (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorSignedEdgeMap p x)
        (φ.incidenceTorSignedEdgeMap q y) := by
  rw [incidenceTorSignedEdgeMap_apply, incidenceTorSign_product,
    EdgeMap.incidenceTorEdgeMap_product, incidenceTorSignedEdgeMap_apply,
    incidenceTorSignedEdgeMap_apply]

/-- The Tor map of a signed edge map sends the unit of Tor to the unit. -/
theorem incidenceTorSignedEdgeMap_one :
    φ.incidenceTorSignedEdgeMap 0 G.incidenceTorOne = H.incidenceTorOne := by
  rw [incidenceTorSignedEdgeMap_apply, incidenceTorSign_one, EdgeMap.incidenceTorEdgeMap_one]

/-- The Tor map of a signed edge map preserves internal degrees. -/
theorem incidenceTorSignedEdgeMap_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorSignedEdgeMap p x ∈ H.incidenceTorInternalPiece p q := by
  rw [incidenceTorSignedEdgeMap_apply]
  exact φ.toEdgeMap.incidenceTorEdgeMap_mem_internalPiece
    (G.incidenceTorSign_mem_internalPiece φ.edgeSign hx)

/-- The Tor map of a signed edge map on bigraded pieces. -/
noncomputable def incidenceTorInternalSignedEdgeMap (p q : ℕ) :
    G.incidenceTorInternalPiece p q →ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorSignedEdgeMap p).restrict fun _ hx =>
    φ.incidenceTorSignedEdgeMap_mem_internalPiece hx

@[simp] theorem incidenceTorInternalSignedEdgeMap_val (p q : ℕ)
    (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalSignedEdgeMap p q x : H.incidenceTor p) =
      φ.incidenceTorSignedEdgeMap p x.val :=
  rfl

/-! ## Identity, composition and special cases -/

/-- **Identity law.** The identity signed edge map acts trivially on Tor. -/
theorem incidenceTorSignedEdgeMap_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorSignedEdgeMap p y = y := by
  rw [incidenceTorSignedEdgeMap_apply]
  exact (EdgeMap.incidenceTorEdgeMap_refl G p _).trans (G.incidenceTorSign_trivial p y)

/-- **Composition law.** The Tor map of a composite of signed edge maps, with signs
`e ↦ ε_φ(e) · ε_ψ(φ e)`, is the composite of the Tor maps. -/
theorem incidenceTorSignedEdgeMap_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : SignedEdgeMap H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans ψ).incidenceTorSignedEdgeMap p y =
      ψ.incidenceTorSignedEdgeMap p (φ.incidenceTorSignedEdgeMap p y) :=
  K.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_signedEdgeMap, incidenceTorFullState_signedEdgeMap,
      incidenceTorFullState_signedEdgeMap, signedStateMap_trans])

/-- An unsigned edge map, regarded as a signed edge map, has its unsigned Tor map. -/
theorem incidenceTorSignedEdgeMap_ofEdgeMap (ψ : EdgeMap G H) (p : ℕ) (y : G.incidenceTor p) :
    (ofEdgeMap ψ).incidenceTorSignedEdgeMap p y = ψ.incidenceTorEdgeMap p y := by
  rw [incidenceTorSignedEdgeMap_apply]
  exact congrArg (ψ.incidenceTorEdgeMap p) (G.incidenceTorSign_trivial p y)

/-- A pure sign change, regarded as a signed edge map, has the Tor automorphism of the edge
sign. -/
theorem incidenceTorSignedEdgeMap_ofEdgeSign (ε : EdgeSign E) (p : ℕ) (y : G.incidenceTor p) :
    (ofEdgeSign G ε).incidenceTorSignedEdgeMap p y = G.incidenceTorSign ε p y := by
  rw [incidenceTorSignedEdgeMap_apply]
  exact EdgeMap.incidenceTorEdgeMap_refl G p _

end SignedEdgeMap

/-! ## Signed relabelings -/

/-- A signed edge relabeling, as a signed edge map. -/
def SignedEdgeRelabel.toSignedEdgeMap {V E E' : Type} {G : Multigraph V E} {H : Multigraph V E'}
    (φ : SignedEdgeRelabel G H) : SignedEdgeMap G H where
  toEdgeMap := φ.toEdgeRelabel.toEdgeMap
  edgeSign := φ.edgeSign

namespace SignedEdgeRelabel

@[simp] theorem toSignedEdgeMap_toEdgeMap {V E E' : Type} {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeRelabel G H) :
    φ.toSignedEdgeMap.toEdgeMap = φ.toEdgeRelabel.toEdgeMap := rfl

@[simp] theorem toSignedEdgeMap_edgeSign {V E E' : Type} {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeRelabel G H) :
    φ.toSignedEdgeMap.edgeSign = φ.edgeSign := rfl

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}
  (φ : SignedEdgeRelabel G H)

/-- For a signed relabeling the signed coefficient homomorphism is the signed coefficient
isomorphism. -/
theorem toSignedEdgeMap_signedCoeffAlgHom (r : IncCoeffRing E) :
    φ.toSignedEdgeMap.signedCoeffAlgHom r = φ.signedCoeffEquiv r := by
  have h : φ.toEdgeRelabel.toEdgeMap.coeffAlgHom = φ.coeffEquiv.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro c
    rw [EdgeMap.coeffAlgHom_X]
    exact (EdgeRelabel.coeffEquiv_X φ.toEdgeRelabel c).symm
  rw [SignedEdgeMap.signedCoeffAlgHom_apply, signedCoeffEquiv_apply]
  exact AlgHom.congr_fun h _

/-- For a signed relabeling the signed state map is the signed relabeling of states. -/
theorem toSignedEdgeMap_signedStateMap (R : Type) [CommRing R] (z : G.IncResolutionBasis →₀ R) :
    φ.toSignedEdgeMap.signedStateMap R z = φ.signedStateRelabel R z := by
  rw [SignedEdgeMap.signedStateMap_apply, signedStateRelabel_apply]
  exact EdgeRelabel.toEdgeMap_stateMap φ.toEdgeRelabel R _

/-- **Agreement with signed relabelings.** For a signed relabeling the Tor map of the underlying
signed edge map is the Tor map `incidenceTorSignedRelabel`. -/
theorem incidenceTorSignedEdgeMap_toSignedEdgeMap (p : ℕ) (y : G.incidenceTor p) :
    φ.toSignedEdgeMap.incidenceTorSignedEdgeMap p y = φ.incidenceTorSignedRelabel p y := by
  rw [SignedEdgeMap.incidenceTorSignedEdgeMap_apply, incidenceTorSignedRelabel_apply]
  exact EdgeRelabel.incidenceTorEdgeMap_toEdgeMap φ.toEdgeRelabel p _

end SignedEdgeRelabel

end BPFixedPoints.Multigraph
