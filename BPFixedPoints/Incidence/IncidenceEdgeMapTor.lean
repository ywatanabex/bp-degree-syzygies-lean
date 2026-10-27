import BPFixedPoints.Incidence.DerivedRingMap
import BPFixedPoints.Incidence.IncidenceEdgeMapResolution

/-!
# The Tor map of an edge map

For `φ : EdgeMap G H` the coefficient ring homomorphism `ρ` and the incidence ring homomorphism,
which is `ρ`-linear on coefficient modules (`incidenceModuleMap`), give the map of actual Tor
spaces `incidenceTorEdgeMap p : Tor_p^{S_G}(𝒰_G, ℂ) → Tor_p^{S_H}(𝒰_H, ℂ)`. It is defined as the
derived ring map `derivedRingMap` along `ρ` (Tor with changing coefficient rings); no flatness of
`ρ` is used and nothing about states enters the definition.

The chain map `F_φ` of the actual free resolutions computes it (`incidenceTorEdgeMapHom_eq`,
`incidenceTorEdgeMap_class`). At the coefficient origin `F_φ` is the state map, so the full state
vector of the image of a Tor class is the state map of its full state vector
(`incidenceTorFullState_edgeMap`): a state of an edge set `S` goes to the wedge sign of `S` times the
same state of `φ S` when `φ` is injective on `S`, and to zero otherwise. Consequently the Tor map
preserves the standard Tor product and the unit, preserves internal degrees, is the identity for the
identity edge map, is compatible with composition, and agrees with the Tor map
`incidenceTorRelabel` of an edge relabeling.

The identity, composition and relabeling laws are proved through the injective full state vectors,
not through `derivedRingMap_id` and `derivedRingMap_comp`. Orientation signs of edges are not
included.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- The incidence ring homomorphism intertwines the coefficient actions. -/
theorem incidenceHom_coeff_mul (r : IncCoeffRing E) (x : G.IncidenceRing) :
    φ.incidenceHom (G.coeffHom r * x) = H.coeffHom (φ.coeffRingHom r) * φ.incidenceHom x := by
  rw [map_mul, incidenceHom_coeffHom, coeffRingHom_apply]

/-- The incidence ring homomorphism as a linear map from the incidence module of `G` to the
incidence module of `H` restricted along the coefficient ring homomorphism. -/
noncomputable def incidenceModuleMap :
    EdgeRelabel.incidenceModule G ⟶
      (ModuleCat.restrictScalars φ.coeffRingHom).obj (EdgeRelabel.incidenceModule H) :=
  ModuleCat.ofHom (X := EdgeRelabel.incidenceModule G)
    (Y := (ModuleCat.restrictScalars φ.coeffRingHom).obj (EdgeRelabel.incidenceModule H))
    { toFun := fun x => φ.incidenceHom x
      map_add' := fun x y => map_add φ.incidenceHom x y
      map_smul' := fun r x => φ.incidenceHom_coeff_mul r x }

theorem incidenceModuleMap_apply (x : G.IncidenceRing) :
    φ.incidenceModuleMap x = φ.incidenceHom x := rfl

/-- **The Tor map of an edge map**, as a morphism: the derived ring map along the coefficient ring
homomorphism of the incidence module map. -/
noncomputable def incidenceTorEdgeMapHom (p : ℕ) : G.incidenceTor p ⟶ H.incidenceTor p :=
  derivedRingMap φ.coeffRingHom constantCoeff constantCoeff φ.constantCoeff_comp_coeffRingHom
    φ.incidenceModuleMap p

/-- **The Tor map of an edge map**, as a linear map. -/
noncomputable def incidenceTorEdgeMap (p : ℕ) : G.incidenceTor p →ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorEdgeMapHom p).hom

theorem incidenceTorEdgeMap_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorEdgeMap p y = φ.incidenceTorEdgeMapHom p y := rfl

/-- The chain map `F_φ` of the actual free resolutions, as a chain map of complexes of coefficient
modules of `G` into the restriction of the resolution of `H`. -/
noncomputable def resolutionChainMap :
    G.incFreeResolution.complex ⟶
      ((ModuleCat.restrictScalars φ.coeffRingHom).mapHomologicalComplex _).obj
        H.incFreeResolution.complex where
  f n := ModuleCat.ofHom (X := G.IncFreeTerm n)
    (Y := (ModuleCat.restrictScalars φ.coeffRingHom).obj
      (ModuleCat.of (IncCoeffRing E') (H.IncFreeTerm n)))
    { toFun := fun x => φ.freeTermMap n x
      map_add' := fun x y => map_add (φ.freeTermMap n) x y
      map_smul' := fun r x => (φ.freeTermMap n).map_smulₛₗ r x }
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    ext x
    change H.incFreeResolution.complex.d (j + 1) j (φ.freeTermMap (j + 1) x) =
      φ.freeTermMap j (G.incFreeResolution.complex.d (j + 1) j x)
    rw [incFreeResolution_d, incFreeResolution_d]
    exact φ.freeTermMap_differential j x

theorem resolutionChainMap_f_apply (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.resolutionChainMap.f n) x = φ.freeTermMap n x := rfl

/-- The chain map `F_φ` lifts the incidence module map. -/
theorem resolutionChainMap_comm_zero :
    φ.resolutionChainMap.f 0 ≫
        (ModuleCat.restrictScalars φ.coeffRingHom).map (H.incFreeResolution.π.f 0) =
      G.incFreeResolution.π.f 0 ≫ φ.incidenceModuleMap := by
  ext x
  change H.incResolutionAugmentation (φ.freeTermMap 0 x) =
    φ.incidenceHom (G.incResolutionAugmentation x)
  exact φ.freeTermMap_augmentation x

/-- **The Tor map is computed by `F_φ`** on the actual free resolutions. -/
theorem incidenceTorEdgeMapHom_eq (p : ℕ) :
    φ.incidenceTorEdgeMapHom p =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map φ.resolutionChainMap) p ≫
          HomologicalComplex.homologyMap
            (restrictExtendComplexHom φ.coeffRingHom constantCoeff constantCoeff
              φ.constantCoeff_comp_coeffRingHom H.incFreeResolution.complex) p ≫
            (H.incFreeResolution.isoLeftDerivedObj
              (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E' →+* ℂ)) p).inv :=
  derivedRingMap_eq φ.coeffRingHom constantCoeff constantCoeff φ.constantCoeff_comp_coeffRingHom
    φ.incidenceModuleMap G.incFreeResolution H.incFreeResolution φ.resolutionChainMap
    φ.resolutionChainMap_comm_zero p

/-- In free-term coordinates the Tor map is the specialization of `F_φ`. -/
theorem incidenceTorIsoFreeTerm_edgeMap (p : ℕ) :
    φ.incidenceTorEdgeMapHom p ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          (φ.resolutionChainMap.f p) ≫
          (restrictExtendHom φ.coeffRingHom constantCoeff constantCoeff
            φ.constantCoeff_comp_coeffRingHom).app _ := by
  have hG : (G.incidenceTorIsoFreeTerm p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).obj G.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (G.incFreeResolution_minimal i j)) p).hom := rfl
  have hH : (H.incidenceTorIsoFreeTerm p).hom =
      (H.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E' →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E' →+* ℂ)).mapHomologicalComplex
            _).obj H.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (H.incFreeResolution_minimal i j)) p).hom := rfl
  rw [hG, hH, incidenceTorEdgeMapHom_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, homologyIsoTermOfZeroDifferentials_naturality]
  rfl

/-- The Tor map sends the specialization of a free-resolution element to the specialization of its
image under `F_φ`. -/
theorem incidenceTorEdgeMap_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorEdgeMap p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.freeTermMap p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom ((φ.incidenceTorEdgeMapHom p) (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (φ.freeTermMap p x))
  rw [← ConcreteCategory.comp_apply, incidenceTorIsoFreeTerm_edgeMap, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul, incFreeTermToTor_eq_tmul]
  rfl

/-- **State formula.** The full state vector of the image of a Tor class is the state map of its
full state vector: a state of an edge set `S` goes to the wedge sign of `S` times the same state of
`φ S` when `φ` is injective on `S`, and to zero otherwise. -/
theorem incidenceTorFullState_edgeMap (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorEdgeMap p y) =
      φ.stateMap ℂ (G.incidenceTorFullState p y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [incidenceTorEdgeMap_class, incidenceTorFullState_class, incidenceTorFullState_class,
    freeTermMap_val, mapRange_resolutionMap]

/-- The Tor map on a class whose full state is a basis state of an edge set where the edge
function is injective. -/
theorem incidenceTorFullState_edgeMap_of_single (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) (r : ℂ) (hy : G.incidenceTorFullState p y = single b r)
    (h : Set.InjOn φ.edge b.1) :
    H.incidenceTorFullState p (φ.incidenceTorEdgeMap p y) =
      single (φ.stateIndex b h) ((φ.wedgeSign b.1 : ℂ) * r) := by
  rw [incidenceTorFullState_edgeMap, hy, stateMap_single_of_injOn _ ℂ _ h]

/-- The Tor map kills a class whose full state is a basis state of an edge set where the edge
function is not injective. -/
theorem incidenceTorEdgeMap_eq_zero_of_single (p : ℕ) (y : G.incidenceTor p)
    (b : G.IncResolutionBasis) (r : ℂ) (hy : G.incidenceTorFullState p y = single b r)
    (h : ¬ Set.InjOn φ.edge b.1) : φ.incidenceTorEdgeMap p y = 0 := by
  apply H.incidenceTorFullState_injective p
  rw [incidenceTorFullState_edgeMap, hy, stateMap_single_of_not_injOn _ ℂ _ h, map_zero]

/-- The Tor map preserves the standard Tor product. -/
theorem incidenceTorEdgeMap_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorEdgeMap (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorEdgeMap p x) (φ.incidenceTorEdgeMap q y) := by
  apply H.incidenceTorFullState_injective (p + q)
  rw [incidenceTorFullState_edgeMap, incidenceTorFullState_product, incidenceTorFullState_product,
    incidenceTorFullState_edgeMap, incidenceTorFullState_edgeMap, stateMap_incStateCup]

/-- The Tor map sends the unit of Tor to the unit. -/
theorem incidenceTorEdgeMap_one :
    φ.incidenceTorEdgeMap 0 G.incidenceTorOne = H.incidenceTorOne := by
  apply H.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_edgeMap, incidenceTorFullState_one, incidenceTorFullState_one,
    stateMap_incStateUnit]

/-! ## Identity, composition and relabelings -/

/-- **Identity law.** The Tor map of the identity edge map is the identity. -/
theorem incidenceTorEdgeMap_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorEdgeMap p y = y :=
  G.incidenceTorFullState_injective p (by rw [incidenceTorFullState_edgeMap, stateMap_refl])

/-- **Composition law.** The Tor map of a composite edge map is the composite of the Tor maps. -/
theorem incidenceTorEdgeMap_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : EdgeMap H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans ψ).incidenceTorEdgeMap p y = ψ.incidenceTorEdgeMap p (φ.incidenceTorEdgeMap p y) :=
  K.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_edgeMap, incidenceTorFullState_edgeMap,
      incidenceTorFullState_edgeMap, stateMap_trans])

/-! ## Internal degrees -/

/-- The state map vanishes at a state which is not the image of a state where the vector is
nonzero. -/
theorem stateMap_apply_eq_zero (R : Type) [CommRing R] (z : G.IncResolutionBasis →₀ R)
    (b : H.IncResolutionBasis)
    (hz : ∀ b' (h : Set.InjOn φ.edge b'.1), φ.stateIndex b' h = b → z b' = 0) :
    φ.stateMap R z b = 0 := by
  rw [← z.sum_single, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [stateMap_single]
  split_ifs with h
  · by_cases hb : φ.stateIndex b' h = b
    · rw [hz b' h hb, mul_zero, single_zero, Finsupp.zero_apply]
    · exact single_eq_of_ne (Ne.symm hb)
  · rfl

/-- The Tor map preserves internal degrees. -/
theorem incidenceTorEdgeMap_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorEdgeMap p x ∈ H.incidenceTorInternalPiece p q := by
  rw [EdgeRelabel.mem_incidenceTorInternalPiece_iff_fullState] at hx ⊢
  intro b hb
  rw [incidenceTorFullState_edgeMap]
  apply stateMap_apply_eq_zero
  intro b' h hb'
  apply hx
  rw [← incResolutionInternalDegree_stateIndex φ b' h, hb']
  exact hb

/-- The Tor map of an edge map on bigraded pieces. -/
noncomputable def incidenceTorInternalEdgeMap (p q : ℕ) :
    G.incidenceTorInternalPiece p q →ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorEdgeMap p).restrict fun _ hx => φ.incidenceTorEdgeMap_mem_internalPiece hx

@[simp] theorem incidenceTorInternalEdgeMap_val (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalEdgeMap p q x : H.incidenceTor p) = φ.incidenceTorEdgeMap p x.val :=
  rfl

end EdgeMap

/-- **Agreement with edge relabelings.** For an edge relabeling the Tor map of the underlying edge
map is the Tor map `incidenceTorRelabel`. -/
theorem EdgeRelabel.incidenceTorEdgeMap_toEdgeMap {V E E' : Type} [DecidableEq V] [Fintype V]
    [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : EdgeRelabel G H) (p : ℕ) (y : G.incidenceTor p) :
    φ.toEdgeMap.incidenceTorEdgeMap p y = φ.incidenceTorRelabel p y :=
  H.incidenceTorFullState_injective p (by
    rw [EdgeMap.incidenceTorFullState_edgeMap, incidenceTorFullState_relabel,
      toEdgeMap_stateMap])

end BPFixedPoints.Multigraph
