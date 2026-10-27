import BPFixedPoints.Incidence.IncidenceVertexRelabelResolution
import BPFixedPoints.Incidence.IncidenceTorRelabel

/-!
# The Tor map of a vertex relabeling

For `φ : VertexRelabel G H` the coefficient ring `IncCoeffRing E` is unchanged and the incidence
ring isomorphism `φ.incidenceEquiv` is the identity on coefficients, so it is an isomorphism of
`IncCoeffRing E`-modules (`incidenceModuleIso`). The Tor map is Mathlib's functoriality of the left
derived functor of extension of scalars along the coefficient origin in the module variable:
`((ModuleCat.extendScalars constantCoeff).leftDerived p).mapIso φ.incidenceModuleIso`
(`incidenceTorVertexIso`). It is not defined through the states.

The relabeling chain map of the actual free resolutions (`resolutionVertexPerm`) lifts the module
isomorphism, so by `ProjectiveResolution.isoLeftDerivedObj_hom_naturality` it computes the Tor
map. At the coefficient origin that chain map is the signed relabeling of states, so the full
state vector of the image of a Tor class is the signed relabeling `statePerm` of its full state
vector (`incidenceTorFullState_vertexRelabel`). The sign is the Koszul sign of reordering the
degree-one factors of a state, which sit at the vertices of nonzero degree; it is nontrivial in
general. Consequently the Tor map preserves internal degrees, the standard Tor product and the
unit, and satisfies the identity and composition laws; composing with the inverse relabeling
gives the identity.

Not covered here: the corresponding map on the Ext-defined cohomology of the exterior bundles and
the naturality square of `incidenceTorExteriorEquiv` for vertex relabelings. The isomorphism of
vertex projective products and the transport of sheaf cohomology along it are in
`VertexProjectivePermutation.lean` and `VertexProjectivePermutationCohomology.lean`; the transport
of the twist sheaves and its effect on states are not formalized.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)

/-- The incidence ring isomorphism commutes with the coefficient actions. -/
theorem incidenceEquiv_coeff_mul (r : IncCoeffRing E) (x : G.IncidenceRing) :
    φ.incidenceEquiv (G.coeffHom r * x) = H.coeffHom r * φ.incidenceEquiv x := by
  rw [map_mul, incidenceEquiv_coeffHom]

/-- The incidence ring isomorphism as an isomorphism of modules over the common coefficient
ring. -/
noncomputable def incidenceLinearEquiv :
    EdgeRelabel.incidenceModule G ≃ₗ[IncCoeffRing E] EdgeRelabel.incidenceModule H where
  toFun x := φ.incidenceEquiv x
  invFun y := φ.incidenceEquiv.symm y
  map_add' x y := map_add φ.incidenceEquiv x y
  map_smul' r x := φ.incidenceEquiv_coeff_mul r x
  left_inv x := φ.incidenceEquiv.symm_apply_apply x
  right_inv y := φ.incidenceEquiv.apply_symm_apply y

/-- The incidence module isomorphism, as an isomorphism of coefficient modules. -/
noncomputable def incidenceModuleIso : EdgeRelabel.incidenceModule G ≅ EdgeRelabel.incidenceModule H :=
  φ.incidenceLinearEquiv.toModuleIso

/-- **The Tor map of a vertex relabeling**: the left derived functor of extension of scalars
along the coefficient origin, applied to the incidence module isomorphism. -/
noncomputable def incidenceTorVertexIso (p : ℕ) : G.incidenceTor p ≅ H.incidenceTor p :=
  ((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).mapIso
    φ.incidenceModuleIso

/-- The Tor map of a vertex relabeling, as a linear isomorphism. -/
noncomputable def incidenceTorVertexRelabel (p : ℕ) : G.incidenceTor p ≃ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorVertexIso p).toLinearEquiv

/-- The relabeling chain map of the actual free resolutions. -/
noncomputable def resolutionChainMap : G.incFreeResolution.complex ⟶ H.incFreeResolution.complex where
  f n := ModuleCat.ofHom (φ.freeTermVertexPerm n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    ext x
    change H.incFreeResolution.complex.d (j + 1) j (φ.freeTermVertexPerm (j + 1) x) =
      φ.freeTermVertexPerm j (G.incFreeResolution.complex.d (j + 1) j x)
    rw [incFreeResolution_d, incFreeResolution_d]
    exact φ.freeTermVertexPerm_differential j x

theorem resolutionChainMap_f_apply (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.resolutionChainMap.f n) x = φ.freeTermVertexPerm n x := rfl

/-- The relabeling chain map lifts the incidence module isomorphism. -/
theorem resolutionChainMap_comm_zero :
    φ.resolutionChainMap.f 0 ≫ H.incFreeResolution.π.f 0 =
      G.incFreeResolution.π.f 0 ≫ φ.incidenceModuleIso.hom := by
  ext x
  change H.incResolutionAugmentation (φ.freeTermVertexPerm 0 x) =
    φ.incidenceEquiv (G.incResolutionAugmentation x)
  exact φ.freeTermVertexPerm_augmentation x

/-- The Tor map of a vertex relabeling is computed by the relabeling chain map of the actual free
resolutions. -/
theorem incidenceTorVertexIso_hom_eq (p : ℕ) :
    (φ.incidenceTorVertexIso p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map φ.resolutionChainMap) p ≫
          (H.incFreeResolution.isoLeftDerivedObj
            (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).inv := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality φ.incidenceModuleIso.hom
    G.incFreeResolution H.incFreeResolution φ.resolutionChainMap φ.resolutionChainMap_comm_zero
    (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p
  rw [← Iso.eq_comp_inv] at h
  rw [incidenceTorVertexIso, Functor.mapIso_hom, h]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc]

/-- In free-term coordinates the Tor map of a vertex relabeling is the specialization of the
relabeling chain map. -/
theorem incidenceTorIsoFreeTerm_vertexRelabel (p : ℕ) :
    (φ.incidenceTorVertexIso p).hom ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          (φ.resolutionChainMap.f p) := by
  have hG : (G.incidenceTorIsoFreeTerm p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).obj G.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (G.incFreeResolution_minimal i j)) p).hom := rfl
  have hH : (H.incidenceTorIsoFreeTerm p).hom =
      (H.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).obj H.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (H.incFreeResolution_minimal i j)) p).hom := rfl
  rw [hG, hH, incidenceTorVertexIso_hom_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [homologyIsoTermOfZeroDifferentials_naturality]
  rfl

/-- The Tor map of a vertex relabeling sends the specialization of a free-resolution element to
the specialization of its relabeling. -/
theorem incidenceTorVertexRelabel_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorVertexRelabel p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.freeTermVertexPerm p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom ((φ.incidenceTorVertexIso p).hom (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (φ.freeTermVertexPerm p x))
  rw [← ConcreteCategory.comp_apply, incidenceTorIsoFreeTerm_vertexRelabel,
    ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul, incFreeTermToTor_eq_tmul]
  rfl

/-- **State formula.** The full state vector of the image of a Tor class under the Tor map of a
vertex relabeling is the signed relabeling of its full state vector. -/
theorem incidenceTorFullState_vertexRelabel (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorVertexRelabel p y) =
      φ.statePerm ℂ (G.incidenceTorFullState p y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [incidenceTorVertexRelabel_class, incidenceTorFullState_class, incidenceTorFullState_class,
    freeTermVertexPerm_val, mapRange_resolutionVertexPerm]

/-- The state formula in coordinates: the coefficient of the relabeled class at the state
`⟨S, κ⟩` of `H` is the Koszul sign of `S` times the coefficient of the class at the
corresponding state of `G`. -/
theorem incidenceTorFullState_vertexRelabel_apply (p : ℕ) (y : G.incidenceTor p)
    (b : H.IncResolutionBasis) :
    H.incidenceTorFullState p (φ.incidenceTorVertexRelabel p y) b =
      φ.stateSign ℂ b.1 * G.incidenceTorFullState p y (φ.stateIndex.symm b) := by
  rw [incidenceTorFullState_vertexRelabel, statePerm_apply]

/-- The inverse Tor map of a vertex relabeling on full state vectors. -/
theorem incidenceTorFullState_vertexRelabel_symm (p : ℕ) (y : H.incidenceTor p) :
    G.incidenceTorFullState p ((φ.incidenceTorVertexRelabel p).symm y) =
      (φ.statePerm ℂ).symm (H.incidenceTorFullState p y) := by
  rw [LinearEquiv.eq_symm_apply, ← incidenceTorFullState_vertexRelabel,
    LinearEquiv.apply_symm_apply]

/-- The Tor map of a vertex relabeling preserves the standard Tor product. -/
theorem incidenceTorVertexRelabel_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorVertexRelabel (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorVertexRelabel p x)
        (φ.incidenceTorVertexRelabel q y) := by
  apply H.incidenceTorFullState_injective (p + q)
  rw [incidenceTorFullState_vertexRelabel, incidenceTorFullState_product,
    incidenceTorFullState_product, incidenceTorFullState_vertexRelabel,
    incidenceTorFullState_vertexRelabel, statePerm_incStateCup]

/-- The Tor map of a vertex relabeling sends the unit of Tor to the unit. -/
theorem incidenceTorVertexRelabel_one :
    φ.incidenceTorVertexRelabel 0 G.incidenceTorOne = H.incidenceTorOne := by
  apply H.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_vertexRelabel, incidenceTorFullState_one, incidenceTorFullState_one,
    statePerm_incStateUnit]

/-! ## Internal degrees -/

/-- The Tor map of a vertex relabeling preserves internal degrees. -/
theorem incidenceTorVertexRelabel_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorVertexRelabel p x ∈ H.incidenceTorInternalPiece p q := by
  rw [EdgeRelabel.mem_incidenceTorInternalPiece_iff_fullState] at hx ⊢
  intro b hb
  rw [incidenceTorFullState_vertexRelabel, statePerm_apply]
  rw [hx _ (by rwa [← φ.incResolutionInternalDegree_stateIndex, Equiv.apply_symm_apply]), mul_zero]

/-- The inverse Tor map of a vertex relabeling preserves internal degrees. -/
theorem incidenceTorVertexRelabel_symm_mem_internalPiece {p q : ℕ} {y : H.incidenceTor p}
    (hy : y ∈ H.incidenceTorInternalPiece p q) :
    (φ.incidenceTorVertexRelabel p).symm y ∈ G.incidenceTorInternalPiece p q := by
  rw [EdgeRelabel.mem_incidenceTorInternalPiece_iff_fullState] at hy ⊢
  intro b hb
  rw [incidenceTorFullState_vertexRelabel_symm, statePerm_symm_apply]
  rw [hy _ (by rwa [φ.incResolutionInternalDegree_stateIndex]), mul_zero]

/-- The Tor map of a vertex relabeling carries each bigraded piece onto the bigraded piece. -/
theorem map_incidenceTorInternalPiece (p q : ℕ) :
    (G.incidenceTorInternalPiece p q).map
        (φ.incidenceTorVertexRelabel p : G.incidenceTor p →ₗ[ℂ] _) =
      H.incidenceTorInternalPiece p q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact φ.incidenceTorVertexRelabel_mem_internalPiece hx
  · intro y hy
    exact ⟨_, φ.incidenceTorVertexRelabel_symm_mem_internalPiece hy,
      LinearEquiv.apply_symm_apply _ y⟩

/-- The Tor map of a vertex relabeling on bigraded pieces. -/
noncomputable def incidenceTorInternalVertexRelabel (p q : ℕ) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorVertexRelabel p).ofSubmodules _ _ (φ.map_incidenceTorInternalPiece p q)

@[simp] theorem incidenceTorInternalVertexRelabel_val (p q : ℕ)
    (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalVertexRelabel p q x : H.incidenceTor p) =
      φ.incidenceTorVertexRelabel p x.val :=
  rfl

/-! ## Identities and composition -/

/-- The Tor map of the identity vertex relabeling is the identity. -/
theorem incidenceTorVertexRelabel_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorVertexRelabel p y = y :=
  G.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_vertexRelabel, statePerm_refl])

/-- The Tor map of a composite vertex relabeling is the composite of the Tor maps. -/
theorem incidenceTorVertexRelabel_trans {X : Type} [DecidableEq X] [Fintype X]
    {K : Multigraph X E} (χ : VertexRelabel H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans χ).incidenceTorVertexRelabel p y =
      χ.incidenceTorVertexRelabel p (φ.incidenceTorVertexRelabel p y) :=
  K.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_vertexRelabel, incidenceTorFullState_vertexRelabel,
      incidenceTorFullState_vertexRelabel, statePerm_trans])

/-- Vertex relabelings are determined by their vertex bijections. -/
theorem ext' {φ φ' : VertexRelabel G H} (h : φ.vertex = φ'.vertex) : φ = φ' := by
  cases φ
  cases φ'
  cases h
  rfl

/-- A vertex relabeling followed by its inverse is the identity relabeling. -/
theorem trans_symm : φ.trans φ.symm = refl G :=
  ext' (by simp)

/-- The inverse vertex relabeling followed by the relabeling is the identity relabeling. -/
theorem symm_trans : φ.symm.trans φ = refl H :=
  ext' (by simp)

/-- **Sanity check.** Composing the Tor map of a vertex relabeling with the Tor map of the
inverse relabeling gives the identity. -/
theorem incidenceTorVertexRelabel_symm_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.symm.incidenceTorVertexRelabel p (φ.incidenceTorVertexRelabel p y) = y := by
  rw [← incidenceTorVertexRelabel_trans, trans_symm, incidenceTorVertexRelabel_refl]

/-- The Tor map of the inverse relabeling is the inverse of the Tor map. -/
theorem incidenceTorVertexRelabel_symm_eq (p : ℕ) (y : H.incidenceTor p) :
    φ.symm.incidenceTorVertexRelabel p y = (φ.incidenceTorVertexRelabel p).symm y := by
  rw [LinearEquiv.eq_symm_apply, ← incidenceTorVertexRelabel_trans, symm_trans,
    incidenceTorVertexRelabel_refl]

end VertexRelabel

end BPFixedPoints.Multigraph
