import BPFixedPoints.Incidence.IncidenceVertexMapRings
import BPFixedPoints.Incidence.IncidenceVertexRelabelTor
import BPFixedPoints.Incidence.ResolutionMapComparison

/-!
# The Tor map of a vertex map

For `φ : VertexMap G H` the coefficient ring `IncCoeffRing E` is unchanged and the incidence ring
map `φ.incidenceHom` is the identity on coefficients, so it is a homomorphism of
`IncCoeffRing E`-modules (`incidenceModuleHom`). The Tor map is Mathlib's functoriality of the
left derived functor of extension of scalars along the coefficient origin in the module variable:
`((ModuleCat.extendScalars constantCoeff).leftDerived p).map φ.incidenceModuleHom`
(`incidenceTorHom`, `incidenceTorMap`). It is not defined through states, and no chain map is
part of the definition. Functoriality gives the identity and composition laws
(`incidenceTorMap_refl`, `incidenceTorMap_trans`), and for a vertex bijection the Tor map is the
Tor isomorphism `incidenceTorVertexIso` of the relabeling (`incidenceTorMap_toVertexMap`).

To compute it, take Mathlib's lift `ProjectiveResolution.lift` of the module map to the actual
free resolutions (`resolutionLift`). By `ProjectiveResolution.isoLeftDerivedObj_hom_naturality` the
Tor map sends the origin specialization of a free-resolution element to the specialization of its
image under the lift (`incidenceTorMap_class`). Assembling the components of the lift over the
homological degrees gives a degree-preserving chain map of the full free modules
(`resolutionFullLift`) lifting the torus map through the torus augmentations.

**Products.** For the standard multiplication lifts `μ_G`, `μ_H` (the resolution cup products),
the two maps `F ∘ μ_G` and `μ_H ∘ (F ⊗ F)` from the graded tensor complex of the free resolution of
`G` to the free resolution of `H` are degree-preserving chain maps (Leibniz rule of `μ_H`, and `F`
commutes with the parity operator because it preserves degrees). In degree zero both lift
`a ⊗ b ↦ φ(ε a) φ(ε b)`, because the augmentations are multiplicative and the torus map is a ring
map. The tensor complex is minimal, so by `incResolutionMap_atOrigin` (homotopy uniqueness of
lifts, `specialized_lifts_eq`) the two maps agree at the coefficient origin. Therefore the Tor
map preserves the standard Tor product (`incidenceTorMap_product`). It sends the unit to the unit
(`incidenceTorMap_one`) because the lift of the chosen unit lift has augmentation one. No state
formula is used.

Not covered here: a state formula for the Tor map in positive homological degrees (pullback along
the diagonal multiplies the state cohomology of identified vertices by the Čech cup product);
preservation of internal degrees in positive homological degrees (the lift used here is not
chosen homogeneous, and the edge-sign argument of `IncidenceVertexMapCycles` is only carried out in
degree zero); the corresponding map on the Ext-defined cohomology of the exterior bundles; and the
geometric sheaf side. Degree zero is treated in `IncidenceVertexMapCycles`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## The module map and the Tor map -/

/-- The incidence ring map as a linear map of modules over the common coefficient ring. -/
noncomputable def incidenceLinearMap :
    EdgeRelabel.incidenceModule G →ₗ[IncCoeffRing E] EdgeRelabel.incidenceModule H where
  toFun x := φ.incidenceHom x
  map_add' x y := map_add φ.incidenceHom x y
  map_smul' r x := φ.incidenceHom_coeff_mul r x

/-- The incidence ring map as a morphism of coefficient modules. -/
noncomputable def incidenceModuleHom :
    EdgeRelabel.incidenceModule G ⟶ EdgeRelabel.incidenceModule H :=
  ModuleCat.ofHom (X := EdgeRelabel.incidenceModule G) (Y := EdgeRelabel.incidenceModule H)
    φ.incidenceLinearMap

theorem incidenceModuleHom_apply (x : G.IncidenceRing) :
    φ.incidenceModuleHom x = φ.incidenceHom x := rfl

/-- **The Tor map of a vertex map**, as a morphism: the left derived functor of extension of
scalars along the coefficient origin, applied to the incidence module map. -/
noncomputable def incidenceTorHom (p : ℕ) : G.incidenceTor p ⟶ H.incidenceTor p :=
  ((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).map
    φ.incidenceModuleHom

/-- **The Tor map of a vertex map**, as a linear map. -/
noncomputable def incidenceTorMap (p : ℕ) : G.incidenceTor p →ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorHom p).hom

theorem incidenceTorMap_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorMap p y = φ.incidenceTorHom p y := rfl

/-! ## Identity, composition and vertex bijections -/

/-- The module map of the identity vertex map is the identity. -/
theorem incidenceModuleHom_refl (G : Multigraph V E) :
    (refl G).incidenceModuleHom = 𝟙 (EdgeRelabel.incidenceModule G) := by
  ext x
  exact incidenceHom_refl_apply G x

/-- The module map of a composite is the composite of the module maps. -/
theorem incidenceModuleHom_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) :
    (φ.trans χ).incidenceModuleHom = φ.incidenceModuleHom ≫ χ.incidenceModuleHom := by
  ext x
  exact incidenceHom_trans_apply φ χ x

/-- **Identity law.** The Tor map of the identity vertex map is the identity. -/
theorem incidenceTorHom_refl (G : Multigraph V E) (p : ℕ) :
    (refl G).incidenceTorHom p = 𝟙 (G.incidenceTor p) := by
  rw [incidenceTorHom, incidenceModuleHom_refl]
  exact CategoryTheory.Functor.map_id _ _

/-- **Composition law.** The Tor map of a composite is the composite of the Tor maps. -/
theorem incidenceTorHom_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) (p : ℕ) :
    (φ.trans χ).incidenceTorHom p = φ.incidenceTorHom p ≫ χ.incidenceTorHom p := by
  rw [incidenceTorHom, incidenceModuleHom_trans]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- **Identity law.** -/
theorem incidenceTorMap_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorMap p y = y := by
  rw [incidenceTorMap_apply, incidenceTorHom_refl]
  rfl

/-- **Composition law.** -/
theorem incidenceTorMap_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans χ).incidenceTorMap p y = χ.incidenceTorMap p (φ.incidenceTorMap p y) := by
  rw [incidenceTorMap_apply, incidenceTorHom_trans]
  rfl

end VertexMap

/-- For a vertex bijection the module map of the underlying vertex map is the module isomorphism
of the relabeling. -/
theorem VertexRelabel.toVertexMap_incidenceModuleHom {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) :
    φ.toVertexMap.incidenceModuleHom = φ.incidenceModuleIso.hom := by
  ext x
  exact φ.toVertexMap_incidenceHom x

/-- **Agreement with vertex bijections.** For a vertex bijection the Tor map of the underlying
vertex map is the Tor isomorphism of the relabeling. -/
theorem VertexRelabel.incidenceTorMap_toVertexMap {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexRelabel G H) (p : ℕ) (y : G.incidenceTor p) :
    φ.toVertexMap.incidenceTorMap p y = φ.incidenceTorVertexRelabel p y := by
  change ((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).map
      φ.toVertexMap.incidenceModuleHom y =
    (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).mapIso
      φ.incidenceModuleIso).hom y
  rw [VertexRelabel.toVertexMap_incidenceModuleHom, Functor.mapIso_hom]

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## A chain-level lift -/

/-- Mathlib's lift of the incidence module map to the actual free resolutions. It is used only to
compute the Tor map. -/
noncomputable def resolutionLift : G.incFreeResolution.complex ⟶ H.incFreeResolution.complex :=
  ProjectiveResolution.lift φ.incidenceModuleHom G.incFreeResolution H.incFreeResolution

/-- The lift commutes with the augmentations. -/
theorem resolutionLift_comm_zero :
    φ.resolutionLift.f 0 ≫ H.incFreeResolution.π.f 0 =
      G.incFreeResolution.π.f 0 ≫ φ.incidenceModuleHom :=
  ProjectiveResolution.lift_commutes_zero _ _ _

/-- The components of the lift. -/
noncomputable def freeTermLift (n : ℕ) : G.IncFreeTerm n →ₗ[IncCoeffRing E] H.IncFreeTerm n :=
  (φ.resolutionLift.f n).hom

/-- In degree zero the lift lifts the incidence ring map through the augmentations. -/
theorem freeTermLift_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.freeTermLift 0 x) =
      φ.incidenceHom (G.incResolutionAugmentation x) :=
  congrArg (fun f => f.hom x) φ.resolutionLift_comm_zero

/-- The components of the lift commute with the differentials. -/
theorem freeTermLift_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.freeTermLift (n + 1) x) =
      φ.freeTermLift n (G.incFreeTermDifferential n x) := by
  have h := φ.resolutionLift.comm (n + 1) n
  rw [G.incFreeResolution_d, H.incFreeResolution_d] at h
  exact congrArg (fun f => f.hom x) h

/-- **The Tor map is computed by the lift** on the actual free resolutions. -/
theorem incidenceTorHom_eq (p : ℕ) :
    φ.incidenceTorHom p =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map φ.resolutionLift) p ≫
          (H.incFreeResolution.isoLeftDerivedObj
            (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).inv := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality φ.incidenceModuleHom
    G.incFreeResolution H.incFreeResolution φ.resolutionLift φ.resolutionLift_comm_zero
    (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p
  rw [← Iso.eq_comp_inv] at h
  rw [incidenceTorHom, h]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc]

/-- In free-term coordinates the Tor map is the specialization of the lift. -/
theorem incidenceTorIsoFreeTerm_vertexMap (p : ℕ) :
    φ.incidenceTorHom p ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          (φ.resolutionLift.f p) := by
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
  rw [hG, hH, incidenceTorHom_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [homologyIsoTermOfZeroDifferentials_naturality]
  rfl

/-- The Tor map sends the specialization of a free-resolution element to the specialization of its
image under the lift. -/
theorem incidenceTorMap_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorMap p (G.incFreeTermToTor p x) = H.incFreeTermToTor p (φ.freeTermLift p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom ((φ.incidenceTorHom p) (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (φ.freeTermLift p x))
  rw [← ConcreteCategory.comp_apply, incidenceTorIsoFreeTerm_vertexMap,
    ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul, incFreeTermToTor_eq_tmul]
  rfl

/-- The full state of the image of a class is the value at the coefficient origin of the lift. -/
theorem incidenceTorFullState_vertexMap_class (p : ℕ) (x : G.IncFreeTerm p) :
    H.incidenceTorFullState p (φ.incidenceTorMap p (G.incFreeTermToTor p x)) =
      mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) (φ.freeTermLift p x).val := by
  rw [incidenceTorMap_class, incidenceTorFullState_class]

/-- **The unit.** The Tor map sends the unit of the Tor algebra to the unit. -/
theorem incidenceTorMap_one : φ.incidenceTorMap 0 G.incidenceTorOne = H.incidenceTorOne := by
  rw [incidenceTorOne, incidenceTorOne, incidenceTorMap_class]
  apply H.incFreeTermToTor_eq_of_augmentation_eq
  rw [freeTermLift_augmentation]
  apply Subtype.ext
  rw [incidenceHom_val, incResolutionAugmentation_val, incResolutionAugmentation_val,
    G.incResolutionUnit_augmentation, H.incResolutionUnit_augmentation, map_one]

/-! ## The lift on the full free modules -/

/-- The components of the lift assembled into a map of the full free modules: a basis state of
homological degree `n` goes to the image of its basis vector under the `n`-th component. -/
noncomputable def resolutionFullLift :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
      (H.IncResolutionBasis →₀ IncCoeffRing E) :=
  Finsupp.linearCombination (IncCoeffRing E) fun b =>
    (φ.freeTermLift (G.incResolutionDegree b)
      ⟨single b 1, single_mem_supported _ _ rfl⟩).val

/-- The full lift on a multiple of a basis state. -/
theorem resolutionFullLift_single (b : G.IncResolutionBasis) (r : IncCoeffRing E) :
    φ.resolutionFullLift (single b r) =
      r • (φ.freeTermLift (G.incResolutionDegree b)
        ⟨single b 1, single_mem_supported _ _ rfl⟩).val := by
  rw [resolutionFullLift, linearCombination_single]

/-- Transport of a basis vector between equal homological degrees. -/
theorem freeTermLift_single_cast (b : G.IncResolutionBasis) {n : ℕ}
    (hb : G.incResolutionDegree b = n) :
    (φ.freeTermLift (G.incResolutionDegree b) ⟨single b 1, single_mem_supported _ _ rfl⟩).val =
      (φ.freeTermLift n ⟨single b 1, single_mem_supported _ _ hb⟩).val := by
  subst hb
  rfl

/-- The basis vectors of a free term are the basis states. -/
theorem incFreeTermBasis_val (n : ℕ)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = n}) :
    ((G.incFreeTermBasis n) b).val = single b.val 1 := by
  simp only [incFreeTermBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

/-- On homological degree `n` the full lift is the `n`-th component of the lift. -/
theorem resolutionFullLift_eq (n : ℕ) (x : G.IncFreeTerm n) :
    φ.resolutionFullLift x.val = (φ.freeTermLift n x).val := by
  have h : φ.resolutionFullLift.comp (gradedPiece (IncCoeffRing E) G.incResolutionDegree n).subtype =
      (gradedPiece (IncCoeffRing E) H.incResolutionDegree n).subtype.comp (φ.freeTermLift n) := by
    apply (G.incFreeTermBasis n).ext
    intro b
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [incFreeTermBasis_val, resolutionFullLift_single, one_smul,
      φ.freeTermLift_single_cast b.val b.property]
    congr 2
    exact Subtype.ext (incFreeTermBasis_val n b).symm
  exact LinearMap.congr_fun h x

/-- The full lift preserves homological degrees. -/
theorem resolutionFullLift_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    φ.resolutionFullLift x ∈ gradedPiece (IncCoeffRing E) H.incResolutionDegree n := by
  rw [show x = (⟨x, hx⟩ : G.IncFreeTerm n).val from rfl, resolutionFullLift_eq]
  exact (φ.freeTermLift n ⟨x, hx⟩).property

/-- The full lift preserves homological degrees, in the integer form used for tensor maps. -/
theorem resolutionFullLift_hasDegree :
    HasDegree (fun b => (G.incResolutionDegree b : ℤ)) (fun b => (H.incResolutionDegree b : ℤ)) 0
      φ.resolutionFullLift := by
  apply HasDegree.of_single
  intro b r
  have h := φ.resolutionFullLift_degree (G.incResolutionDegree b)
    (single_mem_supported (IncCoeffRing E) r (rfl : G.incResolutionDegree b = _))
  simpa only [gradedPiece, add_zero, Int.natCast_inj] using h

/-- The full lift is a chain map of the full free modules. -/
theorem resolutionFullLift_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incResolutionDifferential (φ.resolutionFullLift x) =
      φ.resolutionFullLift (G.incResolutionDifferential x) := by
  have hdeg : ∀ n (y : G.IncResolutionBasis →₀ IncCoeffRing E),
      y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n →
        H.incResolutionDifferential (φ.resolutionFullLift y) =
          φ.resolutionFullLift (G.incResolutionDifferential y) := by
    intro n y hy
    cases n with
    | zero =>
      rw [H.incResolutionDifferential_zero_degree _ (φ.resolutionFullLift_degree 0 hy),
        G.incResolutionDifferential_zero_degree _ hy, map_zero]
    | succ m =>
      have hDy := G.incResolutionDifferential_degree m y hy
      rw [show y = (⟨y, hy⟩ : G.IncFreeTerm (m + 1)).val from rfl, resolutionFullLift_eq,
        show G.incResolutionDifferential (⟨y, hy⟩ : G.IncFreeTerm (m + 1)).val =
          (G.incFreeTermDifferential m ⟨y, hy⟩).val from rfl, resolutionFullLift_eq,
        ← freeTermLift_differential]
      rfl
  have h : H.incResolutionDifferential.comp φ.resolutionFullLift =
      φ.resolutionFullLift.comp G.incResolutionDifferential := by
    apply Finsupp.lhom_ext
    intro b r
    exact hdeg _ _ (single_mem_supported _ r rfl)
  exact LinearMap.congr_fun h x

/-- The full lift commutes with the parity operators. -/
theorem resolutionFullLift_parity (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    φ.resolutionFullLift (gradedParity G.incResolutionDegree x) =
      gradedParity H.incResolutionDegree (φ.resolutionFullLift x) := by
  have h : φ.resolutionFullLift.comp (gradedParity G.incResolutionDegree) =
      (gradedParity H.incResolutionDegree).comp φ.resolutionFullLift := by
    apply Finsupp.lhom_ext
    intro b r
    have hb : single b r ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree
        (G.incResolutionDegree b) := single_mem_supported _ r rfl
    simp only [LinearMap.comp_apply]
    rw [gradedParity_homogeneous _ _ hb,
      gradedParity_homogeneous _ _ (φ.resolutionFullLift_degree _ hb), map_smul]
  exact LinearMap.congr_fun h x

/-- In degree zero the full lift lifts the torus map through the torus augmentations. -/
theorem resolutionFullLift_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    H.incResolutionTorusAugmentation (φ.resolutionFullLift x) =
      φ.torusHom (G.incResolutionTorusAugmentation x) := by
  rw [show x = (⟨x, hx⟩ : G.IncFreeTerm 0).val from rfl, resolutionFullLift_eq]
  exact congrArg Subtype.val (φ.freeTermLift_augmentation ⟨x, hx⟩)

/-! ## Products -/

/-- The two composites `F ∘ μ_G` and `μ_H ∘ (F ⊗ F)` of the full lift with the standard
multiplication lifts agree at the coefficient origin on every homogeneous element of the graded
tensor module. -/
theorem lift_cup_atOrigin (n : ℕ)
    (z : gradedPiece (IncCoeffRing E)
      (fun a : G.IncResolutionBasis × G.IncResolutionBasis =>
        G.incResolutionDegree a.1 + G.incResolutionDegree a.2) n) :
    letI : Algebra (IncCoeffRing E) ℂ := (constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
    (1 : ℂ) ⊗ₜ[IncCoeffRing E]
        φ.resolutionFullLift (G.incResolutionMultiplication.linearize z.val) =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] H.incResolutionMultiplication.linearize
        (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift z.val) := by
  have hFF : ∀ (x y : G.IncResolutionBasis →₀ IncCoeffRing E),
      freeTensorMap φ.resolutionFullLift φ.resolutionFullLift
          (finsuppTensorFinsupp' (IncCoeffRing E) _ _ (x ⊗ₜ[IncCoeffRing E] y)) =
        finsuppTensorFinsupp' (IncCoeffRing E) _ _
          (φ.resolutionFullLift x ⊗ₜ[IncCoeffRing E] φ.resolutionFullLift y) := by
    intro x y
    simp only [freeTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  have hFFdeg : ∀ m {w : G.IncResolutionBasis × G.IncResolutionBasis →₀ IncCoeffRing E},
      w ∈ gradedPiece (IncCoeffRing E)
          (fun a : G.IncResolutionBasis × G.IncResolutionBasis =>
            G.incResolutionDegree a.1 + G.incResolutionDegree a.2) m →
        freeTensorMap φ.resolutionFullLift φ.resolutionFullLift w ∈ gradedPiece (IncCoeffRing E)
          (fun a : H.IncResolutionBasis × H.IncResolutionBasis =>
            H.incResolutionDegree a.1 + H.incResolutionDegree a.2) m := by
    intro m w hw
    have h := φ.resolutionFullLift_hasDegree.freeTensorMap φ.resolutionFullLift_hasDegree
      (m : ℤ) w (by simpa only [gradedPiece, ← Nat.cast_add, Int.natCast_inj] using hw)
    simpa only [gradedPiece, ← Nat.cast_add, add_zero, Int.natCast_inj] using h
  have hpair : ∀ (a b : G.IncResolutionBasis),
      G.incResolutionDegree a = 0 → G.incResolutionDegree b = 0 →
        H.incResolutionTorusAugmentation (φ.resolutionFullLift
            (G.incResolutionMultiplication.linearize (single (a, b) 1))) =
          H.incResolutionTorusAugmentation (H.incResolutionMultiplication.linearize
            (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift (single (a, b) 1))) := by
    intro a b ha hb
    have ha' : single a (1 : IncCoeffRing E) ∈
        gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 := single_mem_supported _ _ ha
    have hb' : single b (1 : IncCoeffRing E) ∈
        gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 := single_mem_supported _ _ hb
    have hs : single (a, b) (1 : IncCoeffRing E) = finsuppTensorFinsupp' (IncCoeffRing E) _ _
        (single a 1 ⊗ₜ[IncCoeffRing E] single b 1) := by
      rw [finsuppTensorFinsupp'_single_tmul_single, one_mul]
    rw [hs, GradedFreePairing.linearize_tmul, hFF, GradedFreePairing.linearize_tmul,
      φ.resolutionFullLift_torusAugmentation
        (G.incResolutionMultiplication.homogeneous 0 0 ha' hb'),
      G.incResolutionMultiplication.augmentation _ _ ha' hb',
      H.incResolutionMultiplication.augmentation _ _ (φ.resolutionFullLift_degree 0 ha')
        (φ.resolutionFullLift_degree 0 hb'),
      map_mul, φ.resolutionFullLift_torusAugmentation ha',
      φ.resolutionFullLift_torusAugmentation hb']
  refine H.incResolutionMap_atOrigin
    (fun a : G.IncResolutionBasis × G.IncResolutionBasis =>
      G.incResolutionDegree a.1 + G.incResolutionDegree a.2)
    (gradedTensorD G.incResolutionDegree G.incResolutionDifferential)
    (gradedTensorD_degree G.incResolutionDegree G.incResolutionDifferential
      G.incResolutionDifferential_hasDegree)
    (gradedTensorD_sq G.incResolutionDegree G.incResolutionDifferential
      G.incResolutionDifferential_hasDegree G.incResolutionDifferential_sq)
    (φ.resolutionFullLift.comp G.incResolutionMultiplication.linearize)
    (H.incResolutionMultiplication.linearize.comp
      (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift)) ?_ ?_ ?_ ?_ ?_ ?_ n z
  · -- `F ∘ μ_G` preserves degrees
    intro m w hw
    exact φ.resolutionFullLift_degree m (G.incResolutionMultiplication.linearize_degree m hw)
  · -- `μ_H ∘ (F ⊗ F)` preserves degrees
    intro m w hw
    exact H.incResolutionMultiplication.linearize_degree m (hFFdeg m hw)
  · -- `F ∘ μ_G` is a chain map
    intro w
    simp only [LinearMap.comp_apply]
    rw [φ.resolutionFullLift_differential, G.incResolutionMultiplication.linearize_chain]
  · -- `μ_H ∘ (F ⊗ F)` is a chain map
    intro w
    have hT : (H.incResolutionDifferential.comp (H.incResolutionMultiplication.linearize.comp
          (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift))).comp
          (finsuppTensorFinsupp' (IncCoeffRing E) G.IncResolutionBasis
            G.IncResolutionBasis).toLinearMap =
        ((H.incResolutionMultiplication.linearize.comp
          (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift)).comp
            (gradedTensorD G.incResolutionDegree G.incResolutionDifferential)).comp
          (finsuppTensorFinsupp' (IncCoeffRing E) G.IncResolutionBasis
            G.IncResolutionBasis).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hFF, GradedFreePairing.linearize_tmul, H.incResolutionMultiplication.leibniz,
        gradedTensorD_tmul, LinearEquiv.map_add, LinearMap.map_add, LinearMap.map_add, hFF, hFF,
        GradedFreePairing.linearize_tmul, GradedFreePairing.linearize_tmul,
        φ.resolutionFullLift_differential, φ.resolutionFullLift_differential,
        φ.resolutionFullLift_parity]
    have h := LinearMap.congr_fun hT
      ((finsuppTensorFinsupp' (IncCoeffRing E) G.IncResolutionBasis G.IncResolutionBasis).symm w)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h
  · -- the graded tensor differential is minimal
    exact gradedTensorD_minimal G.incResolutionDegree G.incResolutionDifferential
      (incCoeffAugmentationIdeal E) G.incResolutionDifferential_minimal
  · -- both lift `a ⊗ b ↦ φ(ε a) φ(ε b)` through the augmentations
    rintro ⟨w, hw⟩
    show H.incResolutionTorusAugmentation
        ((φ.resolutionFullLift.comp G.incResolutionMultiplication.linearize) w) =
      H.incResolutionTorusAugmentation ((H.incResolutionMultiplication.linearize.comp
        (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift)) w)
    replace hw : w ∈ Finsupp.supported (IncCoeffRing E) (IncCoeffRing E)
        {a : G.IncResolutionBasis × G.IncResolutionBasis |
          G.incResolutionDegree a.1 + G.incResolutionDegree a.2 = 0} := hw
    rw [Finsupp.supported_eq_span_single] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
      have hd : G.incResolutionDegree a + G.incResolutionDegree b = 0 := hab
      exact hpair a b (by omega) (by omega)
    | zero => simp only [LinearMap.map_zero]
    | add x y _ _ hx hy => simp only [LinearMap.map_add, hx, hy]
    | smul r x _ hx => simp only [LinearMap.map_smul, hx]

/-- **The Tor map preserves the standard Tor product.** -/
theorem incidenceTorMap_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorMap (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorMap p x) (φ.incidenceTorMap q y) := by
  obtain ⟨a, rfl⟩ := G.incFreeTermToTor_surjective p x
  obtain ⟨b, rfl⟩ := G.incFreeTermToTor_surjective q y
  rw [incidenceTorProduct_eq_transferred, incidenceTorMap_class, incidenceTorMap_class,
    incidenceTorMap_class, incidenceTorProduct_eq_transferred]
  apply H.incidenceTorFullState_injective (p + q)
  rw [incidenceTorFullState_class, incidenceTorFullState_class]
  change mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _)
      (φ.freeTermLift (p + q) ⟨G.incResolutionCup a.val b.val,
        G.incResolutionCup_degree p q a.property b.property⟩).val =
    mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _)
      (H.incResolutionCup (φ.freeTermLift p a).val (φ.freeTermLift q b).val)
  rw [← resolutionFullLift_eq, ← resolutionFullLift_eq, ← resolutionFullLift_eq]
  have h := φ.lift_cup_atOrigin (p + q)
    ⟨freePair a.val b.val, freePair_degree _ p q a.property b.property⟩
  have h' := congrArg H.incOriginStateEquiv h
  rw [incOriginStateEquiv_tmul, incOriginStateEquiv_tmul] at h'
  have e1 : G.incResolutionMultiplication.linearize (freePair a.val b.val) =
      G.incResolutionCup a.val b.val :=
    G.incResolutionMultiplication.linearize_tmul a.val b.val
  have e2 : H.incResolutionMultiplication.linearize
      (freeTensorMap φ.resolutionFullLift φ.resolutionFullLift (freePair a.val b.val)) =
        H.incResolutionCup (φ.resolutionFullLift a.val) (φ.resolutionFullLift b.val) := by
    rw [freePair_apply]
    simp only [freeTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
    exact H.incResolutionMultiplication.linearize_tmul _ _
  rw [e1, e2] at h'
  exact h'

end VertexMap

end BPFixedPoints.Multigraph
