import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedComplex

/-! # The derived base change on cohomology: Tor, the acceptance test, sheaf cohomology

Continuation of `IncidenceZeroBaseChangeDerivedComplex`, which builds the isomorphism
`zbdDerivedIso : Q(ℂ ⊗ F⁻) ≅ Q(C₀)` in `DerivedCategory (ModuleCat ℂ)` from the explicit
homotopy equivalence (no flatness). This file computes what it does on cohomology.

* **(a) `ℂ ⊗ F⁻` computes Tor.** Its differentials vanish (`zbdResolutionComplexC_d`: the free
  resolution is minimal; the pieces are direct summands through `zbdResolutionRetraction`).
  `F⁻` is the projective resolution `incFreeResolution` reindexed (`zbdTermIso`,
  `zbdTermIso_comm`). `zbdTorIso p : incidenceTor p ≅ H^{-p}(ℂ ⊗ F⁻)` composes Mathlib's left
  derived extension of scalars computed on that resolution (`incidenceTorIsoFreeTerm`) with the
  term isomorphism and the homology of a complex with zero differentials; on Tor classes it is
  the class of `1 ⊗ x` (`zbdTorIso_hom_class`). `zbdTorDerivedIso` is the same in the derived
  category (`DerivedCategory.homologyFunctorFactors`).
* **(b) `C₀` computes sheaf cohomology.** The cohomology `ZbcCohomology p q` of the model in
  bidegree `(p, q)` maps injectively into the cohomology of the model in degree `-p`
  (`zbdCohomologyToModel_injective`: the Čech differential preserves the exterior degree, so a
  boundary can be projected to bidegree `(p + 1, q)` with `zbdCardFilter`), hence into the
  cohomology of `Q(C₀)` (`zbdCohomologyToDerived_injective`). Composed with `zbcSheafEquiv`,
  `zbdSheafToDerived` embeds `H^j(X_G, ∧^q F_G^∨)` (`j + p = q`) into `H^{-p}(Q(C₀))`.
* **Acceptance test** (`zbd_homologyMap_torClass`, `zbdDerivedModelIso_torClass`,
  `zbdDerivedIso_torClass`): the cohomology in degree `-p` of the derived isomorphism sends the
  Tor class of `x` of internal degree `q` to the image of `zbcTorEquiv x`; since the target map is
  injective, the derived isomorphism determines `zbcTorEquiv` (`zbdDerivedIso_torClass_eq_iff`).
  Against sheaf cohomology (`zbdDerivedIso_exterior`, `zbdDerivedIso_exterior_eq_iff`) it gives
  `zbcExteriorEquiv = incidenceTorExteriorEquiv`, and on every state class the exterior class of
  the same state with coefficient `+1` (`zbdDerivedIso_stateClass`).

The comparison is between the cohomology maps induced by one morphism of `D(ℂ)` and the existing
bigraded isomorphisms; no statement here infers a derived isomorphism from cohomology alone. That
the internal-degree pieces exhaust `H^{-p}(Q(C₀))` is in
`IncidenceZeroBaseChangeDerivedDecomposition`. Products are not compared here.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CechProduct ProjectiveLine IncidencePerturbation Finsupp ResolutionTools
open scoped TensorProduct ChangeOfRings

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-! ### `ℂ ⊗ F⁻` has zero differentials and computes Tor -/

/-- The projection of the free module onto a piece of the resolution. -/
def zbdResolutionRetraction (n : ℤ) :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E] G.incResolutionPiece n :=
  restrictDom (IncCoeffRing E) (IncCoeffRing E) {b | (G.incResolutionDegree b : ℤ) = n}

theorem zbdResolutionRetraction_val {n : ℤ} (x : G.incResolutionPiece n) :
    G.zbdResolutionRetraction n x.val = x :=
  LinearMap.congr_fun (restrictDom_comp_subtype (M := IncCoeffRing E) (R := IncCoeffRing E)
    {b | (G.incResolutionDegree b : ℤ) = n}) x

/-- The differentials of `F⁻` have image in the augmentation ideal multiples. -/
theorem zbdResolutionComplex_d_range (i j : ℤ) :
    LinearMap.range (G.zbdResolutionComplex.d i j).hom ≤
      RingHom.ker (zbcOrigin E) •
        (⊤ : Submodule (IncCoeffRing E) (G.zbdResolutionComplex.X j)) := by
  rintro _ ⟨x, rfl⟩
  by_cases h : i + 1 = j
  · have hx : G.zbdResolutionComplex.d i j x = G.zbdResolutionRetraction (-j)
        (G.incResolutionDifferential (Subtype.val (p := (· ∈ G.incResolutionPiece (-i))) x)) := by
      have h1 := G.zbdResolutionRetraction_val (n := -j) (G.zbdResolutionComplex.d i j x)
      rw [ZbdGradedComplex.complex_d_val _ h] at h1
      exact h1.symm
    rw [hx]
    exact map_mem_ideal_smul_top _ _ (G.incResolutionDifferential_minimal x.val)
  · rw [G.zbdResolutionComplex.shape i j h]
    exact Submodule.zero_mem _

/-- **`ℂ ⊗ F⁻` has zero differentials** (minimality of the free resolution). -/
theorem zbdResolutionComplexC_d (i j : ℤ) : G.zbdResolutionComplexC.d i j = 0 :=
  extendScalars_map_eq_zero (zbcOrigin E) _ (G.zbdResolutionComplex_d_range i j)

theorem zbd_gradedPiece_eq (p : ℕ) :
    gradedPiece (IncCoeffRing E) G.incResolutionDegree p = G.incResolutionPiece (-(-(p : ℤ))) := by
  rw [neg_neg, gradedPiece, incResolutionPiece]
  congr 1
  ext b
  simp

/-- The term `F_p` of the projective resolution is the term of `F⁻` in degree `-p`. -/
def zbdTermIso (p : ℕ) :
    ModuleCat.of (IncCoeffRing E) (G.IncFreeTerm p) ≅ G.zbdResolutionComplex.X (-(p : ℤ)) :=
  (LinearEquiv.ofEq _ _ (G.zbd_gradedPiece_eq p)).toModuleIso

theorem zbdTermIso_hom_val (p : ℕ) (x : G.IncFreeTerm p) :
    Subtype.val (p := (· ∈ G.incResolutionPiece (-(-(p : ℤ))))) ((G.zbdTermIso p).hom x) =
      x.val := rfl

/-- `F⁻` is the projective resolution `incFreeResolution` reindexed: the term isomorphisms
intertwine the differentials. -/
theorem zbdTermIso_comm (p : ℕ) :
    G.incFreeResolution.complex.d (p + 1) p ≫ (G.zbdTermIso p).hom =
      (G.zbdTermIso (p + 1)).hom ≫ G.zbdResolutionComplex.d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) := by
  rw [G.incFreeResolution_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (G.incFreeTermDifferential p x).val = Subtype.val
    (p := (· ∈ G.incResolutionPiece (-(-(p : ℤ)))))
    (G.zbdResolutionComplex.d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ((G.zbdTermIso (p + 1)).hom x))
  rw [ZbdGradedComplex.complex_d_val _ (by push_cast; ring)]
  rfl

/-- If both differentials vanish, the class map composed with the homology-to-term
isomorphism is the inclusion of the cycles. -/
theorem zbd_homologyπ_homologyIsoTermOfZeroDifferentials {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (hD : ∀ i j, K.d i j = 0) (n : ℤ) :
    K.homologyπ n ≫ (homologyIsoTermOfZeroDifferentials K hD n).hom = K.iCycles n := by
  change (K.sc n).homologyπ ≫ (ShortComplex.LeftHomologyData.ofZeros (K.sc n) (hD _ _)
    (hD _ _)).homologyIso.hom = (K.sc n).iCycles
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  have h := (ShortComplex.LeftHomologyData.ofZeros (K.sc n) (hD _ _) (hD _ _)).cyclesIso_hom_comp_i
  exact h

/-- The inverse of the homology-to-term isomorphism is the class of the term. -/
theorem zbd_homologyIsoTermOfZeroDifferentials_inv {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (hD : ∀ i j, K.d i j = 0) (n : ℤ) :
    (homologyIsoTermOfZeroDifferentials K hD n).inv =
      K.liftCycles (𝟙 _) _ rfl (by rw [hD, Limits.comp_zero]) ≫ K.homologyπ n := by
  symm
  rw [← Iso.comp_hom_eq_id, Category.assoc, zbd_homologyπ_homologyIsoTermOfZeroDifferentials,
    HomologicalComplex.liftCycles_i]

/-- **`ℂ ⊗ F⁻` computes Tor.** `H^{-p}(ℂ ⊗ F⁻)` is Mathlib's left derived extension of scalars
`incidenceTor p`: through `incidenceTorIsoFreeTerm` (the derived functor computed on the
projective resolution `incFreeResolution`, whose specialized differentials vanish), the term
isomorphism `zbdTermIso`, and the zero differentials of `ℂ ⊗ F⁻`. -/
def zbdTorIso (p : ℕ) : G.incidenceTor p ≅ G.zbdResolutionComplexC.homology (-(p : ℤ)) :=
  G.incidenceTorIsoFreeTerm p ≪≫ (zbdBaseChange E).mapIso (G.zbdTermIso p) ≪≫
    (homologyIsoTermOfZeroDifferentials G.zbdResolutionComplexC G.zbdResolutionComplexC_d _).symm

/-- The element `1 ⊗ x` of `ℂ ⊗ F⁻` in degree `-p`, for `x` in the term `F_p`. -/
def zbdTorTerm (p : ℕ) (f : G.IncFreeTerm p) : G.zbdResolutionComplexC.X (-(p : ℤ)) :=
  (1 : ℂ) ⊗ₜ[IncCoeffRing E, zbcOrigin E] (G.zbdTermIso p).hom f

/-- The Tor class of a free-resolution element is the homology class of `1 ⊗ x`. -/
theorem zbdTorIso_hom_class (p : ℕ) (f : G.IncFreeTerm p) :
    (G.zbdTorIso p).hom (G.incFreeTermToTor p f) =
      (G.zbdResolutionComplexC.liftCycles (𝟙 _) _ rfl
          (by rw [G.zbdResolutionComplexC_d, Limits.comp_zero]) ≫
        G.zbdResolutionComplexC.homologyπ (-(p : ℤ))) (G.zbdTorTerm p f) := by
  rw [← zbd_homologyIsoTermOfZeroDifferentials_inv G.zbdResolutionComplexC
    G.zbdResolutionComplexC_d]
  change (homologyIsoTermOfZeroDifferentials G.zbdResolutionComplexC G.zbdResolutionComplexC_d
    _).inv ((zbdBaseChange E).map (G.zbdTermIso p).hom
      ((G.incidenceTorIsoFreeTerm p).hom (G.incFreeTermToTor p f))) = _
  have h := G.incFreeTermToTor_eq_tmul p f
  erw [h]
  rfl

/-- The image of `1 ⊗ x` under the base change of `ι` followed by the model isomorphism is the
specialization of `ι x`. -/
theorem zbd_torTerm_image (p : ℕ) (f : G.IncFreeTerm p) :
    Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
      ((G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom).f (-(p : ℤ)) (G.zbdTorTerm p f)) =
      zbcSpecialize (G.incResolutionInclusion f.val) :=
  G.zbdModelIsoApp_hom_tmul (-(p : ℤ))
    (G.zbdHomotopyEquiv.hom.f (-(p : ℤ)) ((G.zbdTermIso p).hom f))

/-! ### The cohomology of the model in a fixed internal degree -/

/-- Chains of bidegree `(p, q)` have total degree `p`. -/
theorem zbdPiece_le_model {p q : ℕ} {z : ZbcModule V E} (hz : z ∈ zbcPiece V E p q) :
    z ∈ zbdModelPiece V E (-(-(p : ℤ))) := by
  intro S
  have h := (mem_zbcSlot_iff p q S (z S)).mp (hz S)
  by_cases hS : S.card = q
  · have hz' := h.1 hS
    rw [zbdSlot, neg_neg, hS]
    exact hz'
  · rw [h.2 hS]
    exact Submodule.zero_mem _

/-- The cycles of bidegree `(p, q)` inside the term of degree `-p` of the model. -/
def zbdCyclesIncl (p q : ℕ) : G.zbcCycles p q →ₗ[ℂ] zbdModelPiece V E (-(-(p : ℤ))) :=
  LinearMap.codRestrict _ (G.zbcCycles p q).subtype fun z => zbdPiece_le_model z.2.1

/-- The cycles of bidegree `(p, q)` as a morphism to the term of degree `-p` of the model. -/
def zbdCyclesToModel (p q : ℕ) :
    ModuleCat.of ℂ (G.zbcCycles p q) ⟶ G.zbdModelComplex.X (-(p : ℤ)) :=
  ModuleCat.ofHom (G.zbdCyclesIncl p q)

theorem zbdCyclesToModel_val (p q : ℕ) (z : G.zbcCycles p q) :
    Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ))))) (G.zbdCyclesToModel p q z) =
      z.val := rfl

theorem zbdCyclesToModel_d (p q : ℕ) :
    G.zbdCyclesToModel p q ≫
      G.zbdModelComplex.d (-(p : ℤ)) ((ComplexShape.up ℤ).next (-(p : ℤ))) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change Subtype.val (p := (· ∈ zbdModelPiece V E (-((ComplexShape.up ℤ).next (-(p : ℤ))))))
    (G.zbdModelComplex.d _ _ (G.zbdCyclesToModel p q z)) = 0
  rw [ZbdGradedComplex.complex_d_val _ (CochainComplex.next ℤ _).symm, zbdCyclesToModel_val]
  exact z.2.2

/-- The class in the model of a cycle of bidegree `(p, q)`. -/
def zbdCyclesClass (p q : ℕ) :
    ModuleCat.of ℂ (G.zbcCycles p q) ⟶ G.zbdModelComplex.homology (-(p : ℤ)) :=
  G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q) ≫
    G.zbdModelComplex.homologyπ _

theorem zbdCyclesClass_boundary (p q : ℕ) (y : zbcPiece V E (p + 1) q) :
    G.zbdCyclesClass p q (G.zbcBoundary p q y) = 0 := by
  let y' : G.zbdModelComplex.X (-((p + 1 : ℕ) : ℤ)) := ⟨y.val, zbdPiece_le_model y.2⟩
  have h : G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl
      (G.zbdCyclesToModel_d p q) (G.zbcBoundary p q y) =
      G.zbdModelComplex.toCycles (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) y' := by
    apply zbd_liftCycles_apply_eq
    apply Subtype.ext
    rw [zbdCyclesToModel_val, zbcBoundary_val,
      ZbdGradedComplex.complex_d_val _ (by push_cast; ring)]
  rw [zbdCyclesClass, ModuleCat.comp_apply, h, ← ModuleCat.comp_apply,
    HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-- **The cohomology of bidegree `(p, q)` inside the cohomology of the model in degree `-p`.** -/
def zbdCohomologyToModel (p q : ℕ) :
    G.ZbcCohomology p q →ₗ[ℂ] G.zbdModelComplex.homology (-(p : ℤ)) :=
  G.zbcLift p q (G.zbdCyclesClass p q).hom (G.zbdCyclesClass_boundary p q)

theorem zbdCohomologyToModel_class (p q : ℕ) (z : G.zbcCycles p q) :
    G.zbdCohomologyToModel p q (G.zbcClass p q z) = G.zbdCyclesClass p q z := rfl

/-- The projection of the model onto exterior degree `q`. -/
def zbdCardFilter (q : ℕ) : Module.End ℂ (ZbcModule V E) :=
  Koszul.diagonal fun S => if S.card = q then LinearMap.id else 0

theorem zbdCardFilter_apply (q : ℕ) (x : ZbcModule V E) (S : Finset E) :
    zbdCardFilter q x S = if S.card = q then x S else 0 := by
  rw [zbdCardFilter, zbd_diagonal_apply]
  split_ifs <;> rfl

theorem zbdCardFilter_d (q : ℕ) (x : ZbcModule V E) :
    G.zbcContraction.d (zbdCardFilter q x) = zbdCardFilter q (G.zbcContraction.d x) := by
  ext S : 1
  rw [zbcContraction_d_apply, zbdCardFilter_apply, zbdCardFilter_apply, zbcContraction_d_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem zbdCardFilter_mem {p q : ℕ} {y : ZbcModule V E}
    (hy : y ∈ zbdModelPiece V E ((p + 1 : ℕ) : ℤ)) :
    zbdCardFilter q y ∈ zbcPiece V E (p + 1) q := by
  intro S
  rw [mem_zbcSlot_iff, zbdCardFilter_apply]
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hS)]
    have h := hy S
    rw [zbdSlot, hS] at h
    exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hS)]

theorem zbdCardFilter_of_mem {p q : ℕ} {z : ZbcModule V E} (hz : z ∈ zbcPiece V E p q) :
    zbdCardFilter q z = z := by
  ext S : 1
  rw [zbdCardFilter_apply]
  split_ifs with hS
  · rfl
  · exact (((mem_zbcSlot_iff p q S (z S)).mp (hz S)).2 hS).symm

/-- **The cohomology of bidegree `(p, q)` injects into the cohomology of the model in degree
`-p`**: a cycle of bidegree `(p, q)` that bounds in the model bounds in bidegree `(p + 1, q)`,
because the Čech differential preserves the exterior degree. -/
theorem zbdCohomologyToModel_injective (p q : ℕ) :
    Function.Injective (G.zbdCohomologyToModel p q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨z, rfl⟩ := G.zbcClass_surjective p q c
  rw [zbdCohomologyToModel_class, zbdCyclesClass, ModuleCat.comp_apply] at hc
  obtain ⟨j, y, hy⟩ := zbd_exists_boundary_of_homologyπ_eq_zero _ _ hc
  rw [← ModuleCat.comp_apply, HomologicalComplex.liftCycles_i] at hy
  rw [zbcClass_eq_zero_iff]
  have h1 := congrArg (Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))) hy
  rw [zbdCyclesToModel_val] at h1
  by_cases hj : j + 1 = -(p : ℤ)
  · rw [ZbdGradedComplex.complex_d_val _ hj] at h1
    refine ⟨zbdCardFilter q (Subtype.val (p := (· ∈ zbdModelPiece V E (-j))) y),
      zbdCardFilter_mem ?_, ?_⟩
    · have h2 := (Subtype.property (p := (· ∈ zbdModelPiece V E (-j))) y)
      generalize Subtype.val (p := (· ∈ zbdModelPiece V E (-j))) y = w at h2 ⊢
      rwa [show -j = ((p + 1 : ℕ) : ℤ) by push_cast; omega] at h2
    · rw [zbdCardFilter_d, h1, zbdCardFilter_of_mem z.2.1]
  · rw [G.zbdModelComplex.shape j _ hj] at h1
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero, ← h1]
    rfl

/-! ### The acceptance test: the derived isomorphism on cohomology is `zbcTorEquiv` -/

/-- **On cohomology, the base change of `ι` followed by the model isomorphism is `zbcTorEquiv`**,
in degree `-p` and internal degree `q`. -/
theorem zbd_homologyMap_torClass {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    HomologicalComplex.homologyMap (G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom)
        (-(p : ℤ)) ((G.zbdTorIso p).hom x.val) =
      G.zbdCohomologyToModel p q (G.zbcTorEquiv p q x) := by
  obtain ⟨f, hf, hfx⟩ := x.2
  rw [zbcTorEquiv_apply, zbdCohomologyToModel_class, zbdCyclesClass]
  have hx : (G.zbdTorIso p).hom x.val = (G.zbdTorIso p).hom (G.incFreeTermToTor p f) := by
    rw [hfx]
  have hmor : (G.zbdResolutionComplexC.liftCycles (𝟙 _) _ rfl
        (by rw [G.zbdResolutionComplexC_d, Limits.comp_zero]) ≫
      G.zbdResolutionComplexC.homologyπ (-(p : ℤ))) ≫
      HomologicalComplex.homologyMap (G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom)
        (-(p : ℤ)) =
      G.zbdModelComplex.liftCycles
        ((G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom).f (-(p : ℤ))) _ rfl
        (by rw [HomologicalComplex.Hom.comm, G.zbdResolutionComplexC_d, Limits.zero_comp]) ≫
        G.zbdModelComplex.homologyπ _ := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
      HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
    simp only [Category.id_comp]
  have key : ∀ t, HomologicalComplex.homologyMap
      (G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom) (-(p : ℤ))
      ((G.zbdResolutionComplexC.liftCycles (𝟙 _) _ rfl
        (by rw [G.zbdResolutionComplexC_d, Limits.comp_zero]) ≫
      G.zbdResolutionComplexC.homologyπ (-(p : ℤ))) t) =
      G.zbdModelComplex.homologyπ _ (G.zbdModelComplex.liftCycles
        ((G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom).f (-(p : ℤ))) _ rfl
        (by rw [HomologicalComplex.Hom.comm, G.zbdResolutionComplexC_d, Limits.zero_comp]) t) :=
    fun t => congrArg (fun φ => φ t) hmor
  rw [hx, zbdTorIso_hom_class, key, ModuleCat.comp_apply]
  congr 1
  apply zbd_liftCycles_apply_eq
  apply Subtype.ext
  rw [zbdCyclesToModel_val, zbd_torTerm_image]
  change _ = G.zbcTorCycle p x.val
  rw [← hfx, zbcTorCycle_class]

/-! ### In the derived category -/

section Derived

universe w

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℂ)]

/-- The cohomology functor of the derived category on the image of a morphism of complexes. -/
theorem zbd_homologyFunctor_map_Q {K L : CochainComplex (ModuleCat.{0} ℂ) ℤ} (f : K ⟶ L)
    (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) n).map (DerivedCategory.Q.map f) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) n).hom.app K ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) _ n).map f ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) n).inv.app L := by
  have h := (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) n).hom.naturality f
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- **Tor as the cohomology of the derived object `Q(ℂ ⊗ F⁻)`** in degree `-p`. -/
def zbdTorDerivedIso (p : ℕ) :
    G.incidenceTor p ≅ (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).obj
      (DerivedCategory.Q.obj G.zbdResolutionComplexC) :=
  G.zbdTorIso p ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).app _).symm

/-- The cohomology of bidegree `(p, q)` inside the cohomology of the derived object of the
model in degree `-p`. -/
def zbdCohomologyToDerivedModel (p q : ℕ) :
    G.ZbcCohomology p q →ₗ[ℂ] (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).obj
      (DerivedCategory.Q.obj G.zbdModelComplex) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).inv.app
    G.zbdModelComplex).hom ∘ₗ G.zbdCohomologyToModel p q

/-- The cohomology of bidegree `(p, q)` inside the cohomology of `Q(C₀)` in degree `-p`. -/
def zbdCohomologyToDerived (p q : ℕ) :
    G.ZbcCohomology p q →ₗ[ℂ] (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).obj
      (DerivedCategory.Q.obj G.zbdTotalComplexC) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map
    (DerivedCategory.Q.map G.zbdModelIso.inv)).hom ∘ₗ G.zbdCohomologyToDerivedModel p q

theorem zbdCohomologyToDerivedModel_injective (p q : ℕ) :
    Function.Injective (G.zbdCohomologyToDerivedModel p q) :=
  (((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).app
    G.zbdModelComplex).symm.toLinearEquiv.injective).comp (G.zbdCohomologyToModel_injective p q)

theorem zbdCohomologyToDerived_injective (p q : ℕ) :
    Function.Injective (G.zbdCohomologyToDerived p q) :=
  (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).mapIso
    (DerivedCategory.Q.mapIso G.zbdModelIso.symm)).toLinearEquiv.injective).comp
    (G.zbdCohomologyToDerivedModel_injective p q)

/-- **Acceptance test, model version.** The cohomology in degree `-p` of the derived
isomorphism `Q(ℂ ⊗ F⁻) ≅ Q(model)` sends the Tor class of bidegree `(p, q)` of `x` to the class
of `zbcTorEquiv x`. -/
theorem zbdDerivedModelIso_torClass {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedModelIso.hom
        ((G.zbdTorDerivedIso p).hom x.val) =
      G.zbdCohomologyToDerivedModel p q (G.zbcTorEquiv p q x) := by
  have e1 : (G.zbdTorDerivedIso p).hom x.val =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).inv.app
        G.zbdResolutionComplexC ((G.zbdTorIso p).hom x.val) := rfl
  have e2 : ∀ y, (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map
      G.zbdDerivedModelIso.hom y =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).inv.app
        G.zbdModelComplex (HomologicalComplex.homologyMap
          (G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom) (-(p : ℤ))
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).hom.app
            G.zbdResolutionComplexC y)) := fun y => by
    rw [zbdDerivedModelIso_hom, zbd_homologyFunctor_map_Q]
    rfl
  have e3 := ModuleCat.hom_inv_apply
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).app
      G.zbdResolutionComplexC) ((G.zbdTorIso p).hom x.val)
  rw [e1, e2]
  erw [e3]
  rw [zbd_homologyMap_torClass]
  rfl

theorem zbdDerivedIso_hom_eq :
    G.zbdDerivedIso.hom = G.zbdDerivedModelIso.hom ≫ DerivedCategory.Q.map G.zbdModelIso.inv := by
  rw [zbdDerivedModelIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Acceptance test.** The cohomology in degree `-p` of the derived isomorphism
`Q(ℂ ⊗ F⁻) ≅ Q(C₀)` sends the Tor class of bidegree `(p, q)` of `x` to the class of
`zbcTorEquiv x`, through the injective map `zbdCohomologyToDerived`. -/
theorem zbdDerivedIso_torClass {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedIso.hom
        ((G.zbdTorDerivedIso p).hom x.val) =
      G.zbdCohomologyToDerived p q (G.zbcTorEquiv p q x) := by
  rw [zbdDerivedIso_hom_eq, Functor.map_comp, ModuleCat.comp_apply, zbdDerivedModelIso_torClass]
  rfl

/-- The derived isomorphism determines `zbcTorEquiv`: the class it produces from `x` is the
image of exactly one element of the cohomology of bidegree `(p, q)`, namely `zbcTorEquiv x`. -/
theorem zbdDerivedIso_torClass_eq_iff {p q : ℕ} (x : G.incidenceTorInternalPiece p q)
    (y : G.ZbcCohomology p q) :
    G.zbdCohomologyToDerived p q y =
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedIso.hom
          ((G.zbdTorDerivedIso p).hom x.val) ↔ y = G.zbcTorEquiv p q x := by
  rw [zbdDerivedIso_torClass]
  exact (G.zbdCohomologyToDerived_injective p q).eq_iff

section Sheaf

open AlgebraicGeometry TopologicalSpace

local instance zbdSheafHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **`C₀` computes sheaf cohomology.** For `j + p = q`, the actual sheaf cohomology
`H^j(X_G, ∧^q F_G^∨)` inside the cohomology of `Q(C₀)` in degree `-p`, through `zbcSheafEquiv`
and the inclusion of internal degree `q`. -/
def zbdSheafToDerived {p q j : ℕ} (hj : j + p = q) :
    letI := G.exteriorBundleCohomologyModule ℂ q j
    Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j →ₗ[ℂ]
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).obj
        (DerivedCategory.Q.obj G.zbdTotalComplexC) :=
  letI := G.exteriorBundleCohomologyModule ℂ q j
  G.zbdCohomologyToDerived p q ∘ₗ (G.zbcSheafEquiv hj).symm.toLinearMap

theorem zbdSheafToDerived_injective {p q j : ℕ} (hj : j + p = q) :
    Function.Injective (G.zbdSheafToDerived hj) :=
  (G.zbdCohomologyToDerived_injective p q).comp (G.zbcSheafEquiv hj).symm.injective

/-- **Acceptance test against sheaf cohomology.** The cohomology in degree `-p` of the derived
isomorphism `Q(ℂ ⊗ F⁻) ≅ Q(C₀)`, read on the Tor class of `x` of internal degree `q`, is the
sheaf cohomology class `incidenceTorExteriorEquiv x` (equivalently `zbcExteriorEquiv x`). -/
theorem zbdDerivedIso_exterior {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedIso.hom
        ((G.zbdTorDerivedIso p).hom x.val) =
      G.zbdSheafToDerived (Nat.sub_add_cancel h) (G.incidenceTorExteriorEquiv h x) := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  rw [zbdDerivedIso_torClass, ← zbcExteriorEquiv_eq]
  change _ = G.zbdCohomologyToDerived p q ((G.zbcSheafEquiv (Nat.sub_add_cancel h)).symm
    (G.zbcSheafEquiv (Nat.sub_add_cancel h) (G.zbcTorEquiv p q x)))
  rw [LinearEquiv.symm_apply_apply]

/-- The derived isomorphism determines the exterior isomorphism: the only sheaf cohomology class
whose image is the class produced from `x` is `incidenceTorExteriorEquiv x`. -/
theorem zbdDerivedIso_exterior_eq_iff {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q)
    (y : letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
      Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p)) :
    G.zbdSheafToDerived (Nat.sub_add_cancel h) y =
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedIso.hom
          ((G.zbdTorDerivedIso p).hom x.val) ↔ y = G.incidenceTorExteriorEquiv h x := by
  rw [zbdDerivedIso_exterior]
  exact (G.zbdSheafToDerived_injective _).eq_iff

/-- **Normalization through the derived isomorphism, every bidegree.** The Tor class of every
state goes to the exterior class of the same state, with coefficient `+1`. -/
theorem zbdDerivedIso_stateClass {p q : ℕ} (h : p ≤ q) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map G.zbdDerivedIso.hom
        ((G.zbdTorDerivedIso p).hom (G.incidenceTorStateClass ⟨S, κ⟩ hb)) =
      G.zbdSheafToDerived (Nat.sub_add_cancel h)
        (G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb)) := by
  have hx := G.zbdDerivedIso_exterior h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
    G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩
  rw [G.incidenceTorExteriorEquiv_stateClass h S κ hb] at hx
  exact hx

end Sheaf

end Derived

end

end BPFixedPoints.Multigraph
