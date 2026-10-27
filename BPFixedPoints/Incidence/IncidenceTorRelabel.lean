import BPFixedPoints.Incidence.IncidenceRelabelResolution
import BPFixedPoints.Incidence.IncidenceRelabelExterior
import BPFixedPoints.Incidence.IncidenceTorExteriorIsomorphism

/-!
# Graph naturality of the bigraded Tor isomorphism under edge relabelings

## Derived functors along a ring isomorphism

Let `σ : R ≃+* R'` be a ring isomorphism compatible with ring maps `ε : R →+* k` and
`ε' : R' →+* k`. Restriction of scalars along `σ` is an equivalence, and extension of scalars
along `ε` of a restricted `R'`-module is its extension along `ε'` (`restrictExtendIso`). Given an
`R`-module `M`, an `R'`-module `M'` and an isomorphism of `R`-modules between `M'` restricted
along `σ` and `M`, the left derived functors give an isomorphism
`(L_n ε^*) M ≅ (L_n ε'^*) M'` (`derivedRingChange`). It is defined through Mathlib's chosen
projective resolution of `M'`; `derivedRingChange_hom_eq` shows that it is computed by any lift
of the module isomorphism to any pair of projective resolutions, hence does not depend on choices.

## The Tor map of an edge relabeling

For `φ : EdgeRelabel G H`, the coefficient ring isomorphism and the incidence ring isomorphism
give the canonical isomorphism of actual Tor spaces (`incidenceTorRelabel`). The relabeling chain
map of the actual free resolutions computes it; at the coefficient origin that chain map is the
signed relabeling of states, so the full state vector of the image of a Tor class is the signed
relabeling of its full state vector (`incidenceTorFullState_relabel`). Consequently the Tor map
preserves internal degrees, the standard Tor product and the unit. Together with the exterior side
(`IncidenceRelabelExterior.lean`) this gives the naturality square of
`incidenceTorExteriorEquiv` (`incidenceTorExteriorEquiv_natural`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-- On complexes with zero differentials, homology maps are the termwise maps. -/
theorem homologyIsoTermOfZeroDifferentials_naturality {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) (φ : K ⟶ L) (n : ι) :
    HomologicalComplex.homologyMap φ n ≫ (homologyIsoTermOfZeroDifferentials L hL n).hom =
      (homologyIsoTermOfZeroDifferentials K hK n).hom ≫ φ.f n :=
  (ShortComplex.LeftHomologyMapData.ofZeros
    ((HomologicalComplex.shortComplexFunctor C c n).map φ) (hK _ _) (hK _ _) (hL _ _)
      (hL _ _)).homologyMap_comm

section RingChange

variable {R R' k : Type} [CommRing R] [CommRing R'] [CommRing k] (σ : R ≃+* R')
  (ε : R →+* k) (ε' : R' →+* k) (hε : ∀ r, ε' (σ r) = ε r)

include hε

/-- Extension of scalars along `ε` of an `R'`-module restricted along `σ` is its extension along
`ε'`, by `z ⊗ n ↦ z ⊗ n`. -/
noncomputable def restrictExtendLinearEquiv (N : ModuleCat.{0} R') :
    (ModuleCat.extendScalars ε).obj ((ModuleCat.restrictScalars σ.toRingHom).obj N) ≃ₗ[k]
      (ModuleCat.extendScalars ε').obj N := by
  letI : Algebra R k := ε.toAlgebra
  letI : Algebra R' k := ε'.toAlgebra
  let fwd : (ModuleCat.extendScalars ε).obj ((ModuleCat.restrictScalars σ.toRingHom).obj N) →+
      (ModuleCat.extendScalars ε').obj N :=
    TensorProduct.liftAddHom
      { toFun := fun z =>
          { toFun := fun n => (z : k) ⊗ₜ[R'] (n : N)
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := by ext n; exact TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => by ext n; exact TensorProduct.add_tmul _ _ _ }
      (fun r z n => by
        change (ε r * (show k from z) : k) ⊗ₜ[R'] (n : N) = (show k from z) ⊗ₜ[R'] (σ r • (n : N))
        rw [← TensorProduct.smul_tmul, ← hε r]
        rfl)
  let bwd : (ModuleCat.extendScalars ε').obj N →+
      (ModuleCat.extendScalars ε).obj ((ModuleCat.restrictScalars σ.toRingHom).obj N) :=
    TensorProduct.liftAddHom
      { toFun := fun z =>
          { toFun := fun n => (z : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars σ.toRingHom).obj N from n)
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := by ext n; exact TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => by ext n; exact TensorProduct.add_tmul _ _ _ }
      (fun r z n => by
        change (ε' r * (show k from z) : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars σ.toRingHom).obj N from n) =
          (show k from z) ⊗ₜ[R] (show (ModuleCat.restrictScalars σ.toRingHom).obj N from r • n)
        have hn : (show (ModuleCat.restrictScalars σ.toRingHom).obj N from r • n) =
            σ.symm r • (show (ModuleCat.restrictScalars σ.toRingHom).obj N from n) := by
          change r • n = σ (σ.symm r) • n
          rw [RingEquiv.apply_symm_apply]
        rw [hn, ← TensorProduct.smul_tmul]
        change (ε' r * (show k from z) : k) ⊗ₜ[R] _ = (ε (σ.symm r) * (show k from z) : k) ⊗ₜ[R] _
        rw [← hε, RingEquiv.apply_symm_apply])
  exact
    { toFun := fwd
      invFun := bwd
      map_add' := map_add fwd
      map_smul' := fun c t => by
        induction t using TensorProduct.inductionOn with
        | tmul z n =>
          change fwd ((c * (show k from z) : k) ⊗ₜ[R] n) = c • fwd (z ⊗ₜ[R] n)
          rfl
        | add t u ht hu => rw [smul_add, map_add, ht, hu, map_add, smul_add]
      left_inv := fun t => by
        induction t using TensorProduct.inductionOn with
        | tmul z n => rfl
        | add t u ht hu => rw [map_add, map_add, ht, hu]
      right_inv := fun t => by
        induction t using TensorProduct.inductionOn with
        | tmul z n => rfl
        | add t u ht hu => rw [map_add, map_add, ht, hu] }

theorem restrictExtendLinearEquiv_tmul (N : ModuleCat.{0} R') (z : k) (n : N) :
    letI : Algebra R k := ε.toAlgebra
    letI : Algebra R' k := ε'.toAlgebra
    restrictExtendLinearEquiv σ ε ε' hε N
        ((z : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars σ.toRingHom).obj N from n)) =
      (z : k) ⊗ₜ[R'] n := rfl

/-- Extension of scalars after restriction along `σ` is extension of scalars along `ε'`. -/
noncomputable def restrictExtendIso :
    ModuleCat.restrictScalars.{0} σ.toRingHom ⋙ ModuleCat.extendScalars ε ≅
      ModuleCat.extendScalars ε' :=
  NatIso.ofComponents (fun N => (restrictExtendLinearEquiv σ ε ε' hε N).toModuleIso)
    (fun {N N'} g => by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      rfl)

theorem restrictExtendIso_hom_app_tmul (N : ModuleCat.{0} R') (n : N) :
    letI : Algebra R k := ε.toAlgebra
    letI : Algebra R' k := ε'.toAlgebra
    (restrictExtendIso σ ε ε' hε).hom.app N
        ((1 : k) ⊗ₜ[R] (show (ModuleCat.restrictScalars σ.toRingHom).obj N from n)) =
      (1 : k) ⊗ₜ[R'] n := rfl

/-- Termwise comparison of complexes: extension along `ε` of a restricted complex is the
extension along `ε'` of the original complex. -/
noncomputable def restrictExtendComplexIso (K : ChainComplex (ModuleCat.{0} R') ℕ) :
    ((ModuleCat.extendScalars ε).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj K) ≅
      ((ModuleCat.extendScalars ε').mapHomologicalComplex _).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (restrictExtendIso σ ε ε' hε).app (K.X i))
    (fun i j _ => ((restrictExtendIso σ ε ε' hε).hom.naturality (K.d i j)).symm)

/-- The comparison of complexes is natural for chain maps. -/
theorem restrictExtendComplexIso_naturality {K L : ChainComplex (ModuleCat.{0} R') ℕ} (f : K ⟶ L) :
    ((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
        (((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).map f) ≫
      (restrictExtendComplexIso σ ε ε' hε L).hom =
        (restrictExtendComplexIso σ ε ε' hε K).hom ≫
          ((ModuleCat.extendScalars ε').mapHomologicalComplex _).map f := by
  ext i : 1
  exact (restrictExtendIso σ ε ε' hε).hom.naturality (f.f i)

omit hε in
/-- The augmentation of a restricted projective resolution in degree zero is the restricted
augmentation. -/
theorem mapProjectiveResolution_π_f_zero {M' : ModuleCat.{0} R'} (Q : ProjectiveResolution M') :
    ((ModuleCat.restrictScalars σ.toRingHom).mapProjectiveResolution Q).π.f 0 =
      (ModuleCat.restrictScalars σ.toRingHom).map (Q.π.f 0) := by
  ext x
  rfl

variable {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'}
  (e : (ModuleCat.restrictScalars σ.toRingHom).obj M' ≅ M)

/-- The isomorphism of left derived functors of extension of scalars induced by a ring isomorphism
and a compatible module isomorphism, computed with Mathlib's chosen projective resolution. -/
noncomputable def derivedRingChange (n : ℕ) :
    ((ModuleCat.extendScalars ε).leftDerived n).obj M ≅
      ((ModuleCat.extendScalars ε').leftDerived n).obj M' :=
  (((ModuleCat.extendScalars ε).leftDerived n).mapIso e).symm ≪≫
    (((ModuleCat.restrictScalars σ.toRingHom).mapProjectiveResolution
      (projectiveResolution M')).isoLeftDerivedObj (ModuleCat.extendScalars ε) n) ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (restrictExtendComplexIso σ ε ε' hε (projectiveResolution M').complex) ≪≫
    ((projectiveResolution M').isoLeftDerivedObj (ModuleCat.extendScalars ε') n).symm

/-- The derived ring change is computed by any lift of the module isomorphism to projective
resolutions; in particular it does not depend on the chosen resolution. -/
theorem derivedRingChange_hom_eq (P : ProjectiveResolution M) (Q : ProjectiveResolution M')
    (g : P.complex ⟶ ((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj Q.complex)
    (hg : g.f 0 ≫ (ModuleCat.restrictScalars σ.toRingHom).map (Q.π.f 0) = P.π.f 0 ≫ e.inv)
    (n : ℕ) :
    (derivedRingChange σ ε ε' hε e n).hom =
      (P.isoLeftDerivedObj (ModuleCat.extendScalars ε) n).hom ≫
        HomologicalComplex.homologyMap (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map g) n ≫
          HomologicalComplex.homologyMap (restrictExtendComplexIso σ ε ε' hε Q.complex).hom n ≫
            (Q.isoLeftDerivedObj (ModuleCat.extendScalars ε') n).inv := by
  let Ψ := ModuleCat.restrictScalars.{0} σ.toRingHom
  let Q₀ := projectiveResolution M'
  let c := ProjectiveResolution.lift (𝟙 M') Q Q₀
  have hc : c.f 0 ≫ Q₀.π.f 0 = Q.π.f 0 ≫ 𝟙 M' := ProjectiveResolution.lift_commutes_zero _ _ _
  have h1 := ProjectiveResolution.isoLeftDerivedObj_hom_naturality e.inv P
    (Ψ.mapProjectiveResolution Q₀) (g ≫ (Ψ.mapHomologicalComplex _).map c) (by
      rw [HomologicalComplex.comp_f, Category.assoc, mapProjectiveResolution_π_f_zero,
        Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, hc]
      have hid : Q.π.f 0 ≫ 𝟙 M' = Q.π.f 0 := Category.comp_id _
      rw [hid, hg])
    (ModuleCat.extendScalars ε) n
  have h2 := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 M') Q Q₀ c hc
    (ModuleCat.extendScalars ε') n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h2
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h2
  have h3 := restrictExtendComplexIso_naturality σ ε ε' hε c
  simp only [derivedRingChange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom]
  rw [reassoc_of% h1]
  simp only [HomologicalComplex.homologyFunctor_map, Functor.map_comp,
    HomologicalComplex.homologyMap_comp, Category.assoc]
  congr 2
  rw [← HomologicalComplex.homologyMap_comp_assoc, h3, HomologicalComplex.homologyMap_comp,
    Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
  exact h2.symm

end RingChange

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- The coefficient ring isomorphism as a ring equivalence. -/
noncomputable abbrev coeffRingEquiv : IncCoeffRing E ≃+* IncCoeffRing E' := φ.coeffEquiv.toRingEquiv

/-- The incidence ring as a module over its coefficient ring, through the coefficient map. -/
noncomputable def incidenceModule {K₀ : Type} [LinearOrder K₀] [Fintype K₀]
    (K : Multigraph V K₀) : ModuleCat.{0} (IncCoeffRing K₀) :=
  letI : Algebra (IncCoeffRing K₀) K.IncidenceRing := K.coeffHom.toRingHom.toAlgebra
  ModuleCat.of (IncCoeffRing K₀) K.IncidenceRing

/-- The inverse incidence ring isomorphism intertwines the coefficient actions. -/
theorem incidenceEquiv_symm_coeff_mul (r : IncCoeffRing E) (y : H.IncidenceRing) :
    φ.incidenceEquiv.symm (H.coeffHom (φ.coeffEquiv r) * y) =
      G.coeffHom r * φ.incidenceEquiv.symm y := by
  rw [map_mul, ← incidenceEquiv_coeffHom, AlgEquiv.symm_apply_apply]

/-- The incidence ring of `H`, restricted along the coefficient isomorphism, is the incidence ring
of `G` as a module over the coefficients of `G`. -/
noncomputable def incidenceLinearEquiv :
    ((ModuleCat.restrictScalars φ.coeffRingEquiv.toRingHom).obj (incidenceModule H)) ≃ₗ[IncCoeffRing E]
      (incidenceModule G) where
  toFun y := φ.incidenceEquiv.symm y
  invFun x := φ.incidenceEquiv x
  map_add' y y' := map_add φ.incidenceEquiv.symm y y'
  map_smul' r y := φ.incidenceEquiv_symm_coeff_mul r y
  left_inv y := φ.incidenceEquiv.apply_symm_apply y
  right_inv x := φ.incidenceEquiv.symm_apply_apply x

/-- The incidence module isomorphism, as an isomorphism of coefficient modules. -/
noncomputable def incidenceModuleIso :
    (ModuleCat.restrictScalars φ.coeffRingEquiv.toRingHom).obj (incidenceModule H) ≅
      incidenceModule G :=
  φ.incidenceLinearEquiv.toModuleIso

/-- The isomorphism of actual Tor spaces induced by an edge relabeling: the derived ring change
along the coefficient isomorphism and the incidence ring isomorphism. -/
noncomputable def incidenceTorRelabelIso (p : ℕ) : G.incidenceTor p ≅ H.incidenceTor p :=
  derivedRingChange φ.coeffRingEquiv constantCoeff constantCoeff φ.constantCoeff_coeffEquiv
    φ.incidenceModuleIso p

/-- The Tor map of an edge relabeling, as a linear isomorphism. -/
noncomputable def incidenceTorRelabel (p : ℕ) : G.incidenceTor p ≃ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorRelabelIso p).toLinearEquiv

/-- The relabeling chain map of the actual free resolutions, as a chain map of complexes of
coefficient modules of `G`. -/
noncomputable def resolutionChainMap :
    G.incFreeResolution.complex ⟶
      ((ModuleCat.restrictScalars φ.coeffRingEquiv.toRingHom).mapHomologicalComplex _).obj
        H.incFreeResolution.complex where
  f n := ModuleCat.ofHom (X := G.IncFreeTerm n)
    (Y := (ModuleCat.restrictScalars φ.coeffRingEquiv.toRingHom).obj
      (ModuleCat.of (IncCoeffRing E') (H.IncFreeTerm n)))
    { toFun := fun x => φ.freeTermRelabel n x
      map_add' := fun x y => map_add (φ.freeTermRelabel n) x y
      map_smul' := fun r x => (φ.freeTermRelabel n).map_smulₛₗ r x }
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    ext x
    change H.incFreeResolution.complex.d (j + 1) j (φ.freeTermRelabel (j + 1) x) =
      φ.freeTermRelabel j (G.incFreeResolution.complex.d (j + 1) j x)
    rw [incFreeResolution_d, incFreeResolution_d]
    exact φ.freeTermRelabel_differential j x

theorem resolutionChainMap_f_apply (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.resolutionChainMap.f n) x = φ.freeTermRelabel n x := rfl

/-- The relabeling chain map lifts the incidence ring isomorphism. -/
theorem resolutionChainMap_comm_zero :
    φ.resolutionChainMap.f 0 ≫
        (ModuleCat.restrictScalars φ.coeffRingEquiv.toRingHom).map (H.incFreeResolution.π.f 0) =
      G.incFreeResolution.π.f 0 ≫ φ.incidenceModuleIso.inv := by
  ext x
  change H.incResolutionAugmentation (φ.freeTermRelabel 0 x) =
    φ.incidenceEquiv (G.incResolutionAugmentation x)
  exact φ.freeTermRelabel_augmentation x

/-- The Tor map of an edge relabeling is computed by the relabeling chain map of the actual free
resolutions. -/
theorem incidenceTorRelabelIso_hom_eq (p : ℕ) :
    (φ.incidenceTorRelabelIso p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map φ.resolutionChainMap) p ≫
          HomologicalComplex.homologyMap
            (restrictExtendComplexIso φ.coeffRingEquiv constantCoeff constantCoeff
              φ.constantCoeff_coeffEquiv H.incFreeResolution.complex).hom p ≫
            (H.incFreeResolution.isoLeftDerivedObj
              (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E' →+* ℂ)) p).inv :=
  derivedRingChange_hom_eq φ.coeffRingEquiv constantCoeff constantCoeff φ.constantCoeff_coeffEquiv
    φ.incidenceModuleIso G.incFreeResolution H.incFreeResolution φ.resolutionChainMap
    φ.resolutionChainMap_comm_zero p

/-- In free-term coordinates the Tor map of an edge relabeling is the specialization of the
relabeling chain map. -/
theorem incidenceTorIsoFreeTerm_relabel (p : ℕ) :
    (φ.incidenceTorRelabelIso p).hom ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          (φ.resolutionChainMap.f p) ≫
          (restrictExtendIso φ.coeffRingEquiv constantCoeff constantCoeff
            φ.constantCoeff_coeffEquiv).hom.app _ := by
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
  rw [hG, hH, incidenceTorRelabelIso_hom_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, homologyIsoTermOfZeroDifferentials_naturality]
  rfl

/-- The Tor map of an edge relabeling sends the specialization of a free-resolution element to the
specialization of its relabeling. -/
theorem incidenceTorRelabel_class (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorRelabel p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.freeTermRelabel p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom ((φ.incidenceTorRelabelIso p).hom (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (φ.freeTermRelabel p x))
  rw [← ConcreteCategory.comp_apply, incidenceTorIsoFreeTerm_relabel, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul, incFreeTermToTor_eq_tmul]
  rfl

/-- The full state vector of the image of a Tor class under the Tor map of an edge relabeling is
the signed relabeling of its full state vector. -/
theorem incidenceTorFullState_relabel (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorRelabel p y) =
      φ.stateRelabel ℂ (G.incidenceTorFullState p y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [incidenceTorRelabel_class, incidenceTorFullState_class, incidenceTorFullState_class,
    freeTermRelabel_val, mapRange_resolutionRelabel]

/-- The inverse Tor map of an edge relabeling on full state vectors. -/
theorem incidenceTorFullState_relabel_symm (p : ℕ) (y : H.incidenceTor p) :
    G.incidenceTorFullState p ((φ.incidenceTorRelabel p).symm y) =
      (φ.stateRelabel ℂ).symm (H.incidenceTorFullState p y) := by
  rw [LinearEquiv.eq_symm_apply, ← incidenceTorFullState_relabel, LinearEquiv.apply_symm_apply]

/-- The Tor map of an edge relabeling preserves the standard Tor product. -/
theorem incidenceTorRelabel_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorRelabel (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorRelabel p x) (φ.incidenceTorRelabel q y) := by
  apply H.incidenceTorFullState_injective (p + q)
  rw [incidenceTorFullState_relabel, incidenceTorFullState_product, incidenceTorFullState_product,
    incidenceTorFullState_relabel, incidenceTorFullState_relabel, stateRelabel_incStateCup]

/-- The Tor map of an edge relabeling sends the unit of Tor to the unit. -/
theorem incidenceTorRelabel_one :
    φ.incidenceTorRelabel 0 G.incidenceTorOne = H.incidenceTorOne := by
  apply H.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_relabel, incidenceTorFullState_one, incidenceTorFullState_one,
    stateRelabel_incStateUnit]

/-- Coefficients of the inverse signed relabeling. -/
theorem stateRelabel_symm_apply (R : Type) [CommRing R] (z : H.IncResolutionBasis →₀ R)
    (b : G.IncResolutionBasis) :
    (φ.stateRelabel R).symm z b = φ.sign R b.1 * z (φ.stateIndex b) := by
  have h := φ.stateRelabel_apply_stateIndex R ((φ.stateRelabel R).symm z) b
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, ← mul_assoc, sign_mul_self, one_mul]

/-- Membership in an internal Tor piece through the full state vector: all coefficients at states
of another internal degree vanish. -/
theorem mem_incidenceTorInternalPiece_iff_fullState {K₀ : Type} [LinearOrder K₀] [Fintype K₀]
    (K : Multigraph V K₀) (p q : ℕ) (x : K.incidenceTor p) :
    x ∈ K.incidenceTorInternalPiece p q ↔
      ∀ b, K.incResolutionInternalDegree b ≠ q → K.incidenceTorFullState p x b = 0 := by
  rw [mem_incidenceTorInternalPiece_iff, Finsupp.mem_supported']
  constructor
  · intro h b hb
    by_cases hp : K.incResolutionDegree b = p
    · rw [show b = (⟨b, hp⟩ : {b : K.IncResolutionBasis // K.incResolutionDegree b = p}).val
        from rfl, incidenceTorFullState_apply]
      exact h ⟨b, hp⟩ hb
    · exact K.incidenceTorFullState_apply_of_ne p x b hp
  · intro h b hb
    rw [← incidenceTorFullState_apply]
    exact h b.val hb

/-- The Tor map of an edge relabeling preserves internal degrees. -/
theorem incidenceTorRelabel_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorRelabel p x ∈ H.incidenceTorInternalPiece p q := by
  rw [mem_incidenceTorInternalPiece_iff_fullState] at hx ⊢
  intro b hb
  rw [incidenceTorFullState_relabel, stateRelabel_apply]
  rw [hx _ (by rwa [← φ.incResolutionInternalDegree_stateIndex, Equiv.apply_symm_apply]), mul_zero]

/-- The inverse Tor map of an edge relabeling preserves internal degrees. -/
theorem incidenceTorRelabel_symm_mem_internalPiece {p q : ℕ} {y : H.incidenceTor p}
    (hy : y ∈ H.incidenceTorInternalPiece p q) :
    (φ.incidenceTorRelabel p).symm y ∈ G.incidenceTorInternalPiece p q := by
  rw [mem_incidenceTorInternalPiece_iff_fullState] at hy ⊢
  intro b hb
  rw [incidenceTorFullState_relabel_symm, stateRelabel_symm_apply]
  rw [hy _ (by rwa [φ.incResolutionInternalDegree_stateIndex]), mul_zero]

theorem map_incidenceTorInternalPiece (p q : ℕ) :
    (G.incidenceTorInternalPiece p q).map (φ.incidenceTorRelabel p : G.incidenceTor p →ₗ[ℂ] _) =
      H.incidenceTorInternalPiece p q := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact φ.incidenceTorRelabel_mem_internalPiece hx
  · intro y hy
    exact ⟨_, φ.incidenceTorRelabel_symm_mem_internalPiece hy, LinearEquiv.apply_symm_apply _ y⟩

/-- The Tor map of an edge relabeling on bigraded pieces. -/
noncomputable def incidenceTorInternalRelabel (p q : ℕ) :
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorRelabel p).ofSubmodules _ _ (φ.map_incidenceTorInternalPiece p q)

@[simp] theorem incidenceTorInternalRelabel_val (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalRelabel p q x : H.incidenceTor p) = φ.incidenceTorRelabel p x.val :=
  rfl

/-- **Graph naturality of the bigraded Tor isomorphism.** For an edge relabeling `φ : G → H`, the
isomorphism `incidenceTorExteriorEquiv` of `H` composed with the Tor map of `φ` is the exterior
cohomology map of `φ` composed with the isomorphism of `G`. -/
theorem incidenceTorExteriorEquiv_natural {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalRelabel p q x) =
      φ.exteriorCohomologyRelabelLinear ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, exteriorCohomologyRelabelLinear_apply,
    exteriorCohomologyState_relabel, exteriorCohomologyState_incidenceTorExteriorEquiv,
    incidenceTorInternalRelabel_val, incidenceTorFullState_relabel]

/-! ## Identities and composition -/

/-- The Tor map of the identity relabeling is the identity. -/
theorem incidenceTorRelabel_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorRelabel p y = y :=
  G.incidenceTorFullState_injective p (by rw [incidenceTorFullState_relabel, stateRelabel_refl])

/-- The Tor map of a composite relabeling is the composite of the Tor maps. -/
theorem incidenceTorRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : EdgeRelabel H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans ψ).incidenceTorRelabel p y = ψ.incidenceTorRelabel p (φ.incidenceTorRelabel p y) :=
  K.incidenceTorFullState_injective p (by
    rw [incidenceTorFullState_relabel, incidenceTorFullState_relabel, incidenceTorFullState_relabel,
      stateRelabel_trans])

section ExteriorFunctoriality

attribute [local instance] exteriorProductHasExt

/-- The exterior cohomology map of the identity relabeling is the identity. -/
theorem exteriorCohomologyRelabel_refl (G : Multigraph V E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (refl G).exteriorCohomologyRelabel ℂ q j x = x :=
  G.exteriorCohomologyState_injective ℂ q j (by
    rw [exteriorCohomologyState_relabel, stateRelabel_refl])

/-- The exterior cohomology map of a composite relabeling is the composite of the maps. -/
theorem exteriorCohomologyRelabel_trans {E'' : Type} [LinearOrder E''] [Fintype E'']
    {K : Multigraph V E''} (ψ : EdgeRelabel H K) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :
    (φ.trans ψ).exteriorCohomologyRelabel ℂ q j x =
      ψ.exteriorCohomologyRelabel ℂ q j (φ.exteriorCohomologyRelabel ℂ q j x) :=
  K.exteriorCohomologyState_injective ℂ q j (by
    rw [exteriorCohomologyState_relabel, exteriorCohomologyState_relabel,
      exteriorCohomologyState_relabel, stateRelabel_trans])

end ExteriorFunctoriality

end EdgeRelabel

end BPFixedPoints.Multigraph
