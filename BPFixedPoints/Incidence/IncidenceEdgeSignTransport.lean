import BPFixedPoints.Incidence.IncidenceTorRelabel

/-!
# Tor maps of coefficient-compatible incidence ring isomorphisms

Let `τ : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E'` preserve the constant coefficient and let
`ι : G.IncidenceRing ≃ₐ[ℂ] H.IncidenceRing` intertwine the coefficient maps through `τ`. The
derived ring change of `IncidenceTorRelabel.lean` along `τ` and the module isomorphism given by
`ι` is an isomorphism of actual Tor spaces (`incidenceTorTransportIso`); the Tor map of an edge
relabeling is the instance `τ = φ.coeffEquiv`, `ι = φ.incidenceEquiv`
(`incidenceTorRelabelIso_eq_transport`, by definition).

Any family of `τ`-semilinear maps of the terms of the actual free resolutions that commutes with
the differentials and lifts `ι` through the augmentations is a chain map (`freeTermChainMap`); it
computes the transported Tor map (`incidenceTorTransportIso_hom_eq`), so the Tor map sends the
specialization of a free-resolution element to the specialization of its image
(`incidenceTorTransport_class`). In particular, if the family specializes at the coefficient
origin to a map of state vectors, the full state vector of the image of a Tor class is that map
applied to the full state vector of the class (`incidenceTorFullState_transport`). This is how
state formulas of Tor maps are proved: the Tor map is defined by the derived functors of the ring
and module maps, and the state formula is read off from an explicit chain map.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial
open scoped TensorProduct

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}

variable (τ : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E')
  (hτ : ∀ r, constantCoeff (τ r) = constantCoeff r)
  (ι : G.IncidenceRing ≃ₐ[ℂ] H.IncidenceRing)
  (hι : ∀ r, ι (G.coeffHom r) = H.coeffHom (τ r))

include hι in
/-- The inverse incidence ring isomorphism intertwines the coefficient actions. -/
theorem incidenceTransport_symm_coeff_mul (r : IncCoeffRing E) (y : H.IncidenceRing) :
    ι.symm (H.coeffHom (τ r) * y) = G.coeffHom r * ι.symm y := by
  rw [map_mul, ← hι, AlgEquiv.symm_apply_apply]

/-- The incidence ring of `H`, restricted along `τ`, is the incidence ring of `G` as a module over
the coefficients of `G`, through the inverse of `ι`. -/
noncomputable def incidenceTransportLinearEquiv :
    ((ModuleCat.restrictScalars τ.toRingEquiv.toRingHom).obj (EdgeRelabel.incidenceModule H)) ≃ₗ[IncCoeffRing E]
      (EdgeRelabel.incidenceModule G) where
  toFun y := ι.symm y
  invFun x := ι x
  map_add' y y' := map_add ι.symm y y'
  map_smul' r y := incidenceTransport_symm_coeff_mul τ ι hι r y
  left_inv y := ι.apply_symm_apply y
  right_inv x := ι.symm_apply_apply x

/-- The isomorphism of actual Tor spaces induced by `τ` and `ι`: the derived ring change along the
coefficient isomorphism and the incidence module isomorphism. -/
noncomputable def incidenceTorTransportIso (p : ℕ) : G.incidenceTor p ≅ H.incidenceTor p :=
  derivedRingChange τ.toRingEquiv constantCoeff constantCoeff hτ
    (incidenceTransportLinearEquiv τ ι hι).toModuleIso p

/-- The transported Tor map as a linear isomorphism. -/
noncomputable def incidenceTorTransport (p : ℕ) : G.incidenceTor p ≃ₗ[ℂ] H.incidenceTor p :=
  (incidenceTorTransportIso τ hτ ι hι p).toLinearEquiv

/-- The Tor map of an edge relabeling is the transported Tor map of its coefficient and incidence
ring isomorphisms. -/
theorem EdgeRelabel.incidenceTorRelabelIso_eq_transport (φ : EdgeRelabel G H) (p : ℕ) :
    φ.incidenceTorRelabelIso p =
      incidenceTorTransportIso φ.coeffEquiv φ.constantCoeff_coeffEquiv φ.incidenceEquiv
        φ.incidenceEquiv_coeffHom p :=
  rfl

/-- A family of `τ`-semilinear maps of the free resolution terms commuting with the differentials,
as a chain map of complexes of coefficient modules of `G`. -/
noncomputable def freeTermChainMap
    (F : ∀ n, G.IncFreeTerm n →ₛₗ[τ.toAlgHom.toRingHom] H.IncFreeTerm n)
    (hF : ∀ n x, H.incFreeTermDifferential n (F (n + 1) x) = F n (G.incFreeTermDifferential n x)) :
    G.incFreeResolution.complex ⟶
      ((ModuleCat.restrictScalars τ.toRingEquiv.toRingHom).mapHomologicalComplex _).obj
        H.incFreeResolution.complex where
  f n := ModuleCat.ofHom (X := G.IncFreeTerm n)
    (Y := (ModuleCat.restrictScalars τ.toRingEquiv.toRingHom).obj
      (ModuleCat.of (IncCoeffRing E') (H.IncFreeTerm n)))
    { toFun := fun x => F n x
      map_add' := fun x y => map_add (F n) x y
      map_smul' := fun r x => (F n).map_smulₛₗ r x }
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    ext x
    change H.incFreeResolution.complex.d (j + 1) j (F (j + 1) x) =
      F j (G.incFreeResolution.complex.d (j + 1) j x)
    rw [incFreeResolution_d, incFreeResolution_d]
    exact hF j x

theorem freeTermChainMap_f_apply
    (F : ∀ n, G.IncFreeTerm n →ₛₗ[τ.toAlgHom.toRingHom] H.IncFreeTerm n)
    (hF : ∀ n x, H.incFreeTermDifferential n (F (n + 1) x) = F n (G.incFreeTermDifferential n x))
    (n : ℕ) (x : G.IncFreeTerm n) :
    ((freeTermChainMap τ F hF).f n) x = F n x := rfl

variable (F : ∀ n, G.IncFreeTerm n →ₛₗ[τ.toAlgHom.toRingHom] H.IncFreeTerm n)
  (hF : ∀ n x, H.incFreeTermDifferential n (F (n + 1) x) = F n (G.incFreeTermDifferential n x))
  (h0 : ∀ x, H.incResolutionAugmentation (F 0 x) = ι (G.incResolutionAugmentation x))

include h0 in
/-- A chain map lifting `ι` through the augmentations, in degree zero. -/
theorem freeTermChainMap_comm_zero :
    (freeTermChainMap τ F hF).f 0 ≫
        (ModuleCat.restrictScalars τ.toRingEquiv.toRingHom).map (H.incFreeResolution.π.f 0) =
      G.incFreeResolution.π.f 0 ≫ (incidenceTransportLinearEquiv τ ι hι).toModuleIso.inv := by
  ext x
  change H.incResolutionAugmentation (F 0 x) = ι (G.incResolutionAugmentation x)
  exact h0 x

include h0 in
/-- The transported Tor map is computed by any semilinear chain map of the actual free resolutions
lifting `ι`. -/
theorem incidenceTorTransportIso_hom_eq (p : ℕ) :
    (incidenceTorTransportIso τ hτ ι hι p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map (freeTermChainMap τ F hF)) p ≫
          HomologicalComplex.homologyMap
            (restrictExtendComplexIso τ.toRingEquiv constantCoeff constantCoeff hτ
              H.incFreeResolution.complex).hom p ≫
            (H.incFreeResolution.isoLeftDerivedObj
              (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E' →+* ℂ)) p).inv :=
  derivedRingChange_hom_eq τ.toRingEquiv constantCoeff constantCoeff hτ
    (incidenceTransportLinearEquiv τ ι hι).toModuleIso G.incFreeResolution H.incFreeResolution
    (freeTermChainMap τ F hF) (freeTermChainMap_comm_zero τ ι hι F hF h0) p

include h0 in
/-- In free-term coordinates the transported Tor map is the specialization of the chain map. -/
theorem incidenceTorIsoFreeTerm_transport (p : ℕ) :
    (incidenceTorTransportIso τ hτ ι hι p).hom ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          ((freeTermChainMap τ F hF).f p) ≫
          (restrictExtendIso τ.toRingEquiv constantCoeff constantCoeff hτ).hom.app _ := by
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
  rw [hG, hH, incidenceTorTransportIso_hom_eq τ hτ ι hι F hF h0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, homologyIsoTermOfZeroDifferentials_naturality]
  rfl

include hF h0 in
/-- The transported Tor map sends the specialization of a free-resolution element to the
specialization of its image under the chain map. -/
theorem incidenceTorTransport_class (p : ℕ) (x : G.IncFreeTerm p) :
    incidenceTorTransport τ hτ ι hι p (G.incFreeTermToTor p x) = H.incFreeTermToTor p (F p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom
      ((incidenceTorTransportIso τ hτ ι hι p).hom (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (F p x))
  rw [← ConcreteCategory.comp_apply, incidenceTorIsoFreeTerm_transport τ hτ ι hι F hF h0,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul,
    incFreeTermToTor_eq_tmul]
  rfl

include hF h0 in
/-- State formula of a transported Tor map: if the chain map specializes at the coefficient origin
to a map `Φ` of state vectors, then the full state vector of the image of a Tor class is `Φ` of its
full state vector. -/
theorem incidenceTorFullState_transport (p : ℕ)
    (Φ : (G.IncResolutionBasis →₀ ℂ) → (H.IncResolutionBasis →₀ ℂ))
    (hΦ : ∀ x : G.IncFreeTerm p,
      mapRange (constantCoeff : IncCoeffRing E' →+* ℂ) (map_zero _) (F p x).val =
        Φ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x.val))
    (y : G.incidenceTor p) :
    H.incidenceTorFullState p (incidenceTorTransport τ hτ ι hι p y) =
      Φ (G.incidenceTorFullState p y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [incidenceTorTransport_class τ hτ ι hι F hF h0, incidenceTorFullState_class,
    incidenceTorFullState_class, hΦ]

end BPFixedPoints.Multigraph
