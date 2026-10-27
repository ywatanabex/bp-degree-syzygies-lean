import BPFixedPoints.Incidence.IncidenceRelativeSpecFaces
import BPFixedPoints.Incidence.IncidenceUniversalKoszulSection
import BPFixedPoints.Incidence.IncidenceKernelSheafCharts
import BPFixedPoints.Incidence.IncidenceProjectiveZeroSections
import BPFixedPoints.Incidence.IncidenceProjectiveZeroAtlas
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # `Z_G ≅ Spec_X Sym(K_G^∨)` for the kernel bundle `K_G` on `X_G = (ℙ¹_ℂ)^V`

Mathlib (pinned) has no relative spectrum of a quasi-coherent algebra. This file builds
`Spec_X Sym(K_G^∨)` for the rank-`3m` kernel bundle `K_G = incKernelSheaf` from local models, glues
them over `X_G` with Mathlib's relative gluing along a locally directed cover
(`Scheme.Cover.RelativeGluingData` over the face cover `vertexFaceCover ℂ V` of
`IncidenceRelativeSpecFaces.lean`), and compares the result with `Z_G`.

* **Local model.** On the face `q` of `X_G`, the model ring is
  `IncSymFaceRing q = FaceRing ℂ q [X_j : j ∈ E × Fin 3]`, the symmetric algebra of the dual of
  `K_G|_q ≅ O^{3m}` in the kernel frame of the chart `vertexFaceBaseChoice V q`; the variables are
  the coordinate functions dual to that frame.
* **Gluing maps.** For a face `r` refining `q`, `incSymRestrict` restricts the base coefficients
  and applies `Sym(g^∨)` (`incLinearSubst`), where `g = incSymTransition` is the vector transition
  `κ_{σ_q} ∘ κ_{σ_r}⁻¹` of the kernel frames. These are the transitions of the trivializations of
  the kernel sheaf (`incKernelSheafTransition_eq`), so coordinate functions transform by the
  transpose of the vector transitions of `K_G` (`incSymRestrict_X_kernelSheaf`); the cocycle
  condition is `incKernelTransition_cocycle_restrict` (`incSymRestrict_comp`). Every naturality
  square of the bundle projection is a pullback (`incSymBaseProj_equifibered`), because polynomial
  rings are base changes (`Algebra.IsPushout`) and `Sym(g^∨)` is an automorphism
  (`incLinearSubstEquiv`).
* **The scheme.** `incSymScheme` is the glued scheme, with the bundle projection
  `incSymProjection : incSymScheme ⟶ X_G`, an affine morphism (`incSymProjection_isAffineHom`).
  Over the face `q` it is `Spec (IncSymFaceRing q)` (`incSymChart_isPullback`,
  `incSymProjection_preimage_face`), and its functions there form the model ring
  (`incSymFaceSectionsIso`): the pushforward algebra is `Sym(K_G^∨)` on every face, in the frame,
  with restriction maps `Sym(g^∨)` (`incSymFaceSectionsIso_restrict`).
  The zero section `incSymZeroSection` is glued over the face cover of `X_G` from `X_j ↦ 0`
  (`incSymZeroSection_projection`). The coefficient functions `incSymCoefficient` send
  `c_{e,α,β}` to the linear form `K_G ⊆ O^{4m} → O` of that coordinate, in each frame.
* **Comparison.** The existing face trivializations `incFaceKernelTriv` of `Z_G` respect the
  overlap maps of the model (`incSymFaceTriv_refinement`, from `incFaceKernelTriv_refinement` and
  `incFaceKernelTriv_transition`), so their spectra glue to
  `incSymGluedIso : incidenceGluedScheme ≅ incSymScheme`, and with the existing comparison to
  `incSymZeroIso : incidenceProjectiveZeroScheme ≅ incSymScheme`. These are isomorphisms over `X_G`
  (`incSymGluedIso_projection`, `incSymZeroIso_projection`), preserve the zero sections
  (`incidenceGluedZeroSection_incSymGluedIso`, `incidenceProjectiveZeroZeroSection_incSymZeroIso`)
  and the coefficient functions (`incSymGluedIso_coefficient`, `incSymZeroIso_coefficient`). The
  projection and the zero section of `Z_G` are glued from its incidence faces (the inclusion of
  base coefficients, resp. `c = 0`); on the original charts `A_σ/(f_e)` of the projective zero
  scheme the projection forgets the coefficients
  (`incidenceProjectiveZeroChartToScheme_projection`).

Not constructed here: the dual sheaf `K_G^∨` and its symmetric algebra as quasi-coherent sheaves of
algebras on `X_G`, and a universal property of the relative spectrum; the identification of the
pushforward algebra with `Sym(K_G^∨)` is through the kernel frames, face by face. The projection
`Z_G ⟶ X_G` of the projective zero scheme is defined through the glued incidence scheme and the
existing comparison `incidenceProjectiveZeroIso`, since the package has no morphism
`(ℙ¹_{S_G})^V ⟶ (ℙ¹_ℂ)^V`; its formula on the original charts is proved.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine MvPolynomial SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

section Pushout

/-- Polynomial rings are base changes, also after an automorphism of the target: for a ring map
`φ : R → A` and an `A`-algebra automorphism `e` of `A[X_ι]`, the square
`R → R[X_ι]`, `R → A`, `e ∘ map φ : R[X_ι] → A[X_ι]`, `A → A[X_ι]` is a pushout of rings. -/
theorem mvPolynomial_isPushout_algEquiv {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A)
    (ι : Type) (e : MvPolynomial ι A ≃ₐ[A] MvPolynomial ι A) :
    IsPushout (CommRingCat.ofHom (C : R →+* MvPolynomial ι R)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp (MvPolynomial.map φ)))
      (CommRingCat.ofHom (C : A →+* MvPolynomial ι A)) := by
  let := φ.toAlgebra
  let : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have h := CommRingCat.isPushout_of_isPushout R (MvPolynomial ι R) A (MvPolynomial ι A)
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.commutes a

end Pushout

section LinearSubstEquiv

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The linear substitution `Sym(g^∨)` of an invertible linear map is an automorphism, with
inverse `Sym((g⁻¹)^∨)`. -/
noncomputable def incLinearSubstEquiv (g : (ι → R) ≃ₗ[R] (ι → R)) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom (incLinearSubst g.toLinearMap) (incLinearSubst g.symm.toLinearMap)
    (by
      rw [← incLinearSubst_comp, LinearEquiv.symm_comp, incLinearSubst_id])
    (by
      rw [← incLinearSubst_comp, LinearEquiv.comp_symm, incLinearSubst_id])

/-- The automorphism acts by the linear substitution. -/
@[simp] theorem incLinearSubstEquiv_apply (g : (ι → R) ≃ₗ[R] (ι → R)) (p : MvPolynomial ι R) :
    incLinearSubstEquiv g p = incLinearSubst g.toLinearMap p :=
  rfl

end LinearSubstEquiv

section Model

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- **The model ring on a face**: the polynomial ring over the face ring `FaceRing ℂ q` of `X_G` in
the `3m` coordinates dual to the kernel frame of the face's own chart, i.e.
`Sym((O^{3m})^∨) = Sym(K_G^∨)` on the face, in the frame of `K_G` given by the chart
`vertexFaceBaseChoice V q`. -/
abbrev IncSymFaceRing (q : V → Fin 3) := MvPolynomial (E × Fin 3) (FaceRing ℂ q)

/-- The transition, on a face `r` refining `q`, from the kernel frame of the chart of `r` to the
kernel frame of the chart of `q`: the transition `g = κ_{σ_q} ∘ κ_{σ_r}⁻¹` of the vector bundle
`K_G` (`incKernelSheafTransition_eq`). -/
noncomputable def incSymTransition {q r : V → Fin 3} (h : FaceRefines q r) :
    (E × Fin 3 → FaceRing ℂ r) ≃ₗ[FaceRing ℂ r] (E × Fin 3 → FaceRing ℂ r) :=
  G.incKernelTransition (vertexFaceBaseChoice_refines V r)
    (faceRefines_trans (vertexFaceBaseChoice_refines V q) h)

/-- **The restriction maps of the model**: restrict the coefficients to the smaller face and apply
the linear substitution `Sym(g^∨)` of the coordinate functions, the contragredient of the vector
transition `g = incSymTransition h`. -/
noncomputable def incSymRestrict {q r : V → Fin 3} (h : FaceRefines q r) :
    IncSymFaceRing (E := E) q →+* IncSymFaceRing (E := E) r :=
  (incLinearSubst (G.incSymTransition h).toLinearMap).toRingHom.comp
    (MvPolynomial.map (faceRefinementMap ℂ h).toRingHom)

/-- The restriction maps restrict base coefficients. -/
@[simp] theorem incSymRestrict_C {q r : V → Fin 3} (h : FaceRefines q r) (a : FaceRing ℂ q) :
    G.incSymRestrict h (C a) = C (faceRefinementMap ℂ h a) := by
  simp [incSymRestrict, incLinearSubst]

/-- The restriction maps send a coordinate function to the transposed linear form. -/
theorem incSymRestrict_X {q r : V → Fin 3} (h : FaceRefines q r) (j : E × Fin 3) :
    G.incSymRestrict h (X j) =
      ∑ i, C (G.incSymTransition h (Pi.single i 1) j) * X i := by
  simp only [incSymRestrict, RingHom.comp_apply, map_X]
  exact incLinearSubst_X _ j

/-- The restriction map of the trivial refinement is the identity. -/
theorem incSymRestrict_refl (q : V → Fin 3) :
    G.incSymRestrict (faceRefines_refl q) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [incSymRestrict_C, faceRefinementMap_refl]
    rfl
  · intro j
    rw [incSymRestrict_X]
    have hg : G.incSymTransition (faceRefines_refl q) = LinearEquiv.refl _ _ :=
      G.incKernelTransition_self (vertexFaceBaseChoice_refines V q)
    rw [hg]
    simp [Pi.single_apply]

/-- **Cocycle condition of the model.** The restriction maps compose: the transitions of `K_G`
satisfy the cocycle condition (`incKernelTransition_cocycle_restrict`). -/
theorem incSymRestrict_comp {q r s : V → Fin 3} (hqr : FaceRefines q r) (hrs : FaceRefines r s) :
    (G.incSymRestrict hrs).comp (G.incSymRestrict hqr) =
      G.incSymRestrict (faceRefines_trans hqr hrs) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, incSymRestrict_C, incSymRestrict_C, incSymRestrict_C,
      overlapFaceRefinementMap_trans]
  · intro j
    have hc := fun i => G.incKernelTransition_cocycle_restrict
      (σ := vertexFaceBaseChoice V s) (τ := vertexFaceBaseChoice V r)
      (ρ := vertexFaceBaseChoice V q)
      (vertexFaceBaseChoice_refines V s) (faceRefines_trans (vertexFaceBaseChoice_refines V r) hrs)
      (vertexFaceBaseChoice_refines V r) (faceRefines_trans (vertexFaceBaseChoice_refines V q) hqr)
      (vertexFaceBaseChoice_refines V s)
      (faceRefines_trans (vertexFaceBaseChoice_refines V q) (faceRefines_trans hqr hrs))
      (faceRefines_refl s) hrs (faceRefines_refl s) i j
    simp only [faceRefinementMap_refl, AlgHom.id_apply] at hc
    rw [RingHom.comp_apply, incSymRestrict_X, map_sum, incSymRestrict_X]
    simp only [map_mul, incSymRestrict_C, incSymRestrict_X, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : G.incSymTransition (faceRefines_trans hqr hrs) (Pi.single k 1) j =
        ∑ i, G.incSymTransition hrs (Pi.single k 1) i *
          faceRefinementMap ℂ hrs (G.incSymTransition hqr (Pi.single i 1) j) :=
      (hc k).symm
    rw [hk, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    ring

/-- The restriction maps of the model are the base change of the restriction maps of `X_G`
followed by the automorphism `Sym(g^∨)`. -/
theorem incSymRestrict_eq {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incSymRestrict h = (incLinearSubstEquiv (G.incSymTransition h)).toRingEquiv.toRingHom.comp
      (MvPolynomial.map (faceRefinementMap ℂ h).toRingHom) :=
  rfl

/-- **The model diagram**: over the face index category of the face cover of `X_G`, the spectra
of the model rings `Sym(K_G^∨)` of the faces, with the spectra of the restriction maps. -/
noncomputable def incSymFaceFunctor : (FaceIndex V)ᵒᵈ ⥤ Scheme where
  obj q := Spec (CommRingCat.of (IncSymFaceRing (E := E) q.ofDual.coord))
  map {i j} f := Spec.map (CommRingCat.ofHom (G.incSymRestrict (leOfHom f)))
  map_id q := by
    change Spec.map (CommRingCat.ofHom (G.incSymRestrict (faceRefines_refl _))) = _
    rw [incSymRestrict_refl]
    exact Spec.map_id _
  map_comp {i j k} f g := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (G.incSymRestrict_comp (leOfHom g) (leOfHom f)).symm

/-- **The bundle projection on faces**: `Spec Sym(K_G^∨)|_q ⟶ Spec FaceRing ℂ q`, the spectrum of
the inclusion of base coefficients. -/
noncomputable def incSymBaseProj :
    G.incSymFaceFunctor ⟶ (vertexFaceCover ℂ V).functorOfLocallyDirected where
  app q := Spec.map (CommRingCat.ofHom
    (C : FaceRing ℂ q.ofDual.coord →+* IncSymFaceRing (E := E) q.ofDual.coord))
  naturality {i j} f := by
    change Spec.map (CommRingCat.ofHom (G.incSymRestrict (leOfHom f))) ≫ Spec.map
        (CommRingCat.ofHom (C : FaceRing ℂ j.ofDual.coord →+* IncSymFaceRing (E := E) _)) =
      Spec.map (CommRingCat.ofHom (C : FaceRing ℂ i.ofDual.coord →+* IncSymFaceRing (E := E) _)) ≫
        Spec.map (CommRingCat.ofHom (faceRefinementMap ℂ (leOfHom f)).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact G.incSymRestrict_C (leOfHom f) a

/-- **The model is locally the base change of the faces of `X_G`**: every naturality square of
the bundle projection is a pullback, because the model rings are polynomial rings and the
restriction maps are base changes followed by automorphisms. -/
theorem incSymBaseProj_equifibered : NatTrans.Equifibered G.incSymBaseProj := by
  intro i j f
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (mvPolynomial_isPushout_algEquiv (faceRefinementMap ℂ (leOfHom f)).toRingHom (E × Fin 3)
      (incLinearSubstEquiv (G.incSymTransition (leOfHom f))))

/-- **The relative gluing datum of `Spec_X Sym(K_G^∨)`** over the locally directed face cover of
`X_G = (ℙ¹_ℂ)^V`. -/
noncomputable def incSymGluingData : (vertexFaceCover ℂ V).RelativeGluingData where
  functor := G.incSymFaceFunctor
  natTrans := G.incSymBaseProj
  equifibered := G.incSymBaseProj_equifibered

/-- **The model `Spec_X Sym(K_G^∨)`**: the scheme glued from the spectra of the model rings. -/
noncomputable abbrev incSymScheme : Scheme := G.incSymGluingData.glued

/-- **The bundle projection** `Spec_X Sym(K_G^∨) ⟶ X_G`. -/
noncomputable def incSymProjection : G.incSymScheme ⟶ vertexScheme ℂ V :=
  G.incSymGluingData.toBase

/-- **The model is affine over `X_G`, with charts `Spec Sym`.** Over the face open of `q`, the
model is the spectrum of the model ring: the square formed by the chart, the bundle projection,
the face of `X_G` and the projection of the chart is a pullback. -/
theorem incSymChart_isPullback (q : (FaceIndex V)ᵒᵈ) :
    IsPullback (G.incSymBaseProj.app q) (colimit.ι G.incSymGluingData.functor q)
      ((vertexFaceCover ℂ V).f q) G.incSymProjection :=
  G.incSymGluingData.isPullback_natTrans_ι_toBase q

/-- The inverse image of the face open of `q` under the bundle projection is the chart `q` of the
model. -/
theorem incSymProjection_preimage_face (q : V → Fin 3) :
    G.incSymProjection ⁻¹ᵁ univFaceOpen ℂ V q =
      (colimit.ι G.incSymGluingData.functor (OrderDual.toDual ⟨q⟩)).opensRange := by
  have h := G.incSymGluingData.toBase_preimage_eq_opensRange_ι (OrderDual.toDual ⟨q⟩)
  calc G.incSymProjection ⁻¹ᵁ univFaceOpen ℂ V q =
        G.incSymProjection ⁻¹ᵁ (vertexFaceι ℂ V q).opensRange := by
          rw [vertexFaceι_opensRange ℂ V q]
    _ = _ := h

/-- **The bundle projection is an affine morphism.** -/
instance incSymProjection_isAffineHom : IsAffineHom G.incSymProjection := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨q, y, hy⟩ := (vertexFaceCover ℂ V).exists_eq x
  have hX : IsAffine ((vertexFaceCover ℂ V).X q) := by
    change IsAffine (Spec _)
    infer_instance
  have hY : IsAffine (G.incSymGluingData.functor.obj q) := by
    change IsAffine (Spec _)
    infer_instance
  refine ⟨((vertexFaceCover ℂ V).f q).opensRange, ⟨y, hy⟩, isAffineOpen_opensRange _, ?_⟩
  have h := G.incSymGluingData.toBase_preimage_eq_opensRange_ι q
  change IsAffineOpen (G.incSymGluingData.toBase ⁻¹ᵁ ((vertexFaceCover ℂ V).f q).opensRange)
  rw [h]
  exact isAffineOpen_opensRange _

/-- **Functions of the model over a face of `X_G`.** The functions on the inverse image of the
face open of `q` are the model ring `Sym(K_G^∨)` of the face: the pushforward algebra of the
bundle projection is `Sym(K_G^∨)` on every face. -/
noncomputable def incSymFaceSectionsIso (q : V → Fin 3) :
    Γ(G.incSymScheme, G.incSymProjection ⁻¹ᵁ univFaceOpen ℂ V q) ≅
      CommRingCat.of (IncSymFaceRing (E := E) q) :=
  affineOpenSectionsIsoAt _ (colimit.ι G.incSymGluingData.functor (OrderDual.toDual ⟨q⟩)) _
    (G.incSymProjection_preimage_face q).symm

/-- **The pushforward algebra is glued by `Sym(g^∨)`.** Under the identifications
`incSymFaceSectionsIso` of the functions over the faces of `X_G` with the model rings, the
restriction of functions from the face `q` to a face `r` refining it is the restriction map
`incSymRestrict h` of the model. -/
theorem incSymFaceSectionsIso_restrict {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incSymScheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono G.incSymProjection
        (vertexBinaryFaceOpen_refinement ℂ V h))).op ≫ (G.incSymFaceSectionsIso r).hom =
      (G.incSymFaceSectionsIso q).hom ≫ CommRingCat.ofHom (G.incSymRestrict h) :=
  affineOpenSectionsIsoAt_naturality (CommRingCat.ofHom (G.incSymRestrict h))
    (colimit.ι G.incSymGluingData.functor (OrderDual.toDual ⟨q⟩))
    (colimit.ι G.incSymGluingData.functor (OrderDual.toDual ⟨r⟩))
    (colimit.w G.incSymGluingData.functor
      (homOfLE h : (OrderDual.toDual ⟨r⟩ : (FaceIndex V)ᵒᵈ) ⟶ OrderDual.toDual ⟨q⟩))
    _ _ (G.incSymProjection_preimage_face q).symm (G.incSymProjection_preimage_face r).symm _

/-- **The coordinate functions transform by the transposed transitions of `K_G`.** The
restriction maps of the model send the coordinate function `X_j` of the frame of `q` to the linear
form whose coefficients are the `j`-th coordinates of the transition `Φ_{σ_q} ∘ Φ_{σ_r}⁻¹` of the
trivializations of the kernel sheaf `K_G` (`incKernelSheafTransition`): the model rings are glued
by `Sym` of the dual (contragredient) of the vector transitions of `K_G`. -/
theorem incSymRestrict_X_kernelSheaf {q r : V → Fin 3} (h : FaceRefines q r) (j : E × Fin 3) :
    G.incSymRestrict h (X j) =
      ∑ i, C (G.incKernelSheafTransition (vertexFaceBaseChoice_refines V r)
        (faceRefines_trans (vertexFaceBaseChoice_refines V q) h) (Pi.single i 1) j) * X i := by
  rw [incSymRestrict_X, incKernelSheafTransition_eq]
  rfl

end Model

section Comparison

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The existing trivialization of `Z_G` over the face `q`, in the kernel frame of the face's own
chart (`incFaceKernelTriv`). -/
noncomputable def incSymFaceTriv (q : V → Fin 3) :
    G.IncFaceRing q ≃ₐ[FaceRing ℂ q] IncSymFaceRing (E := E) q :=
  G.incFaceKernelTriv (vertexFaceBaseChoice_refines V q)

/-- **The trivializations of `Z_G` respect the overlap maps of the model**: restricting a function
of `Z_G` to a smaller face and reading it in the frame of that face is the model restriction of
its reading in the frame of the larger face. -/
theorem incSymFaceTriv_refinement {q r : V → Fin 3} (h : FaceRefines q r) (x : G.IncFaceRing q) :
    G.incSymFaceTriv r (G.incFaceRefinement h x) = G.incSymRestrict h (G.incSymFaceTriv q x) := by
  have h1 := AlgHom.congr_fun
    (G.incFaceKernelTriv_refinement (vertexFaceBaseChoice_refines V q) h) x
  have h2 := AlgHom.congr_fun (G.incFaceKernelTriv_transition
    (faceRefines_trans (vertexFaceBaseChoice_refines V q) h) (vertexFaceBaseChoice_refines V r))
    (G.incFaceKernelTriv (faceRefines_trans (vertexFaceBaseChoice_refines V q) h)
      (G.incFaceRefinement h x))
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at h2
  change G.incFaceKernelTriv (vertexFaceBaseChoice_refines V r) (G.incFaceRefinement h x) = _
  rw [h2]
  change incLinearSubst (G.incSymTransition h).toLinearMap
      (G.incFaceKernelTriv (faceRefines_trans (vertexFaceBaseChoice_refines V q) h)
        (G.incFaceRefinement h x)) = _
  rw [show G.incFaceKernelTriv (faceRefines_trans (vertexFaceBaseChoice_refines V q) h)
      (G.incFaceRefinement h x) = _ from h1]
  rfl

/-- The inverse trivializations intertwine the model restrictions with the restrictions of
`Z_G`. -/
theorem incSymFaceTriv_symm_restrict {q r : V → Fin 3} (h : FaceRefines q r)
    (y : IncSymFaceRing (E := E) q) :
    G.incFaceRefinement h ((G.incSymFaceTriv q).symm y) =
      (G.incSymFaceTriv r).symm (G.incSymRestrict h y) := by
  rw [AlgEquiv.eq_symm_apply, incSymFaceTriv_refinement, AlgEquiv.apply_symm_apply]

/-- The chart isomorphism of `Z_G` with the model on the face `q`: the spectrum of the face
trivialization `incSymFaceTriv q`. -/
noncomputable def incSymComparisonApp (q : V → Fin 3) :
    G.incidenceAffineFace q ≅ Spec (CommRingCat.of (IncSymFaceRing (E := E) q)) :=
  Scheme.Spec.mapIso (G.incSymFaceTriv q).symm.toRingEquiv.toCommRingCatIso.op

/-- The chart isomorphism is the spectrum of the inverse face trivialization. -/
theorem incSymComparisonApp_hom (q : V → Fin 3) :
    (G.incSymComparisonApp q).hom =
      Spec.map (CommRingCat.ofHom (G.incSymFaceTriv q).symm.toRingEquiv.toRingHom) :=
  rfl

/-- The inverse chart isomorphism is the spectrum of the face trivialization. -/
theorem incSymComparisonApp_inv (q : V → Fin 3) :
    (G.incSymComparisonApp q).inv =
      Spec.map (CommRingCat.ofHom (G.incSymFaceTriv q).toRingEquiv.toRingHom) :=
  rfl

/-- **The chart isomorphisms respect the overlap maps**: the restriction maps of `Z_G` and of the
model correspond under the chart isomorphisms. -/
@[reassoc] theorem incSymComparisonApp_naturality {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceFaceMap h ≫ (G.incSymComparisonApp q).hom =
      (G.incSymComparisonApp r).hom ≫ Spec.map (CommRingCat.ofHom (G.incSymRestrict h)) := by
  rw [incSymComparisonApp_hom, incSymComparisonApp_hom, incidenceFaceMap, ← Spec.map_comp,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro y
  exact G.incSymFaceTriv_symm_restrict h y

/-- The inverse chart isomorphisms respect the overlap maps. -/
@[reassoc] theorem incSymComparisonApp_inv_naturality {q r : V → Fin 3} (h : FaceRefines q r) :
    Spec.map (CommRingCat.ofHom (G.incSymRestrict h)) ≫ (G.incSymComparisonApp q).inv =
      (G.incSymComparisonApp r).inv ≫ G.incidenceFaceMap h := by
  rw [Iso.comp_inv_eq, Category.assoc, incSymComparisonApp_naturality, Iso.inv_hom_id_assoc]

/-- The faces of `Z_G` mapped to the model through the chart isomorphisms. -/
noncomputable def incSymCoconeOfIncidence : Cocone G.incidenceFaceDiagram where
  pt := G.incSymScheme
  ι.app q := (G.incSymComparisonApp q.ofDual.coord).hom ≫
    colimit.ι G.incSymGluingData.functor q
  ι.naturality {i j} f := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (G.incSymComparisonApp_naturality_assoc (leOfHom f) _).trans
      (congrArg (fun k => (G.incSymComparisonApp i.ofDual.coord).hom ≫ k)
        (colimit.w G.incSymGluingData.functor f))

/-- The faces of the model mapped to `Z_G` through the inverse chart isomorphisms. -/
noncomputable def incidenceCoconeOfIncSym : Cocone G.incSymGluingData.functor where
  pt := G.incidenceGluedScheme
  ι.app q := (G.incSymComparisonApp q.ofDual.coord).inv ≫ G.incidenceFaceι q.ofDual.coord
  ι.naturality {i j} f := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (G.incSymComparisonApp_inv_naturality_assoc (leOfHom f) _).trans
      (congrArg (fun k => (G.incSymComparisonApp (OrderDual.ofDual i).coord).inv ≫ k)
        (G.incidenceFaceι_naturality (leOfHom f)))

/-- **`Z_G ≅ Spec_X Sym(K_G^∨)`** for the glued incidence scheme: the chart isomorphisms of `Z_G`
with the model glue, since they respect the overlap maps. -/
noncomputable def incSymGluedIso : G.incidenceGluedScheme ≅ G.incSymScheme where
  hom := colimit.desc G.incidenceFaceDiagram G.incSymCoconeOfIncidence
  inv := colimit.desc G.incSymGluingData.functor G.incidenceCoconeOfIncSym
  hom_inv_id := by
    apply colimit.hom_ext
    intro q
    refine (colimit.ι_desc_assoc _ _ _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    change ((G.incSymComparisonApp q.ofDual.coord).hom ≫
      colimit.ι G.incSymGluingData.functor q) ≫ _ = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => (G.incSymComparisonApp q.ofDual.coord).hom ≫ k)
      (colimit.ι_desc G.incidenceCoconeOfIncSym q)).trans ?_
    exact Iso.hom_inv_id_assoc _ _
  inv_hom_id := by
    apply colimit.hom_ext
    intro q
    refine (colimit.ι_desc_assoc _ _ _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    change ((G.incSymComparisonApp q.ofDual.coord).inv ≫
      colimit.ι G.incidenceFaceDiagram q) ≫ _ = _
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => (G.incSymComparisonApp q.ofDual.coord).inv ≫ k)
      (colimit.ι_desc G.incSymCoconeOfIncidence q)).trans ?_
    exact Iso.inv_hom_id_assoc _ _

/-- **`Z_G ≅ Spec_X Sym(K_G^∨)`** for the independent projective zero scheme. -/
noncomputable def incSymZeroIso : G.incidenceProjectiveZeroScheme ≅ G.incSymScheme :=
  G.incidenceProjectiveZeroIso.symm ≪≫ G.incSymGluedIso

/-- On every face, the comparison is the spectrum of the face trivialization of `Z_G`. -/
@[reassoc] theorem incidenceFaceι_incSymGluedIso (q : V → Fin 3) :
    G.incidenceFaceι q ≫ G.incSymGluedIso.hom =
      (G.incSymComparisonApp q).hom ≫
        colimit.ι G.incSymGluingData.functor (OrderDual.toDual ⟨q⟩) :=
  colimit.ι_desc G.incSymCoconeOfIncidence (OrderDual.toDual ⟨q⟩)

/-! ### The projection to `X_G` -/

/-- The base coefficients of a face of `Z_G` are compatible with restriction. -/
theorem incFaceRefinement_algebraMap {q r : V → Fin 3} (h : FaceRefines q r) (a : FaceRing ℂ q) :
    G.incFaceRefinement h (algebraMap (FaceRing ℂ q) (G.IncFaceRing q) a) =
      algebraMap (FaceRing ℂ r) (G.IncFaceRing r) (faceRefinementMap ℂ h a) :=
  G.incFaceRefinement_C h a

/-- The projection of the face `q` of `Z_G` to `X_G`: the inclusion of base coefficients
`FaceRing ℂ q → IncFaceRing q` followed by the face chart of `X_G`. -/
noncomputable def incidenceFaceProjection (q : V → Fin 3) :
    G.incidenceAffineFace q ⟶ vertexScheme ℂ V :=
  Spec.map (CommRingCat.ofHom (algebraMap (FaceRing ℂ q) (G.IncFaceRing q))) ≫ vertexFaceι ℂ V q

/-- The face projections are compatible with restriction. -/
@[reassoc] theorem incidenceFaceMap_projection {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceFaceMap h ≫ G.incidenceFaceProjection q = G.incidenceFaceProjection r := by
  rw [incidenceFaceProjection, incidenceFaceProjection, incidenceFaceMap,
    ← vertexFaceι_refinement ℂ V h, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact G.incFaceRefinement_algebraMap h a

/-- The projections of the faces of `Z_G` to the faces of `X_G`, through the inclusion of base
coefficients `FaceRing ℂ q → IncFaceRing q`. -/
noncomputable def incidenceProjectionCocone : Cocone G.incidenceFaceDiagram where
  pt := vertexScheme ℂ V
  ι.app q := G.incidenceFaceProjection q.ofDual.coord
  ι.naturality {i j} f := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact G.incidenceFaceMap_projection (leOfHom f)

/-- **The vector-bundle projection of `Z_G`** `Z_G ⟶ X_G`, glued from the inclusions of base
coefficients of the faces of `Z_G`. -/
noncomputable def incidenceGluedProjection : G.incidenceGluedScheme ⟶ vertexScheme ℂ V :=
  colimit.desc G.incidenceFaceDiagram G.incidenceProjectionCocone

/-- The vector-bundle projection of the independent projective zero scheme. -/
noncomputable def incidenceProjectiveZeroProjection :
    G.incidenceProjectiveZeroScheme ⟶ vertexScheme ℂ V :=
  G.incidenceProjectiveZeroIso.inv ≫ G.incidenceGluedProjection

/-- **The comparison is an isomorphism over `X_G`.** -/
@[reassoc] theorem incSymGluedIso_projection :
    G.incSymGluedIso.hom ≫ G.incSymProjection = G.incidenceGluedProjection := by
  apply colimit.hom_ext
  intro q
  rw [← Category.assoc]
  change (G.incidenceFaceι q.ofDual.coord ≫ G.incSymGluedIso.hom) ≫ _ = _
  rw [incidenceFaceι_incSymGluedIso, Category.assoc]
  change _ ≫ colimit.ι G.incSymGluingData.functor q ≫ G.incSymGluingData.toBase = _
  rw [Scheme.Cover.RelativeGluingData.ι_toBase]
  refine Eq.trans ?_ (colimit.ι_desc G.incidenceProjectionCocone q).symm
  change Spec.map (CommRingCat.ofHom (G.incSymFaceTriv q.ofDual.coord).symm.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (C : FaceRing ℂ q.ofDual.coord →+*
        IncSymFaceRing (E := E) q.ofDual.coord)) ≫ vertexFaceι ℂ V q.ofDual.coord =
    G.incidenceFaceProjection q.ofDual.coord
  rw [incidenceFaceProjection, ← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (G.incSymFaceTriv q.ofDual.coord).symm.commutes a

/-- **The projection of `Z_G` on its original charts.** On the chart `A_σ/(f_e)` of the projective
zero scheme, with `A_σ = S_G[t_V]`, the projection to `X_G` is the spectrum of the inclusion of
the vertex coordinates `ℂ[t_V] → A_σ/(f_e)` followed by the chart `σ` of `X_G`: it forgets the
coefficients. -/
theorem incidenceProjectiveZeroChartToScheme_projection (σ : V → Bool) :
    G.incidenceProjectiveZeroChartToScheme σ ≫ G.incidenceProjectiveZeroProjection =
      Spec.map (CommRingCat.ofHom (R := MvPolynomial V ℂ)
        (S := G.IncidenceProjectiveZeroChartRing σ)
        (G.incidenceProjectiveZeroChartBase σ).toRingHom) ≫
        vertexChartι ℂ V (vertexBooleanPivot V σ) := by
  have hext : ((G.incidenceProjectiveZeroChartEquiv σ).symm.toAlgHom.restrictScalars ℂ).comp
      ((IsScalarTower.toAlgHom ℂ (FaceRing ℂ (chartFace σ)) (G.IncFaceRing (chartFace σ))).comp
        (chartFaceRingEquiv (R := ℂ) σ).symm.toAlgHom) =
      G.incidenceProjectiveZeroChartBase σ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [incidenceProjectiveZeroChartBase, aeval_X]
    change (G.incidenceProjectiveZeroChartEquiv σ).symm (algebraMap (FaceRing ℂ (chartFace σ))
      (G.IncFaceRing (chartFace σ)) ((chartFaceRingEquiv (R := ℂ) σ).symm (X v))) = _
    rw [show (chartFaceRingEquiv (R := ℂ) σ).symm (X v) = faceVariable ℂ (chartFace σ) v by
      rw [AlgEquiv.symm_apply_eq, chartFaceRingEquiv_variable], AlgEquiv.symm_apply_eq,
      incidenceProjectiveZeroChartEquiv_mk]
    change _ = Ideal.Quotient.mk _ (G.incidenceChartAmbientPolynomialEquiv σ (X v))
    rw [incidenceChartAmbientPolynomialEquiv_X]
    rfl
  have h := G.incidenceProjectiveZeroChartIso_hom_toScheme σ
  have h1 : G.incidenceProjectiveZeroChartToScheme σ =
      (G.incidenceProjectiveZeroChartIso σ).inv ≫ G.incidenceFaceι (chartFace σ) ≫
        G.incidenceProjectiveZeroIso.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  have h2 : G.incidenceFaceι (chartFace σ) ≫ G.incidenceGluedProjection =
      G.incidenceFaceProjection (chartFace σ) :=
    colimit.ι_desc G.incidenceProjectionCocone (OrderDual.toDual ⟨chartFace σ⟩)
  have h3 : (G.incidenceProjectiveZeroChartIso σ).inv ≫ G.incidenceFaceProjection (chartFace σ) =
      Spec.map (CommRingCat.ofHom (R := MvPolynomial V ℂ)
        (S := G.IncidenceProjectiveZeroChartRing σ)
        (G.incidenceProjectiveZeroChartBase σ).toRingHom) ≫
        vertexChartι ℂ V (vertexBooleanPivot V σ) := by
    have hinv : (G.incidenceProjectiveZeroChartIso σ).inv =
        Spec.map (CommRingCat.ofHom (R := G.IncFaceRing (chartFace σ))
          (S := G.IncidenceProjectiveZeroChartRing σ)
          (G.incidenceProjectiveZeroChartEquiv σ).symm.toRingEquiv.toRingHom) :=
      rfl
    rw [hinv, incidenceFaceProjection, ← vertexFaceι_chart, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hext
  calc G.incidenceProjectiveZeroChartToScheme σ ≫ G.incidenceProjectiveZeroProjection =
        (G.incidenceProjectiveZeroChartIso σ).inv ≫ G.incidenceFaceι (chartFace σ) ≫
          G.incidenceGluedProjection := by
          rw [h1, incidenceProjectiveZeroProjection, Category.assoc, Category.assoc,
            Iso.hom_inv_id_assoc]
    _ = _ := by rw [h2]; exact h3

/-- The comparison of the projective zero scheme with the model is an isomorphism over `X_G`. -/
theorem incSymZeroIso_projection :
    G.incSymZeroIso.hom ≫ G.incSymProjection = G.incidenceProjectiveZeroProjection := by
  rw [incSymZeroIso, Iso.trans_hom, Category.assoc, incSymGluedIso_projection]
  rfl

/-! ### Zero sections -/

/-- Constant coefficients are compatible with the restriction maps of the model: the linear
substitutions fix the zero section. -/
theorem constantCoeff_incSymRestrict {q r : V → Fin 3} (h : FaceRefines q r)
    (p : IncSymFaceRing (E := E) q) :
    constantCoeff (G.incSymRestrict h p) = faceRefinementMap ℂ h (constantCoeff p) := by
  have hc : (constantCoeff : IncSymFaceRing (E := E) r →+* FaceRing ℂ r).comp
      (G.incSymRestrict h) = (faceRefinementMap ℂ h).toRingHom.comp constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [incSymRestrict_C]
    · intro j
      simp [incSymRestrict_X]
  exact RingHom.congr_fun hc p

/-- The zero section of the model on the face `q`: the spectrum of the constant coefficient,
followed by the chart of the model. -/
noncomputable def incSymFaceZero (q : (vertexFaceCover ℂ V).I₀) :
    (vertexFaceCover ℂ V).X q ⟶ G.incSymScheme :=
  Spec.map (CommRingCat.ofHom (constantCoeff : IncSymFaceRing (E := E) q.ofDual.coord →+*
    FaceRing ℂ q.ofDual.coord)) ≫ colimit.ι G.incSymGluingData.functor q

/-- The zero sections of the faces of the model are compatible with the transition maps of the
face cover of `X_G`. -/
theorem incSymFaceZero_trans {i j : (vertexFaceCover ℂ V).I₀} (hij : i ⟶ j) :
    (vertexFaceCover ℂ V).trans hij ≫ G.incSymFaceZero j = G.incSymFaceZero i := by
    change Spec.map (CommRingCat.ofHom (faceRefinementMap ℂ (leOfHom hij)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (constantCoeff : IncSymFaceRing (E := E) j.ofDual.coord →+*
          FaceRing ℂ j.ofDual.coord)) ≫ colimit.ι G.incSymGluingData.functor j =
      Spec.map (CommRingCat.ofHom (constantCoeff : IncSymFaceRing (E := E) i.ofDual.coord →+*
          FaceRing ℂ i.ofDual.coord)) ≫ colimit.ι G.incSymGluingData.functor i
    rw [← colimit.w G.incSymGluingData.functor hij]
    change _ = Spec.map (CommRingCat.ofHom (constantCoeff :
          IncSymFaceRing (E := E) i.ofDual.coord →+*
          FaceRing ℂ i.ofDual.coord)) ≫
        Spec.map (CommRingCat.ofHom (G.incSymRestrict (leOfHom hij))) ≫
          colimit.ι G.incSymGluingData.functor j
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact (G.constantCoeff_incSymRestrict (leOfHom hij) p).symm

/-- **The zero section of the model** `X_G ⟶ Spec_X Sym(K_G^∨)`, glued on the face cover of `X_G`
from the zero sections `t ↦ 0` of the faces. -/
noncomputable def incSymZeroSection : vertexScheme ℂ V ⟶ G.incSymScheme :=
  (vertexFaceCover ℂ V).glueMorphismsOfLocallyDirected G.incSymFaceZero G.incSymFaceZero_trans

/-- The zero section of the model on every face of `X_G`. -/
@[reassoc] theorem vertexFaceCover_incSymZeroSection (q : (vertexFaceCover ℂ V).I₀) :
    (vertexFaceCover ℂ V).f q ≫ G.incSymZeroSection = G.incSymFaceZero q :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (vertexFaceCover ℂ V) G.incSymFaceZero
    G.incSymFaceZero_trans q

/-- **The zero section is a section of the bundle projection.** -/
theorem incSymZeroSection_projection :
    G.incSymZeroSection ≫ G.incSymProjection = 𝟙 (vertexScheme ℂ V) := by
  apply (vertexFaceCover ℂ V).hom_ext
  intro q
  rw [vertexFaceCover_incSymZeroSection_assoc, Category.comp_id, incSymFaceZero, Category.assoc]
  change _ ≫ colimit.ι G.incSymGluingData.functor q ≫ G.incSymGluingData.toBase = _
  rw [Scheme.Cover.RelativeGluingData.ι_toBase]
  change Spec.map (CommRingCat.ofHom (constantCoeff : IncSymFaceRing (E := E) q.ofDual.coord →+*
      FaceRing ℂ q.ofDual.coord)) ≫ Spec.map (CommRingCat.ofHom
        (C : FaceRing ℂ q.ofDual.coord →+* IncSymFaceRing (E := E) q.ofDual.coord)) ≫
      (vertexFaceCover ℂ V).f q = (vertexFaceCover ℂ V).f q
  rw [← Spec.map_comp_assoc]
  have hc : CommRingCat.ofHom (C : FaceRing ℂ q.ofDual.coord →+*
      IncSymFaceRing (E := E) q.ofDual.coord) ≫ CommRingCat.ofHom constantCoeff = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact constantCoeff_C _ a
  rw [hc, Spec.map_id, Category.id_comp]

/-- The constant coefficient vanishes on the edge equations: `c = 0` lies on `Z_G`. -/
theorem constantCoeff_incFaceIdeal (q : V → Fin 3) {p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)}
    (hp : p ∈ G.incFaceIdeal q) : constantCoeff p = 0 := by
  have h : G.incFaceIdeal q ≤ RingHom.ker (constantCoeff :
      MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q) →+* FaceRing ℂ q) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨e, rfl⟩
    simp [incFaceEquation]
  exact h hp

/-- The zero section of the face `q` of `Z_G`: all coefficients `c_{e,α,β}` set to zero. -/
noncomputable def incFaceZeroHom (q : V → Fin 3) : G.IncFaceRing q →+* FaceRing ℂ q :=
  Ideal.Quotient.lift _ constantCoeff fun _ hp => G.constantCoeff_incFaceIdeal q hp

/-- The zero section of a face of `Z_G` on representatives. -/
@[simp] theorem incFaceZeroHom_mk (q : V → Fin 3)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :
    G.incFaceZeroHom q (Ideal.Quotient.mk _ p) = constantCoeff p :=
  rfl

/-- The zero sections of the faces of `Z_G` are compatible with restriction. -/
theorem incFaceZeroHom_refinement {q r : V → Fin 3} (h : FaceRefines q r) (x : G.IncFaceRing q) :
    G.incFaceZeroHom r (G.incFaceRefinement h x) =
      faceRefinementMap ℂ h (G.incFaceZeroHom q x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [incFaceRefinement_mk, incFaceZeroHom_mk, incFaceZeroHom_mk, facePolynomialRefinement,
    MvPolynomial.mapAlgHom_apply, MvPolynomial.constantCoeff_map]
  rfl

/-- The zero section of `Z_G` on the face `q` of `X_G`. -/
noncomputable def incidenceFaceZero (q : (vertexFaceCover ℂ V).I₀) :
    (vertexFaceCover ℂ V).X q ⟶ G.incidenceGluedScheme :=
  Spec.map (CommRingCat.ofHom (G.incFaceZeroHom q.ofDual.coord)) ≫
    G.incidenceFaceι q.ofDual.coord

/-- The zero sections of the faces of `Z_G` are compatible with the transition maps of the face
cover of `X_G`. -/
theorem incidenceFaceZero_trans {i j : (vertexFaceCover ℂ V).I₀} (hij : i ⟶ j) :
    (vertexFaceCover ℂ V).trans hij ≫ G.incidenceFaceZero j = G.incidenceFaceZero i := by
    change Spec.map (CommRingCat.ofHom (faceRefinementMap ℂ (leOfHom hij)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (G.incFaceZeroHom j.ofDual.coord)) ≫
          G.incidenceFaceι j.ofDual.coord =
      Spec.map (CommRingCat.ofHom (G.incFaceZeroHom i.ofDual.coord)) ≫
        G.incidenceFaceι i.ofDual.coord
    rw [← G.incidenceFaceι_naturality (q := (OrderDual.ofDual j).coord)
      (r := (OrderDual.ofDual i).coord) (leOfHom hij), incidenceFaceMap, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (G.incFaceZeroHom_refinement (leOfHom hij) x).symm

/-- **The zero section of `Z_G`** `X_G ⟶ Z_G`, `c = 0`, glued on the face cover of `X_G`. -/
noncomputable def incidenceGluedZeroSection : vertexScheme ℂ V ⟶ G.incidenceGluedScheme :=
  (vertexFaceCover ℂ V).glueMorphismsOfLocallyDirected G.incidenceFaceZero
    G.incidenceFaceZero_trans

/-- The zero section of `Z_G` on every face of `X_G`. -/
@[reassoc] theorem vertexFaceCover_incidenceGluedZeroSection (q : (vertexFaceCover ℂ V).I₀) :
    (vertexFaceCover ℂ V).f q ≫ G.incidenceGluedZeroSection = G.incidenceFaceZero q :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (vertexFaceCover ℂ V) G.incidenceFaceZero
    G.incidenceFaceZero_trans q

/-- The face trivializations of `Z_G` send the zero section to the zero section. -/
theorem constantCoeff_incSymFaceTriv (q : V → Fin 3) (x : G.IncFaceRing q) :
    constantCoeff (G.incSymFaceTriv q x) = G.incFaceZeroHom q x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
    change constantCoeff (G.incFaceKernelTriv (vertexFaceBaseChoice_refines V q)
      (Ideal.Quotient.mk (G.incFaceIdeal q) (C a))) = _
    rw [incFaceKernelTriv_mk_C, incFaceZeroHom_mk, constantCoeff_C, constantCoeff_C]
  | add p p' hp hp' => rw [map_add, map_add, map_add, map_add, hp, hp']
  | mul_X p c hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    have hX : constantCoeff (G.incSymFaceTriv q
        (Ideal.Quotient.mk (G.incFaceIdeal q) (X c))) = 0 := by
      change constantCoeff (G.incFaceKernelTriv (vertexFaceBaseChoice_refines V q)
        (Ideal.Quotient.mk (G.incFaceIdeal q) (X c))) = 0
      rw [incFaceKernelTriv_mk_X, incKernelRingVal, incChartKernelExtend_generic]
      simp
    rw [hX, incFaceZeroHom_mk, incFaceZeroHom_mk, constantCoeff_X]

/-- **The comparison preserves the zero sections.** -/
theorem incidenceGluedZeroSection_incSymGluedIso :
    G.incidenceGluedZeroSection ≫ G.incSymGluedIso.hom = G.incSymZeroSection := by
  apply (vertexFaceCover ℂ V).hom_ext
  intro q
  rw [vertexFaceCover_incidenceGluedZeroSection_assoc, vertexFaceCover_incSymZeroSection,
    incidenceFaceZero, Category.assoc, incidenceFaceι_incSymGluedIso, incSymFaceZero,
    incSymComparisonApp_hom, ← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro y
  change G.incFaceZeroHom q.ofDual.coord ((G.incSymFaceTriv q.ofDual.coord).symm y) =
    constantCoeff y
  rw [← constantCoeff_incSymFaceTriv, AlgEquiv.apply_symm_apply]

/-- The zero section of the glued incidence scheme is a section of its projection to `X_G`. -/
theorem incidenceGluedZeroSection_projection :
    G.incidenceGluedZeroSection ≫ G.incidenceGluedProjection = 𝟙 (vertexScheme ℂ V) := by
  rw [← incSymGluedIso_projection, ← Category.assoc, incidenceGluedZeroSection_incSymGluedIso,
    incSymZeroSection_projection]

/-- The zero section of the independent projective zero scheme: the zero section of the glued
incidence scheme transported along the existing comparison. -/
noncomputable def incidenceProjectiveZeroZeroSection :
    vertexScheme ℂ V ⟶ G.incidenceProjectiveZeroScheme :=
  G.incidenceGluedZeroSection ≫ G.incidenceProjectiveZeroIso.hom

/-- **The comparison of the projective zero scheme with the model preserves the zero
sections.** -/
theorem incidenceProjectiveZeroZeroSection_incSymZeroIso :
    G.incidenceProjectiveZeroZeroSection ≫ G.incSymZeroIso.hom = G.incSymZeroSection := by
  rw [incidenceProjectiveZeroZeroSection, incSymZeroIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, incidenceGluedZeroSection_incSymGluedIso]

/-- The zero section of `Z_G` is a section of its projection to `X_G`. -/
theorem incidenceProjectiveZeroZeroSection_projection :
    G.incidenceProjectiveZeroZeroSection ≫ G.incidenceProjectiveZeroProjection =
      𝟙 (vertexScheme ℂ V) := by
  rw [← incSymZeroIso_projection, ← Category.assoc,
    incidenceProjectiveZeroZeroSection_incSymZeroIso, incSymZeroSection_projection]

/-! ### Coefficient functions -/

/-- **The coefficient functions on a face of the model.** The coefficient `c_{e,α,β}` is the linear
form on `K_G` given by the inclusion `K_G ⊆ O^{4m}` followed by the `c`-th coordinate, read in the
kernel frame of the face's chart: the kernel extension of the generic fibre coordinates. -/
noncomputable def incSymFaceCoefficientHom (q : V → Fin 3) :
    IncCoeffRing E →ₐ[ℂ] IncSymFaceRing (E := E) q :=
  aeval fun c => G.incKernelRingVal (vertexFaceBaseChoice V q)
    (incOverlapPoint (vertexFaceBaseChoice_refines V q)) c

/-- The coefficient functions of the model are the coefficient variables of `Z_G` read in the
face trivializations. -/
theorem incSymFaceCoefficientHom_eq (q : V → Fin 3) (p : IncCoeffRing E) :
    G.incSymFaceCoefficientHom q p = G.incSymFaceTriv q (G.incidenceFaceCoefficientHom q p) := by
  have h : G.incSymFaceCoefficientHom q =
      ((G.incSymFaceTriv q).toAlgHom.restrictScalars ℂ).comp (G.incidenceFaceCoefficientHom q) := by
    apply MvPolynomial.algHom_ext
    intro c
    rw [AlgHom.comp_apply, incidenceFaceCoefficientHom_X, incSymFaceCoefficientHom, aeval_X]
    exact (G.incFaceKernelTriv_mk_X (vertexFaceBaseChoice_refines V q) c).symm
  exact AlgHom.congr_fun h p

/-- The coefficient functions of the model are compatible with the restriction maps. -/
theorem incSymRestrict_coefficient {q r : V → Fin 3} (h : FaceRefines q r) (p : IncCoeffRing E) :
    G.incSymRestrict h (G.incSymFaceCoefficientHom q p) = G.incSymFaceCoefficientHom r p := by
  rw [incSymFaceCoefficientHom_eq, incSymFaceCoefficientHom_eq, ← incSymFaceTriv_refinement]
  congr 1
  exact AlgHom.congr_fun (G.incidenceFaceCoefficientHom_refinement h) p

/-- The coefficient functions on the faces of the model. -/
noncomputable def incSymCoefficientCocone : Cocone G.incSymGluingData.functor where
  pt := Spec (CommRingCat.of (IncCoeffRing E))
  ι.app q := Spec.map (CommRingCat.ofHom (G.incSymFaceCoefficientHom q.ofDual.coord).toRingHom)
  ι.naturality {i j} f := by
    refine Eq.trans ?_ (Category.comp_id _).symm
    change Spec.map (CommRingCat.ofHom (G.incSymRestrict (leOfHom f))) ≫
        Spec.map (CommRingCat.ofHom (G.incSymFaceCoefficientHom j.ofDual.coord).toRingHom) =
      Spec.map (CommRingCat.ofHom (G.incSymFaceCoefficientHom i.ofDual.coord).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact G.incSymRestrict_coefficient (leOfHom f) p

/-- **The coefficient functions of the model** `Spec_X Sym(K_G^∨) ⟶ Spec S_G`. -/
noncomputable def incSymCoefficient : G.incSymScheme ⟶ Spec (CommRingCat.of (IncCoeffRing E)) :=
  colimit.desc G.incSymGluingData.functor G.incSymCoefficientCocone

/-- On a face, the coefficient functions of the model pull back to the coefficient variables of
`Z_G` along the chart isomorphism. -/
theorem incSymComparisonApp_coefficient (q : V → Fin 3) :
    (G.incSymComparisonApp q).hom ≫
        Spec.map (CommRingCat.ofHom (G.incSymFaceCoefficientHom q).toRingHom) =
      Spec.map (CommRingCat.ofHom (G.incidenceFaceCoefficientHom q).toRingHom) := by
  rw [incSymComparisonApp_hom, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change (G.incSymFaceTriv q).symm (G.incSymFaceCoefficientHom q p) =
    G.incidenceFaceCoefficientHom q p
  rw [incSymFaceCoefficientHom_eq, AlgEquiv.symm_apply_apply]

/-- **The comparison preserves the coefficient functions.** -/
theorem incSymGluedIso_coefficient :
    G.incSymGluedIso.hom ≫ G.incSymCoefficient = G.incidenceCoefficientMorphism := by
  apply colimit.hom_ext
  intro q
  have h1 := G.incidenceFaceι_incSymGluedIso_assoc q.ofDual.coord G.incSymCoefficient
  have h2 : colimit.ι G.incSymGluingData.functor q ≫ G.incSymCoefficient =
      Spec.map (CommRingCat.ofHom (G.incSymFaceCoefficientHom q.ofDual.coord).toRingHom) :=
    colimit.ι_desc G.incSymCoefficientCocone q
  have h3 := G.incidenceFaceι_coefficient q.ofDual.coord
  refine h1.trans (Eq.trans ?_ h3.symm)
  refine (congrArg (fun k => (G.incSymComparisonApp q.ofDual.coord).hom ≫ k) h2).trans ?_
  exact G.incSymComparisonApp_coefficient q.ofDual.coord

/-- The comparison of the projective zero scheme with the model preserves the coefficient
functions: on the model they are `incSymCoefficient`, on `Z_G ⊆ (ℙ¹)^V × Spec S_G` they are the
second projection. -/
theorem incSymZeroIso_coefficient :
    G.incSymZeroIso.hom ≫ G.incSymCoefficient = G.incidenceProjectiveZeroToBase := by
  rw [incSymZeroIso, Iso.trans_hom, Category.assoc, incSymGluedIso_coefficient, Iso.symm_hom,
    ← G.incidenceProjectiveZeroIso_hom_toBase, Iso.inv_hom_id_assoc]
  rfl

end Comparison

end BPFixedPoints.Multigraph
