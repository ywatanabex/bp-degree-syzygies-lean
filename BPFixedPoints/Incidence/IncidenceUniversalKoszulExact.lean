import BPFixedPoints.Incidence.IncidenceUniversalKoszulFaces

/-! # `K_G` is exact in negative degrees as a complex of sheaves

This file proves that the universal Koszul complex `K_G = incUniversalKoszulComplex` on
`(ℙ¹)^V × B_G` is exact at every homological degree `k+1 ≥ 1` (cohomological degree `-(k+1)`)
in the abelian category of sheaves of modules (`incUniversalKoszulComplex_exactAt`): the
"resolution" half of the paper's statement that `K_G` resolves `O_{Z_G}` (eq.
`alg:universal-koszul`), the cokernel of `∧^1 F_G^∨ ⟶ O` being identified chart by chart with the
chart rings of the zero scheme in `IncidenceUniversalKoszulFaces.lean`.

* **Localization.** Exactness of the graded Koszul complex in a positive degree is preserved by
  every localization (`gradedKoszul_exact_localization`).
* **Charts and their basic opens.** Over the ring of functions on a chart, the graded Koszul
  complex of the chart functions of the universal edge sections is exact in positive degrees
  (`incUnivChartKoszul_exact`, from the chart exactness of `IncidenceUniversalKoszulFaces.lean`);
  the chart opens are affine (`univChartOpen_isAffineOpen`), so on every basic open of a chart
  the sections of `K_G` are exact in positive degrees (`incUniversalKoszul_basicOpen_exact`).
* **Sheaves.** A morphism of sheaves of modules on a scheme that is surjective near every point
  is an epimorphism (`schemeModules_epi_of_locally_surjective`); since the basic opens of the
  charts form a basis, the map from `∧^{k+2} F_G^∨` to the cycles of `∧^{k+1} F_G^∨` is an
  epimorphism, which is the exactness of `K_G` at `k+1`.

Not proved here: the identification of the cokernel sheaf of `∧^1 F_G^∨ ⟶ O` with the pushforward
of `O_{Z_G}` as a sheaf (only the chart-wise identification of sections is proved).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 100000

/-! ### Exactness of the graded Koszul complex is preserved by localization -/

section Localization

variable {E : Type} [LinearOrder E] [Fintype E] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B]

/-- **Localization preserves exactness of the graded Koszul complex.** If every cycle of degree
`k+1` of the graded Koszul complex of `f` over `A` is a boundary, the same holds over every
localization of `A`, for the images of the `f_e`. -/
theorem gradedKoszul_exact_localization (M : Submonoid A) [IsLocalization M B] (f : E → A)
    (k : ℕ)
    (hA : ∀ y : Set.powersetCard E (k + 1) → A, gradedKoszul f k y = 0 →
      ∃ y', gradedKoszul f (k + 1) y' = y)
    (y : Set.powersetCard E (k + 1) → B)
    (hy : gradedKoszul (fun e => algebraMap A B (f e)) k y = 0) :
    ∃ y', gradedKoszul (fun e => algebraMap A B (f e)) (k + 1) y' = y := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M y
  choose y0 hy0 using hb
  -- `y0` has image `b • y`.
  have hy0' : (fun S => algebraMap A B (y0 S)) = (algebraMap A B (b : A)) • y := by
    funext S
    rw [hy0 S, Algebra.smul_def, Pi.smul_apply, smul_eq_mul]
  have himage : ∀ T, algebraMap A B (gradedKoszul f k y0 T) = 0 := by
    intro T
    have h := gradedKoszul_map (algebraMap A B) f k y0
    have h' := congrFun h T
    rw [← h', hy0', map_smul, hy, smul_zero, Pi.zero_apply]
  choose m hm using fun T => (IsLocalization.map_eq_zero_iff M B _).mp (himage T)
  let c : M := ∏ T, m T
  have hc : ∀ T, (c : A) * gradedKoszul f k y0 T = 0 := by
    intro T
    have hdvd : (m T : A) ∣ (c : A) := by
      change (m T : A) ∣ ((∏ T, m T : M) : A)
      rw [Submonoid.coe_finsetProd]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ T)
    obtain ⟨d, hd⟩ := hdvd
    rw [hd, mul_comm (m T : A) d, mul_assoc, hm T, mul_zero]
  have hcycle : gradedKoszul f k ((c : A) • y0) = 0 := by
    funext T
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hc T, Pi.zero_apply]
  obtain ⟨y', hy'⟩ := hA _ hcycle
  have hu : IsUnit (algebraMap A B ((c : A) * (b : A))) :=
    IsLocalization.map_units B (c * b)
  let u : B := ((hu.unit⁻¹ : Bˣ) : B)
  have hinv : u * (algebraMap A B (c : A) * algebraMap A B (b : A)) = 1 := by
    rw [← map_mul]
    exact hu.val_inv_mul
  refine ⟨u • fun S => algebraMap A B (y' S), ?_⟩
  rw [map_smul, gradedKoszul_map (algebraMap A B) f (k + 1) y', hy']
  funext S
  have hS := hy0 S
  rw [Algebra.smul_def] at hS
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hS]
  calc u * (algebraMap A B (c : A) * (algebraMap A B (b : A) * y S)) =
      (u * (algebraMap A B (c : A) * algebraMap A B (b : A))) * y S := by ring
    _ = y S := by rw [hinv, one_mul]

end Localization

/-! ### Epimorphisms of sheaves of modules on a scheme from local surjectivity -/

/-- **Local surjectivity on a scheme gives epimorphisms.** A morphism of sheaves of modules on a
scheme is an epimorphism if every section of the target is, near every point, the image of a
section of the source. -/
theorem schemeModules_epi_of_locally_surjective {X : Scheme.{0}}
    {M N : SheafOfModules X.ringCatSheaf} (φ : M ⟶ N)
    (h : ∀ (U : X.Opens) (s : N.val.obj (op U)) (x : X), x ∈ U →
      ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧
        ∃ t : M.val.obj (op W), (φ.val.app (op W)).hom t = N.val.map (homOfLE hWU).op s) :
    Epi φ := by
  have := Functor.reflectsEpimorphisms_of_faithful (SheafOfModules.toSheaf X.ringCatSheaf)
  apply (SheafOfModules.toSheaf _).epi_of_epi_map
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    ⟨fun {U} s => by
      intro x hx
      obtain ⟨W, hWU, hxW, t, ht⟩ := h U s x hx
      exact ⟨W, homOfLE hWU, ⟨t, ht⟩, hxW⟩⟩
  exact Sheaf.epi_of_isLocallySurjective _

/-! ### Exactness of `K_G` on basic opens of the charts -/

section Sheaf

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The chart opens of `(ℙ¹)^V` over any ring are affine opens. -/
theorem univChartOpen_isAffineOpen (R : Type) [CommRing R] (σ : V → Bool) :
    IsAffineOpen (univChartOpen R V σ) :=
  isAffineOpen_opensRange (vertexChartι R V (vertexBooleanPivot V σ))

/-- Restriction along the identity of an open is the identity. -/
theorem univPresheaf_map_le_rfl {R : Type} [CommRing R] (W : (vertexScheme R V).Opens)
    (z : Γ(vertexScheme R V, W)) :
    (vertexScheme R V).presheaf.map (homOfLE (le_refl W)).op z = z := by
  change (vertexScheme R V).presheaf.map (𝟙 _).op z = z
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The chart function of the universal edge section `s_e` on the chart `σ`. -/
noncomputable def incUnivChartFunction (σ : V → Bool) (e : E) :
    Γ(vertexScheme (IncCoeffRing E) V, univChartOpen (IncCoeffRing E) V σ) :=
  twistChartFunction (G.edgeFaceSection (R := IncCoeffRing E) MvPolynomial.X e) σ

/-- **Exactness of the chart Koszul complex.** Over the ring of functions on the chart `σ`, the
graded Koszul complex of the chart functions of the universal edge sections is exact in every
positive degree. -/
theorem incUnivChartKoszul_exact (σ : V → Bool) (k : ℕ)
    (y : Set.powersetCard E (k + 1) →
      Γ(vertexScheme (IncCoeffRing E) V, univChartOpen (IncCoeffRing E) V σ))
    (hy : gradedKoszul (G.incUnivChartFunction σ) k y = 0) :
    ∃ y', gradedKoszul (G.incUnivChartFunction σ) (k + 1) y' = y := by
  have hf : (fun e => (vertexScheme (IncCoeffRing E) V).presheaf.map
      (homOfLE (le_refl (univChartOpen (IncCoeffRing E) V σ))).op
        (twistChartFunction (G.edgeFaceSection (R := IncCoeffRing E) MvPolynomial.X e) σ)) =
      G.incUnivChartFunction σ := by
    funext e
    exact univPresheaf_map_le_rfl _ _
  let F := fun j => G.exteriorChartEquiv (R := IncCoeffRing E) j σ
    (univChartOpen (IncCoeffRing E) V σ) le_rfl
  let x := (F (k + 1)).symm y
  have hdx : ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op _)).hom x = 0 := by
    apply (F k).injective
    rw [map_zero]
    change G.exteriorChartEquiv k σ _ le_rfl _ = 0
    rw [univKoszulDifferential_chart, hf]
    change gradedKoszul _ k ((F (k + 1)) ((F (k + 1)).symm y)) = 0
    rw [LinearEquiv.apply_symm_apply, hy]
  obtain ⟨x', hx'⟩ := G.incUniversalKoszul_chart_exact k σ x hdx
  refine ⟨F (k + 2) x', ?_⟩
  have h := G.univKoszulDifferential_chart (R := IncCoeffRing E) MvPolynomial.X (k + 1) σ _ le_rfl x'
  rw [hf] at h
  change gradedKoszul _ (k + 1) (F (k + 2) x') = y
  rw [← h, hx']
  exact LinearEquiv.apply_symm_apply _ y

/-- **Exactness of `K_G` on the basic opens of the charts.** On every basic open of a chart (a
localization of the chart ring), a section of `∧^{k+1} F_G^∨` killed by the differential is a
boundary. -/
theorem incUniversalKoszul_basicOpen_exact (σ : V → Bool)
    (g : Γ(vertexScheme (IncCoeffRing E) V, univChartOpen (IncCoeffRing E) V σ)) (k : ℕ)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), (vertexScheme (IncCoeffRing E) V).basicOpen g))
    (hx : ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op _)).hom x = 0) :
    ∃ x' : Γ(G.exteriorBundle (IncCoeffRing E) (k + 2),
        (vertexScheme (IncCoeffRing E) V).basicOpen g),
      ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X (k + 1)).val.app
        (op _)).hom x' = x := by
  have hW : (vertexScheme (IncCoeffRing E) V).basicOpen g ≤ univChartOpen (IncCoeffRing E) V σ :=
    (vertexScheme (IncCoeffRing E) V).basicOpen_le g
  have := (univChartOpen_isAffineOpen (IncCoeffRing E) σ).isLocalization_basicOpen g
  have hf : (fun e => (vertexScheme (IncCoeffRing E) V).presheaf.map (homOfLE hW).op
      (twistChartFunction (G.edgeFaceSection (R := IncCoeffRing E) MvPolynomial.X e) σ)) =
      fun e => algebraMap _ _ (G.incUnivChartFunction σ e) := by
    funext e
    rfl
  let F := fun j => G.exteriorChartEquiv (R := IncCoeffRing E) j σ _ hW
  have hy : gradedKoszul (fun e => algebraMap _ _ (G.incUnivChartFunction σ e)) k
      (F (k + 1) x) = 0 := by
    have h := G.univKoszulDifferential_chart (R := IncCoeffRing E) MvPolynomial.X k σ _ hW x
    rw [hf, hx, map_zero] at h
    exact h.symm
  obtain ⟨y', hy'⟩ := gradedKoszul_exact_localization (Submonoid.powers g)
    (G.incUnivChartFunction σ) k (G.incUnivChartKoszul_exact σ k) _ hy
  refine ⟨(F (k + 2)).symm y', ?_⟩
  apply (F (k + 1)).injective
  change G.exteriorChartEquiv (k + 1) σ _ hW _ = _
  rw [univKoszulDifferential_chart, hf]
  change gradedKoszul _ (k + 1) ((F (k + 2)) ((F (k + 2)).symm y')) = _
  rw [LinearEquiv.apply_symm_apply, hy']


set_option maxHeartbeats 1000000 in
/-- **`K_G` is exact in negative degrees as a complex of sheaves.** The universal Koszul complex
`incUniversalKoszulComplex` is exact at every homological degree `k+1 ≥ 1` (cohomological degree
`-(k+1)`) in the abelian category of sheaves of modules on `(ℙ¹)^V × B_G`: every local cycle is
locally a boundary, on the basic opens of the charts. -/
theorem incUniversalKoszulComplex_exactAt (k : ℕ) :
    G.incUniversalKoszulComplex.ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  have h1 : G.incUniversalKoszulComplex.d (k + 2) (k + 1) =
      G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X (k + 1) :=
    G.univKoszulComplex_d _ (k + 1)
  have h0 : G.incUniversalKoszulComplex.d (k + 1) k =
      G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k :=
    G.univKoszulComplex_d _ k
  apply schemeModules_epi_of_locally_surjective
  intro U s x hx
  let S := G.incUniversalKoszulComplex.sc' (k + 2) (k + 1) k
  let z := ((kernel.ι S.g).val.app (op U)).hom s
  have hz : ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op U)).hom z = 0 := by
    have h := kernel_ι_app_comp S.g (op U) s
    change ((G.incUniversalKoszulComplex.d (k + 1) k).val.app (op U)).hom z = 0 at h
    rw [h0] at h
    exact h
  obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (univChartOpen_iSup_top (IncCoeffRing E) V (show x ∈ (⊤ : (vertexScheme (IncCoeffRing E) V).Opens) from trivial))
  obtain ⟨g, hgU, hxg⟩ :=
    (univChartOpen_isAffineOpen (IncCoeffRing E) σ).exists_basicOpen_le (V := U) ⟨x, hx⟩ hσ
  let zW : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1),
      (vertexScheme (IncCoeffRing E) V).basicOpen g) :=
    (G.exteriorBundle (IncCoeffRing E) (k + 1)).val.map (homOfLE hgU).op z
  have hzW : ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op _)).hom zW = 0 := by
    have h := PresheafOfModules.naturality_apply
      (G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val (homOfLE hgU).op z
    change ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op _)).hom zW = (G.exteriorBundle (IncCoeffRing E) k).val.map (homOfLE hgU).op
        (((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
          (op U)).hom z) at h
    rw [h, hz, map_zero]
  obtain ⟨t, ht⟩ := G.incUniversalKoszul_basicOpen_exact σ g k zW hzW
  refine ⟨_, hgU, hxg, t, ?_⟩
  apply kernel_ι_app_injective S.g
  have hl : ((kernel.ι S.g).val.app (op ((vertexScheme (IncCoeffRing E) V).basicOpen g))).hom
      (((kernel.lift S.g S.f S.zero).val.app
        (op ((vertexScheme (IncCoeffRing E) V).basicOpen g))).hom t) =
      ((S.f).val.app (op ((vertexScheme (IncCoeffRing E) V).basicOpen g))).hom t :=
    congrArg (fun φ => (φ.val.app (op ((vertexScheme (IncCoeffRing E) V).basicOpen g))).hom t)
      (kernel.lift_ι S.g S.f S.zero)
  rw [hl]
  erw [PresheafOfModules.naturality_apply]
  change ((G.incUniversalKoszulComplex.d (k + 2) (k + 1)).val.app _).hom t = zW
  rw [h1]
  exact ht

end Sheaf

end BPFixedPoints.Multigraph
