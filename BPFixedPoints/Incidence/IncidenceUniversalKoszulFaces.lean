import BPFixedPoints.Incidence.IncidenceUniversalKoszulComplex
import BPFixedPoints.Incidence.KoszulLocalModel

/-! # The universal Koszul complex on faces and charts: local exactness and augmentation

For `K_G = incUniversalKoszulComplex` over `S_G = IncCoeffRing E`, this file proves the local
part of the paper's claim that `K_G` resolves `O_{Z_G}` (eq. `alg:universal-koszul` with
Lemma `alg:incidence-vector-bundle`), on the face opens of the finite product cover of `(ℙ¹)^V`
(the chart opens and all their intersections).

* **Face sections are the face-level Koszul complex.** Exchanging coefficient variables and face
  coordinates (`facePolynomialEquiv`) sends the face section of `s^univ` to the face equation
  `incFaceEquation q e` (`facePolynomialEquiv_edgeFaceSection`). In the resulting face Koszul frame
  `incUnivFaceKoszulEquiv`, the differential of `K_G` over the face open of `q` is the graded
  Koszul differential of `incFaceEquation q` (`incUniversalKoszul_face`); in the total exterior
  module it is the differential of the existing face contraction `incFaceContractionOver q`
  (`incUniversalKoszul_face_total`), and it is the face component of the existing perturbation
  `incKoszulPerturbation` of `IncTotalModule` up to the Čech sign `(-1)^{faceDegree q}`
  (`incUniversalKoszul_face_perturbation`).
* **Exactness.** On every face open, `K_G` is exact in all positive homological degrees
  (`incUniversalKoszul_face_exact`); on every chart open in particular
  (`incUniversalKoszul_chart_exact`). The proof uses the existing explicit contraction of the
  face Koszul complex onto `IncFaceRing q` (built from the triangular coordinate change that turns
  the edge equations into coefficient variables).
* **Augmentation.** `incUniversalKoszulFaceAugmentation q` sends a section of `∧^0 F_G^∨ = O` on
  the face open to `IncFaceRing q`; it is surjective and its kernel is the image of
  `∧^1 F_G^∨ ⟶ ∧^0 F_G^∨` (`incUniversalKoszulFaceAugmentation_exact`).
* **Charts and the zero scheme.** On the chart `σ`, in the polynomial chart frame
  `incUnivChartKoszulEquiv` with values in `MvPolynomial V S_G`, the differential is the graded
  Koszul differential of the paper's chart equations `incidenceProjectiveEquation σ`
  (`incUniversalKoszul_chart`), the sequence of `incidenceProjectiveEquationList_isRegular`. The
  augmentation `incUniversalKoszulChartAugmentation σ` lands in
  `IncidenceProjectiveZeroChartRing σ`, the coordinate ring of the chart
  `incidenceProjectiveZeroChart σ` of the original zero scheme `incidenceProjectiveZeroScheme`;
  it is surjective with kernel the image of the last differential
  (`incUniversalKoszulChartAugmentation_exact`) and agrees with the face augmentation under
  `incidenceProjectiveZeroChartEquiv` (`incidenceProjectiveZeroChartEquiv_chartAugmentation`).

Exactness of `K_G` as a complex of sheaves is deduced in `IncidenceUniversalKoszulExact.lean`;
a second proof of the chart case, from the regular sequence of chart equations and the general
fact that regular sequences are Koszul-regular (Stacks 062F), is in
`IncidenceUniversalKoszulRegular.lean`. Not proved here: the augmentation as a morphism of
sheaves into the pushforward of `O_{Z_G}`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 100000

/-! ### Exchanging coefficient variables and face coordinates -/

section Exchange

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- A constant coefficient polynomial on a face monomial goes to the constant face monomial. -/
theorem facePolynomialEquiv_single_C (q : V → Fin 3) (m : FaceMonoid q) (r : ℂ) :
    facePolynomialEquiv ℂ (IncCoeffIdx E) q
        (AddMonoidAlgebra.single m (MvPolynomial.C r : IncCoeffRing E)) =
      MvPolynomial.C (AddMonoidAlgebra.single m r) := by
  change AddMonoidAlgebra.commAlgEquiv ℂ
      (AddMonoidAlgebra.single m (AddMonoidAlgebra.single 0 r)) =
    AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single m r)
  rw [AddMonoidAlgebra.commAlgEquiv_single_single]

/-- The coefficient variable `c` of the face ring over `S_G` is the coefficient variable. -/
theorem facePolynomialEquiv_algebraMap_X (q : V → Fin 3) (c : IncCoeffIdx E) :
    facePolynomialEquiv ℂ (IncCoeffIdx E) q
        (algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) (X c)) = X c := by
  change facePolynomialEquiv ℂ (IncCoeffIdx E) q (AddMonoidAlgebra.single 0 (X c)) = X c
  rw [facePolynomialEquiv_single_X, ← AddMonoidAlgebra.one_def, map_one, one_mul]

/-- A face variable over `S_G` is the constant face variable over `ℂ`. -/
theorem facePolynomialEquiv_faceVariable (q : V → Fin 3) (v : V) :
    facePolynomialEquiv ℂ (IncCoeffIdx E) q (faceVariable (IncCoeffRing E) q v) =
      MvPolynomial.C (faceVariable ℂ q v) := by
  change facePolynomialEquiv ℂ (IncCoeffIdx E) q
    (AddMonoidAlgebra.single _ (MvPolynomial.C 1 : IncCoeffRing E)) = _
  rw [facePolynomialEquiv_single_C]
  rfl

/-- **The universal edge section on a face is the face incidence equation.** Exchanging the
coefficient variables and the face coordinates sends the face section `edgeFaceSection c e q` of
the universal section to the face equation `incFaceEquation q e` of the existing face-level
Koszul complex. -/
theorem facePolynomialEquiv_edgeFaceSection (q : V → Fin 3) (e : E) :
    facePolynomialEquiv ℂ (IncCoeffIdx E) q (G.edgeFaceSection X e q) = G.incFaceEquation q e := by
  simp only [edgeFaceSection, incFaceEquation, map_sum, map_mul,
    facePolynomialEquiv_algebraMap_X, incChartMonomial, faceOrientation, map_incCoord,
    facePolynomialEquiv_faceVariable, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

end Exchange

/-! ### The universal Koszul complex on every face -/

section Faces

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The face Koszul frame of `∧^k F_G^∨` on the face open of `q` over `S_G`: the face coordinates
of the components, with coefficient variables exchanged with face coordinates, so that values lie
in the ring `MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)` of the existing face-level complex. -/
noncomputable def incUnivFaceKoszulEquiv (k : ℕ) (q : V → Fin 3) :
    Γ(G.exteriorBundle (IncCoeffRing E) k, univFaceOpen (IncCoeffRing E) V q) ≃+
      (Set.powersetCard E k → MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :=
  (G.exteriorFaceEquiv k q).trans
    (AddEquiv.piCongrRight fun _ => (facePolynomialEquiv ℂ (IncCoeffIdx E) q).toAddEquiv)

/-- The face Koszul frame exchanges coefficient variables and face coordinates componentwise. -/
theorem incUnivFaceKoszulEquiv_apply (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) k, univFaceOpen (IncCoeffRing E) V q))
    (S : Set.powersetCard E k) :
    G.incUnivFaceKoszulEquiv k q x S =
      facePolynomialEquiv ℂ (IncCoeffIdx E) q (G.exteriorFaceEquiv k q x S) := rfl

/-- **`K_G` on a face is the Koszul complex of the face incidence equations.** On the face open
of every Čech face `q` (charts and all overlaps), in the face Koszul frame, the differential of
`incUniversalKoszulComplex` is the graded Koszul differential of the face equations
`incFaceEquation q`. -/
theorem incUniversalKoszul_face (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), univFaceOpen (IncCoeffRing E) V q)) :
    G.incUnivFaceKoszulEquiv k q
        (((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x) =
      gradedKoszul (G.incFaceEquation q) k (G.incUnivFaceKoszulEquiv (k + 1) q x) := by
  have h := gradedKoszul_map (facePolynomialEquiv ℂ (IncCoeffIdx E) q).toRingEquiv.toRingHom
    (fun e => G.edgeFaceSection X e q) k (G.exteriorFaceEquiv (k + 1) q x)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
    facePolynomialEquiv_edgeFaceSection] at h
  funext T
  rw [incUnivFaceKoszulEquiv_apply, univKoszulDifferential_face]
  exact (congrFun h T).symm

/-- **Comparison with the face-level Koszul complex.** Placed in the total exterior module, the
face sections of `K_G` and their differential are the existing face-level Koszul complex
`Koszul.differential (incFaceEquation q)`, the differential of `incFaceContractionOver q`. -/
theorem incUniversalKoszul_face_total (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), univFaceOpen (IncCoeffRing E) V q)) :
    koszulEmbed k (G.incUnivFaceKoszulEquiv k q
        (((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x)) =
      (G.incFaceContractionOver q).d (koszulEmbed (k + 1) (G.incUnivFaceKoszulEquiv (k + 1) q x)) := by
  rw [incUniversalKoszul_face, G.incFaceContractionOver_d, LinearMap.restrictScalars_apply,
    koszul_differential_embed]

/-- **Comparison with the incidence total complex.** If the face-`q` part of an element `z` of the
existing total module `IncTotalModule` is the face section `x` of `K_G`, then the face-`q` part of
`incKoszulPerturbation z` is the face section `d x`, up to the Čech totalization sign
`(-1)^{faceDegree q}`. -/
theorem incUniversalKoszul_face_perturbation (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), univFaceOpen (IncCoeffRing E) V q))
    (z : IncTotalModule (V := V) (E := E))
    (hz : totalFaceEquiv ℂ (IncCoeffIdx E) E z q =
      koszulEmbed (k + 1) (G.incUnivFaceKoszulEquiv (k + 1) q x)) :
    totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulPerturbation z) q =
      (-1 : ℂ) ^ faceDegree q • koszulEmbed k (G.incUnivFaceKoszulEquiv k q
        (((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x)) := by
  rw [G.totalFaceEquiv_incKoszulPerturbation, hz, incUniversalKoszul_face,
    koszul_differential_embed]

/-- **Exactness of `K_G` on every face.** On the face open of every Čech face `q`, a section of
`∧^{k+1} F_G^∨` killed by the differential is a boundary. The proof uses the existing contraction
`incFaceContractionOver q` of the face Koszul complex onto the face incidence ring. -/
theorem incUniversalKoszul_face_exact (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), univFaceOpen (IncCoeffRing E) V q))
    (hx : ((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x = 0) :
    ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) (k + 2), univFaceOpen (IncCoeffRing E) V q),
      ((G.univKoszulDifferential (R := IncCoeffRing E) X (k + 1)).val.app (op _)).hom y = x := by
  have hy : gradedKoszul (G.incFaceEquation q) k (G.incUnivFaceKoszulEquiv (k + 1) q x) = 0 := by
    rw [← incUniversalKoszul_face, hx, map_zero]
  obtain ⟨y', hy'⟩ := gradedKoszul_exact_of_contraction (G.incFaceEquation q)
    (G.incFaceContractionOver q)
    (fun z => by rw [G.incFaceContractionOver_d, LinearMap.restrictScalars_apply])
    (fun z hz => by rw [G.incFaceContractionOver_p, hz, map_zero]) k _ hy
  refine ⟨(G.incUnivFaceKoszulEquiv (k + 2) q).symm y', ?_⟩
  apply (G.incUnivFaceKoszulEquiv (k + 1) q).injective
  rw [incUniversalKoszul_face, AddEquiv.apply_symm_apply, hy']

/-- The unique empty edge subset, as a `0`-element edge subset. -/
def powersetCardEmpty (E : Type) : Set.powersetCard E 0 :=
  ⟨∅, Finset.card_empty⟩

/-- **The augmentation of `K_G` on a face** to the face incidence ring `IncFaceRing q`, the ring
of `Z_G` over the face: the face coordinate of a section of `∧^0 F_G^∨ = O`, taken modulo the face
incidence equations. -/
noncomputable def incUniversalKoszulFaceAugmentation (q : V → Fin 3) :
    Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V q) →+
      G.IncFaceRing q :=
  (Ideal.Quotient.mk (G.incFaceIdeal q)).toAddMonoidHom.comp
    ((Pi.evalAddMonoidHom _ (powersetCardEmpty E)).comp
      (G.incUnivFaceKoszulEquiv 0 q).toAddMonoidHom)

/-- The face augmentation is the quotient class of the face coordinate of the `∅` component. -/
theorem incUniversalKoszulFaceAugmentation_apply (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V q)) :
    G.incUniversalKoszulFaceAugmentation q x =
      Ideal.Quotient.mk (G.incFaceIdeal q) (G.incUnivFaceKoszulEquiv 0 q x (powersetCardEmpty E)) :=
  rfl

/-- The face augmentation is surjective. -/
theorem incUniversalKoszulFaceAugmentation_surjective (q : V → Fin 3) :
    Function.Surjective (G.incUniversalKoszulFaceAugmentation q) := by
  intro u
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨(G.incUnivFaceKoszulEquiv 0 q).symm (fun _ => p), ?_⟩
  rw [incUniversalKoszulFaceAugmentation_apply, AddEquiv.apply_symm_apply]

/-- **`H_0` of `K_G` on a face.** The kernel of the face augmentation is exactly the image of the
differential `∧^1 F_G^∨ ⟶ ∧^0 F_G^∨` on the face open: the cokernel of the last differential of
`K_G` over the face is the ring `IncFaceRing q` of `Z_G` over the face. -/
theorem incUniversalKoszulFaceAugmentation_exact (q : V → Fin 3)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V q)) :
    G.incUniversalKoszulFaceAugmentation q x = 0 ↔
      ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) 1, univFaceOpen (IncCoeffRing E) V q),
        ((G.univKoszulDifferential (R := IncCoeffRing E) X 0).val.app (op _)).hom y = x := by
  rw [incUniversalKoszulFaceAugmentation_apply, Ideal.Quotient.eq_zero_iff_mem, incFaceIdeal,
    gradedKoszul_zero_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(G.incUnivFaceKoszulEquiv 1 q).symm y, ?_⟩
    apply (G.incUnivFaceKoszulEquiv 0 q).injective
    funext T
    have hT : T = powersetCardEmpty E :=
      Subtype.ext (Finset.card_eq_zero.mp (Set.powersetCard.card_eq T))
    subst hT
    rw [incUniversalKoszul_face, AddEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨G.incUnivFaceKoszulEquiv 1 q y, by rw [incUniversalKoszul_face]⟩

/-- The augmentation kills boundaries. -/
theorem incUniversalKoszulFaceAugmentation_d (q : V → Fin 3)
    (y : Γ(G.exteriorBundle (IncCoeffRing E) 1, univFaceOpen (IncCoeffRing E) V q)) :
    G.incUniversalKoszulFaceAugmentation q
      (((G.univKoszulDifferential (R := IncCoeffRing E) X 0).val.app (op _)).hom y) = 0 :=
  (G.incUniversalKoszulFaceAugmentation_exact q _).mpr ⟨y, rfl⟩

end Faces

/-! ### Charts: the regular sequence and the zero scheme -/

section Charts

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The chart Koszul frame of `∧^k F_G^∨` on the chart `σ` (the face open of `chartFace σ`), with
values in the polynomial chart ring `MvPolynomial V S_G` of `(ℙ¹)^V × B_G`. -/
noncomputable def incUnivChartKoszulEquiv (k : ℕ) (σ : V → Bool) :
    Γ(G.exteriorBundle (IncCoeffRing E) k, univFaceOpen (IncCoeffRing E) V (chartFace σ)) ≃+
      (Set.powersetCard E k → MvPolynomial V (IncCoeffRing E)) :=
  (G.incUnivFaceKoszulEquiv k (chartFace σ)).trans
    (AddEquiv.piCongrRight fun _ => (G.incidenceChartAmbientPolynomialEquiv σ).symm.toAddEquiv)

/-- The chart Koszul frame is the face Koszul frame in the polynomial chart coordinates. -/
theorem incUnivChartKoszulEquiv_apply (k : ℕ) (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) k, univFaceOpen (IncCoeffRing E) V (chartFace σ)))
    (S : Set.powersetCard E k) :
    G.incUnivChartKoszulEquiv k σ x S =
      (G.incidenceChartAmbientPolynomialEquiv σ).symm (G.incUnivFaceKoszulEquiv k (chartFace σ) x S) :=
  rfl

/-- **`K_G` on a chart is the Koszul complex of the chart equations.** On the chart `σ`, in the
chart Koszul frame, the differential of `K_G` is the graded Koszul differential of the paper's
dehomogenized chart equations `incidenceProjectiveEquation σ` in `MvPolynomial V S_G`, which form
a regular sequence (`incidenceProjectiveEquationList_isRegular`). -/
theorem incUniversalKoszul_chart (k : ℕ) (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1),
      univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    G.incUnivChartKoszulEquiv k σ
        (((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x) =
      gradedKoszul (G.incidenceProjectiveEquation σ) k (G.incUnivChartKoszulEquiv (k + 1) σ x) := by
  have h := gradedKoszul_map (G.incidenceChartAmbientPolynomialEquiv σ).symm.toRingEquiv.toRingHom
    (G.incFaceEquation (chartFace σ)) k (G.incUnivFaceKoszulEquiv (k + 1) (chartFace σ) x)
  funext T
  rw [incUnivChartKoszulEquiv_apply, incUniversalKoszul_face]
  exact (congrFun h T).symm

/-- **The augmentation of `K_G` on a chart to the original zero scheme.** On the chart `σ`, the
chart coordinate of a section of `∧^0 F_G^∨ = O`, taken modulo the chart equations: the value
lies in `IncidenceProjectiveZeroChartRing σ`, the coordinate ring of the chart
`incidenceProjectiveZeroChart σ` of the original zero scheme `incidenceProjectiveZeroScheme`. -/
noncomputable def incUniversalKoszulChartAugmentation (σ : V → Bool) :
    Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V (chartFace σ)) →+
      G.IncidenceProjectiveZeroChartRing σ :=
  (Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ)).toAddMonoidHom.comp
    ((Pi.evalAddMonoidHom _ (powersetCardEmpty E)).comp
      (G.incUnivChartKoszulEquiv 0 σ).toAddMonoidHom)

/-- The chart augmentation is the quotient class of the chart coordinate of the `∅`
component. -/
theorem incUniversalKoszulChartAugmentation_apply (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    G.incUniversalKoszulChartAugmentation σ x =
      Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ)
        (G.incUnivChartKoszulEquiv 0 σ x (powersetCardEmpty E)) := rfl

/-- The chart augmentation is the face augmentation followed by the identification of the face
incidence ring with the chart ring of the zero scheme. -/
theorem incidenceProjectiveZeroChartEquiv_chartAugmentation (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    G.incidenceProjectiveZeroChartEquiv σ (G.incUniversalKoszulChartAugmentation σ x) =
      G.incUniversalKoszulFaceAugmentation (chartFace σ) x := by
  rw [incUniversalKoszulChartAugmentation_apply, incidenceProjectiveZeroChartEquiv_mk,
    incUnivChartKoszulEquiv_apply]
  change Ideal.Quotient.mk _ ((G.incidenceChartAmbientPolynomialEquiv σ)
    ((G.incidenceChartAmbientPolynomialEquiv σ).symm _)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The chart augmentation is surjective. -/
theorem incUniversalKoszulChartAugmentation_surjective (σ : V → Bool) :
    Function.Surjective (G.incUniversalKoszulChartAugmentation σ) := by
  intro u
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨(G.incUnivChartKoszulEquiv 0 σ).symm (fun _ => p), ?_⟩
  rw [incUniversalKoszulChartAugmentation_apply, AddEquiv.apply_symm_apply]

/-- **`H_0` of `K_G` on a chart is the chart ring of the zero scheme.** The kernel of the chart
augmentation is exactly the image of `∧^1 F_G^∨ ⟶ ∧^0 F_G^∨` on the chart. -/
theorem incUniversalKoszulChartAugmentation_exact (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    G.incUniversalKoszulChartAugmentation σ x = 0 ↔
      ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) 1, univFaceOpen (IncCoeffRing E) V (chartFace σ)),
        ((G.univKoszulDifferential (R := IncCoeffRing E) X 0).val.app (op _)).hom y = x := by
  rw [← G.incUniversalKoszulFaceAugmentation_exact,
    ← incidenceProjectiveZeroChartEquiv_chartAugmentation]
  exact (map_eq_zero_iff _ (AlgEquiv.injective _)).symm

/-- **Exactness of `K_G` on a chart** (in positive homological degrees), stated on the chart
open itself. -/
theorem incUniversalKoszul_chart_exact (k : ℕ) (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1), univChartOpen (IncCoeffRing E) V σ))
    (hx : ((G.univKoszulDifferential (R := IncCoeffRing E) X k).val.app (op _)).hom x = 0) :
    ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) (k + 2), univChartOpen (IncCoeffRing E) V σ),
      ((G.univKoszulDifferential (R := IncCoeffRing E) X (k + 1)).val.app (op _)).hom y = x := by
  have h := G.incUniversalKoszul_face_exact k (chartFace σ)
  rw [univFaceOpen_chartFace] at h
  exact h x hx

end Charts

end BPFixedPoints.Multigraph
