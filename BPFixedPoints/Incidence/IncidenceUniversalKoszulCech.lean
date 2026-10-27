import BPFixedPoints.Incidence.IncidenceUniversalKoszulFaces
import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalComparison
import BPFixedPoints.Incidence.ResolutionDegree
import BPFixedPoints.Incidence.ResolutionInternalGrading

/-! # The Čech–Koszul total complex of `K_G` on the face cover and the incidence total complex

The finite cover of `(ℙ¹)^V × B_G` used here is the product of the standard two-chart covers:
its members and all their intersections are the face opens `univFaceOpen (IncCoeffRing E) V q`,
`q : V → Fin 3`, with Čech degree `faceDegree q` (the cubical Čech complex of the existing
files). This file builds the Čech–Koszul total complex of `K_G = incUniversalKoszulComplex` from
actual sheaf sections on these opens and identifies it with the existing incidence total complex
`IncTotalModule`, `incTotalDifferential` of `KoszulCech.lean`.

* **The total module.** `UnivCechKoszulModule G` has, for every edge subset `S` and every face
  `q`, an actual section of the summand `O(-d_S)` of `∧^{|S|} F_G^∨` over the face open of `q`,
  with the geometric `S_G`-action.
* **The total differential.** `univCechKoszulDifferential = univCechDifferential +
  univCechKoszulPerturbation`: the Čech part is the existing cubical differential of actual
  sections (signed sheaf restrictions, `vertexTwistCubicalD`) on every summand; the Koszul part
  is the differential of `K_G` on face sections (the sheaf morphisms `s_e`), with the exterior
  sign `Koszul.sign T e` and the totalization sign `(-1)^{faceDegree q}`.
* **Comparison.** `univCechKoszulEquiv : UnivCechKoszulModule G ≃ₗ[S_G] IncTotalModule` is the
  existing signed face-coordinate comparison `vertexTwistCubicalChainEquiv` on every summand. It
  carries the Čech part to `incCechContraction.d` (`univCechKoszulEquiv_cech`), the Koszul part to
  `incKoszulPerturbation` (`univCechKoszulEquiv_koszul`), hence the total differential to
  `incTotalDifferential` (`univCechKoszulEquiv_differential`); it preserves total degree
  (`univCechKoszulEquiv_mem_piece`, for `incTotalPiece`) and internal degree
  (`univCechKoszulEquiv_mem_internalPiece`, for `incTotalInternalPiece`), and the projection
  `incKoszulContraction.p` to the local incidence rings is the face augmentation of sections up
  to the Čech sign (`incKoszulContraction_p_univ`).

Not proved here: that this Čech total complex computes the derived global sections of `K_G`
(that requires a hypercohomology theory of bounded complexes of sheaves and Čech acyclicity of
the terms on the face cover); the cohomology of the total complex is in
`IncidenceUniversalKoszulCohomology.lean`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools ResolutionTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-! ### The existing total complex, face by face -/

section Existing

/-- The existing Koszul perturbation of `IncTotalModule` at an edge subset `T`: the sum over
`e ∉ T` of the Čech-parity-signed exterior sign times the edge action on the `T ∪ {e}`
component. -/
theorem incKoszulPerturbation_apply (z : IncTotalModule (V := V) (E := E)) (T : Finset E) :
    G.incKoszulPerturbation z T = ∑ e : E, if e ∉ T then
      (contraction (IncCoeffRing E) (G.deg T)).sign
        (Koszul.sign (A := IncCoeffRing E) T e • G.incEdgeAction e (z (insert e T))) else 0 := by
  induction z using Finsupp.induction_linear with
  | zero =>
    simp
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∉ T
    · rw [ite_eq_left he, ite_eq_left he, ite_eq_left he, Finsupp.add_apply, map_add, smul_add,
        map_add]
    · rw [ite_eq_right he, ite_eq_right he, ite_eq_right he, add_zero]
  | single S w =>
    rw [G.incKoszulPerturbation_single, Finsupp.finsetSum_apply]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl fun e he => ?_
      rw [Finsupp.single_apply]
      by_cases hT : S.erase e = T
      · subst hT
        rw [ite_eq_left rfl, ite_eq_left (Finset.notMem_erase e S), Finset.insert_erase he,
          Finsupp.single_eq_same, Koszul.sign_erase_self]
      · rw [ite_eq_right hT]
        by_cases heT : e ∉ T
        · rw [ite_eq_left heT, Finsupp.single_apply, ite_eq_right, map_zero, smul_zero, map_zero]
          intro hS
          apply hT
          rw [hS, Finset.erase_insert heT]
        · rw [ite_eq_right heT]
    · intro e _ he
      by_cases heT : e ∉ T
      · rw [ite_eq_left heT, Finsupp.single_apply, ite_eq_right, map_zero, smul_zero, map_zero]
        intro hS
        exact he (hS ▸ Finset.mem_insert_self e T)
      · rw [ite_eq_right heT]

/-- On every face, the existing edge action is multiplication by the face edge section of the
universal section. -/
theorem faceEquiv_incEdgeAction (e : E) (w : IncCechModule (V := V) (E := E)) (q : V → Fin 3) :
    faceEquiv (IncCoeffRing E) (G.incEdgeAction e w) q =
      G.edgeFaceSection MvPolynomial.X e q * faceEquiv (IncCoeffRing E) w q := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, Finset.sum_apply,
    map_smul, Pi.smul_apply, faceEquiv_multiply, G.incFaceShift_monomial, edgeFaceSection,
    Finset.sum_mul, Fintype.sum_prod_type, incChartMonomial, faceOrientation]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Algebra.smul_def]
  ring

/-- The existing statewise operator `Koszul.diagonal` acts componentwise. -/
theorem koszul_diagonal_apply {A W : Type*} [CommRing A] [AddCommGroup W] [Module A W]
    (f : Finset E → Module.End A W) (z : Koszul.Space E W) (S : Finset E) :
    Koszul.diagonal f z S = f S (z S) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, map_add]
  | single T w =>
    rw [Koszul.diagonal_single]
    by_cases h : T = S
    · subst h
      simp
    · rw [Finsupp.single_apply, ite_eq_right h, Finsupp.single_apply, ite_eq_right h, map_zero]

end Existing

/-! ### The Čech–Koszul total complex of `K_G` on the face cover -/

section Total

/-- **The Čech–Koszul total module of `K_G`** on the finite product cover of `(ℙ¹)^V × B_G` by
the face opens: for every edge subset `S` and every Čech face `q`, an actual section of the
summand `O(-d_S)` of `∧^{|S|} F_G^∨` over the face open of `q`, with the geometric action of
`S_G`. -/
abbrev UnivCechKoszulModule :=
  (S : Finset E) → VertexTwistCubicalSections (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ))

/-- The Čech differential of the total module: on each summand `O(-d_S)` the existing cubical
differential `vertexTwistCubicalD` of actual sections, a signed sum of sheaf restrictions. -/
noncomputable def univCechDifferential : Module.End (IncCoeffRing E) G.UnivCechKoszulModule :=
  LinearMap.pi fun S =>
    (vertexTwistCubicalD (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ))).comp (LinearMap.proj S)

/-- The Koszul component of the total module: the sheaf morphism `s_e : O(-d_{T ∪ {e}}) ⟶ O(-d_T)`
of `K_G` on sections over the face open of `q`, linear for the geometric action of `S_G`. -/
noncomputable def univCechKoszulComponent (T : Finset E) (e : E) (he : e ∉ T) (q : V → Fin 3) :
    vertexTwistCubicalFace (IncCoeffRing E) V (fun v => -(G.deg (insert e T) v : ℤ)) q →ₗ[IncCoeffRing E]
      vertexTwistCubicalFace (IncCoeffRing E) V (fun v => -(G.deg T v : ℤ)) q :=
  schemeBaseOpenHomLinear (vertexToBase (IncCoeffRing E) V)
    (G.edgeSectionMul (R := IncCoeffRing E) MvPolynomial.X e (G.exteriorTwist_insert he)) _

/-- The Koszul part of the total differential: the differential of `K_G` on face sections, with
the totalization sign `(-1)^{faceDegree q}` of the Čech degree. At `T` and the face `q` it is
`Σ_{e ∉ T} (-1)^{faceDegree q} sign(T, e) s_e x_{T ∪ {e}, q}`. -/
noncomputable def univCechKoszulPerturbation : Module.End (IncCoeffRing E) G.UnivCechKoszulModule :=
  LinearMap.pi fun T => LinearMap.pi fun q => ∑ e : E, if he : e ∉ T then
    ((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
      ((G.univCechKoszulComponent T e he q).comp
        ((LinearMap.proj (R := IncCoeffRing E)
          (φ := fun r => vertexTwistCubicalFace (IncCoeffRing E) V
            (fun v => -(G.deg (insert e T) v : ℤ)) r) q).comp
          (LinearMap.proj (R := IncCoeffRing E)
            (φ := fun S : Finset E => VertexTwistCubicalSections (IncCoeffRing E) V
              (fun v => -(G.deg S v : ℤ))) (insert e T))))
  else 0

/-- **The total differential of the Čech–Koszul complex of `K_G`.** -/
noncomputable def univCechKoszulDifferential : Module.End (IncCoeffRing E) G.UnivCechKoszulModule :=
  G.univCechDifferential + G.univCechKoszulPerturbation

/-- The Koszul part of the total differential at the edge subset `T` and the face `q`. -/
theorem univCechKoszulPerturbation_apply (x : G.UnivCechKoszulModule) (T : Finset E)
    (q : V → Fin 3) :
    G.univCechKoszulPerturbation x T q = ∑ e : E, if he : e ∉ T then
      ((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
        G.univCechKoszulComponent T e he q (x (insert e T) q) else 0 := by
  simp only [univCechKoszulPerturbation, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e ∉ T
  · rw [dite_eq_left he, dite_eq_left he]
    rfl
  · rw [dite_eq_right he, dite_eq_right he]
    rfl

/-- **The comparison with the existing total module**: on each summand `O(-d_S)` the existing
signed face coordinates `vertexTwistCubicalChainEquiv`. It is `S_G`-linear. -/
noncomputable def univCechKoszulEquiv :
    G.UnivCechKoszulModule ≃ₗ[IncCoeffRing E] IncTotalModule (V := V) (E := E) :=
  (LinearEquiv.piCongrRight fun S =>
    vertexTwistCubicalChainEquiv (IncCoeffRing E) V (G.deg S)).trans
    (Finsupp.linearEquivFunOnFinite (IncCoeffRing E) (IncCechModule (V := V) (E := E))
      (Finset E)).symm

/-- The comparison is the signed face-coordinate comparison on every summand. -/
theorem univCechKoszulEquiv_apply (x : G.UnivCechKoszulModule) (S : Finset E) :
    G.univCechKoszulEquiv x S = vertexTwistCubicalChainEquiv (IncCoeffRing E) V (G.deg S) (x S) :=
  rfl

/-- The comparison intertwines the Čech differentials. -/
theorem univCechKoszulEquiv_cech (x : G.UnivCechKoszulModule) :
    G.univCechKoszulEquiv (G.univCechDifferential x) =
      G.incCechContraction.d (G.univCechKoszulEquiv x) := by
  ext1 S
  rw [G.incCechContraction_d, koszul_diagonal_apply, univCechKoszulEquiv_apply,
    univCechKoszulEquiv_apply]
  exact vertexTwistCubicalChainEquiv_d (IncCoeffRing E) V (G.deg S) (x S)

/-- The face coordinate of the existing cubical comparison is the face coordinate of
`IncidenceUniversalKoszulComplex.lean`. -/
theorem vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate (a : V → ℤ) (q : V → Fin 3)
    (y : vertexTwistCubicalFace (IncCoeffRing E) V a q) :
    vertexTwistSheafFaceSectionsEquiv (IncCoeffRing E) V a q y = twistFaceCoordinate a q y :=
  rfl

/-- The Koszul component multiplies face coordinates by the face edge section. -/
theorem univCechKoszulComponent_faceCoordinate (T : Finset E) (e : E) (he : e ∉ T)
    (q : V → Fin 3)
    (y : vertexTwistCubicalFace (IncCoeffRing E) V (fun v => -(G.deg (insert e T) v : ℤ)) q) :
    twistFaceCoordinate (fun v => -(G.deg T v : ℤ)) q (G.univCechKoszulComponent T e he q y) =
      twistFaceCoordinate (fun v => -(G.deg (insert e T) v : ℤ)) q y *
        G.edgeFaceSection MvPolynomial.X e q :=
  twistMul_faceCoordinate (G.exteriorTwist_insert he)
    (G.edgeFaceSection_isTwistFaceFamily MvPolynomial.X e) q y

/-- `((-1)^n)^2 = 1`. -/
theorem neg_one_pow_mul_self' {A : Type*} [CommRing A] (n : ℕ) :
    (-1 : A) ^ n * (-1 : A) ^ n = 1 := by
  rw [← mul_pow]
  simp

/-- The face coordinates of the sheaf-side Koszul part. -/
theorem faceEquiv_univCechKoszulPerturbation (x : G.UnivCechKoszulModule) (T : Finset E)
    (q : V → Fin 3) :
    faceEquiv (IncCoeffRing E) (G.univCechKoszulEquiv (G.univCechKoszulPerturbation x) T) q =
      ∑ e : E, if e ∉ T then
        algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) (Koszul.sign T e) *
          (twistFaceCoordinate (fun v => -(G.deg (insert e T) v : ℤ)) q (x (insert e T) q) *
            G.edgeFaceSection MvPolynomial.X e q) else 0 := by
  rw [univCechKoszulEquiv_apply, vertexTwistCubicalChainEquiv_face,
    vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate, univCechKoszulPerturbation_apply,
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e ∉ T
  · rw [dite_eq_left he, ite_eq_left he]
    have hc := (vertexTwistSheafFaceSectionsEquiv (IncCoeffRing E) V
      (fun v => -(G.deg T v : ℤ)) q).map_smul ((-1 : IncCoeffRing E) ^ faceDegree q *
        Koszul.sign T e) (G.univCechKoszulComponent T e he q (x (insert e T) q))
    rw [vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate,
      vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate] at hc
    rw [hc, univCechKoszulComponent_faceCoordinate]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, map_neg, map_one]
    calc _ = ((-1 : FaceRing (IncCoeffRing E) q) ^ faceDegree q *
          (-1 : FaceRing (IncCoeffRing E) q) ^ faceDegree q) *
          (algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) (Koszul.sign T e) *
            (twistFaceCoordinate (fun v => -(G.deg (insert e T) v : ℤ)) q (x (insert e T) q) *
              G.edgeFaceSection MvPolynomial.X e q)) := by ring
      _ = _ := by rw [neg_one_pow_mul_self', one_mul]
  · rw [dite_eq_right he, ite_eq_right he, map_zero, smul_zero]

/-- The face coordinates of the existing Koszul part on the image of the comparison. -/
theorem faceEquiv_incKoszulPerturbation_univ (x : G.UnivCechKoszulModule) (T : Finset E)
    (q : V → Fin 3) :
    faceEquiv (IncCoeffRing E) (G.incKoszulPerturbation (G.univCechKoszulEquiv x) T) q =
      ∑ e : E, if e ∉ T then
        algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) (Koszul.sign T e) *
          (twistFaceCoordinate (fun v => -(G.deg (insert e T) v : ℤ)) q (x (insert e T) q) *
            G.edgeFaceSection MvPolynomial.X e q) else 0 := by
  rw [incKoszulPerturbation_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e ∉ T
  · rw [ite_eq_left he, ite_eq_left he, ← parity_eq, faceEquiv_parity, map_smul, Pi.smul_apply,
      faceEquiv_incEdgeAction, univCechKoszulEquiv_apply, vertexTwistCubicalChainEquiv_face,
      vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_neg, map_one]
    calc _ = ((-1 : FaceRing (IncCoeffRing E) q) ^ faceDegree q *
          (-1 : FaceRing (IncCoeffRing E) q) ^ faceDegree q) *
          (algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) (Koszul.sign T e) *
            (twistFaceCoordinate (fun v => -(G.deg (insert e T) v : ℤ)) q (x (insert e T) q) *
              G.edgeFaceSection MvPolynomial.X e q)) := by ring
      _ = _ := by rw [neg_one_pow_mul_self', one_mul]
  · rw [ite_eq_right he, ite_eq_right he, map_zero, Pi.zero_apply]

/-- The comparison intertwines the Koszul parts, with their totalization signs. -/
theorem univCechKoszulEquiv_koszul (x : G.UnivCechKoszulModule) :
    G.univCechKoszulEquiv (G.univCechKoszulPerturbation x) =
      G.incKoszulPerturbation (G.univCechKoszulEquiv x) := by
  ext1 T
  apply (faceEquiv (IncCoeffRing E)).injective
  funext q
  rw [faceEquiv_univCechKoszulPerturbation, faceEquiv_incKoszulPerturbation_univ]

/-- **The Čech–Koszul total complex of `K_G` is the existing incidence total complex.** The
`S_G`-linear comparison `univCechKoszulEquiv` carries the total differential of sections of
`K_G` on the face cover (Čech restrictions plus the sheaf differential of `K_G` with the
totalization sign) to the existing total differential `incTotalDifferential`. -/
theorem univCechKoszulEquiv_differential (x : G.UnivCechKoszulModule) :
    G.univCechKoszulEquiv (G.univCechKoszulDifferential x) =
      G.incTotalDifferential (G.univCechKoszulEquiv x) := by
  rw [univCechKoszulDifferential, LinearMap.add_apply, map_add, univCechKoszulEquiv_cech,
    univCechKoszulEquiv_koszul, incTotalDifferential, LinearMap.add_apply]

/-- The total differential of sections of `K_G` on the face cover squares to zero. -/
theorem univCechKoszulDifferential_sq (x : G.UnivCechKoszulModule) :
    G.univCechKoszulDifferential (G.univCechKoszulDifferential x) = 0 := by
  apply G.univCechKoszulEquiv.injective
  rw [univCechKoszulEquiv_differential, univCechKoszulEquiv_differential, map_zero]
  exact LinearMap.congr_fun G.incTotalDifferential_sq _

/-! ### Degrees, internal degree and augmentation -/

/-- **Total degree on the sheaf side.** An element of the Čech–Koszul total module has total
degree `n` (homological convention: `n = |S| - (Čech degree)`, as in `incTotalPiece`) when its
`(S, q)` component vanishes unless `faceDegree q = |S| - n`. -/
def univCechKoszulPiece (n : ℤ) : Submodule (IncCoeffRing E) G.UnivCechKoszulModule where
  carrier := {x | ∀ S, VertexTwistCubicalHomogeneous (IncCoeffRing E) V _ ((S.card : ℤ) - n) (x S)}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro x y hx hy S q hq
    change x S q + y S q = 0
    rw [hx S q hq, hy S q hq, add_zero]
  smul_mem' := by
    intro c x hx S q hq
    change c • x S q = 0
    rw [hx S q hq, smul_zero]

/-- **The comparison preserves total degree.** -/
theorem univCechKoszulEquiv_mem_piece (n : ℤ) (x : G.UnivCechKoszulModule) :
    G.univCechKoszulEquiv x ∈ incTotalPiece (V := V) (E := E) n ↔ x ∈ G.univCechKoszulPiece n :=
  forall_congr' fun S => vertexTwistCubicalChainEquiv_degree (IncCoeffRing E) V (G.deg S) _ (x S)

/-- Coefficientwise conditions on the Čech module are conditions on the face coordinates. -/
theorem mem_coefficientwise_iff_faceEquiv (P : Submodule ℂ (IncCoeffRing E))
    (w : IncCechModule (V := V) (E := E)) :
    w ∈ coefficientwise P ↔
      ∀ (q : V → Fin 3) (m : FaceMonoid q), (faceEquiv (IncCoeffRing E) w q).coeff m ∈ P := by
  constructor
  · intro hw q m
    rw [faceEquiv_coeff]
    exact hw _
  · intro hw b
    obtain ⟨⟨q, m⟩, rfl⟩ := faceBasisEquiv.symm.surjective b
    have h := hw q m
    rwa [faceEquiv_coeff] at h

/-- **Internal degree on the sheaf side.** An element of the Čech–Koszul total module has internal
degree `n` when every coefficient (in `S_G`) of the face coordinates of its `(S, q)` component is
homogeneous of degree `n - |S|`: the generator of `∧^{|S|} F_G^∨ ⊗ S_G(-|S|)` has internal degree
`|S|`. -/
def IsUnivCechKoszulInternal (n : ℤ) (x : G.UnivCechKoszulModule) : Prop :=
  ∀ (S : Finset E) (q : V → Fin 3) (m : FaceMonoid q),
    (twistFaceCoordinate (fun v => -(G.deg S v : ℤ)) q (x S q)).coeff m ∈
      homogeneousCoeffPiece (σ := IncCoeffIdx E) (k := ℂ) (n - (S.card : ℤ))

/-- **The comparison preserves internal degree.** -/
theorem univCechKoszulEquiv_mem_internalPiece (n : ℤ) (x : G.UnivCechKoszulModule) :
    G.univCechKoszulEquiv x ∈ incTotalInternalPiece (V := V) (E := E) n ↔
      G.IsUnivCechKoszulInternal n x := by
  change (∀ S, G.univCechKoszulEquiv x S ∈ incCechInternalPiece (V := V) (E := E)
    (n - (S.card : ℤ))) ↔ _
  refine forall_congr' fun S => ?_
  rw [incCechInternalPiece, mem_coefficientwise_iff_faceEquiv]
  refine forall_congr' fun q => forall_congr' fun m => ?_
  rw [univCechKoszulEquiv_apply, vertexTwistCubicalChainEquiv_face,
    vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate]
  rcases Nat.even_or_odd (faceDegree q) with h | h
  · rw [h.neg_one_pow, one_smul]
  · rw [h.neg_one_pow, neg_one_smul]
    exact Submodule.neg_mem_iff _

/-- **The augmentation of the Čech–Koszul total module** at a face `q`: the face coordinate of
the `∅` component (a section of `O`), with coefficient variables exchanged and taken modulo the
face incidence equations; a value in the ring `IncFaceRing q` of `Z_G` over the face. -/
noncomputable def univCechKoszulFaceAugmentation (x : G.UnivCechKoszulModule) (q : V → Fin 3) :
    G.IncFaceRing q :=
  Ideal.Quotient.mk (G.incFaceIdeal q) (facePolynomialEquiv ℂ (IncCoeffIdx E) q
    (twistFaceCoordinate (fun v => -(G.deg ∅ v : ℤ)) q (x ∅ q)))

/-- **The comparison preserves the augmentation.** The existing projection of the total module
to the local incidence rings (`incKoszulContraction.p`) is, on the image of the comparison, the
face augmentation of sections, up to the Čech sign `(-1)^{faceDegree q}` (which is `1` in Čech
degree zero). -/
theorem incKoszulContraction_p_univ (x : G.UnivCechKoszulModule) (q : V → Fin 3) :
    G.incKoszulContraction.p (G.univCechKoszulEquiv x) q =
      (-1 : ℂ) ^ faceDegree q • G.univCechKoszulFaceAugmentation x q := by
  rw [incKoszulContraction_p, polynomialFaceEquiv_apply, univCechKoszulEquiv_apply,
    vertexTwistCubicalChainEquiv_face, vertexTwistSheafFaceSectionsEquiv_eq_twistFaceCoordinate,
    univCechKoszulFaceAugmentation]
  rcases Nat.even_or_odd (faceDegree q) with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_smul, neg_one_smul, map_neg, map_neg]

end Total

end BPFixedPoints.Multigraph
