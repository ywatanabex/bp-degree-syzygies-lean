import BPFixedPoints.Incidence.IncidenceKernelSheafEvaluation

/-! # The universal section of the edge bundle over the coefficient ring

This file starts the sheaf-level universal Koszul complex of the paper (eq.
`alg:universal-koszul`, `K_G^{-q} = ∧^q F_G^∨ ⊗ S_G(-q)`, `d = ι_{s^univ}`) on
`X_G × B_G = vertexScheme S_G V`, with `S_G = IncCoeffRing E`. Everything except the last
definition works over an arbitrary commutative base ring `R`.

* **Charts and faces over `R`.** `univChartOpen R V σ` and `univFaceOpen R V q` are the standard
  chart opens and Čech face opens of `(ℙ¹)^V` over `R`; the charts cover
  (`univChartOpen_iSup_top`, `univChartOpen_coversTop`), chart overlaps lie in face opens
  (`univChartOpen_inf_le_faceJoin`), and the face open of a chart face is the chart open
  (`univFaceOpen_chartFace`).
* **Sections of twists in face frames.** `IsTwistFaceFamily R b g` says that the family of
  face-ring elements `g q` is compatible with all face refinements through the transition units
  of `O(b)`. For such a family and `c = a + b`, `twistMul hc hg : O(a) ⟶ O(c)` is the morphism of
  sheaves of modules glued (by `moduleHomGlue`) from multiplication by the chart functions of `g`.
  It acts by multiplication by the chart function in every chart frame (`twistMul_coefficient`)
  and by multiplication by `g r` in the frame of every face `r` (`twistMul_faceCoefficient`,
  `twistMul_faceSections`).
* **Edge sections.** For coefficients `κ : IncCoeffIdx E → R`, `edgeFaceSection κ e` is the
  section `Σ_{α,β} κ_{e,α,β} X_{fst e,α} X_{snd e,β}` of `O(d_e)` in face frames
  (`edgeFaceSection_isTwistFaceFamily`, loops included), `edgeSectionMul κ e` is multiplication by
  it, and `edgeUniversalSection κ : O ⟶ F_G` is the section of the edge bundle with these
  components.
* **The universal section.** `incUniversalSection` is `edgeUniversalSection` over `S_G` with the
  coefficient variables `c_{e,α,β}`: the paper's `s^univ`.

The Koszul complex built from these multiplications is in `IncidenceUniversalKoszulComplex.lean`.
Not proved here: any statement about the zero scheme of the universal section.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

/-! ### Chart opens and face opens over an arbitrary base ring -/

section Opens

variable (R : Type) [CommRing R] (V : Type) [DecidableEq V] [Fintype V]

/-- The open of the standard chart `σ` of `(ℙ¹)^V` over the base ring `R`. -/
noncomputable abbrev univChartOpen (σ : V → Bool) : (vertexScheme R V).Opens :=
  vertexChartOpen R V (vertexBooleanPivot V σ)

/-- The open of the Čech face `q` of `(ℙ¹)^V` over `R`: the rectangular intersection of the
coordinate opens. -/
noncomputable abbrev univFaceOpen (q : V → Fin 3) : (vertexScheme R V).Opens :=
  SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q

/-- The standard charts `σ : V → Bool` cover `(ℙ¹)^V`. -/
theorem univChartOpen_iSup_top : (⊤ : (vertexScheme R V).Opens) ≤ ⨆ σ, univChartOpen R V σ := by
  intro x hx
  obtain ⟨τ, hτ⟩ := TopologicalSpace.Opens.mem_iSup.mp (vertexChartOpen_iSup_top R V hx)
  have h : vertexBooleanPivot V (fun v => decide (τ v = 1)) = τ := by
    have hb : ∀ i : Fin 2, (if decide (i = 1) = true then (1 : Fin 2) else 0) = i := by decide
    funext v
    exact hb (τ v)
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨fun v => decide (τ v = 1), by rw [univChartOpen, h]; exact hτ⟩

/-- The chart opens cover the terminal object of the site of `(ℙ¹)^V`. -/
theorem univChartOpen_coversTop :
    (Opens.grothendieckTopology (vertexScheme R V)).CoversTop (univChartOpen R V) := by
  intro W x hx
  obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (univChartOpen_iSup_top R V (show x ∈ (⊤ : (vertexScheme R V).Opens) from trivial))
  exact ⟨W ⊓ univChartOpen R V σ, homOfLE inf_le_left, ⟨σ, ⟨homOfLE inf_le_right⟩⟩, hx, hσ⟩

/-- The overlap of two charts lies in the face open of the join of their chart faces. -/
theorem univChartOpen_inf_le_faceJoin (σ τ : V → Bool) :
    univChartOpen R V σ ⊓ univChartOpen R V τ ≤
      univFaceOpen R V (faceJoin (chartFace σ) (chartFace τ)) := by
  refine le_iInf fun v => ?_
  have hσ : univChartOpen R V σ ≤ vertexCoordinateOpen R V v (vertexBooleanPivot V σ v) := by
    rw [univChartOpen, vertexChartOpen_eq_coordinateOpen]
    exact iInf_le _ v
  have hτ : univChartOpen R V τ ≤ vertexCoordinateOpen R V v (vertexBooleanPivot V τ v) := by
    rw [univChartOpen, vertexChartOpen_eq_coordinateOpen]
    exact iInf_le _ v
  cases hs : σ v <;> cases ht : τ v
  · have h0 : vertexBooleanPivot V σ v = 0 := by simp [vertexBooleanPivot, hs]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 0 := by simp [faceJoin, chartFace, hs, ht]
    rw [h0] at hσ
    rw [hj]
    exact inf_le_left.trans hσ
  · have h0 : vertexBooleanPivot V σ v = 0 := by simp [vertexBooleanPivot, hs]
    have h1 : vertexBooleanPivot V τ v = 1 := by simp [vertexBooleanPivot, ht]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 2 := by simp [faceJoin, chartFace, hs, ht]
    rw [h0] at hσ
    rw [h1] at hτ
    rw [hj]
    exact le_inf (inf_le_left.trans hσ) (inf_le_right.trans hτ)
  · have h1 : vertexBooleanPivot V σ v = 1 := by simp [vertexBooleanPivot, hs]
    have h0 : vertexBooleanPivot V τ v = 0 := by simp [vertexBooleanPivot, ht]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 2 := by simp [faceJoin, chartFace, hs, ht]
    rw [h1] at hσ
    rw [h0] at hτ
    rw [hj]
    exact le_inf (inf_le_right.trans hτ) (inf_le_left.trans hσ)
  · have h1 : vertexBooleanPivot V σ v = 1 := by simp [vertexBooleanPivot, hs]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 1 := by simp [faceJoin, chartFace, hs, ht]
    rw [h1] at hσ
    rw [hj]
    exact inf_le_left.trans hσ

/-- Each chart open lies in the face open of its chart face. -/
theorem univChartOpen_le_chartFace (σ : V → Bool) :
    univChartOpen R V σ ≤ univFaceOpen R V (chartFace σ) := by
  have h := univChartOpen_inf_le_faceJoin R V σ σ
  have hj : faceJoin (chartFace σ) (chartFace σ) = chartFace σ := by
    funext v
    simp [faceJoin]
  rw [inf_idem, hj] at h
  exact h

/-- A face refined by chart `σ` lies in the chart open of `σ`. -/
theorem univFaceOpen_le_chart {σ : V → Bool} {r : V → Fin 3} (hσ : FaceRefines (chartFace σ) r) :
    univFaceOpen R V r ≤ univChartOpen R V σ :=
  vertexBinaryFaceOpen_le_chart R V σ r hσ

/-- A face lies in the chart open of its own chart `vertexFaceBaseChoice V r`. -/
theorem univFaceOpen_le_baseChart (r : V → Fin 3) :
    univFaceOpen R V r ≤ univChartOpen R V (vertexFaceBaseChoice V r) :=
  univFaceOpen_le_chart R V (vertexFaceBaseChoice_refines V r)

/-- The face open of a chart face is the chart open. -/
theorem univFaceOpen_chartFace (σ : V → Bool) :
    univFaceOpen R V (chartFace σ) = univChartOpen R V σ :=
  le_antisymm (univFaceOpen_le_chart R V (faceRefines_refl _)) (univChartOpen_le_chartFace R V σ)

end Opens

/-! ### Multiplication by a section of a multi-twist given in face frames -/

section TwistMul

variable {R : Type} [CommRing R] {V : Type} [DecidableEq V] [Fintype V]

/-- Restriction of functions along two inclusions of opens is restriction along the composite. -/
theorem univPresheaf_restrict_restrict {W U U' : (vertexScheme R V).Opens} (i : W ⟶ U)
    (j : U ⟶ U') (k : W ⟶ U') (x : Γ(vertexScheme R V, U')) :
    (vertexScheme R V).presheaf.map i.op ((vertexScheme R V).presheaf.map j.op x) =
      (vertexScheme R V).presheaf.map k.op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Chart coefficients depend only on the chart, not on the term naming it. -/
theorem univTwistChartCoefficient_congr (a : V → ℤ) {σ₁ σ₂ : V → Fin 2} (h : σ₁ = σ₂)
    (W : (vertexScheme R V).Opens) (h₁ : W ≤ vertexChartOpen R V σ₁)
    (h₂ : W ≤ vertexChartOpen R V σ₂) (y : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V a σ₁ W h₁ y =
      vertexTwistSheafChartCoefficient R V a σ₂ W h₂ y := by
  subst h
  rfl

/-- Pair transition coefficients restrict to pair transition coefficients. -/
theorem univPairTransition_restrict (a : V → ℤ) (σ τ : V → Fin 2)
    {W W' : (vertexScheme R V).Opens} (h : W' ≤ W) (hW : W ≤ vertexChartPairOpen R V σ τ) :
    vertexTwistSheafPairTransitionCoefficient R V a σ τ W' (h.trans hW) =
      (vertexScheme R V).presheaf.map (homOfLE h).op
        (vertexTwistSheafPairTransitionCoefficient R V a σ τ W hW) := by
  rw [vertexTwistSheafPairTransitionCoefficient, vertexTwistSheafPairTransitionCoefficient,
    moduleOverMultiplicationCoefficient_geometric, moduleOverMultiplicationCoefficient_geometric]
  exact (univPresheaf_restrict_restrict _ _ _ _).symm

/-- The pair transition coefficient of a sum of twists is the product of the coefficients. -/
theorem univPairTransition_add {a b c : V → ℤ} (hc : c = a + b) (σ τ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ) :
    vertexTwistSheafPairTransitionCoefficient R V c σ τ W hW =
      vertexTwistSheafPairTransitionCoefficient R V a σ τ W hW *
        vertexTwistSheafPairTransitionCoefficient R V b σ τ W hW := by
  subst hc
  rw [vertexTwistSheafPairTransitionCoefficient, vertexTwistSheafPairTransitionCoefficient,
    vertexTwistSheafPairTransitionCoefficient, moduleOverMultiplicationCoefficient_geometric,
    moduleOverMultiplicationCoefficient_geometric, moduleOverMultiplicationCoefficient_geometric,
    vertexTwistSheafPairUnit_add, Units.val_mul, map_mul, map_mul]

/-- Pair transition coefficients are units. -/
theorem univPairTransition_isUnit (a : V → ℤ) (σ τ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartPairOpen R V σ τ) :
    IsUnit (vertexTwistSheafPairTransitionCoefficient R V a σ τ W hW) := by
  rw [vertexTwistSheafPairTransitionCoefficient, moduleOverMultiplicationCoefficient_geometric]
  exact ((Units.isUnit _).map _).map _

variable (R) in
/-- **Sections of a multi-twist in face frames.** A family `g` of elements `g q` of the face
rings is a section of the multi-twist `O(b)`, read in the frames of the faces' own charts, when it
is compatible with every face refinement `q → r`: the restriction of `g q` is the transition unit
of `O(b)` times `g r`. -/
def IsTwistFaceFamily (b : V → ℤ) (g : ∀ q : V → Fin 3, FaceRing R q) : Prop :=
  ∀ ⦃q r : V → Fin 3⦄ (h : FaceRefines q r),
    faceRefinementMap R h (g q) = (multiTwistTransition R h b : FaceRing R r) * g r

/-- The function on the face open of `q` whose face coordinates are `g q`. -/
noncomputable def twistFaceFunction (g : ∀ q : V → Fin 3, FaceRing R q) (q : V → Fin 3) :
    Γ(vertexScheme R V, univFaceOpen R V q) :=
  (vertexFaceSectionsEquiv R V q).symm (g q)

/-- The function on the chart open of `σ` with face coordinates `g (chartFace σ)`: the chart
coefficient of the section `g`. -/
noncomputable def twistChartFunction (g : ∀ q : V → Fin 3, FaceRing R q) (σ : V → Bool) :
    Γ(vertexScheme R V, univChartOpen R V σ) :=
  (vertexScheme R V).presheaf.map (homOfLE (univChartOpen_le_chartFace R V σ)).op
    (twistFaceFunction g (chartFace σ))

/-- **The chart function on a face.** On the face open of a face `r` refined by the chart `σ`,
the chart function of `σ` is the pair transition coefficient of `O(b)` from the frame of `σ` to
the frame of the face's own chart, times the face function of `r`. -/
theorem twistChartFunction_face {b : V → ℤ} {g : ∀ q : V → Fin 3, FaceRing R q}
    (hg : IsTwistFaceFamily R b g) {σ : V → Bool} {r : V → Fin 3}
    (hσ : FaceRefines (chartFace σ) r) :
    (vertexScheme R V).presheaf.map (homOfLE (univFaceOpen_le_chart R V hσ)).op
        (twistChartFunction g σ) =
      vertexTwistSheafPairTransitionCoefficient R V b
          (vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)))
          (vertexBooleanPivot V (vertexFaceBaseChoice V r)) (univFaceOpen R V r)
          (vertexFaceRefinement_le_pair R V hσ) *
        twistFaceFunction g r := by
  apply (vertexFaceSectionsEquiv R V r).injective
  rw [twistChartFunction,
    univPresheaf_restrict_restrict _ _ (homOfLE (vertexBinaryFaceOpen_refinement R V hσ)),
    vertexFaceSections_restrict R V hσ, twistFaceFunction, RingEquiv.apply_symm_apply, map_mul,
    vertexFaceRefinement_pair_unit, twistFaceFunction, RingEquiv.apply_symm_apply]
  exact hg hσ

/-- The local multiplication on the chart `σ`: the chart frame of `O(a)`, multiplication by the
chart function of `g`, and the inverse chart frame of `O(c)`. -/
noncomputable def twistMulLocal (a c : V → ℤ) (g : ∀ q : V → Fin 3, FaceRing R q)
    (σ : V → Bool) :
    (vertexTwistSheaf R V a).over (univChartOpen R V σ) ⟶
      (vertexTwistSheaf R V c).over (univChartOpen R V σ) :=
  (vertexTwistOverChartIso R V a (vertexBooleanPivot V σ)).hom ≫
    moduleOverMultiplication (vertexScheme R V) (univChartOpen R V σ)
      ((univChartOpen R V σ).topIso.inv (twistChartFunction g σ)) ≫
    (vertexTwistOverChartIso R V c (vertexBooleanPivot V σ)).inv

/-- **The local multiplication in the chart frame.** -/
theorem twistMulLocal_coefficient (a c : V → ℤ) (g : ∀ q : V → Fin 3, FaceRing R q)
    (σ : V → Bool) (W : (vertexScheme R V).Opens) (hW : W ≤ univChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V c (vertexBooleanPivot V σ) W hW
        (((twistMulLocal a c g σ).val.app (op (Over.mk (homOfLE hW)))).hom x) =
      vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V σ) W hW x *
        (vertexScheme R V).presheaf.map (homOfLE hW).op (twistChartFunction g σ) := by
  let Fa := vertexTwistOverChartIso R V a (vertexBooleanPivot V σ)
  let Fc := vertexTwistOverChartIso R V c (vertexBooleanPivot V σ)
  let m := moduleOverMultiplication (vertexScheme R V) (univChartOpen R V σ)
      ((univChartOpen R V σ).topIso.inv (twistChartFunction g σ))
  let S : (Over (univChartOpen R V σ))ᵒᵖ := op (Over.mk (homOfLE hW))
  have h := congrArg (fun φ => (φ.val.app S).hom ((m.val.app S).hom ((Fa.hom.val.app S).hom x)))
    Fc.inv_hom_id
  change (Fc.hom.val.app S).hom ((Fc.inv.val.app S).hom
    ((m.val.app S).hom ((Fa.hom.val.app S).hom x))) = _
  refine h.trans ?_
  change (show Γ(vertexScheme R V, W) from (m.val.app S).hom ((Fa.hom.val.app S).hom x)) = _
  rw [moduleOverMultiplication_app, moduleOverMultiplicationCoefficient_geometric,
    Iso.inv_hom_id_apply]
  rfl

/-- **The local multiplication in a face frame.** Let `r` be a face refined by the chart `σ`. On
every subopen `W` of the face open of `r`, the local multiplication of `σ`, read in the frame of
the face's own chart, is multiplication by the face function of `r`: it does not depend on `σ`. -/
theorem twistMulLocal_faceCoefficient {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) {σ : V → Bool}
    {r : V → Fin 3} (hσ : FaceRefines (chartFace σ) r) (W : (vertexScheme R V).Opens)
    (hW : W ≤ univFaceOpen R V r) (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V c (vertexBooleanPivot V (vertexFaceBaseChoice V r)) W
        (hW.trans (univFaceOpen_le_baseChart R V r))
        (((twistMulLocal a c g σ).val.app
          (op (Over.mk (homOfLE (hW.trans (univFaceOpen_le_chart R V hσ)))))).hom x) =
      vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V (vertexFaceBaseChoice V r)) W
          (hW.trans (univFaceOpen_le_baseChart R V r)) x *
        (vertexScheme R V).presheaf.map (homOfLE hW).op (twistFaceFunction g r) := by
  have hσσ : vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)) =
      vertexBooleanPivot V σ := congrArg _ (vertexFaceBaseChoice_chartFace σ)
  have hWp : W ≤ vertexChartPairOpen R V
      (vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)))
      (vertexBooleanPivot V (vertexFaceBaseChoice V r)) :=
    hW.trans (vertexFaceRefinement_le_pair R V hσ)
  let y := ((twistMulLocal a c g σ).val.app
    (op (Over.mk (homOfLE (hW.trans (univFaceOpen_le_chart R V hσ)))))).hom x
  let Ta := vertexTwistSheafPairTransitionCoefficient R V a _ _ W hWp
  let Tb := vertexTwistSheafPairTransitionCoefficient R V b _ _ W hWp
  have hy := vertexTwistSheafChartCoefficient_pair_transition R V c _ _ W hWp y
  have hx := vertexTwistSheafChartCoefficient_pair_transition R V a _ _ W hWp x
  rw [univTwistChartCoefficient_congr c hσσ W _ (hW.trans (univFaceOpen_le_chart R V hσ)),
    twistMulLocal_coefficient,
    univTwistChartCoefficient_congr a hσσ.symm W _ (hWp.trans inf_le_left), hx,
    univPairTransition_add hc] at hy
  have hf : (vertexScheme R V).presheaf.map
        (homOfLE (hW.trans (univFaceOpen_le_chart R V hσ))).op (twistChartFunction g σ) =
      Tb * (vertexScheme R V).presheaf.map (homOfLE hW).op (twistFaceFunction g r) := by
    rw [← univPresheaf_restrict_restrict (homOfLE hW) (homOfLE (univFaceOpen_le_chart R V hσ)),
      twistChartFunction_face hg hσ, map_mul]
    congr 1
    exact (univPairTransition_restrict b _ _ hW (vertexFaceRefinement_le_pair R V hσ)).symm
  rw [hf] at hy
  have hu : IsUnit (Ta * Tb) :=
    (univPairTransition_isUnit a _ _ W hWp).mul (univPairTransition_isUnit b _ _ W hWp)
  apply hu.mul_left_inj.mp
  change _ = _ * (vertexScheme R V).presheaf.map (homOfLE hW).op (twistFaceFunction g r) * (Ta * Tb)
  rw [← hy]
  ring

/-- The local multiplications agree on chart overlaps: both have the same coefficient in the
frame of the face `faceJoin (chartFace σ) (chartFace τ)`. -/
theorem twistMulLocal_compatible {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R V))
      (moduleHomSheaf (vertexScheme R V) (vertexTwistSheaf R V a)
        (vertexTwistSheaf R V c)).obj (univChartOpen R V)
      (fun σ => moduleOverHomSection (vertexScheme R V) _ _ (univChartOpen R V σ)
        (twistMulLocal a c g σ)) := by
  intro σ τ
  apply BPFixedPoints.PresheafOfModules.InternalHom.naturalFamilies_ext
  intro Y j x
  have hY : Y.unop ≤ univChartOpen R V σ ⊓ univChartOpen R V τ := j.unop.le
  have hYr : Y.unop ≤ univFaceOpen R V (faceJoin (chartFace σ) (chartFace τ)) :=
    hY.trans (univChartOpen_inf_le_faceJoin R V σ τ)
  change ((twistMulLocal a c g σ).val.app (op (Over.mk (homOfLE
      (hYr.trans (univFaceOpen_le_chart R V (faceRefines_join_left _ _))))))).hom x =
    ((twistMulLocal a c g τ).val.app (op (Over.mk (homOfLE
      (hYr.trans (univFaceOpen_le_chart R V (faceRefines_join_right _ _))))))).hom x
  apply (vertexTwistChartCoefficientEquiv R V c _ Y.unop
    (hYr.trans (univFaceOpen_le_baseChart R V _))).injective
  rw [vertexTwistChartCoefficientEquiv_apply, vertexTwistChartCoefficientEquiv_apply,
    twistMulLocal_faceCoefficient hc hg (faceRefines_join_left _ _) Y.unop hYr,
    twistMulLocal_faceCoefficient hc hg (faceRefines_join_right _ _) Y.unop hYr]

/-- **Multiplication by a section of a multi-twist.** For a section `g` of `O(b)` in face frames
and `c = a + b`, the morphism of sheaves of modules `O(a) ⟶ O(c)` glued from the local
multiplications by the chart functions of `g`. -/
noncomputable def twistMul {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) :
    vertexTwistSheaf R V a ⟶ vertexTwistSheaf R V c :=
  moduleHomGlue (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V c)
    (univChartOpen R V) (univChartOpen_iSup_top R V) (fun σ => twistMulLocal a c g σ)
    (twistMulLocal_compatible hc hg)

/-- The glued multiplication restricts on each chart to the local multiplication. -/
theorem twistMul_over {a b c : V → ℤ} (hc : c = a + b) {g : ∀ q : V → Fin 3, FaceRing R q}
    (hg : IsTwistFaceFamily R b g) (σ : V → Bool) :
    (SheafOfModules.overFunctor _ (univChartOpen R V σ)).map (twistMul hc hg) =
      twistMulLocal a c g σ :=
  moduleHomGlue_over (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V c)
    (univChartOpen R V) (univChartOpen_iSup_top R V) (fun σ => twistMulLocal a c g σ)
    (twistMulLocal_compatible hc hg) σ

/-- On a subopen of the chart `σ`, the glued multiplication is the local multiplication. -/
theorem twistMul_app {a b c : V → ℤ} (hc : c = a + b) {g : ∀ q : V → Fin 3, FaceRing R q}
    (hg : IsTwistFaceFamily R b g) (σ : V → Bool) (W : (vertexScheme R V).Opens)
    (hW : W ≤ univChartOpen R V σ) (x : Γ(vertexTwistSheaf R V a, W)) :
    ((twistMul hc hg).val.app (op W)).hom x =
      ((twistMulLocal a c g σ).val.app (op (Over.mk (homOfLE hW)))).hom x :=
  congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hW)))).hom x) (twistMul_over hc hg σ)

/-- **The multiplication in a chart frame.** On every subopen `W` of the chart `σ`, the chart
coefficient of the product is the chart coefficient of the factor times the chart function. -/
theorem twistMul_coefficient {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) (σ : V → Bool)
    (W : (vertexScheme R V).Opens) (hW : W ≤ univChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V c (vertexBooleanPivot V σ) W hW
        (((twistMul hc hg).val.app (op W)).hom x) =
      vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V σ) W hW x *
        (vertexScheme R V).presheaf.map (homOfLE hW).op (twistChartFunction g σ) := by
  rw [twistMul_app hc hg σ W hW]
  exact twistMulLocal_coefficient a c g σ W hW x

/-- **The multiplication in a face frame.** On every subopen `W` of the face open of `r`, the
coefficient of the product in the frame of the face's own chart is the coefficient of the factor
times the face function of `r`. -/
theorem twistMul_faceCoefficient {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) (r : V → Fin 3)
    (W : (vertexScheme R V).Opens) (hW : W ≤ univFaceOpen R V r)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V c (vertexBooleanPivot V (vertexFaceBaseChoice V r)) W
        (hW.trans (univFaceOpen_le_baseChart R V r)) (((twistMul hc hg).val.app (op W)).hom x) =
      vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V (vertexFaceBaseChoice V r)) W
          (hW.trans (univFaceOpen_le_baseChart R V r)) x *
        (vertexScheme R V).presheaf.map (homOfLE hW).op (twistFaceFunction g r) := by
  rw [twistMul_app hc hg (vertexFaceBaseChoice V r) W (hW.trans (univFaceOpen_le_baseChart R V r))]
  exact twistMulLocal_faceCoefficient hc hg (vertexFaceBaseChoice_refines V r) W hW x

/-- **The multiplication in face coordinates.** On the face open of `r`, the face coordinates of
the product are the face coordinates of the factor times `g r`. -/
theorem twistMul_faceSections {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) (r : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a, univFaceOpen R V r)) :
    vertexTwistSheafFaceSectionsEquiv R V c r (((twistMul hc hg).val.app (op _)).hom x) =
      vertexTwistSheafFaceSectionsEquiv R V a r x * g r := by
  rw [vertexTwistSheafFaceSectionsEquiv_apply, vertexTwistSheafFaceSectionsEquiv_apply,
    twistMul_faceCoefficient hc hg r _ le_rfl x, map_mul]
  congr 1
  change vertexFaceSectionsEquiv R V r ((vertexScheme R V).presheaf.map (𝟙 _).op
    (twistFaceFunction g r)) = g r
  rw [op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply, twistFaceFunction,
    RingEquiv.apply_symm_apply]

end TwistMul

/-! ### The edge sections and the universal section -/

section Edge

variable {R : Type} [CommRing R] {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E]
  [Fintype E] (G : Multigraph V E)

/-- The transition unit of the edge twist `O(d_e)` is the product of the vertex transition units
at the two endpoints of `e` (twice the same unit for a loop). -/
theorem multiTwistTransition_endCount {q r : V → Fin 3} (h : FaceRefines q r) (e : E) :
    multiTwistTransition R h (fun v => (G.endCount e v : ℤ)) =
      faceTransitionUnit R h (G.fst e) * faceTransitionUnit R h (G.snd e) := by
  have hw (w : V) : ∏ v, faceTransitionUnit R h v ^ (if w = v then (1 : ℤ) else 0) =
      faceTransitionUnit R h w := by
    rw [Finset.prod_eq_single w (fun v _ hv => by simp [Ne.symm hv])
      (fun hw => (hw (Finset.mem_univ w)).elim)]
    simp
  simp only [multiTwistTransition, endCount, Nat.cast_add, zpow_add, Finset.prod_mul_distrib,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hw]

/-- **The edge section with coefficients `κ`, in face frames.** On the face `q`, the section
`Σ_{α,β} κ_{e,α,β} X_{fst e,α} X_{snd e,β}` of the edge twist `O(d_e)` is the element
`Σ_{α,β} κ_{e,α,β} · (chart monomial of the face's own chart)` of the face ring. -/
noncomputable def edgeFaceSection (κ : IncCoeffIdx E → R) (e : E) (q : V → Fin 3) :
    FaceRing R q :=
  ∑ ab : Fin 2 × Fin 2, algebraMap R (FaceRing R q) (κ (e, ab)) *
    G.incChartMonomial (faceOrientation q) (faceVariable R q) e ab

/-- The edge sections with coefficients `κ` are sections of the edge twist `O(d_e)`. -/
theorem edgeFaceSection_isTwistFaceFamily (κ : IncCoeffIdx E → R) (e : E) :
    IsTwistFaceFamily R (fun v => (G.endCount e v : ℤ)) (G.edgeFaceSection κ e) := by
  intro q r h
  simp only [edgeFaceSection, map_sum, map_mul, AlgHom.commutes, incChartMonomial,
    faceOrientation, faceRefinement_incCoord R h]
  rw [multiTwistTransition_endCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Units.val_mul]
  ring

/-- **Multiplication by the edge section** `s_e`: the morphism `O(a) ⟶ O(c)` for `c = a + d_e`. -/
noncomputable def edgeSectionMul (κ : IncCoeffIdx E → R) (e : E) {a c : V → ℤ}
    (hc : c = a + fun v => (G.endCount e v : ℤ)) :
    vertexTwistSheaf R V a ⟶ vertexTwistSheaf R V c :=
  twistMul hc (G.edgeFaceSection_isTwistFaceFamily κ e)

/-- Multiplication by the edge section in face coordinates. -/
theorem edgeSectionMul_faceSections (κ : IncCoeffIdx E → R) (e : E) {a c : V → ℤ}
    (hc : c = a + fun v => (G.endCount e v : ℤ)) (r : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a, univFaceOpen R V r)) :
    vertexTwistSheafFaceSectionsEquiv R V c r (((G.edgeSectionMul κ e hc).val.app (op _)).hom x) =
      vertexTwistSheafFaceSectionsEquiv R V a r x * G.edgeFaceSection κ e r :=
  twistMul_faceSections hc _ r x

/-- **The universal section of the edge bundle**, with coefficients `κ`: the morphism
`O ⟶ F_G = ⨁_e L_e` from the untwisted multi-twist whose `L_e` component is multiplication by
`s_e = Σ_{α,β} κ_{e,α,β} X_{fst e,α} X_{snd e,β}`. With `R = S_G` and `κ` the coefficient
variables this is the paper's `s^univ` (`incUniversalSection`). -/
noncomputable def edgeUniversalSection (κ : IncCoeffIdx E → R) :
    (vertexTwistSheaf R V (fun _ => 0) : SheafOfModules (vertexScheme R V).ringCatSheaf) ⟶
      G.edgeBundle R :=
  biproduct.lift (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
    fun e => G.edgeSectionMul κ e (by funext v; simp)

/-- The `L_e` component of the universal section is multiplication by `s_e`. -/
theorem edgeUniversalSection_π (κ : IncCoeffIdx E → R) (e : E) :
    G.edgeUniversalSection κ ≫
        biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
          (fun e => G.edgeLineSheaf R e) e =
      G.edgeSectionMul κ e (by funext v; simp) :=
  biproduct.lift_π (C := SheafOfModules (vertexScheme R V).ringCatSheaf) _ e

end Edge

section Universal

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- **The universal section `s^univ` of `F_G` on `(ℙ¹)^V × B_G`.** Over the coefficient ring
`S_G = IncCoeffRing E`, the `L_e` component is multiplication by
`Σ_{α,β} c_{e,α,β} X_{fst e,α} X_{snd e,β}`, with `c_{e,α,β}` the coefficient variables. -/
noncomputable def incUniversalSection :
    (vertexTwistSheaf (IncCoeffRing E) V (fun _ => 0) :
      SheafOfModules (vertexScheme (IncCoeffRing E) V).ringCatSheaf) ⟶
        G.edgeBundle (IncCoeffRing E) :=
  G.edgeUniversalSection MvPolynomial.X

end Universal

end BPFixedPoints.Multigraph
