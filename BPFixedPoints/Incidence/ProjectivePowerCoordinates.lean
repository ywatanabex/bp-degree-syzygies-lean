import BPFixedPoints.Incidence.VertexProjectiveProducts

/-! # Original coordinates of the actual projective product charts

The product comparisons preserve every original polynomial variable. In
particular, projection of a chart onto a vertex is the ordinary chart map
evaluated at that vertex's original polynomial coordinate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The first affine factor receives the original zero coordinate. -/
@[reassoc] theorem affinePowerIso_hom_fst (n : ℕ) :
    ((affinePowerIso R (n+1)).hom ≫ prod.fst).left =
      Spec.map (CommRingCat.ofHom
        (rename (R := R) (fun _ : PUnit => (0 : Fin (n+1)))).toRingHom) := by
  change (((successorAffineOverIso R n).hom ≫
    (SchemeTools.polynomialSumOverIso R PUnit (Fin n)).hom ≫
      prod.map (𝟙 _) (affinePowerIso R n).hom) ≫ prod.fst).left = _
  simp only [Category.assoc, prod.map_fst, Category.comp_id]
  rw [Over.comp_left, SchemeTools.polynomialSumOverIso_hom_fst,
    successorAffineOverIso_hom_left, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro u
    simp [renameEquiv_symm]

/-- The remaining affine factors receive the original successor coordinates. -/
@[reassoc] theorem affinePowerIso_hom_snd (n : ℕ) :
    ((affinePowerIso R (n+1)).hom ≫ prod.snd).left =
      Spec.map (CommRingCat.ofHom (rename (R := R) Fin.succ).toRingHom) ≫
        (affinePowerIso R n).hom.left := by
  change (((successorAffineOverIso R n).hom ≫
    (SchemeTools.polynomialSumOverIso R PUnit (Fin n)).hom ≫
      prod.map (𝟙 _) (affinePowerIso R n).hom) ≫ prod.snd).left = _
  simp only [Category.assoc, prod.map_snd]
  have h : (((successorAffineOverIso R n).hom ≫
      (SchemeTools.polynomialSumOverIso R PUnit (Fin n)).hom ≫ prod.snd) ≫
        (affinePowerIso R n).hom).left =
      (successorAffineOverIso R n).hom.left ≫
        ((SchemeTools.polynomialSumOverIso R PUnit (Fin n)).hom ≫ prod.snd).left ≫
          (affinePowerIso R n).hom.left := by
    simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc _ _ (affinePowerIso R n).hom,
    ← Category.assoc _ _ (affinePowerIso R n).hom, h,
    SchemeTools.polynomialSumOverIso_hom_snd, successorAffineOverIso_hom_left]
  rw [← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp [renameEquiv_symm]

@[simp] theorem affineLineOverIso_hom_left :
    (affineLineOverIso R).hom.left =
      Spec.map (CommRingCat.ofHom (uniqueAlgEquiv R PUnit).symm.toRingHom) := rfl

/-- Each actual projective chart projection is evaluation at the original variable. -/
@[reassoc] theorem powerChartι_projection (n : ℕ) (σ : Fin n → Fin 2) (i : Fin n) :
    powerChartι R n σ ≫ (powerProjectionOver R n i).left =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (X i : MvPolynomial (Fin n) R)).toRingHom) ≫
        chartι R (σ i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((affinePowerIso R (n+1)).hom ≫
        prod.map (affineLineChartOver R (σ 0))
          (affinePowerChartOver R n (fun j => σ j.succ)) ≫ prod.fst).left = _
      rw [prod.map_fst, ← Category.assoc, Over.comp_left, affinePowerIso_hom_fst]
      change _ ≫ ((affineLineOverIso R).hom.left ≫ chartι R (σ 0)) = _
      rw [← Category.assoc, affineLineOverIso_hom_left]
      congr 1
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro r
        simp [uniqueAlgEquiv]
      · simp [uniqueAlgEquiv]
    · change ((affinePowerIso R (n+1)).hom ≫
        prod.map (affineLineChartOver R (σ 0))
          (affinePowerChartOver R n (fun j => σ j.succ)) ≫
            (prod.snd ≫ powerProjectionOver R n j)).left = _
      rw [← Category.assoc (prod.map _ _), prod.map_snd, ← Category.assoc,
        ← Category.assoc]
      change ((affinePowerIso R (n+1)).hom ≫ prod.snd).left ≫
        (affinePowerChartOver R n (fun j => σ j.succ)).left ≫
          (powerProjectionOver R n j).left = _
      rw [affinePowerIso_hom_snd]
      simp only [Category.assoc]
      rw [show (affinePowerIso R n).hom.left ≫
          (affinePowerChartOver R n (fun j => σ j.succ)).left ≫
            (powerProjectionOver R n j).left = _ from ih (fun j => σ j.succ) j]
      rw [← Category.assoc, ← Spec.map_comp]
      congr 1
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro r
        simp
      · simp

variable (V : Type) [Fintype V]

@[simp] theorem vertexAffineIso_hom_left :
    (vertexAffineIso R V).hom.left =
      Spec.map (CommRingCat.ofHom
        (renameEquiv R (Fintype.equivFin V)).symm.toRingHom) := rfl

/-- Projection to an original vertex uses exactly its original polynomial variable. -/
@[reassoc] theorem vertexChartι_projection (σ : V → Fin 2) (v : V) :
    vertexChartι R V σ ≫ (vertexProjectionOver R V v).left =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (X v : MvPolynomial V R)).toRingHom) ≫
        chartι R (σ v) := by
  change ((vertexAffineIso R V).hom.left ≫
    powerChartι R (Fintype.card V) (fun j => σ ((Fintype.equivFin V).symm j))) ≫
      (powerProjectionOver R (Fintype.card V) (Fintype.equivFin V v)).left = _
  rw [Category.assoc, powerChartι_projection]
  simp only [Equiv.symm_apply_apply]
  rw [← Category.assoc, vertexAffineIso_hom_left, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp [renameEquiv_symm]

/-- The original-labelled projective scheme is the actual indexed product over the base. -/
theorem vertexProduct_comparison :
    Nonempty (vertexOverBase R V ≅ ∏ᶜ (fun _ : V => overBase R)) :=
  ⟨vertexPiIso R V⟩

end BPFixedPoints.ProjectiveLine
