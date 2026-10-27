import BPFixedPoints.Incidence.ProjectiveLinePowers
import BPFixedPoints.Incidence.AffinePolynomialProducts
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Original affine polynomial charts in actual products of Proj lines

Mathlib's algebra-Spec functor and its product comparison identify the product
of original affine lines with the original multivariate polynomial scheme.
The chart maps are actual product morphisms over the original coefficient base.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The product morphism in the category over a base is the genuine pullback map. -/
theorem overProdMap_pullback {S : Scheme}
    {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y') :
    (prod.map f g).left ≫ (Over.prodLeftIsoPullback X' Y').hom =
      (Over.prodLeftIsoPullback X Y).hom ≫
        pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S)
          (by simpa using f.w.symm) (by simpa using g.w.symm) := by
  apply pullback.hom_ext <;> simp [Category.assoc, ← Over.comp_left]

/-- Products of actual open immersions over a fixed base remain open immersions. -/
instance overProdMap_isOpenImmersion {S : Scheme}
    {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    IsOpenImmersion ((prod.map f g).left) := by
  let m := pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S)
    (by simpa using f.w.symm) (by simpa using g.w.symm)
  have h : (prod.map f g).left ≫ (Over.prodLeftIsoPullback X' Y').hom =
      (Over.prodLeftIsoPullback X Y).hom ≫ m := overProdMap_pullback f g
  have he := congrArg (fun k => k ≫ (Over.prodLeftIsoPullback X' Y').inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  haveI : IsOpenImmersion m := by dsimp only [m]; infer_instance
  rw [he]
  infer_instance

/-- The genuine product-map image is the intersection of the two original inverse images.
This uses Mathlib's scheme-theoretic pullback image theorem. -/
theorem overProdMap_range {S : Scheme} {X Y X' Y' : Over S}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    Set.range (prod.map f g).left =
      (prod.fst : X' ⨯ Y' ⟶ X').left ⁻¹' Set.range f.left ∩
      (prod.snd : X' ⨯ Y' ⟶ Y').left ⁻¹' Set.range g.left := by
  let m := pullback.map X.hom Y.hom X'.hom Y'.hom f.left g.left (𝟙 S)
    (by simpa using f.w.symm) (by simpa using g.w.symm)
  let e := Over.prodLeftIsoPullback X Y
  let e' := Over.prodLeftIsoPullback X' Y'
  have hc : (prod.map f g).left ≫ e'.hom = e.hom ≫ m := overProdMap_pullback f g
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · refine ⟨(prod.fst : X ⨯ Y ⟶ X).left y, ?_⟩
      have h := congrArg (fun q => q.left y) (prod.map_fst f g)
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h.symm
    · refine ⟨(prod.snd : X ⨯ Y ⟶ Y).left y, ?_⟩
      have h := congrArg (fun q => q.left y) (prod.map_snd f g)
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h.symm
  · rintro ⟨hx, hy⟩
    have hp₁ := congrArg (fun q => q x) (Over.prodLeftIsoPullback_hom_fst X' Y')
    have hp₂ := congrArg (fun q => q x) (Over.prodLeftIsoPullback_hom_snd X' Y')
    simp only [Scheme.Hom.comp_apply] at hp₁ hp₂
    have hr : e'.hom x ∈ Set.range m := by
      dsimp only [m]
      rw [Scheme.Pullback.range_map]
      exact ⟨by change _ ∈ Set.range f.left; rw [hp₁]; exact hx,
        by change _ ∈ Set.range g.left; rw [hp₂]; exact hy⟩
    obtain ⟨z, hz⟩ := hr
    refine ⟨e.inv z, ?_⟩
    have hs : e.hom (e.inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have ht (q : (X' ⨯ Y').left) : e'.inv (e'.hom q) = q := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    have h := congrArg (fun q => q (e.inv z)) hc
    simp only [Scheme.Hom.comp_apply] at h
    rw [hs, hz] at h
    simpa only [ht] using congrArg e'.inv h

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

local instance algSpecPreservesSmallLimits :
    PreservesLimitsOfSize.{0,0} (AlgebraicGeometry.algSpec (CommRingCat.of R)) :=
  AlgebraicGeometry.preservesLimitsOfSize_algSpec

/-- The existing algebra equivalence identifies the one-variable affine chart over the base. -/
noncomputable def affineLineOverIso :
    SchemeTools.polynomialOverBase R PUnit ≅ polynomialOverBase R :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.uniqueAlgEquiv R PUnit)).symm.op

/-- The original one-variable polynomial chart as a morphism over the actual base. -/
noncomputable def affineLineChartOver (i : Fin 2) :
    SchemeTools.polynomialOverBase R PUnit ⟶ overBase R :=
  (affineLineOverIso R).hom ≫ chartOverBase R i

instance affineLineChartOver_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (affineLineChartOver R i).left := by
  change IsOpenImmersion ((affineLineOverIso R).hom.left ≫ chartι R i)
  infer_instance

/-- Actual products of the original affine-line objects over the coefficient scheme. -/
noncomputable def affinePowerOver : ℕ → Over (Spec (CommRingCat.of R))
  | 0 => Over.mk (𝟙 _)
  | n+1 => SchemeTools.polynomialOverBase R PUnit ⨯ affinePowerOver n

/-- Match the original zero coordinate and successor coordinates with the product factors. -/
def successorIndexEquiv (n : ℕ) : Fin (n+1) ≃ PUnit ⊕ Fin n :=
  (_root_.finSuccEquiv n).trans
    ((Equiv.optionEquivSumPUnit (Fin n)).trans (Equiv.sumComm _ _))

@[simp] theorem successorIndexEquiv_symm_inl (n : ℕ) (u : PUnit) :
    (successorIndexEquiv n).symm (Sum.inl u) = 0 := by
  cases u
  rfl

@[simp] theorem successorIndexEquiv_symm_inr (n : ℕ) (j : Fin n) :
    (successorIndexEquiv n).symm (Sum.inr j) = j.succ := by
  rfl

/-- The original coordinate relabelling before taking the actual product. -/
noncomputable def successorAffineOverIso (n : ℕ) :
    SchemeTools.polynomialOverBase R (Fin (n+1)) ≅
      SchemeTools.polynomialOverBase R (PUnit ⊕ Fin n) :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.renameEquiv R (successorIndexEquiv n))).symm.op

@[simp] theorem successorAffineOverIso_hom_left (n : ℕ) :
    (successorAffineOverIso R n).hom.left =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.renameEquiv R (successorIndexEquiv n)).symm.toRingHom) := rfl

/-- The original polynomial scheme is the actual product of its affine-line factors. -/
noncomputable def affinePowerIso : (n : ℕ) →
    SchemeTools.polynomialOverBase R (Fin n) ≅ affinePowerOver R n
  | 0 =>
      (AlgebraicGeometry.algSpec (CommRingCat.of R)).mapIso
          (CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv R (Fin 0))).symm.op ≪≫
        CartesianMonoidalCategory.preservesTerminalIso (AlgebraicGeometry.algSpec (CommRingCat.of R))
  | n+1 =>
      successorAffineOverIso R n ≪≫
        SchemeTools.polynomialSumOverIso R PUnit (Fin n) ≪≫
        prod.mapIso (Iso.refl _) (affinePowerIso n)

/-- The original product chart morphism, with the specified pivot at every vertex. -/
noncomputable def affinePowerChartOver : (n : ℕ) → (Fin n → Fin 2) →
    (affinePowerOver R n ⟶ powerOverBase R n)
  | 0, _ => 𝟙 _
  | n+1, σ => prod.map (affineLineChartOver R (σ 0))
      (affinePowerChartOver n (fun j => σ j.succ))

instance affinePowerChartOver_isOpenImmersion (n : ℕ) (σ : Fin n → Fin 2) :
    IsOpenImmersion (affinePowerChartOver R n σ).left := by
  induction n with
  | zero => change IsOpenImmersion (𝟙 (Spec (CommRingCat.of R))); infer_instance
  | succ n ih =>
    haveI := ih (fun j => σ j.succ)
    change IsOpenImmersion ((prod.map (affineLineChartOver R (σ 0))
      (affinePowerChartOver R n (fun j => σ j.succ))).left)
    infer_instance

/-- The actual product chart with its independently defined polynomial coordinate source. -/
noncomputable def powerChartOver (n : ℕ) (σ : Fin n → Fin 2) :
    SchemeTools.polynomialOverBase R (Fin n) ⟶ powerOverBase R n :=
  (affinePowerIso R n).hom ≫ affinePowerChartOver R n σ

/-- Original affine polynomial chart mapping into the actual product of Proj lines. -/
noncomputable def powerChartι (n : ℕ) (σ : Fin n → Fin 2) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) R)) ⟶ powerScheme R n :=
  (powerChartOver R n σ).left

instance powerChartι_isOpenImmersion (n : ℕ) (σ : Fin n → Fin 2) :
    IsOpenImmersion (powerChartι R n σ) := by
  change IsOpenImmersion ((affinePowerIso R n).hom.left ≫ (affinePowerChartOver R n σ).left)
  infer_instance

/-- The actual product chart preserves the original coefficient map. -/
@[reassoc] theorem powerChartι_toBase (n : ℕ) (σ : Fin n → Fin 2) :
    powerChartι R n σ ≫ powerToBase R n =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))) :=
  (powerChartOver R n σ).w

end BPFixedPoints.ProjectiveLine
