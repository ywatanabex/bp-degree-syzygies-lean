import BPFixedPoints.Incidence.ProjectivePowerAffineCharts

/-! # The original polynomial charts cover the actual projective product

Coverage follows from Mathlib's pullback image theorem applied to each genuine
binary product. The empty product is included. The source rings are the
original polynomial rings, independently identified with the affine factors.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- Both original affine-line charts cover the actual Proj line over the base. -/
theorem affineLineChartOver_covers (x : projectiveLine R) :
    ∃ i : Fin 2, x ∈ Set.range (affineLineChartOver R i).left := by
  obtain ⟨i, y, hy⟩ := (polynomialChartCover R).exists_eq x
  have he : (affineLineOverIso R).hom.left ((affineLineOverIso R).inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]
    rfl
  refine ⟨i, (affineLineOverIso R).inv.left y, ?_⟩
  change chartι R i ((affineLineOverIso R).hom.left ((affineLineOverIso R).inv.left y)) = x
  rw [he]
  exact hy

/-- The original product chart morphisms jointly cover the actual product, for every n. -/
theorem affinePowerChartOver_covers (n : ℕ) (x : powerScheme R n) :
    ∃ σ : Fin n → Fin 2, x ∈ Set.range (affinePowerChartOver R n σ).left := by
  induction n with
  | zero => exact ⟨Fin.elim0, x, rfl⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := affineLineChartOver_covers R
      ((prod.fst : overBase R ⨯ powerOverBase R n ⟶ overBase R).left x)
    obtain ⟨σ, hσ⟩ := ih
      ((prod.snd : overBase R ⨯ powerOverBase R n ⟶ powerOverBase R n).left x)
    refine ⟨Fin.cases i σ, ?_⟩
    change x ∈ Set.range (prod.map (affineLineChartOver R i)
      (affinePowerChartOver R n σ)).left
    rw [SchemeTools.overProdMap_range]
    exact ⟨hi, hσ⟩

/-- Coverage by the independently specified original multivariate polynomial schemes. -/
theorem powerChart_covers (n : ℕ) (x : powerScheme R n) :
    ∃ σ : Fin n → Fin 2, ∃ y, powerChartι R n σ y = x := by
  obtain ⟨σ, y, hy⟩ := affinePowerChartOver_covers R n x
  have he : (affinePowerIso R n).hom.left ((affinePowerIso R n).inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]
    rfl
  refine ⟨σ, (affinePowerIso R n).inv.left y, ?_⟩
  change (affinePowerChartOver R n σ).left
    ((affinePowerIso R n).hom.left ((affinePowerIso R n).inv.left y)) = x
  rw [he]
  exact hy

/-- Genuine affine open cover of the actual product by all original pivot choices. -/
noncomputable def polynomialPowerChartCover (n : ℕ) : (powerScheme R n).AffineOpenCover where
  I₀ := Fin n → Fin 2
  X _ := CommRingCat.of (MvPolynomial (Fin n) R)
  f := powerChartι R n
  idx x := (powerChart_covers R n x).choose
  covers x := (powerChart_covers R n x).choose_spec

end BPFixedPoints.ProjectiveLine
