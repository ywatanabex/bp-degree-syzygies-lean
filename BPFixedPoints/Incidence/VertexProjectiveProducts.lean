import BPFixedPoints.Incidence.ProjectivePowerChartCover

/-! # Actual projective products with the original finite vertex labels

An enumeration is used internally to reuse the iterated products. The full
product universal property uses the original vertex labels. The affine cover
has exactly the original vertex polynomial ring and all original pivot choices.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] (V : Type) [Fintype V]

/-- Actual product over the coefficient scheme, with one Proj factor per original vertex. -/
noncomputable def vertexOverBase : Over (Spec (CommRingCat.of R)) :=
  powerOverBase R (Fintype.card V)

noncomputable def vertexScheme : Scheme := (vertexOverBase R V).left

noncomputable def vertexToBase : vertexScheme R V ⟶ Spec (CommRingCat.of R) :=
  (vertexOverBase R V).hom

/-- Original vertex-labelled coordinate projections over the coefficient scheme. -/
noncomputable def vertexProjectionOver (v : V) : vertexOverBase R V ⟶ overBase R :=
  powerProjectionOver R (Fintype.card V) (Fintype.equivFin V v)

/-- The actual cone indexed by the original vertex set. -/
noncomputable def vertexFan : Fan (fun _ : V => overBase R) :=
  Fan.mk (vertexOverBase R V) (vertexProjectionOver R V)

/-- The full product universal property with the original vertex labels. -/
noncomputable def vertexIsProduct : IsLimit (vertexFan R V) where
  lift s := powerLiftOver R (Fintype.card V) s.pt
    (fun j => s.π.app ⟨(Fintype.equivFin V).symm j⟩)
  fac s v := by
    rcases v with ⟨v⟩
    let f : V → (s.pt ⟶ overBase R) := fun j => s.π.app ⟨j⟩
    exact (powerLiftOver_projection R (Fintype.card V) s.pt
      (fun j => f ((Fintype.equivFin V).symm j)) (Fintype.equivFin V v)).trans
        (congrArg f ((Fintype.equivFin V).symm_apply_apply v))
  uniq s g h := by
    apply powerLiftOver_unique R (Fintype.card V) s.pt _ g
    intro j
    simpa [vertexFan, vertexProjectionOver] using h ⟨(Fintype.equivFin V).symm j⟩

/-- The original-labelled construction is the actual indexed product in Mathlib. -/
noncomputable def vertexPiIso : vertexOverBase R V ≅ ∏ᶜ (fun _ : V => overBase R) :=
  (vertexIsProduct R V).conePointUniqueUpToIso (limit.isLimit _)

/-- Original vertex polynomial coordinates are identified over the original base. -/
noncomputable def vertexAffineIso :
    SchemeTools.polynomialOverBase R V ≅
      SchemeTools.polynomialOverBase R (Fin (Fintype.card V)) :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.renameEquiv R (Fintype.equivFin V))).symm.op

/-- The actual chart over the original coefficient scheme for every original pivot choice. -/
noncomputable def vertexChartOver (σ : V → Fin 2) :
    SchemeTools.polynomialOverBase R V ⟶ vertexOverBase R V :=
  (vertexAffineIso R V).hom ≫ powerChartOver R (Fintype.card V)
    (fun j => σ ((Fintype.equivFin V).symm j))

/-- Chart source is the original polynomial ring on the original vertices. -/
noncomputable def vertexChartι (σ : V → Fin 2) :
    Spec (CommRingCat.of (MvPolynomial V R)) ⟶ vertexScheme R V :=
  (vertexChartOver R V σ).left

instance vertexChartι_isOpenImmersion (σ : V → Fin 2) :
    IsOpenImmersion (vertexChartι R V σ) := by
  change IsOpenImmersion ((vertexAffineIso R V).hom.left ≫
    powerChartι R (Fintype.card V) (fun j => σ ((Fintype.equivFin V).symm j)))
  infer_instance

/-- Every original vertex-labelled chart retains its original coefficient map. -/
@[reassoc] theorem vertexChartι_toBase (σ : V → Fin 2) :
    vertexChartι R V σ ≫ vertexToBase R V =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial V R))) :=
  (vertexChartOver R V σ).w

/-- All original pivot choices cover the actual vertex-labelled projective product. -/
theorem vertexChart_covers (x : vertexScheme R V) :
    ∃ σ : V → Fin 2, ∃ y, vertexChartι R V σ y = x := by
  obtain ⟨τ, y, hy⟩ := powerChart_covers R (Fintype.card V) x
  have he : (vertexAffineIso R V).hom.left ((vertexAffineIso R V).inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]
    rfl
  refine ⟨(fun v => τ (Fintype.equivFin V v)), (vertexAffineIso R V).inv.left y, ?_⟩
  change powerChartι R (Fintype.card V)
    (fun j => τ (Fintype.equivFin V ((Fintype.equivFin V).symm j)))
    ((vertexAffineIso R V).hom.left ((vertexAffineIso R V).inv.left y)) = x
  simpa only [Equiv.apply_symm_apply, he] using hy

/-- Genuine affine open cover by the original vertex polynomial charts. -/
noncomputable def vertexPolynomialCover : (vertexScheme R V).AffineOpenCover where
  I₀ := V → Fin 2
  X _ := CommRingCat.of (MvPolynomial V R)
  f := vertexChartι R V
  idx x := (vertexChart_covers R V x).choose
  covers x := (vertexChart_covers R V x).choose_spec

end BPFixedPoints.ProjectiveLine
