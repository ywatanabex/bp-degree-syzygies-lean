import BPFixedPoints.Incidence.ProjectiveLineOverBase
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Actual finite products of projective lines over the original base

The powers are iterated binary products in the category over the coefficient
scheme. Their coordinate projections satisfy the full finite-product universal
property, including the empty product, by Mathlib's product constructions.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The actual n-fold product of Proj lines over the original coefficient scheme. -/
noncomputable def powerOverBase : ℕ → Over (Spec (CommRingCat.of R))
  | 0 => Over.mk (𝟙 _)
  | n+1 => overBase R ⨯ powerOverBase n

/-- Underlying scheme of the actual product over the original coefficient scheme. -/
noncomputable def powerScheme (n : ℕ) : Scheme := (powerOverBase R n).left

/-- The original common-base structural morphism of the actual product. -/
noncomputable def powerToBase (n : ℕ) : powerScheme R n ⟶ Spec (CommRingCat.of R) :=
  (powerOverBase R n).hom

/-- The next genuine product is Mathlib's fiber product over the common base. -/
noncomputable def powerSuccessorIso (n : ℕ) :
    powerScheme R (n+1) ≅ pullback (toSpecBase R) (powerToBase R n) :=
  Over.prodLeftIsoPullback (overBase R) (powerOverBase R n)

/-- Original coordinate projections of the finite product. -/
noncomputable def powerProjectionOver :
    (n : ℕ) → Fin n → (powerOverBase R n ⟶ overBase R)
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.cases prod.fst (fun j => prod.snd ≫ powerProjectionOver n j) i

/-- Assemble morphisms over the actual common base using Mathlib's product lifts. -/
noncomputable def powerLiftOver : (n : ℕ) → (X : Over (Spec (CommRingCat.of R))) →
    (Fin n → (X ⟶ overBase R)) → (X ⟶ powerOverBase R n)
  | 0, X, _ => Over.mkIdTerminal.from X
  | n+1, X, f => prod.lift (f 0) (powerLiftOver n X (fun j => f j.succ))

/-- Every original coordinate of the actual product lift is the specified map. -/
@[reassoc] theorem powerLiftOver_projection (n : ℕ)
    (X : Over (Spec (CommRingCat.of R))) (f : Fin n → (X ⟶ overBase R)) (i : Fin n) :
    powerLiftOver R n X f ≫ powerProjectionOver R n i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [powerLiftOver, powerProjectionOver]
    · simpa [powerLiftOver, powerProjectionOver, Category.assoc] using
        ih (fun j => f j.succ) j

/-- Original coordinate maps determine a unique morphism to the actual product. -/
theorem powerLiftOver_unique (n : ℕ)
    (X : Over (Spec (CommRingCat.of R))) (f : Fin n → (X ⟶ overBase R))
    (g : X ⟶ powerOverBase R n)
    (h : ∀ i, g ≫ powerProjectionOver R n i = f i) : g = powerLiftOver R n X f := by
  induction n with
  | zero => exact Over.mkIdTerminal.hom_ext _ _
  | succ n ih =>
    apply prod.hom_ext
    · simpa [powerLiftOver, powerProjectionOver] using h 0
    · simp only [powerLiftOver, prod.lift_snd]
      apply ih (fun j => f j.succ) (g ≫ prod.snd)
      intro j
      simpa [powerProjectionOver, Category.assoc] using h j.succ

/-- The finite product cone with its actual projections over the original base. -/
noncomputable def powerFan (n : ℕ) : Fan (fun _ : Fin n => overBase R) :=
  Fan.mk (powerOverBase R n) (powerProjectionOver R n)

/-- The full finite-product universal property, including n=0. -/
noncomputable def powerIsProduct (n : ℕ) : IsLimit (powerFan R n) where
  lift s := powerLiftOver R n s.pt (fun i => s.π.app ⟨i⟩)
  fac s i := powerLiftOver_projection R n s.pt _ i.as
  uniq s g h := powerLiftOver_unique R n s.pt _ g (fun i => h ⟨i⟩)

/-- The constructed powers agree with Mathlib's indexed product over the actual base. -/
noncomputable def powerPiIso (n : ℕ) :
    powerOverBase R n ≅ ∏ᶜ (fun _ : Fin n => overBase R) :=
  (powerIsProduct R n).conePointUniqueUpToIso (limit.isLimit _)

end BPFixedPoints.ProjectiveLine
