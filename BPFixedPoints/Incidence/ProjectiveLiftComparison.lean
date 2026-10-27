/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-APACHE-2.0.
Original authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou

Adapted from Mathlib.CategoryTheory.Abelian.Projective.Resolution (v4.35.0).
Modified in this project: the source is any nonnegative chain complex with
projective terms, rather than a projective resolution. No source exactness is used.
-/
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Uniqueness of lifts from complexes of projective terms to resolutions

For product comparison the source is the tensor complex of two resolutions;
its exactness cannot be assumed. Construct a homotopy between two chain maps
with the same augmentation using only projectivity of source terms.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Category

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : ChainComplex C ℕ} [∀ n, Projective (K.X n)]
  {X : C} (P : ProjectiveResolution X)

noncomputable def projectiveLiftHomotopyZero₀ (f : K ⟶ P.complex) (h : f ≫ P.π = 0) :
    K.X 0 ⟶ P.complex.X 1 :=
  P.exact₀.liftFromProjective (f.f 0) congr($(h).f 0)

@[reassoc (attr := simp)] theorem projectiveLiftHomotopyZero₀_comp
    (f : K ⟶ P.complex) (h : f ≫ P.π = 0) :
    projectiveLiftHomotopyZero₀ P f h ≫ P.complex.d 1 0 = f.f 0 :=
  P.exact₀.liftFromProjective_comp _ _

noncomputable def projectiveLiftHomotopyZero₁ (f : K ⟶ P.complex) (h : f ≫ P.π = 0) :
    K.X 1 ⟶ P.complex.X 2 :=
  (P.exact_succ 0).liftFromProjective (f.f 1 - K.d 1 0 ≫ projectiveLiftHomotopyZero₀ P f h)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
      projectiveLiftHomotopyZero₀_comp, sub_self])

@[reassoc (attr := simp)] theorem projectiveLiftHomotopyZero₁_comp
    (f : K ⟶ P.complex) (h : f ≫ P.π = 0) :
    projectiveLiftHomotopyZero₁ P f h ≫ P.complex.d 2 1 =
      f.f 1 - K.d 1 0 ≫ projectiveLiftHomotopyZero₀ P f h :=
  (P.exact_succ 0).liftFromProjective_comp _ _

noncomputable def projectiveLiftHomotopyZeroSucc (f : K ⟶ P.complex) (n : ℕ)
    (g : K.X n ⟶ P.complex.X (n + 1)) (g' : K.X (n + 1) ⟶ P.complex.X (n + 2))
    (w : f.f (n + 1) = K.d (n + 1) n ≫ g + g' ≫ P.complex.d (n + 2) (n + 1)) :
    K.X (n + 2) ⟶ P.complex.X (n + 3) :=
  (P.exact_succ (n + 1)).liftFromProjective (f.f (n + 2) - K.d _ _ ≫ g') (by simp [w])

@[reassoc (attr := simp)] theorem projectiveLiftHomotopyZeroSucc_comp
    (f : K ⟶ P.complex) (n : ℕ) (g : K.X n ⟶ P.complex.X (n + 1))
    (g' : K.X (n + 1) ⟶ P.complex.X (n + 2))
    (w : f.f (n + 1) = K.d (n + 1) n ≫ g + g' ≫ P.complex.d (n + 2) (n + 1)) :
    projectiveLiftHomotopyZeroSucc P f n g g' w ≫ P.complex.d (n + 3) (n + 2) =
      f.f (n + 2) - K.d _ _ ≫ g' :=
  (P.exact_succ (n + 1)).liftFromProjective_comp _ _

noncomputable def projectiveLiftHomotopyZero (f : K ⟶ P.complex) (h : f ≫ P.π = 0) :
    Homotopy f 0 :=
  Homotopy.mkInductive _ (projectiveLiftHomotopyZero₀ P f h) (by simp)
    (projectiveLiftHomotopyZero₁ P f h) (by simp) fun n ⟨g, g', w⟩ =>
      ⟨projectiveLiftHomotopyZeroSucc P f n g g' w, by simp⟩

/-- Compare augmentation-preserving lifts without requiring source exactness. -/
noncomputable def projectiveLiftHomotopy (f g : K ⟶ P.complex)
    (h : f ≫ P.π = g ≫ P.π) : Homotopy f g :=
  Homotopy.equivSubZero.invFun (projectiveLiftHomotopyZero P (f - g) (by simp [h]))

end BPFixedPoints.ResolutionTools
