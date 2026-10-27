import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedFive
import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedTruncation
import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedBase

/-! # Hom-complex cohomology computes derived morphisms into bounded acyclic complexes

Let `P` be a chain complex with an exact epic augmentation `π : P_0 ⟶ A`, exact in positive
degrees (a resolution of `A`), and let `Y` be a bounded chain complex indexed by `ℕ` whose terms
are all acyclic against `P` (`ComplexAcyclicAgainst`: the positive `Ext` groups from the terms of
`P` vanish). This file proves:

* `derivedMapBijective_negativeComplex_single`, `derivedMapBijective_negativeComplex_extend`: the
  localization functor `Qh` from the homotopy category to the derived category is bijective on
  all shifted morphisms from the negative complex of `P` to every single object and to `Y`
  (extended along `n ↦ p - n`). The proof is an induction on the length of `Y` with the stupid
  truncation triangles (`IncidenceUniversalKoszulDerivedTruncation.lean`) and the five lemma
  (`IncidenceUniversalKoszulDerivedFive.lean`); the base case is the single-object statement of
  `IncidenceUniversalKoszulDerivedBase.lean`.
* `derivedCohomologyClassHom`, `derivedCohomologyClassHom_bijective`,
  `derivedCohomologyClassEquiv`: under this bijectivity, the degree-`n` cohomology of the Hom
  complex from the negative complex of `P` to a cochain complex `K` is additively isomorphic to
  `Hom_{D}(A[0], K[n])`.

No spectral sequence and no unbounded complex is used.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape BPFixedPoints.ExtResolutionTools

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

universe w w' v u

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π = 0)
  (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n + 1))

include π z e hP in
/-- For a single complex on an object against which `P` is acyclic, `Qh` is bijective on all
shifted morphisms from the negative complex of `P`. -/
theorem derivedMapBijective_negativeComplex_single (Y : C) (ha : ComplexAcyclicAgainst P Y)
    (p : ℤ) :
    DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient C (up ℤ)).obj (negativeComplex P))
      ((HomotopyCategory.quotient C (up ℤ)).obj ((single C (up ℤ) p).obj Y)) := by
  intro n
  let e₁ := ((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).app ((single C (up ℤ) p).obj Y)
  let e₂ := (HomotopyCategory.quotient C (up ℤ)).mapIso
    (((CochainComplex.singleFunctors C).shiftIso n (p - n) p (by omega)).app Y)
  exact map_bijective_of_iso DerivedCategory.Qh (e₂.symm ≪≫ e₁)
    (qh_map_bijective_negativeComplex_single P π z e hP Y ha (p - n))

include π z e hP in
/-- **The derived comparison for bounded complexes.** Let `Y` be a bounded chain complex whose
terms are all acyclic against the resolution `P`. Then `Qh` is bijective on shifted morphisms from
the negative complex of `P` to `Y` extended along `n ↦ p - n`: homotopy classes of maps compute
morphisms in the derived category. -/
theorem derivedMapBijective_negativeComplex_extend (Y : ChainComplex C ℕ) (m : ℕ)
    (hY : ∀ n, m ≤ n → IsZero (Y.X n)) (ha : ∀ n, ComplexAcyclicAgainst P (Y.X n)) (p : ℤ) :
    DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient C (up ℤ)).obj (negativeComplex P))
      ((HomotopyCategory.quotient C (up ℤ)).obj (Y.extend (embeddingUpIntLE p))) :=
  chainExtend_induction
    (DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient C (up ℤ)).obj (negativeComplex P)))
    (fun e h => DerivedMapBijective.of_iso _ e h)
    (fun _ h => DerivedMapBijective.of_isZero _ h)
    (fun T hT h₁ h₃ => DerivedMapBijective.of_triangle₂ _ T hT h₁ h₃)
    (ComplexAcyclicAgainst P)
    (fun Y' p' hY' => derivedMapBijective_negativeComplex_single P π z e hP Y' hY' p')
    m Y hY ha p

include π z e hP in
/-- The additive map underlying `derivedCohomologyClassEquiv`: a cohomology class of the Hom
complex from the negative complex of `P` to `K` is sent to the corresponding morphism in the
homotopy category, then to the derived category, and transported along the augmentation
quasi-isomorphism of `P`. -/
noncomputable def derivedCohomologyClassHom (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass (negativeComplex P) K n →+
      ShiftedHom (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj A))
        (DerivedCategory.Q.obj K) n where
  toFun x := (((DerivedCategory.quotientCompQhIso C).app (negativeComplex P) ≪≫
      nativeAugmentationIso P π z e hP).homCongr
      ((DerivedCategory.Qh.commShiftIso n).app ((HomotopyCategory.quotient C (up ℤ)).obj K) ≪≫
        (shiftFunctor (DerivedCategory C) n).mapIso ((DerivedCategory.quotientCompQhIso C).app K)))
    (DerivedCategory.Qh.map (((Iso.refl _).homCongr
      (((HomotopyCategory.quotient C (up ℤ)).commShiftIso n).app K))
        (CochainComplex.HomComplex.CohomologyClass.toHom x)))
  map_zero' := by simp [Iso.homCongr_apply]
  map_add' x y := by
    simp only [map_add, Iso.homCongr_apply, Preadditive.add_comp, Preadditive.comp_add,
      Functor.map_add]

include π z e hP in
/-- **Hom-complex cohomology computes derived morphisms out of a resolved object.** If `Qh` is
bijective on shifted morphisms from the negative complex of the resolution `P` to `K`, then the
degree-`n` cohomology of the Hom complex from that negative complex to `K` is additively
isomorphic to the degree-`n` shifted morphisms in the derived category from the augmentation
target `A` (in degree zero) to `K`. -/
theorem derivedCohomologyClassHom_bijective (K : CochainComplex C ℤ)
    (hK : DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient C (up ℤ)).obj (negativeComplex P))
      ((HomotopyCategory.quotient C (up ℤ)).obj K)) (n : ℤ) :
    Function.Bijective (derivedCohomologyClassHom P π z e hP K n) :=
  (Iso.homCongr _ _).bijective.comp ((hK n).comp ((Iso.homCongr _ _).bijective.comp
    (CochainComplex.HomComplex.CohomologyClass.toHom_bijective _ _ _)))

include π z e hP in
/-- The additive isomorphism of `derivedCohomologyClassHom_bijective`. -/
noncomputable def derivedCohomologyClassEquiv (K : CochainComplex C ℤ)
    (hK : DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient C (up ℤ)).obj (negativeComplex P))
      ((HomotopyCategory.quotient C (up ℤ)).obj K)) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass (negativeComplex P) K n ≃+
      ShiftedHom (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj A))
        (DerivedCategory.Q.obj K) n :=
  AddEquiv.ofBijective _ (derivedCohomologyClassHom_bijective P π z e hP K hK n)

end Comparison

end BPFixedPoints.Multigraph
