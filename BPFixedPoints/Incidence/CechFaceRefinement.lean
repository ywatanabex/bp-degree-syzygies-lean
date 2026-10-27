import BPFixedPoints.Incidence.CechRestrictionTorus

/-! # Refinement maps among all polynomial and Laurent Čech faces

A face refines another by replacing any subset of chart coordinates with overlap
coordinates. A right-chart coordinate becomes the inverse Laurent coordinate.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*}

/-- Refinement replaces chart coordinates by overlaps and leaves other coordinates fixed. -/
def FaceRefines (q r : V → Fin 3) : Prop := ∀ v, q v = r v ∨ r v = 2

theorem faceRefines_refl (q : V → Fin 3) : FaceRefines q q := fun _ => Or.inl rfl

theorem faceRefines_trans {q r s : V → Fin 3} (hqr : FaceRefines q r) (hrs : FaceRefines r s) :
    FaceRefines q s := by
  intro v
  rcases hrs v with hrs | hs
  · rw [← hrs]
    exact hqr v
  · exact Or.inr hs

/-- Exponent change for a single refined vertex. -/
def refinementCoordinate {q r : Fin 3} (h : q = r ∨ r = 2) :
    FaceExponent q →+ FaceExponent r := by
  by_cases hr : r = 2
  · exact (AddEquiv.cast (M := FaceExponent) hr.symm).toAddMonoidHom.comp
      (if q = 1 then -(exponentToInt q) else exponentToInt q)
  · exact (AddEquiv.cast (M := FaceExponent) (h.resolve_right hr)).toAddMonoidHom

/-- The only sign change is inversion from a right chart to an overlap. -/
theorem refinementCoordinate_toInt {q r : Fin 3} (h : q = r ∨ r = 2) (m : FaceExponent q) :
    exponentToInt r (refinementCoordinate h m) =
      if q = 1 ∧ r = 2 then -(exponentToInt q m) else exponentToInt q m := by
  by_cases hr : r = 2
  · subst r
    by_cases hq : q = 1 <;> simp [refinementCoordinate, hq, exponentToInt] <;> rfl
  · simp only [refinementCoordinate, dif_neg hr, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, exponentToInt_cast]
    simp [hr]

/-- Coordinatewise exponent map for arbitrary higher intersections. -/
def refinementExponent {q r : V → Fin 3} (h : FaceRefines q r) :
    FaceMonoid q →+ FaceMonoid r where
  toFun m v := refinementCoordinate (h v) (m v)
  map_zero' := by funext v; exact map_zero _
  map_add' m n := by funext v; exact map_add _ _ _

theorem faceToInt_refinement {q r : V → Fin 3} (h : FaceRefines q r)
    (m : FaceMonoid q) (v : V) :
    faceToInt r (refinementExponent h m) v =
      if q v = 1 ∧ r v = 2 then -(faceToInt q m v) else faceToInt q m v :=
  refinementCoordinate_toInt (h v) (m v)

/-- The exponent sign change exactly compensates the change of vertex unit. -/
theorem refinementCoordinate_unit {A : Type*} [Group A] (u : A)
    {q r : Fin 3} (h : q = r ∨ r = 2) (m : FaceExponent q) :
    (if r = 1 then u⁻¹ else u) ^ exponentToInt r (refinementCoordinate h m) =
      (if q = 1 then u⁻¹ else u) ^ exponentToInt q m := by
  rw [refinementCoordinate_toInt]
  rcases h with he | he
  · subst r
    by_cases hq : q = 1 <;> simp [hq]
  · subst r
    by_cases hq : q = 1 <;> simp [hq, inv_zpow, zpow_neg]

variable (R : Type*) [CommRing R]

/-- Ring restriction among arbitrary polynomial/Laurent faces. -/
noncomputable def faceRefinementMap {q r : V → Fin 3} (h : FaceRefines q r) :
    FaceRing R q →ₐ[R] FaceRing R r :=
  AddMonoidAlgebra.mapDomainAlgHom R R (refinementExponent h)

@[simp] theorem faceRefinementMap_single {q r : V → Fin 3} (h : FaceRefines q r)
    (m : FaceMonoid q) (c : R) :
    faceRefinementMap R h (AddMonoidAlgebra.single m c) =
      AddMonoidAlgebra.single (refinementExponent h m) c :=
  AddMonoidAlgebra.mapDomain_single

/-- Universal coefficient variables are fixed by refinement. -/
noncomputable def facePolynomialRefinement (J : Type*) {q r : V → Fin 3} (h : FaceRefines q r) :
    MvPolynomial J (FaceRing R q) →ₐ[R] MvPolynomial J (FaceRing R r) :=
  MvPolynomial.mapAlgHom (faceRefinementMap R h)

end BPFixedPoints.CechProduct
