import BPFixedPoints.Family.Ring

/-!
# Admissible BP points in arbitrary commutative rings

Replace nonzero conditions over fields by unit conditions over general rings.
This presentation supports the infinitesimal lifting proof of smoothness of `FamilyRing`.
-/

namespace BPFixedPoints.Multigraph

open BP MvPolynomial
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)
variable {R : Type*} [CommRing R]

def ringCavity (b : V → R) (y : Dart E → R) (α : Dart E) : R :=
  b (G.tail α) * ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), y γ

def ringField (b : V → R) (y : Dart E → R) (i : V) : R :=
  b i * ∏ α ∈ G.inDarts i, y α

theorem ringField_tail (b : V → R) (y : Dart E → R) (α : Dart E) :
    G.ringField b y (G.tail α) = G.ringCavity b y α * y (rev α) := by
  unfold ringField ringCavity
  rw [← Finset.mul_prod_erase (G.inDarts (G.tail α)) y (G.rev_mem_inDarts α)]
  ring

/-- A BP point on the admissible open set, with unit parameters as well. -/
@[ext] structure FamilyPoint (R : Type*) [CommRing R] where
  a : E → R
  b : V → R
  y : Dart E → R
  a_unit : ∀ e, IsUnit (a e)
  b_unit : ∀ i, IsUnit (b i)
  y_unit : ∀ α, IsUnit (y α)
  den_unit : ∀ α, IsUnit (G.ringCavity b y α + a α.1)
  field_unit : ∀ i, IsUnit (1 + G.ringField b y i)
  equation : ∀ α, y α * (G.ringCavity b y α + a α.1) =
    a α.1 * G.ringCavity b y α + 1

namespace FamilyPoint

variable {G} (p : G.FamilyPoint R)

abbrev F (i : V) : R := G.ringField p.b p.y i
abbrev X (α : Dart E) : R := G.ringCavity p.b p.y α

theorem F_unit (i : V) : IsUnit (p.F i) :=
  (p.b_unit i).mul (IsUnit.prod_iff.mpr fun α _ => p.y_unit α)

theorem X_unit (α : Dart E) : IsUnit (p.X α) :=
  (p.b_unit _).mul (IsUnit.prod_iff.mpr fun γ _ => p.y_unit γ)

def val : FamVar V E → R := Sum.elim p.a (Sum.elim p.b p.y)

variable {S : Type*} [CommRing S]

def map (φ : R →+* S) : G.FamilyPoint S where
  a := φ ∘ p.a
  b := φ ∘ p.b
  y := φ ∘ p.y
  a_unit e := (p.a_unit e).map φ
  b_unit i := (p.b_unit i).map φ
  y_unit α := (p.y_unit α).map φ
  den_unit α := by simpa [ringCavity] using (p.den_unit α).map φ
  field_unit i := by simpa [ringField] using (p.field_unit i).map φ
  equation α := by simpa [ringCavity] using congrArg φ (p.equation α)

section Algebra

variable [Algebra ℂ R]

@[simp] theorem eval_a (e : E) : aeval p.val (famA (V := V) e) = p.a e := by
  simp [famA, val]
@[simp] theorem eval_b (i : V) : aeval p.val (famB (E := E) i) = p.b i := by
  simp [famB, val]
@[simp] theorem eval_y (α : Dart E) : aeval p.val (famY (V := V) α) = p.y α := by
  simp [famY, val]
@[simp] theorem eval_cavity (α : Dart E) : aeval p.val (G.famCavity α) = p.X α := by
  simp [famCavity, ringCavity]
@[simp] theorem eval_field (i : V) : aeval p.val (G.famTotalField i) = p.F i := by
  simp [famTotalField, ringField]

theorem eval_den_unit : IsUnit (aeval p.val G.famDen) := by
  simp only [famDen, map_mul, map_prod, map_add, map_one, eval_a, eval_b, eval_y,
    eval_cavity, eval_field]
  exact ((((IsUnit.prod_iff.mpr fun e _ => p.a_unit e).mul
    (IsUnit.prod_iff.mpr fun i _ => p.b_unit i)).mul
    (IsUnit.prod_iff.mpr fun α _ => p.y_unit α)).mul
    (IsUnit.prod_iff.mpr fun α _ => p.den_unit α)).mul
    (IsUnit.prod_iff.mpr fun i _ => p.field_unit i)

noncomputable def toLocalization : Localization.Away G.famDen →ₐ[ℂ] R :=
  IsLocalization.Away.liftAlgHom _ p.eval_den_unit

@[simp] theorem toLocalization_map (f : MvPolynomial (FamVar V E) ℂ) :
    p.toLocalization (algebraMap _ (Localization.Away G.famDen) f) = aeval p.val f :=
  IsLocalization.Away.lift_eq _ p.eval_den_unit _

noncomputable def toHom : G.FamilyRing →ₐ[ℂ] R :=
  Ideal.Quotient.liftₐ _ p.toLocalization <| by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨α, rfl⟩
      simp [famResidual, p.equation]
    · exact map_zero _
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [smul_eq_mul, hx]

@[simp] theorem toHom_map (f : MvPolynomial (FamVar V E) ℂ) :
    p.toHom (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing f) = aeval p.val f := by
  exact p.toLocalization_map f

end Algebra
end FamilyPoint

section Universal

variable [Algebra ℂ R]

theorem familyRing_hom_ext {f g : G.FamilyRing →ₐ[ℂ] R}
    (h : ∀ i, f (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (X i)) =
      g (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (Submonoid.powers G.famDen)
  exact MvPolynomial.algHom_ext h

theorem familyRing_den_unit :
    IsUnit (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing G.famDen) := by
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away G.famDen)
    G.famDen).map (algebraMap (Localization.Away G.famDen) G.FamilyRing)

theorem familyRing_residual (α : Dart E) :
    algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (G.famResidual α) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨α, rfl⟩

noncomputable def familyPointOfHom (f : G.FamilyRing →ₐ[ℂ] R) : G.FamilyPoint R := by
  let φ := f.comp (IsScalarTower.toAlgHom ℂ (MvPolynomial (FamVar V E) ℂ) G.FamilyRing)
  have hu := (G.familyRing_den_unit).map f
  change IsUnit (φ G.famDen) at hu
  simp only [famDen, map_mul, map_prod, map_add, map_one, IsUnit.mul_iff,
    IsUnit.prod_univ_iff] at hu
  refine ⟨fun e => φ (famA e), fun i => φ (famB i), fun α => φ (famY α),
    hu.1.1.1.1, hu.1.1.1.2, hu.1.1.2, ?_, ?_, ?_⟩
  · intro α; simpa [famCavity, ringCavity] using hu.1.2 α
  · intro i; simpa [famTotalField, ringField] using hu.2 i
  · intro α
    have h := congrArg f (G.familyRing_residual α)
    change φ (G.famResidual α) = f 0 at h
    simpa [famResidual, famCavity, ringCavity, sub_eq_zero] using h

@[simp] theorem familyPointOfHom_a (f : G.FamilyRing →ₐ[ℂ] R) (e : E) :
    (G.familyPointOfHom f).a e = f (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (famA e)) := rfl
@[simp] theorem familyPointOfHom_b (f : G.FamilyRing →ₐ[ℂ] R) (i : V) :
    (G.familyPointOfHom f).b i = f (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (famB i)) := rfl
@[simp] theorem familyPointOfHom_y (f : G.FamilyRing →ₐ[ℂ] R) (α : Dart E) :
    (G.familyPointOfHom f).y α = f (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (famY α)) := rfl

@[simp] theorem toHom_familyPointOfHom (f : G.FamilyRing →ₐ[ℂ] R) :
    (G.familyPointOfHom f).toHom = f := by
  apply G.familyRing_hom_ext
  intro i
  rw [FamilyPoint.toHom_map, MvPolynomial.aeval_X]
  rcases i with e | i | α <;> rfl

theorem FamilyPoint.map_toHom (p : G.FamilyPoint R) {S : Type*} [CommRing S] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) : (p.map φ.toRingHom).toHom = φ.comp p.toHom := by
  apply G.familyRing_hom_ext
  intro i
  simp only [AlgHom.comp_apply, FamilyPoint.toHom_map, MvPolynomial.aeval_X]
  rcases i with e | i | α <;> rfl

end Universal

end BPFixedPoints.Multigraph
