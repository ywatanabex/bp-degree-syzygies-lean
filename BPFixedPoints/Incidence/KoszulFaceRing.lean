import BPFixedPoints.Incidence.CechFaces
import BPFixedPoints.Incidence.KoszulLaurent
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Compare face coordinate rings with polynomial and common Laurent rings -/

namespace BPFixedPoints.CechProduct

variable {V J R : Type*} [CommRing R]

/-- Read face exponents as ordinary integers. -/
def exponentToInt : (q : Fin 3) → FaceExponent q →+ ℤ
  | 0 => Nat.castAddMonoidHom ℤ
  | 1 => Nat.castAddMonoidHom ℤ
  | 2 => AddMonoidHom.id ℤ

theorem exponentToInt_injective (q : Fin 3) : Function.Injective (exponentToInt q) := by
  fin_cases q
  · exact Int.ofNat_injective
  · exact Int.ofNat_injective
  · exact Function.injective_id

@[simp] theorem exponentToInt_one (q : Fin 3) :
    exponentToInt q (faceOneExponent q) = 1 := by
  fin_cases q <;> rfl

def faceToInt (q : V → Fin 3) : FaceMonoid q →+ (V → ℤ) where
  toFun m v := exponentToInt (q v) (m v)
  map_zero' := by funext v; exact map_zero _
  map_add' m n := by funext v; exact map_add _ _ _

theorem faceToInt_injective (q : V → Fin 3) : Function.Injective (faceToInt q) := by
  intro m n h
  funext v
  exact exponentToInt_injective (q v) (congrFun h v)

theorem faceToInt_vertex [DecidableEq V] (q : V → Fin 3) (v : V) :
    faceToInt q (Pi.single v (faceOneExponent (q v))) = Pi.single v (1 : ℤ) := by
  funext w
  by_cases hw : w = v
  · subst w; simp [faceToInt]
  · simp [faceToInt, hw]

/-- An overlap-free face is exactly a zero/infinity chart. -/
def chartFace (σ : V → Bool) : V → Fin 3 := fun v => if σ v then 1 else 0

@[simp] theorem chartFace_ne_two (σ : V → Bool) (v : V) : chartFace σ v ≠ 2 := by
  cases h : σ v <;> simp [chartFace, h]

def exponentNatEquiv : (q : Fin 3) → (h : q ≠ 2) → FaceExponent q ≃+ ℕ
  | 0, _ => AddEquiv.refl ℕ
  | 1, _ => AddEquiv.refl ℕ
  | 2, h => (h rfl).elim

@[simp] theorem exponentNatEquiv_one (q : Fin 3) (h : q ≠ 2) :
    exponentNatEquiv q h (faceOneExponent q) = 1 := by
  fin_cases q
  · rfl
  · rfl
  · exact (h rfl).elim

noncomputable def funFinsuppNatEquiv [Fintype V] : (V → ℕ) ≃+ (V →₀ ℕ) where
  toEquiv := Finsupp.equivFunOnFinite.symm
  map_add' m n := by ext v; rfl

noncomputable def chartExponentEquiv [Fintype V] (σ : V → Bool) :
    FaceMonoid (chartFace σ) ≃+ (V →₀ ℕ) :=
  (AddEquiv.piCongrRight fun v => exponentNatEquiv (chartFace σ v) (chartFace_ne_two σ v)).trans
    funFinsuppNatEquiv

@[simp] theorem chartExponentEquiv_apply [Fintype V] (σ : V → Bool)
    (m : FaceMonoid (chartFace σ)) (v : V) :
    chartExponentEquiv σ m v = exponentNatEquiv (chartFace σ v) (chartFace_ne_two σ v) (m v) := rfl

theorem chartExponentEquiv_vertex [Fintype V] [DecidableEq V] (σ : V → Bool) (v : V) :
    chartExponentEquiv σ (Pi.single v (faceOneExponent (chartFace σ v))) =
      Finsupp.single v 1 := by
  ext w
  rw [chartExponentEquiv_apply]
  by_cases hw : w = v
  · subst w
    simp only [Pi.single_eq_same, Finsupp.single_eq_same, exponentNatEquiv_one]
  · rw [Pi.single_eq_of_ne hw, map_zero, Finsupp.single_eq_of_ne hw]

/-- The coordinate ring of an overlap-free face is the polynomial ring in vertex coordinates. -/
noncomputable def chartFaceRingEquiv [Fintype V] (σ : V → Bool) :
    FaceRing R (chartFace σ) ≃ₐ[R] MvPolynomial V R :=
  AddMonoidAlgebra.domCongr R R (chartExponentEquiv σ)

@[simp] theorem chartFaceRingEquiv_variable [Fintype V] [DecidableEq V]
    (σ : V → Bool) (v : V) :
    chartFaceRingEquiv (R := R) σ (faceVariable R (chartFace σ) v) = MvPolynomial.X v := by
  change AddMonoidAlgebra.domCongr R R (chartExponentEquiv σ)
    (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.domCongr_single, chartExponentEquiv_vertex]
  rfl

/-- Embed face and free-coefficient exponents into common integer exponents. -/
def faceFreeExponent (q : V → Fin 3) :
    ((J →₀ ℕ) × FaceMonoid q) →+ ((V ⊕ J) → ℤ) where
  toFun m := Sum.elim (faceToInt q m.2) (IncidenceLaurent.natExponent m.1)
  map_zero' := by funext i; rcases i with v | j <;> simp [faceToInt, IncidenceLaurent.natExponent]
  map_add' m n := by
    funext i
    rcases i with v | j <;> simp [faceToInt, IncidenceLaurent.natExponent]

theorem faceFreeExponent_injective (q : V → Fin 3) :
    Function.Injective (faceFreeExponent (J := J) q) := by
  intro m n h
  apply Prod.ext
  · ext j
    exact Int.ofNat_inj.mp (congrFun h (Sum.inr j))
  · apply faceToInt_injective q
    funext v
    exact congrFun h (Sum.inl v)

/-- Embed a face's free polynomial ring into the common Laurent ring. -/
noncomputable def faceFreeMap (q : V → Fin 3) :
    MvPolynomial J (FaceRing R q) →ₐ[R] IncidenceLaurent.LaurentRing (V ⊕ J) R :=
  (AddMonoidAlgebra.mapDomainAlgHom R R (faceFreeExponent q)).comp
    (AddMonoidAlgebra.curryAlgEquiv R).symm.toAlgHom

theorem faceFreeMap_injective (q : V → Fin 3) :
    Function.Injective (faceFreeMap (J := J) (R := R) q) :=
  (AddMonoidAlgebra.mapDomain_injective (faceFreeExponent_injective q)).comp
    (AddMonoidAlgebra.curryAlgEquiv R).symm.injective

@[simp] theorem faceFreeMap_monomial_single (q : V → Fin 3) (d : J →₀ ℕ)
    (m : FaceMonoid q) (r : R) :
    faceFreeMap q (MvPolynomial.monomial d (AddMonoidAlgebra.single m r)) =
      AddMonoidAlgebra.single (faceFreeExponent q (d, m)) r := by
  simp [faceFreeMap, MvPolynomial.monomial]

end BPFixedPoints.CechProduct
