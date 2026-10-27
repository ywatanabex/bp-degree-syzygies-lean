import BPFixedPoints.Incidence.CechProductBasis
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Čech faces and decomposition into their coordinate rings

The values 0,1,2 denote the left chart, right chart and overlap. Each face
coordinate ring is a commutative monoid ring with ordinary and Laurent exponents.
-/

namespace BPFixedPoints.CechProduct

open Finsupp

/-- Use natural exponents on left/right charts and integer exponents on overlaps. -/
def FaceExponent (q : Fin 3) : Type := if q = 2 then ℤ else ℕ

instance (q : Fin 3) : AddCommMonoid (FaceExponent q) := by
  unfold FaceExponent
  split_ifs <;> infer_instance

/-- Monomial exponents on a Čech face. -/
abbrev FaceMonoid {V : Type*} (q : V → Fin 3) := (v : V) → FaceExponent (q v)

/-- Polynomial/Laurent coordinate ring of a face. -/
abbrev FaceRing (R : Type*) [CommRing R] {V : Type*} (q : V → Fin 3) :=
  AddMonoidAlgebra R (FaceMonoid q)

def vertexFaceEquiv : Basis ≃ Σ q : Fin 3, FaceExponent q where
  toFun
    | Sum.inl k => ⟨0, k⟩
    | Sum.inr (Sum.inl k) => ⟨1, k⟩
    | Sum.inr (Sum.inr k) => ⟨2, k⟩
  invFun
    | ⟨0, k⟩ => Sum.inl k
    | ⟨1, k⟩ => Sum.inr (Sum.inl k)
    | ⟨2, k⟩ => Sum.inr (Sum.inr k)
  left_inv := by rintro (k | k | k) <;> rfl
  right_inv := by rintro ⟨q, k⟩; fin_cases q <;> rfl

private def piSigmaEquiv {V : Type*} {A : V → Type*} {B : (v : V) → A v → Type*} :
    ((v : V) → Σ a : A v, B v a) ≃ Σ a : (v : V) → A v, (v : V) → B v (a v) where
  toFun f := ⟨fun v => (f v).1, fun v => (f v).2⟩
  invFun x := fun v => ⟨x.1 v, x.2 v⟩
  left_inv f := by funext v; exact Sigma.eta (f v)
  right_inv := by rintro ⟨a, b⟩; rfl

/-- Decompose a product monomial into its face and exponent vector. -/
def faceBasisEquiv {V : Type*} : (V → Basis) ≃ Σ q : V → Fin 3, FaceMonoid q :=
  (Equiv.piCongrRight fun _ => vertexFaceEquiv).trans piSigmaEquiv

def embedFace {V : Type*} (q : V → Fin 3) (m : FaceMonoid q) : V → Basis :=
  faceBasisEquiv.symm ⟨q, m⟩

@[simp] theorem faceBasisEquiv_embedFace {V : Type*} (q : V → Fin 3) (m : FaceMonoid q) :
    faceBasisEquiv (embedFace q m) = ⟨q, m⟩ := Equiv.apply_symm_apply _ _

theorem embedFace_injective {V : Type*} (q : V → Fin 3) :
    Function.Injective (embedFace q) := by
  intro m n h
  have he := congrArg faceBasisEquiv h
  simpa only [faceBasisEquiv_embedFace, Sigma.mk.injEq, heq_eq_eq, true_and] using he

theorem embedFace_ne_of_ne {V : Type*} {q q' : V → Fin 3} (h : q ≠ q')
    (m : FaceMonoid q) (m' : FaceMonoid q') : embedFace q m ≠ embedFace q' m' := by
  intro he
  have hh := congrArg (fun x : V → Basis => (faceBasisEquiv x).1) he
  exact h (by simpa using hh)

/-- Exponents of a homogeneous monomial in face coordinates. -/
def faceShiftExponent (q : Fin 3) (a b : ℕ) : FaceExponent q :=
  match q with
  | 0 => a
  | 1 => b
  | 2 => (a : ℤ)

theorem vertexFaceEquiv_shift (q : Fin 3) (m : FaceExponent q) (a b : ℕ) :
    shift a b (vertexFaceEquiv.symm ⟨q, m⟩) =
      vertexFaceEquiv.symm ⟨q, m + faceShiftExponent q a b⟩ := by
  fin_cases q <;> rfl

def faceShift {V : Type*} (q : V → Fin 3) (a b : V → ℕ) : FaceMonoid q :=
  fun v => faceShiftExponent (q v) (a v) (b v)

@[simp] theorem faceShiftExponent_zero (q : Fin 3) :
    faceShiftExponent q 0 0 = 0 := by
  fin_cases q <;> rfl

theorem faceShiftExponent_add (q : Fin 3) (a b a' b' : ℕ) :
    faceShiftExponent q (a + a') (b + b') =
      faceShiftExponent q a b + faceShiftExponent q a' b' := by
  fin_cases q <;> simp [faceShiftExponent, FaceExponent] <;> rfl

def faceOneExponent (q : Fin 3) : FaceExponent q := faceShiftExponent q 1 1

def faceVertexExponent {V : Type*} [DecidableEq V]
    (q : V → Fin 3) (v : V) (a b : ℕ) : FaceMonoid q :=
  Pi.single v (faceShiftExponent (q v) a b)

theorem faceShiftExponent_bit (q : Fin 3) (α : Fin 2) :
    faceShiftExponent q α.val (1 - α.val) =
      if q = 1 then (if α = 0 then faceOneExponent q else 0)
      else (if α = 0 then 0 else faceOneExponent q) := by
  fin_cases q <;> fin_cases α <;> rfl

theorem shift_embedFace {V : Type*} (q : V → Fin 3) (m : FaceMonoid q) (a b : V → ℕ) :
    (fun v => shift (a v) (b v) (embedFace q m v)) = embedFace q (m + faceShift q a b) := by
  funext v
  exact vertexFaceEquiv_shift (q v) (m v) (a v) (b v)

variable (R : Type*) [CommRing R]

noncomputable def faceVariable {V : Type*} [DecidableEq V]
    (q : V → Fin 3) (v : V) : FaceRing R q :=
  AddMonoidAlgebra.single (Pi.single v (faceOneExponent (q v))) 1

/-- The full Čech module is the finite direct sum of face coordinate rings. -/
noncomputable def faceEquiv {V : Type*} [Fintype V] :
    C R V ≃ₗ[R] ((q : V → Fin 3) → FaceRing R q) := by
  classical
  exact (Finsupp.mapDomain.linearEquiv R R faceBasisEquiv).trans
    ((Finsupp.sigmaFinsuppLEquivPiFinsupp R).trans
      (LinearEquiv.piCongrRight fun _ => (AddMonoidAlgebra.coeffLinearEquiv R).symm))

@[simp] theorem faceEquiv_coeff {V : Type*} [Fintype V]
    (x : C R V) (q : V → Fin 3) (m : FaceMonoid q) :
    (faceEquiv R x q).coeff m = x (embedFace q m) := by
  classical
  change mapDomain faceBasisEquiv x ⟨q, m⟩ = _
  exact mapDomain_equiv_apply (f := faceBasisEquiv) x ⟨q, m⟩

@[simp] theorem faceEquiv_single_same {V : Type*} [Fintype V]
    (q : V → Fin 3) (m : FaceMonoid q) (r : R) :
    faceEquiv R (single (embedFace q m) r) q = AddMonoidAlgebra.single m r := by
  classical
  ext k
  simp only [faceEquiv_coeff, AddMonoidAlgebra.coeff_single, single_apply,
    (embedFace_injective q).eq_iff]

theorem faceEquiv_single_ne {V : Type*} [Fintype V]
    {q q' : V → Fin 3} (h : q ≠ q') (m : FaceMonoid q') (r : R) :
    faceEquiv R (single (embedFace q' m) r) q = 0 := by
  classical
  ext k
  simp only [faceEquiv_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact single_eq_of_ne (embedFace_ne_of_ne h k m)

/-- The degree of a face counts its overlap vertices. -/
def faceDegree {V : Type*} [Fintype V] (q : V → Fin 3) : ℕ :=
  ∑ v, if q v = 2 then 1 else 0

theorem cechDegree_embedFace {V : Type*} [Fintype V]
    (q : V → Fin 3) (m : FaceMonoid q) : cechDegree (embedFace q m) = faceDegree q := by
  have h (k : Fin 3) (a : FaceExponent k) :
      lineDegree (vertexFaceEquiv.symm ⟨k, a⟩) = if k = 2 then 1 else 0 := by
    fin_cases k <;> rfl
  apply Finset.sum_congr rfl
  intro v _
  exact h (q v) (m v)

end BPFixedPoints.CechProduct
