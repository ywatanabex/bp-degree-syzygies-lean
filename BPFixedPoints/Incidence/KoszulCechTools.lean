import BPFixedPoints.Incidence.KoszulLinear
import BPFixedPoints.Incidence.PerturbationSum

/-! # Total complex of statewise Čech and Koszul differentials -/

namespace BPFixedPoints.Koszul

variable {E R W : Type*} [LinearOrder E] [Fintype E] [CommRing R]
  [AddCommGroup W] [Module R W]

/-- Direct sum of statewise linear maps. -/
noncomputable def diagonal (f : Finset E → Module.End R W) :
    Module.End R (Space E W) :=
  Finsupp.lsum R fun S => (Finsupp.lsingle S).comp (f S)

@[simp] theorem diagonal_single (f : Finset E → Module.End R W)
    (S : Finset E) (x : W) :
    diagonal f (Finsupp.single S x) = Finsupp.single S (f S x) := by
  simp [diagonal, Finsupp.lsum_single]

theorem diagonal_mul (f g : Finset E → Module.End R W) :
    diagonal f * diagonal g = diagonal (fun S => f S * g S) := by
  apply Finsupp.lhom_ext
  intro S x
  simp [Module.End.mul_apply]

@[simp] theorem diagonal_zero : diagonal (fun _ : Finset E => (0 : Module.End R W)) = 0 := by
  apply Finsupp.lhom_ext
  intro S x
  simp

theorem diagonal_add (f g : Finset E → Module.End R W) :
    diagonal (fun S => f S + g S) = diagonal f + diagonal g := by
  apply Finsupp.lhom_ext
  intro S x
  simp

theorem diagonal_neg (f : Finset E → Module.End R W) :
    diagonal (fun S => -f S) = -diagonal f := by
  apply Finsupp.lhom_ext
  intro S x
  simp

@[simp] theorem diagonal_one : diagonal (fun _ : Finset E => (1 : Module.End R W)) = 1 := by
  apply Finsupp.lhom_ext
  intro S x
  simp

theorem diagonal_sq (f : Finset E → Module.End R W) (hf : ∀ S, f S * f S = 0) :
    diagonal f * diagonal f = 0 := by rw [diagonal_mul]; simp only [hf, diagonal_zero]

theorem diagonal_linearTerm (d : Finset E → Module.End R W) (e : E)
    (f : Module.End R W)
    (hf : ∀ S, e ∈ S → d (S.erase e) * f = f * d S) :
    diagonal d * linearTerm e f = linearTerm e f * diagonal d := by
  apply Finsupp.lhom_ext
  intro S x
  simp only [Module.End.mul_apply, linearTerm_single, diagonal_single]
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, diagonal_single, map_smul]
    have hh := LinearMap.congr_fun (hf S he) x
    change d (S.erase e) (f x) = f (d S x) at hh
    rw [hh]
  · simp [he]

theorem diagonal_differentialLinear (d : Finset E → Module.End R W)
    (f : E → Module.End R W)
    (hf : ∀ S e, e ∈ S → d (S.erase e) * f e = f e * d S) :
    diagonal d * differentialLinear f = differentialLinear f * diagonal d := by
  unfold differentialLinear
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  exact diagonal_linearTerm d e (f e) fun S he => hf S e he

/-- Koszul part of the total differential, multiplied by Čech-degree parity. -/
noncomputable def signedDifferential (sign : Finset E → Module.End R W) (f : E → Module.End R W) :
    Module.End R (Space E W) := diagonal sign * differentialLinear f

theorem total_differential_sq (d : Finset E → Module.End R W)
    (sign : Finset E → Module.End R W) (f : E → Module.End R W)
    (hd : ∀ S, d S * d S = 0)
    (hf : ∀ e j, Commute (f e) (f j))
    (hdf : ∀ S e, e ∈ S → d (S.erase e) * f e = f e * d S)
    (hsf : ∀ S e, e ∈ S → sign (S.erase e) * f e = f e * sign S)
    (hds : ∀ S, d S * sign S = -(sign S * d S)) :
    (diagonal d + signedDifferential sign f) *
      (diagonal d + signedDifferential sign f) = 0 := by
  have hdd := diagonal_sq d hd
  have hkk := differentialLinear_sq f hf
  have hdk := diagonal_differentialLinear d f hdf
  have hsk := diagonal_differentialLinear sign f hsf
  have hds' : diagonal d * diagonal sign =
      -(diagonal sign * diagonal d) := by
    rw [diagonal_mul, diagonal_mul, ← diagonal_neg]
    congr 1
    funext S
    exact hds S
  have hss : signedDifferential sign f * signedDifferential sign f = 0 := by
    unfold signedDifferential
    calc
      _ = diagonal sign * (differentialLinear f * diagonal sign) *
          differentialLinear f := by simp only [mul_assoc]
      _ = diagonal sign * (diagonal sign * differentialLinear f) *
          differentialLinear f := by rw [← hsk]
      _ = (diagonal sign * diagonal sign) *
          (differentialLinear f * differentialLinear f) := by simp only [mul_assoc]
      _ = 0 := by rw [hkk, mul_zero]
  have hdsigned : diagonal d * signedDifferential sign f =
      -(signedDifferential sign f * diagonal d) := by
    apply LinearMap.ext
    intro x
    have hs := LinearMap.congr_fun hds' (differentialLinear f x)
    have hk := LinearMap.congr_fun hdk x
    change diagonal d (differentialLinear f x) = differentialLinear f (diagonal d x) at hk
    change diagonal d (diagonal sign (differentialLinear f x)) =
      -(diagonal sign (diagonal d (differentialLinear f x))) at hs
    change diagonal d (diagonal sign (differentialLinear f x)) =
      -(diagonal sign (differentialLinear f (diagonal d x)))
    rw [hs, hk]
  rw [add_mul, mul_add, mul_add, hdd, hss, zero_add, add_zero,
    hdsigned, neg_add_cancel]

end BPFixedPoints.Koszul
