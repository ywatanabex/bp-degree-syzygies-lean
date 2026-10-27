import BPFixedPoints.Incidence.ResolutionTorUnit
import BPFixedPoints.Incidence.ResolutionTorAssociativity
import BPFixedPoints.Incidence.ResolutionTorCommutativity
import Mathlib.Algebra.DirectSum.Algebra

/-!
# Graded algebra on the direct sum of actual Tor spaces

Package the unit, associativity and bilinearity in Mathlib's graded ring
structure. Commutativity carries the homological Koszul sign rather than
ordinary commutativity.
-/
namespace BPFixedPoints.Multigraph
open CategoryTheory
open scoped DirectSum

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incidenceTor_mk_eq {p q : ℕ} (h : p = q) (x : G.incidenceTor p) (y : G.incidenceTor q)
    (hxy : G.incidenceTorCast h x = y) :
    GradedMonoid.mk (A := fun n => G.incidenceTor n) p x = GradedMonoid.mk q y := by
  subst q
  change x = y at hxy
  exact congrArg (GradedMonoid.mk p) hxy

noncomputable instance incidenceTorGOne : GradedMonoid.GOne (fun n => G.incidenceTor n) :=
  ⟨G.incidenceTorOne⟩

noncomputable instance incidenceTorGMul : GradedMonoid.GMul (fun n => G.incidenceTor n) where
  mul {p q} x y := G.incidenceTorProduct p q x y

noncomputable instance incidenceTorGradedRing : DirectSum.GRing (fun n => G.incidenceTor n) where
  one := G.incidenceTorOne
  mul {p q} x y := G.incidenceTorProduct p q x y
  mul_zero := by intros; exact map_zero _
  zero_mul := by intros; simp
  mul_add := by intros; exact map_add _ _ _
  add_mul := by intros; rw [map_add, LinearMap.add_apply]
  one_mul := by
    rintro ⟨p,x⟩
    exact G.incidenceTor_mk_eq (Nat.zero_add p) _ _ (G.incidenceTorOne_mul p x)
  mul_one := by
    rintro ⟨p,x⟩
    exact G.incidenceTor_mk_eq rfl _ _ (G.incidenceTor_mul_one p x)
  mul_assoc := by
    rintro ⟨p,x⟩ ⟨q,y⟩ ⟨r,z⟩
    exact G.incidenceTor_mk_eq (Nat.add_assoc p q r) _ _ (G.incidenceTorProduct_assoc p q r x y z)
  natCast n := n • G.incidenceTorOne
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • G.incidenceTorOne
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := negSucc_zsmul _ _

/-- Standard Tor algebra of the original incidence ring on the homological direct sum. -/
noncomputable abbrev IncidenceTorAlgebra := ⨁ n : ℕ, G.incidenceTor n

noncomputable instance incidenceTorGradedAlgebra : DirectSum.GAlgebra ℂ (fun n => G.incidenceTor n) where
  toFun := (LinearMap.toSpanSingleton ℂ _ G.incidenceTorOne).toAddMonoidHom
  map_one := one_smul _ _
  map_mul r s := by
    apply G.incidenceTor_mk_eq rfl
    change (r * s) • G.incidenceTorOne = G.incidenceTorProduct 0 0
      (r • G.incidenceTorOne) (s • G.incidenceTorOne)
    rw [LinearMap.map_smul₂, map_smul, G.incidenceTor_mul_one, smul_smul]
  commutes r x := by
    rcases x with ⟨p,x⟩
    apply G.incidenceTor_mk_eq (Nat.zero_add p)
    change G.incidenceTorCast (Nat.zero_add p)
      (G.incidenceTorProduct 0 p (r • G.incidenceTorOne) x) =
      G.incidenceTorProduct p 0 x (r • G.incidenceTorOne)
    rw [LinearMap.map_smul₂, map_smul, map_smul, G.incidenceTorOne_mul, G.incidenceTor_mul_one]
  smul_def r x := by
    rcases x with ⟨p,x⟩
    symm
    apply G.incidenceTor_mk_eq (Nat.zero_add p)
    change G.incidenceTorCast (Nat.zero_add p)
      (G.incidenceTorProduct 0 p (r • G.incidenceTorOne) x) = r • x
    rw [LinearMap.map_smul₂, map_smul, G.incidenceTorOne_mul]

noncomputable instance : Ring G.IncidenceTorAlgebra := inferInstance
noncomputable instance : Algebra ℂ G.IncidenceTorAlgebra := inferInstance

theorem incidenceTorAlgebra_of_mul (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    DirectSum.of (fun n => G.incidenceTor n) p x * DirectSum.of (fun n => G.incidenceTor n) q y =
      DirectSum.of (fun n => G.incidenceTor n) (p + q) (G.incidenceTorProduct p q x y) :=
  by
    exact DirectSum.of_mul_of (A := fun n => G.incidenceTor n) x y

theorem incidenceTorAlgebra_graded_comm (p q : ℕ)
    (x : G.incidenceTor p) (y : G.incidenceTor q) :
    DirectSum.of (fun n => G.incidenceTor n) p x * DirectSum.of (fun n => G.incidenceTor n) q y =
      (-1 : ℂ) ^ (p * q) •
        (DirectSum.of (fun n => G.incidenceTor n) q y * DirectSum.of (fun n => G.incidenceTor n) p x) := by
  rw [G.incidenceTorAlgebra_of_mul, G.incidenceTorAlgebra_of_mul]
  have h := DirectSum.of_eq_of_gradedMonoid_eq
    (G.incidenceTor_mk_eq (Nat.add_comm p q) _ _ (G.incidenceTorProduct_graded_comm p q x y))
  exact h.trans (DirectSum.of_smul ℂ _ _ _)

end BPFixedPoints.Multigraph
