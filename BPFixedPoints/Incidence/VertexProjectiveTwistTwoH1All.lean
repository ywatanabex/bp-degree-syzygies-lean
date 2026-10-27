import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1States
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1ZeroSecond
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoNegativeCohomology

/-! # Actual H1 of every nonpositive two-vertex twist -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance allTwoH1HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual H1 of every nonpositive two-vertex twist equals its original degree-one state piece. -/
noncomputable def vertexTwistTwoH1StateEquiv (d : Fin 2 → ℕ) :
    vertexTwistTwoH1Module R d ≃ₗ[R] twoMiddleStatePiece R d :=
  if hd : d 1 = 0 then vertexTwistTwoH1ZeroSecondStateEquiv R d hd
  else vertexTwistTwoH1PositiveSecondStateEquiv R d (by omega)

/-- For negative second twist the all-twist comparison retains the specified original restriction-kernel route. -/
theorem vertexTwistTwoH1StateEquiv_of_pos (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoH1StateEquiv R d = vertexTwistTwoH1PositiveSecondStateEquiv R d hd := by
  simp only [vertexTwistTwoH1StateEquiv,dite_eq_right (Nat.ne_of_gt hd)]

/-- For zero second twist the all-twist comparison retains the specified original connecting-cokernel route. -/
theorem vertexTwistTwoH1StateEquiv_of_zero (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    vertexTwistTwoH1StateEquiv R d = vertexTwistTwoH1ZeroSecondStateEquiv R d hd := by
  simp only [vertexTwistTwoH1StateEquiv,dite_eq_left hd]

/-- Actual two-vertex H1 is free over the original geometric base for every nonpositive twist. -/
theorem vertexTwistTwoH1_free (d : Fin 2 → ℕ) : Module.Free R (vertexTwistTwoH1Module R d) :=
  Module.Free.of_equiv ((vertexTwistTwoH1StateEquiv R d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- Actual two-vertex H1 is finite over the original base, including zero twists and zero rings. -/
theorem vertexTwistTwoH1_finite (d : Fin 2 → ℕ) : Module.Finite R (vertexTwistTwoH1Module R d) := by
  classical
  exact Module.Finite.equiv ((vertexTwistTwoH1StateEquiv R d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- The actual geometric H1 rank of every nonpositive two-vertex twist, with natural subtraction. -/
theorem vertexTwistTwoH1_finrank [Nontrivial R] (d : Fin 2 → ℕ) :
    Module.finrank R (vertexTwistTwoH1Module R d) =
      (if d 0 = 0 then d 1-1 else 0) + (if d 1 = 0 then d 0-1 else 0) := by
  classical
  by_cases hd : d 1 = 0
  · rw [(vertexTwistTwoZeroSecondLineH1Equiv R d hd).finrank_eq]
    simp [CechLine.H1,CechLine.H1Index,hd]
  · rw [vertexTwistTwoH1PositiveSecond_finrank R d (by omega)]
    simp [hd]

/-- Any original minus-one factor annihilates actual H1, including when the other twist is zero. -/
theorem vertexTwistTwoH1_eq_zero_of_one (d : Fin 2 → ℕ) (v : Fin 2) (hv : d v = 1)
    (x : vertexTwistTwoH1Module R d) : x = 0 := by
  apply (vertexTwistTwoH1StateEquiv R d).injective
  apply Subtype.ext
  apply Finsupp.ext
  intro κ
  have he := (κ v).isLt
  have hz : phi (d v) = 0 := by rw [hv,phi_one]
  omega

/-- An original minus-one factor annihilates every actual group for all nonpositive two-vertex twists. -/
theorem vertexTwistTwo_cohomology_eq_zero_of_one (d : Fin 2 → ℕ) (v : Fin 2) (hv : d v = 1)
    (n : ℕ) (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H n) : x = 0 := by
  rcases n with _ | _ | _ | k
  · exact vertexTwistH0_eq_zero_of_pos R (Fin 2) d v (by omega) x
  · exact vertexTwistTwoH1_eq_zero_of_one R d v hv x
  · exact vertexTwistTwoH2_eq_zero_of_one_all R d v hv x
  · have he : Fintype.card (Fin 2)+k+1 = k+3 := by simp; omega
    have hz := vertexTwistSheaf_higher_cohomology_eq_zero R (Fin 2) (fun v => -(d v : ℤ)) k
    rw [he] at hz
    exact hz x

/-- Actual H1 of the original twist (-2,0) is the original base module through its original connecting map. -/
noncomputable def vertexTwistTwoH1_minus_two_zero :
    vertexTwistTwoH1Module R (![2,0] : Fin 2 → ℕ) ≃ₗ[R] R := by
  letI : Subsingleton (CechLine.H1Index (![2,0] 0)) := by change Subsingleton (Fin 1); infer_instance
  exact (vertexTwistTwoZeroSecondLineH1Equiv R (![2,0] : Fin 2 → ℕ) rfl).trans
    (Finsupp.uniqueLinearEquiv R R (0 : Fin 1))

/-- The actual original Laurent gap connecting representative of H1(-2,0) maps to its original scalar. -/
theorem vertexTwistTwoH1_minus_two_zero_representative (r : R) :
    vertexTwistTwoH1_minus_two_zero R
      (vertexTwistTwoZeroSecondCoefficientH1Equiv R (![2,0] : Fin 2 → ℕ) rfl
        (Submodule.Quotient.mk (AddMonoidAlgebra.single (-1 : ℤ) r))) = r := by
  change vertexTwistTwoZeroSecondLineH1Equiv R (![2,0] : Fin 2 → ℕ) rfl
    (vertexTwistTwoZeroSecondCoefficientH1Equiv R (![2,0] : Fin 2 → ℕ) rfl
      (Submodule.Quotient.mk (AddMonoidAlgebra.single (-1 : ℤ) r))) (0 : Fin 1) = r
  have he := vertexTwistTwoZeroSecondLineH1Equiv_gap R (![2,0] : Fin 2 → ℕ) rfl (0 : Fin 1) r
  have he0 := congrArg (fun z : CechLine.H1 R 2 => z (0 : Fin 1)) he
  simp only [Fin.val_zero,Nat.cast_zero,neg_zero,zero_sub,Finsupp.single_eq_same] at he0
  convert he0 using 1

end BPFixedPoints.ProjectiveLine
