import BPFixedPoints.Incidence.CechProductDegree
import BPFixedPoints.Incidence.CechCupSigns

/-! # The original degree-zero cocycles and the original degree-zero state piece -/

namespace BPFixedPoints.CechProduct
open Finsupp ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 500000
variable {V : Type} [Fintype V] (R : Type) [CommRing R]

/-- Degree-zero cocycles of the original coefficient complex. -/
noncomputable abbrev zeroCycleModule (d : V → ℕ) : Submodule R (C R V) :=
  supported R R {b | (cechDegree b : ℤ) = 0} ⊓ LinearMap.ker (contraction R d).d

/-- The degree-zero submodule of the original state module. -/
abbrev zeroStatePiece (d : V → ℕ) : Submodule R (H R d) :=
  supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = 0}

/-- The original homotopy is zero on degree-zero chains because it lowers degree. -/
theorem contraction_h_zero_degree (d : V → ℕ) (x : C R V)
    (hx : x ∈ supported R R {b | (cechDegree b : ℤ) = 0}) : (contraction R d).h x = 0 := by
  have he := contraction_h_degree R d 0 x hx
  apply Finsupp.ext
  intro b
  apply (mem_supported' R _).mp he
  change (cechDegree b : ℤ) ≠ 0+(-1)
  omega

/-- A closed original degree-zero chain is precisely its original inclusion-projection representative. -/
theorem zeroCycle_inclusion_projection (d : V → ℕ) (x : zeroCycleModule R d) :
    (contraction R d).i ((contraction R d).p x) = x := by
  have he := GradedContraction.ChainPairing.cycle_decomposition x.property.2
  rw [contraction_h_zero_degree R d x x.property.1,map_zero,zero_add] at he
  exact he.symm

/-- Original degree-zero cocycles equal the original degree-zero states, with the specified original maps. -/
noncomputable def zeroCycleStateEquiv (d : V → ℕ) : zeroCycleModule R d ≃ₗ[R] zeroStatePiece R d where
  toFun x := ⟨(contraction R d).p x, contraction_p_degree R d 0 x x.property.1⟩
  invFun s := ⟨(contraction R d).i s,
    ⟨contraction_i_degree R d 0 s s.property,LinearMap.congr_fun (contraction R d).d_i s⟩⟩
  left_inv x := Subtype.ext (zeroCycle_inclusion_projection R d x)
  right_inv s := Subtype.ext (LinearMap.congr_fun (contraction R d).p_i s)
  map_add' x y := Subtype.ext ((contraction R d).p.map_add x y)
  map_smul' r x := Subtype.ext ((contraction R d).p.map_smul r x)

/-- Every cocycle has its original projection as its state coordinate. -/
theorem zeroCycleStateEquiv_val (d : V → ℕ) (x : zeroCycleModule R d) :
    (zeroCycleStateEquiv R d x).val = (contraction R d).p x := rfl

/-- Every degree-zero state retains its original contraction inclusion. -/
theorem zeroCycleStateEquiv_symm_val (d : V → ℕ) (s : zeroStatePiece R d) :
    ((zeroCycleStateEquiv R d).symm s).val = (contraction R d).i s := rfl

/-- The original state degree is zero exactly when every original twist entry is zero. -/
theorem cohomologyDegree_zero_iff (d : V → ℕ) : cohomologyDegree d = 0 ↔ ∀ v, d v = 0 := by
  simp [cohomologyDegree,lineCohomologyDegree,Finset.sum_eq_zero_iff]

/-- Any positive twist parameter makes the original degree-zero state piece vanish. -/
theorem zeroStatePiece_eq_zero_of_pos (d : V → ℕ) (v : V) (hv : 0 < d v)
    (s : zeroStatePiece R d) : s = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro κ
  apply (mem_supported' R _).mp s.property
  change (cohomologyDegree d : ℤ) ≠ 0
  have he : cohomologyDegree d ≠ 0 := by
    intro h
    have hh := (cohomologyDegree_zero_iff d).mp h v
    omega
  exact_mod_cast he

end BPFixedPoints.CechProduct
