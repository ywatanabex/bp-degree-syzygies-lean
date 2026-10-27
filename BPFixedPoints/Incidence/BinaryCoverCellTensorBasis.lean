import BPFixedPoints.Incidence.BinaryCoverCellTensorTerms
import BPFixedPoints.Incidence.BinaryCoverCellFree

/-! # The original supported cell generators determine the tensor comparison

Only the existing supported Finsupp coordinates are used. The actions are
the original module actions before constructing any tensor comparison.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance tensorBasisChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorBasisChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance tensorBasisPairedAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorBasisPairedModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- Original cell labels carry exactly the original availability and degree proofs. -/
noncomputable def cellCoordinates (W : Opens T) (n : ℕ) : chains U R W n ≃ₗ[R] CellIndex U W n →₀ R := by
  let e : chains U R W n ≃ₗ[R]
      supported R R {p | W ≤ binaryCoverFaceOpen U p ∧ cellDegree p = -(n : ℤ)} :=
    { toFun x := ⟨x.val,fun p hp => ⟨x.property.1 hp,x.property.2 hp⟩⟩
      invFun x := ⟨x.val,(fun p hp => (x.property hp).1),fun p hp => (x.property hp).2⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  exact e.trans (Finsupp.supportedEquivFinsupp _)

/-- Supported single coordinates retain the original cell itself and coefficient. -/
theorem cellCoordinates_symm_single (W : Opens T) (n : ℕ) (p : CellIndex U W n) (r : R) :
    ((cellCoordinates U R W n).symm (single p r)).val = single p.val r := by
  exact Finsupp.supportedEquivFinsupp_symm_single (R := R) _ p r

/-- The original degree proof can equally be read as the original overlap count. -/
theorem cellIndex_degree (W : Opens T) (n : ℕ) (p : CellIndex U W n) : faceDegree p.val=n := by
  have h := p.property.2
  change -(faceDegree p.val : ℤ) = -(n : ℤ) at h
  omega

/-- Each supported single coordinate is the specified original cell generator. -/
theorem cellCoordinates_generator (W : Opens T) (n : ℕ) (p : CellIndex U W n) (r : R) :
    (cellCoordinates U R W n).symm (single p r) =
      cellGenerator U R W n p.val p.property.1 (cellIndex_degree U W n p) r :=
  Subtype.ext (cellCoordinates_symm_single U R W n p r)

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Equality on every original cell generator determines the original linear map. -/
theorem cellLinear_ext (W : Opens T) (n : ℕ) (f g : chains U R W n →ₗ[R] M)
    (h : ∀ p hp hd r, f (cellGenerator U R W n p hp hd r) = g (cellGenerator U R W n p hp hd r)) : f = g := by
  have he : f.comp (cellCoordinates U R W n).symm.toLinearMap =
      g.comp (cellCoordinates U R W n).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro p r
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,cellCoordinates_generator] using
      h p.val p.property.1 (cellIndex_degree U W n p) r
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun he (cellCoordinates U R W n x)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hh

/-- Original available pair labels carry exactly the original two opens and total degree. -/
def PairCellIndex (W : Opens T) (n : ℕ) :=
  {z : (V → Fin 3) × (V → Fin 3) // W ≤ binaryCoverFaceOpen U z.1 ∧
    W ≤ binaryCoverFaceOpen U z.2 ∧ faceDegree z.1+faceDegree z.2=n}

/-- Original pair coordinates, retaining every original coefficient. -/
noncomputable def pairCellCoordinates (W : Opens T) (n : ℕ) :
    pairedChains U R W n ≃ₗ[R] PairCellIndex U W n →₀ R := Finsupp.supportedEquivFinsupp _

/-- Every original pair generator is its same original supported coordinate. -/
theorem pairCellCoordinates_generator (W : Opens T) (n : ℕ) (z : PairCellIndex U W n) (r : R) :
    (pairCellCoordinates U R W n).symm (single z r) =
      pairGenerator U R W n z.val.1 z.val.2 z.property.1 z.property.2.1 z.property.2.2 r := by
  apply Subtype.ext
  exact Finsupp.supportedEquivFinsupp_symm_single (R := R) _ z r

/-- Equality on all original pair generators determines the original linear map. -/
theorem pairLinear_ext (W : Opens T) (n : ℕ) (f g : pairedChains U R W n →ₗ[R] M)
    (h : ∀ p q hp hq hd r, f (pairGenerator U R W n p q hp hq hd r) =
      g (pairGenerator U R W n p q hp hq hd r)) : f = g := by
  have he : f.comp (pairCellCoordinates U R W n).symm.toLinearMap =
      g.comp (pairCellCoordinates U R W n).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro z r
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,pairCellCoordinates_generator] using
      h z.val.1 z.val.2 z.property.1 z.property.2.1 z.property.2.2 r
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun he (pairCellCoordinates U R W n x)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hh

/-- Each original coefficient is the original scalar multiple of the same coefficient-one cell. -/
theorem cellGenerator_smul (W : Opens T) (n : ℕ) (p : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hd : faceDegree p=n) (r : R) :
    cellGenerator U R W n p hp hd r = r • cellGenerator U R W n p hp hd 1 := by
  apply Subtype.ext
  simp [cellGenerator]

/-- The original coefficient-one generators determine each original cell map. -/
theorem cellLinear_ext_one (W : Opens T) (n : ℕ) (f g : chains U R W n →ₗ[R] M)
    (h : ∀ p hp hd, f (cellGenerator U R W n p hp hd 1) = g (cellGenerator U R W n p hp hd 1)) : f = g := by
  apply cellLinear_ext U R W n f g
  intro p hp hd r
  rw [cellGenerator_smul,map_smul,map_smul,h]

/-- Each original pair coefficient is the original scalar multiple of its coefficient-one pair. -/
theorem pairGenerator_smul (W : Opens T) (n : ℕ) (p q : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q=n) (r : R) :
    pairGenerator U R W n p q hp hq hd r = r • pairGenerator U R W n p q hp hq hd 1 := by
  apply Subtype.ext
  simp [pairGenerator]

/-- The original coefficient-one pair generators determine every original pair map. -/
theorem pairLinear_ext_one (W : Opens T) (n : ℕ) (f g : pairedChains U R W n →ₗ[R] M)
    (h : ∀ p q hp hq hd, f (pairGenerator U R W n p q hp hq hd 1) =
      g (pairGenerator U R W n p q hp hq hd 1)) : f = g := by
  apply pairLinear_ext U R W n f g
  intro p q hp hq hd r
  rw [pairGenerator_smul,map_smul,map_smul,h]

end BPFixedPoints.SheafTools.BinaryCells
