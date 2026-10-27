import BPFixedPoints.Incidence.VertexProjectiveTwistStateProduct
import BPFixedPoints.Incidence.CechProductCupStatePieces

/-! # Transfer of product laws from state coordinates to actual cohomology

For nonpositive twists the standard product, followed by the original twist
identity, is the product of the actual cohomology of the family of twists
-d. Its state coordinates are the existing state product and the state
coordinates are injective in every degree. Hence any associativity, graded
commutativity or unit law of the state product, stated with explicit
transports of twists and degrees, holds for the standard product on actual
cohomology. The product is geometric; only its laws are read off through
the injective comparison.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct Finsupp
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexProductTransferHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Transport of actual cohomology of nonpositive twists along equalities of twists and degrees. -/
def vertexNegativeHCast {d d' : V → ℕ} (h : d = d') {n n' : ℕ} (hn : n = n') :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n ≃+
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d' v : ℤ))) n' := by
  subst h
  subst hn
  exact AddEquiv.refl _

variable [IsNoetherianRing R]

/-- The product of actual cohomology of nonpositive twists: the standard product followed by the original twist identity. -/
def vertexNegativeProduct (d e : V → ℕ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -((d+e) v : ℤ))) (i+j) :=
  vertexTwistHCast R V (vertexTwistNegativeAdd V d e) (i+j) (vertexTwistStandardClassCup R V _ _ i j x y)

/-- The state coordinate of the product is the existing state product. -/
theorem vertexNegativeProduct_state (d e : V → ℕ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j) :
    (vertexTwistActualStateAt R V (d+e) (i+j) (vertexNegativeProduct R V d e i j x y)).val =
      cohomologyCup R d e (vertexTwistActualStateAt R V d i x).val (vertexTwistActualStateAt R V e j y).val :=
  vertexTwistActualStateAt_standardCup R V d e i j x y

/-- State coordinates commute with the transports of twists and degrees. -/
theorem vertexTwistActualStateAt_cast {d d' : V → ℕ} (h : d = d') {n n' : ℕ} (hn : n = n')
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    (vertexTwistActualStateAt R V d' n' (vertexNegativeHCast R V h hn x)).val =
      castH R h (vertexTwistActualStateAt R V d n x).val := by
  subst h
  subst hn
  rfl

/-- Associativity of the state product, with the transport of twists, gives associativity of the actual product. -/
theorem vertexNegativeProduct_assoc
    (hassoc : ∀ (d e f : V → ℕ) (s : H R d) (t : H R e) (u : H R f),
      castH R (add_assoc d e f) (cohomologyCup R (d+e) f (cohomologyCup R d e s t) u) =
        cohomologyCup R d (e+f) s (cohomologyCup R e f t u))
    (d e f : V → ℕ) (i j k : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(f v : ℤ))) k) :
    vertexNegativeHCast R V (add_assoc d e f) (add_assoc i j k)
        (vertexNegativeProduct R V (d+e) f (i+j) k (vertexNegativeProduct R V d e i j x y) z) =
      vertexNegativeProduct R V d (e+f) i (j+k) x (vertexNegativeProduct R V e f j k y z) := by
  apply vertexTwistActualStateAt_injective R V (d+(e+f)) (i+(j+k))
  apply Subtype.ext
  rw [vertexTwistActualStateAt_cast,vertexNegativeProduct_state,vertexNegativeProduct_state,
    vertexNegativeProduct_state,vertexNegativeProduct_state]
  exact hassoc d e f _ _ _

/-- Graded commutativity of the state product on state degree pieces gives graded commutativity of the actual product. -/
theorem vertexNegativeProduct_comm
    (hcomm : ∀ (d e : V → ℕ) (i j : ℕ) (s : H R d) (t : H R e),
      s ∈ stateDegreePiece R d i → t ∈ stateDegreePiece R e j →
        cohomologyCup R e d t s = ((i*j : ℕ) : ℤ).negOnePow • castH R (add_comm d e) (cohomologyCup R d e s t))
    (d e : V → ℕ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j) :
    vertexNegativeProduct R V e d j i y x =
      ((i*j : ℕ) : ℤ).negOnePow • vertexNegativeHCast R V (add_comm d e) (add_comm i j)
        (vertexNegativeProduct R V d e i j x y) := by
  apply vertexTwistActualStateAt_injective R V (e+d) (j+i)
  apply Subtype.ext
  rw [Units.smul_def,map_zsmul,Submodule.coe_smul_of_tower,vertexTwistActualStateAt_cast,
    vertexNegativeProduct_state,vertexNegativeProduct_state,
    hcomm d e i j _ _ (vertexTwistActualStateAt R V d i x).property (vertexTwistActualStateAt R V e j y).property,
    Units.smul_def]

omit [DecidableEq V] [IsNoetherianRing R] in
/-- Graded commutativity of the state product on state degree pieces, with an integer sign. -/
theorem cohomologyCup_comm_negOnePow (d e : V → ℕ) (i j : ℕ) (s : H R d) (t : H R e)
    (hs : s ∈ stateDegreePiece R d i) (ht : t ∈ stateDegreePiece R e j) :
    cohomologyCup R e d t s = ((i*j : ℕ) : ℤ).negOnePow • castH R (add_comm d e) (cohomologyCup R d e s t) := by
  rw [cohomologyCup_comm_of_mem_stateDegreePiece R d e hs ht,Units.smul_def,Int.coe_negOnePow_natCast,
    ← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

/-- The product of actual cohomology of nonpositive twists is associative, with the transport of twists and degrees. -/
theorem vertexNegativeProduct_assoc' (d e f : V → ℕ) (i j k : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(f v : ℤ))) k) :
    vertexNegativeHCast R V (add_assoc d e f) (add_assoc i j k)
        (vertexNegativeProduct R V (d+e) f (i+j) k (vertexNegativeProduct R V d e i j x y) z) =
      vertexNegativeProduct R V d (e+f) i (j+k) x (vertexNegativeProduct R V e f j k y z) :=
  vertexNegativeProduct_assoc R V (cohomologyCup_assoc R) d e f i j k x y z

/-- The product of actual cohomology of nonpositive twists is graded commutative with the sign (-1)^(ij). -/
theorem vertexNegativeProduct_comm' (d e : V → ℕ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) j) :
    vertexNegativeProduct R V e d j i y x =
      ((i*j : ℕ) : ℤ).negOnePow • vertexNegativeHCast R V (add_comm d e) (add_comm i j)
        (vertexNegativeProduct R V d e i j x y) :=
  vertexNegativeProduct_comm R V (cohomologyCup_comm_negOnePow R V) d e i j x y

/-- The unit of actual cohomology of twist zero: the original degree-zero cell cocycle of the state unit. -/
def vertexNegativeUnit : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -((0 : V → ℕ) v : ℤ))) 0 :=
  vertexTwistCellActualAtLinearEquiv R V _ 0
    (vertexTwistCellStateInclusion R V 0 0 ⟨cohomologyUnit R,cohomologyUnit_mem_stateDegreePiece R⟩)

/-- The state coordinate of the unit is the state unit. -/
theorem vertexNegativeUnit_state :
    (vertexTwistActualStateAt R V 0 0 (vertexNegativeUnit R V)).val = cohomologyUnit R := by
  rw [vertexNegativeUnit,vertexTwistActualStateAt_actual]
  change (vertexTwistCellCycleProjection R V 0 0 (vertexTwistCellStateInclusion R V 0 0 _)).val = _
  rw [vertexTwistCellCycleProjection_inclusion]

omit [IsNoetherianRing R] in
/-- The original cell representative of the unit has, in original coefficients, the per-vertex constant one on both charts. -/
theorem vertexNegativeUnit_coefficient :
    (vertexTwistCellCoefficientEquiv R V 0 0 (vertexTwistCellStateInclusion R V 0 0
      ⟨cohomologyUnit R,cohomologyUnit_mem_stateDegreePiece R⟩).val).val = chainUnit R := by
  rw [vertexTwistCellStateInclusion_coefficient]
  change (contraction R 0).i ((contraction R 0).p (chainUnit R)) = chainUnit R
  have hom := LinearMap.congr_fun (contraction R (0 : V → ℕ)).homotopy (chainUnit R)
  have hh : (contraction R (0 : V → ℕ)).h (chainUnit R) = 0 := by
    have hdeg : chainUnit R ∈ supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = 0} := by
      classical
      rw [chainUnit]
      refine Submodule.sum_mem _ fun s _ => ?_
      apply Finsupp.single_mem_supported
      simp [cechDegree,lineDegree_unitBasis]
    have hm := contraction_h_degree R (0 : V → ℕ) 0 (chainUnit R) hdeg
    rw [Finsupp.mem_supported] at hm
    ext b
    by_contra hb
    have := hm (Finsupp.mem_support_iff.mpr hb)
    simp only [Set.mem_ofPred_eq] at this
    omega
  simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.comp_apply,Module.End.one_apply,
    hh,contraction_d_chainUnit,map_zero,zero_add] at hom
  exact hom

/-- Left unit law for the product of actual cohomology. -/
theorem vertexNegativeProduct_unit_left (d : V → ℕ) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    vertexNegativeHCast R V (zero_add d) (zero_add n) (vertexNegativeProduct R V 0 d 0 n (vertexNegativeUnit R V) x) = x := by
  apply vertexTwistActualStateAt_injective R V d n
  apply Subtype.ext
  rw [vertexTwistActualStateAt_cast,vertexNegativeProduct_state,vertexNegativeUnit_state,cohomologyCup_unit_left]

/-- Right unit law for the product of actual cohomology. -/
theorem vertexNegativeProduct_unit_right (d : V → ℕ) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    vertexNegativeHCast R V (add_zero d) (add_zero n) (vertexNegativeProduct R V d 0 n 0 x (vertexNegativeUnit R V)) = x := by
  apply vertexTwistActualStateAt_injective R V d n
  apply Subtype.ext
  rw [vertexTwistActualStateAt_cast,vertexNegativeProduct_state,vertexNegativeUnit_state,cohomologyCup_unit_right]
  rfl

end
end BPFixedPoints.ProjectiveLine
