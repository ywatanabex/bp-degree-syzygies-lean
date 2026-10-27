import BPFixedPoints.Incidence.SerreComparisonLineCells
import BPFixedPoints.Incidence.VertexProjectiveTwistZeroRouteAgreement
import BPFixedPoints.StrongField.SerreComparison

/-!
# The cup pairing H^1(ℙ¹, O(−k)) × H^0(ℙ¹, O(k−2)) → K in coordinates (`sf:serre-comparison`)

One vertex (`V = Unit`), a field K, and k = s + 2 ≥ 2, so r = k − 1 = s + 1. All cohomology is
the repository's Ext-defined sheaf cohomology `Sheaf.H` of the twist sheaves on ℙ¹ over K, and the
product is the standard product `vertexTwistStandardClassCup`.

* `h0Coord`: H^0(ℙ¹, O(s)) → B = K[w]/(w^{s+1}), the class of the left chart polynomial of the
  cell representative. It is bijective (`h0Coord_bijective`): global sections of O(s) are the
  polynomials of degree at most s = r − 1 (`h0OfPoly`, `h0Coord_h0OfPoly`, `exists_h0OfPoly`).
* `gapCoord s j`: the state coordinate of the Laurent gap monomial z^{−j−1} on H^1(ℙ¹, O(−(s+2))),
  0 ≤ j ≤ s; on a cell cocycle it is minus the coefficient of z^{−j−1} (`gapCoord_actual`).
* `minusTwoTrace`: H^1(ℙ¹, O(−2)) → K, the state coordinate of z^{−1}.
* `serreCup s`: the standard product H^1(O(−(s+2))) × H^0(O(s)) → H^1(O(−2)), transported along
  −(s+2) + s = −2 (`twist_add`), followed by `minusTwoTrace`.

Main result: `serreCup_h0OfPoly`, the pairing of x with the section z ↦ P(z) (deg P ≤ s) is
Σ_j P_j · gap_j(x). It is computed from the definition of the standard product through the
existing Yoneda comparison with the cell cup (`vertexTwistStandardClassCup_yoneda`) and the
one-vertex cell formulas of `SerreComparisonLineCells.lean`.

Not claimed here: the identification of H^1(O(−2)) with K is the chosen state coordinate, not a
canonical trace; the linear structure and perfectness are in `SerreComparisonProjectiveLine.lean`.
-/

namespace BPFixedPoints.SerreComparison
open CechProduct Polynomial LaurentPolynomial
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

/-- Coefficients of a Laurent polynomial times a polynomial of degree at most s. -/
theorem coeff_mul_toLaurent (s : ℕ) (F : K[T;T⁻¹]) (P : K[X]) (hP : P.natDegree ≤ s) (n : ℤ) :
    (F * toLaurent P).coeff n = ∑ j : Fin (s + 1), P.coeff j * F.coeff (n - j) := by
  conv_lhs => rw [P.as_sum_range' (s + 1) (by omega)]
  rw [map_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    ← Fin.sum_univ_eq_sum_range (fun j => (F * toLaurent (monomial j (P.coeff j))).coeff n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toLaurent_C_mul_T, mul_comm, mul_assoc, mul_comm (T _) F, ← mul_assoc, mul_comm, coeff_T_mul,
    ← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]

section Cohomology
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open SheafTools SheafTools.BinaryCells ProjectiveLine CechCubicalCell ExtResolutionTools
set_option maxRecDepth 8000

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

noncomputable local instance serreComparisonHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme K Unit)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The comparison of cell cohomology with Ext-defined cohomology, as an additive equivalence. -/
noncomputable def cellActualAddEquiv (a : Unit → ℤ) (n : ℕ) :
    vertexTwistCellCohomologyAt K Unit a n ≃+ Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n := by
  letI := vertexTwistCellAtModule K Unit a n
  letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n) :=
    SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit a) n
  exact (vertexTwistCellActualAtLinearEquiv K Unit a n).toAddEquiv

/-- The additive comparison is the existing linear comparison. -/
theorem cellActualAddEquiv_apply (a : Unit → ℤ) (n : ℕ) (z : vertexTwistCellCohomologyAt K Unit a n) :
    cellActualAddEquiv K a n z = vertexTwistCellActualAtLinearEquiv K Unit a n z := rfl

/-- The left chart polynomial of a degree-zero cocycle of O(s). -/
noncomputable def cycleLeftPoly (s : ℕ) :
    (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 →+ K[X] where
  toFun g := leftEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 g.val leftFace)
  map_zero' := by
    change leftEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 0 leftIndex.val) = 0
    rw [vertexTwistCellFaceCoefficient_sections, map_zero, Pi.zero_apply, map_zero, map_zero]
  map_add' g g' := by
    change leftEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (g.val + g'.val)
      leftIndex.val) = _
    rw [vertexTwistCellFaceCoefficient_add, map_add]
    rfl


/-- The degree-zero cocycle of the section z ↦ P(z) of O(s), for deg P ≤ s. -/
noncomputable def polyCycle (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 :=
  ⟨polyCochain K s P, polyCochain_mem K s P hP⟩

/-- The left chart polynomial of the cocycle of P is P. -/
theorem cycleLeftPoly_polyCycle (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    cycleLeftPoly K s (polyCycle K s P hP) = P := by
  change leftEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s P)
    leftFace) = P
  rw [polyCochain_left, AlgEquiv.apply_symm_apply]

/-- The left chart polynomial of a degree-zero cocycle of O(s) has degree at most s. -/
theorem natDegree_cycleLeftPoly_le (s : ℕ)
    (g : (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    (cycleLeftPoly K s g).natDegree ≤ s :=
  natDegree_le_of_toLaurent_eq K s ((mem_zeroCycles_iff_laurent K s g.val).1 g.property)

/-- Every degree-zero cocycle of O(s) is the cocycle of its left chart polynomial. -/
theorem polyCycle_cycleLeftPoly (s : ℕ)
    (g : (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    polyCycle K s (cycleLeftPoly K s g) (natDegree_cycleLeftPoly_le K s g) = g := by
  have hg := (mem_zeroCycles_iff_laurent K s g.val).1 g.property
  apply Subtype.ext
  apply zeroCochain_ext K (posTwist s)
  · change vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s _) leftFace = _
    rw [polyCochain_left]
    apply (leftEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · change vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s _) rightFace = _
    rw [polyCochain_right]
    apply (rightEquiv K).injective
    rw [AlgEquiv.apply_symm_apply]
    apply toLaurent_injective
    apply (invert (R := K)).injective
    apply (isUnit_T (s : ℤ)).mul_left_cancel
    rw [toLaurent_reversePoly K s _ (natDegree_cycleLeftPoly_le K s g)]
    exact hg

/-- The cohomology class of the section z ↦ P(z) of O(s), for deg P ≤ s. -/
noncomputable def h0OfPoly (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 :=
  vertexTwistCellActualAtLinearEquiv K Unit (posTwist s) 0 (polyCycle K s P hP)

/-- **Coordinates on H^0(ℙ¹, O(s)).** The class in B = K[w]/(w^{s+1}) of the left chart
polynomial of the cell representative. -/
noncomputable def h0Coord (s : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 →+ TruncLine K (s + 1) :=
  ((AdjoinRoot.mk (X ^ (s + 1) : K[X])).toAddMonoidHom.comp (cycleLeftPoly K s)).comp
    (cellActualAddEquiv K (posTwist s) 0).symm.toAddMonoidHom

/-- The coordinate of the section z ↦ P(z) is the class of P. -/
theorem h0Coord_h0OfPoly (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    h0Coord K s (h0OfPoly K s P hP) = AdjoinRoot.mk _ P := by
  change AdjoinRoot.mk _ (cycleLeftPoly K s
    ((cellActualAddEquiv K (posTwist s) 0).symm
      (cellActualAddEquiv K (posTwist s) 0 (polyCycle K s P hP)))) = _
  rw [AddEquiv.symm_apply_apply, cycleLeftPoly_polyCycle]

/-- Every class of H^0(ℙ¹, O(s)) is the class of a polynomial of degree at most s. -/
theorem exists_h0OfPoly (s : ℕ) (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    ∃ (P : K[X]) (hP : P.natDegree ≤ s), y = h0OfPoly K s P hP := by
  obtain ⟨g, rfl⟩ := (cellActualAddEquiv K (posTwist s) 0).surjective y
  refine ⟨cycleLeftPoly K s g, natDegree_cycleLeftPoly_le K s g, ?_⟩
  rw [h0OfPoly, polyCycle_cycleLeftPoly]
  rfl

/-- A polynomial of degree at most s divisible by w^{s+1} is zero. -/
theorem eq_of_mk_eq (s : ℕ) {P Q : K[X]} (hP : P.natDegree ≤ s) (hQ : Q.natDegree ≤ s)
    (h : AdjoinRoot.mk (X ^ (s + 1) : K[X]) P = AdjoinRoot.mk _ Q) : P = Q := by
  rw [AdjoinRoot.mk_eq_mk] at h
  have h0 := eq_zero_of_dvd_of_natDegree_lt h (by
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt (natDegree_sub_le P Q) (by omega))
  exact sub_eq_zero.mp h0

/-- Every element of B is the class of a polynomial of degree at most s. -/
theorem exists_mk_eq (s : ℕ) (f : TruncLine K (s + 1)) :
    ∃ P : K[X], P.natDegree ≤ s ∧ AdjoinRoot.mk _ P = f := by
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective f
  refine ⟨Q %ₘ X ^ (s + 1), ?_, ?_⟩
  · have h := natDegree_modByMonic_lt Q (monic_X_pow (s + 1)) (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow, natDegree_one] at this
      omega)
    rw [natDegree_X_pow] at h
    omega
  · rw [← AdjoinRoot.modByMonicHom_mk (monic_X_pow (s + 1))]
    exact AdjoinRoot.mk_leftInverse _ _

/-- **H^0(ℙ¹, O(s)) is the space of polynomials of degree at most s**, read in B = K[w]/(w^{s+1}). -/
theorem h0Coord_bijective (s : ℕ) : Function.Bijective (h0Coord K s) := by
  constructor
  · intro y y' h
    obtain ⟨P, hP, rfl⟩ := exists_h0OfPoly K s y
    obtain ⟨Q, hQ, rfl⟩ := exists_h0OfPoly K s y'
    rw [h0Coord_h0OfPoly, h0Coord_h0OfPoly] at h
    obtain rfl := eq_of_mk_eq K s hP hQ h
    rfl
  · intro f
    obtain ⟨P, hP, rfl⟩ := exists_mk_eq K s f
    exact ⟨h0OfPoly K s P hP, h0Coord_h0OfPoly K s P hP⟩


/-- The twist identity −(s+2) + s = −2. -/
theorem twist_add (s : ℕ) :
    (fun v => -((negTwist s v : ℕ) : ℤ)) + posTwist s = fun v => -((negTwist 0 v : ℕ) : ℤ) := by
  funext v
  simp only [Pi.add_apply]
  push_cast
  ring

/-- The state coordinate of the gap monomial z^{−1} on H^n(ℙ¹, O(−2)); in degree one this is the
trace H^1(ℙ¹, O(−2)) → K (`minusTwoTrace`). -/
noncomputable def minusTwoTraceAt (n : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ))) n →+ K where
  toFun z := (vertexTwistActualStateAt K Unit (negTwist 0) n z).val (fun _ => (0 : Fin 1))
  map_zero' := by
    rw [map_zero]
    rfl
  map_add' z z' := by
    rw [map_add]
    rfl

/-- The state coordinate of z^{−1} reads the actual state coordinates. -/
theorem minusTwoTraceAt_apply (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ))) n) :
    minusTwoTraceAt K n z =
      (vertexTwistActualStateAt K Unit (negTwist 0) n z).val (fun _ => (0 : Fin 1)) := rfl

/-- The trace H^1(ℙ¹, O(−2)) → K: the state coordinate of the gap monomial z^{−1}. -/
noncomputable abbrev minusTwoTrace :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ))) 1 →+ K :=
  minusTwoTraceAt K 1

/-- The gap coordinate j of H^1(ℙ¹, O(−(s+2))): the state coordinate of z^{−j−1}. -/
noncomputable def gapCoord (s : ℕ) (j : Fin (s + 1)) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 →+ K where
  toFun z := (vertexTwistActualStateAt K Unit (negTwist s) 1 z).val (fun _ => j)
  map_zero' := by
    rw [map_zero]
    rfl
  map_add' z z' := by
    rw [map_add]
    rfl

/-- The gap coordinate reads the state coordinate of z^{−j−1}. -/
theorem gapCoord_apply (s : ℕ) (j : Fin (s + 1))
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :
    gapCoord K s j z = (vertexTwistActualStateAt K Unit (negTwist s) 1 z).val (fun _ => j) := rfl

/-- **The cup pairing.** H^1(ℙ¹, O(−(s+2))) × H^0(ℙ¹, O(s)) → H^1(ℙ¹, O(−2)) → K, the standard
product on Ext-defined cohomology followed by the transport along −(s+2) + s = −2 and the trace. -/
noncomputable def serreCup (s : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 →+
      Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 →+ K :=
  (vertexTwistStandardClassCup K Unit _ (posTwist s) 1 0).compr₂
    ((minusTwoTraceAt K (1 + 0)).comp (vertexTwistHCast K Unit (twist_add s) (1 + 0)).toAddMonoidHom)

/-- The trace of a class given by a cell cocycle of twist −2 is minus the coefficient of z^{−1} of
its overlap coefficient. -/
theorem minusTwoTrace_actual (w : vertexTwistCellCycles K Unit (negTwist 0) 1) :
    minusTwoTrace K (vertexTwistCellActualAtLinearEquiv K Unit _ 1
        ((cubicalTower (vertexCoordinateOpen K Unit)).classAt _ 1 w)) =
      -(overlapEquiv K (vertexTwistCellFaceCoefficient K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ)) 1
        w.val overlapFace)).coeff (-1) := by
  have h := cycleProjection_gap K 0 w 0
  rw [← vertexTwistCellStateAt_class, ← vertexTwistActualStateAt_actual] at h
  rw [minusTwoTraceAt_apply, h]
  norm_num

/-- The gap coordinates of a class given by a cell cocycle. -/
theorem gapCoord_actual (s : ℕ) (j : Fin (s + 1)) (w : vertexTwistCellCycles K Unit (negTwist s) 1) :
    gapCoord K s j (vertexTwistCellActualAtLinearEquiv K Unit _ 1
        ((cubicalTower (vertexCoordinateOpen K Unit)).classAt _ 1 w)) =
      -(overlapEquiv K (vertexTwistCellFaceCoefficient K Unit (fun v => -((negTwist s v : ℕ) : ℤ)) 1
        w.val overlapFace)).coeff (-(j : ℤ) - 1) := by
  have h := cycleProjection_gap K s w j
  rw [← vertexTwistCellStateAt_class, ← vertexTwistActualStateAt_actual] at h
  rw [gapCoord_apply, h]


/-- **The cup pairing on cell representatives.** For a degree-one cocycle f of O(−(s+2)) and a
degree-zero cocycle g of O(s), the pairing is minus the coefficient of z^{−1} of the overlap
coefficient of the cell cup. -/
theorem serreCup_cell (s : ℕ) (f : vertexTwistCellCycles K Unit (negTwist s) 1)
    (g : (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    serreCup K s (vertexTwistCellActualAtLinearEquiv K Unit _ 1
        ((cubicalTower (vertexCoordinateOpen K Unit)).classAt _ 1 f))
      (vertexTwistCellActualAtLinearEquiv K Unit (posTwist s) 0 g) =
      -(overlapEquiv K (vertexTwistCellFaceCoefficient K Unit _ 1
        (vertexTwistCellCupAt K Unit _ (posTwist s) 1 1 0 f.val g.val) overlapFace)).coeff (-1) := by
  rw [serreCup, AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply]
  rw [← vertexTwistStandardClassCup_yoneda]
  let X := (vertexTwistCellCohomologyCupAt K Unit (fun v => -((negTwist s v : ℕ) : ℤ)) (posTwist s)
    (1 + 0) 1 0) ((cubicalTower (vertexCoordinateOpen K Unit)).classAt _ 1 f) g
  have key := vertexTwistHCast_mapAt K Unit (twist_add s) (1 + 0) X
    (fun c z => vertexTwistCellActualAtLinearEquiv K Unit c (1 + 0) z)
  have key' : (vertexTwistHCast K Unit (twist_add s) (1 + 0)).toAddMonoidHom
      (vertexTwistCellActualAtLinearEquiv K Unit _ (1 + 0) X) =
      vertexTwistCellActualAtLinearEquiv K Unit _ (1 + 0)
        ((cubicalTower (vertexCoordinateOpen K Unit)).mapAt
          (eqToHom (congrArg (vertexTwistAbelianSheaf K Unit) (twist_add s))) (1 + 0) X) := key.symm
  rw [key']
  have hc : X = (cubicalTower (vertexCoordinateOpen K Unit)).classAt _ (1 + 0)
      (cubicalCyclesCupAt (vertexCoordinateOpen K Unit)
        (vertexTwistAbelianSectionPairing K Unit (fun v => -((negTwist s v : ℕ) : ℤ)) (posTwist s))
        (1 + 0) 1 0 f g) :=
    vertexTwistCellCohomologyCupAt_class K Unit (fun v => -((negTwist s v : ℕ) : ℤ))
      (posTwist s) (1 + 0) 1 0 f g
  rw [hc, ExactTower.mapAt_class]
  have hm := minusTwoTrace_actual K ((cubicalTower (vertexCoordinateOpen K Unit)).mapCycles
    (eqToHom (congrArg (vertexTwistAbelianSheaf K Unit) (twist_add s))) (1 + 0)
    (cubicalCyclesCupAt (vertexCoordinateOpen K Unit)
      (vertexTwistAbelianSectionPairing K Unit (fun v => -((negTwist s v : ℕ) : ℤ)) (posTwist s))
      (1 + 0) 1 0 f g))
  refine hm.trans ?_
  rw [← vertexTwistCellFaceCoefficient_eqToHom K Unit _ _ (twist_add s)]
  rfl


/-- **The cup pairing in coordinates.** For deg P ≤ s, the pairing of x with the section
z ↦ P(z) is Σ_j P_j · gap_j(x). -/
theorem serreCup_h0OfPoly (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (P : K[X]) (hP : P.natDegree ≤ s) :
    serreCup K s x (h0OfPoly K s P hP) = ∑ j : Fin (s + 1), P.coeff j * gapCoord K s j x := by
  obtain ⟨z, rfl⟩ := (cellActualAddEquiv K _ 1).surjective x
  obtain ⟨f, rfl⟩ := (cubicalTower (vertexCoordinateOpen K Unit)).classAt_surjective _ 1 z
  rw [cellActualAddEquiv_apply, h0OfPoly, serreCup_cell]
  simp only [gapCoord_actual]
  rw [cellCup_overlap, map_mul, overlapEquiv_restrict_right]
  change -(overlapEquiv K _ * (T s * invert (toLaurent (rightEquiv K
    (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s P) rightFace))))).coeff (-1) = _
  rw [polyCochain_right, AlgEquiv.apply_symm_apply, toLaurent_reversePoly K s P hP,
    coeff_mul_toLaurent K s _ P hP, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg]
  congr 3
  ring

end Cohomology

end BPFixedPoints.SerreComparison
