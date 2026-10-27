import BPFixedPoints.Incidence.VertexProjectiveTwistStateProduct
import BPFixedPoints.Incidence.VertexProjectiveTwistCupCoefficientFaces
import BPFixedPoints.Incidence.CechProductProjectionCoefficients
import Mathlib.Algebra.Polynomial.Laurent

/-!
# One-vertex cell cochains of twists in polynomial and Laurent coordinates (`sf:serre-comparison`)

For a single vertex (`V = Unit`) and a field K, the cubical cell complex of the standard chart
cover of ℙ¹ has two cells of degree zero (the left and right charts) and one cell of degree one
(their overlap). This file makes the existing face coordinates of the twist sheaves concrete:

* the face rings of the two charts are K[z] and K[u], and that of the overlap is K[z, z⁻¹]
  (`leftEquiv`, `rightEquiv`, `overlapEquiv`, algebra isomorphisms);
* the existing restriction maps with their frame units become z ↦ z from the left chart and, for
  the twist s ≥ 0, u ↦ z⁻¹ followed by multiplication by z^s from the right chart
  (`overlapEquiv_restrict_left`, `overlapEquiv_restrict_right`);
* a degree-zero cochain of O(s) is a cocycle iff its chart polynomials satisfy
  L(z) = z^s R(1/z) (`mem_zeroCycles_iff_laurent`); then deg L ≤ s
  (`natDegree_le_of_toLaurent_eq`), and every polynomial P of degree ≤ s gives the cocycle
  `polyCochain` with chart polynomials P and its reversal (`polyCochain_mem`);
* on the overlap, the cell cup of a degree-one cochain f and a degree-zero cochain g is f times the
  restriction of the right chart coefficient of g (`cellCup_overlap`), read off the existing
  mixed-face formula `vertexTwistCellCupAt_face` (the diagonal term has sign +1);
* the state coordinate j of a degree-one cocycle of O(−(s+2)) is minus the coefficient of
  z^{−j−1} of its overlap coefficient (`cycleProjection_gap`).

These are statements about the existing cell representatives only. The comparison with
Ext-defined cohomology and the cup pairing is `SerreComparisonProjectiveLine.lean`.
-/

namespace BPFixedPoints.SerreComparison
open CechProduct Polynomial LaurentPolynomial
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

/-- The overlap face of the single vertex. -/
abbrev overlapFace : Unit → Fin 3 := fun _ => 2
/-- The left chart face of the single vertex (coordinate z). -/
abbrev leftFace : Unit → Fin 3 := fun _ => 0
/-- The right chart face of the single vertex (coordinate u = z⁻¹). -/
abbrev rightFace : Unit → Fin 3 := fun _ => 1

/-- Overlap exponents of one vertex are integers. -/
def overlapExponentEquiv : FaceMonoid overlapFace ≃+ ℤ :=
  (AddEquiv.piUnique fun _ : Unit => FaceExponent 2).trans (AddEquiv.refl ℤ)
/-- Left chart exponents of one vertex are natural numbers. -/
def leftExponentEquiv : FaceMonoid leftFace ≃+ ℕ :=
  (AddEquiv.piUnique fun _ : Unit => FaceExponent 0).trans (AddEquiv.refl ℕ)
/-- Right chart exponents of one vertex are natural numbers. -/
def rightExponentEquiv : FaceMonoid rightFace ≃+ ℕ :=
  (AddEquiv.piUnique fun _ : Unit => FaceExponent 1).trans (AddEquiv.refl ℕ)

/-- The overlap face ring of one vertex is the Laurent polynomial ring K[z, z⁻¹]. -/
noncomputable def overlapEquiv : FaceRing K overlapFace ≃ₐ[K] K[T;T⁻¹] :=
  AddMonoidAlgebra.domCongr K K (overlapExponentEquiv)

/-- The left chart face ring of one vertex is K[z]. -/
noncomputable def leftEquiv : FaceRing K leftFace ≃ₐ[K] K[X] :=
  (AddMonoidAlgebra.domCongr K K leftExponentEquiv).trans (toFinsuppIsoAlg K).symm

/-- The right chart face ring of one vertex is K[u]. -/
noncomputable def rightEquiv : FaceRing K rightFace ≃ₐ[K] K[X] :=
  (AddMonoidAlgebra.domCongr K K rightExponentEquiv).trans (toFinsuppIsoAlg K).symm

/-- A monomial of the overlap face is a Laurent monomial. -/
theorem overlapEquiv_single (m : FaceMonoid overlapFace) (c : K) :
    overlapEquiv K (AddMonoidAlgebra.single m c) = LaurentPolynomial.C c * T (m ()) := by
  rw [overlapEquiv, AddMonoidAlgebra.domCongr_single, ← single_eq_C_mul_T]
  rfl

/-- Mathlib's identification K[ℕ] ≅ K[X] sends a single to a monomial. -/
theorem toFinsuppIsoAlg_symm_single (n : ℕ) (c : K) :
    (toFinsuppIsoAlg K).symm (AddMonoidAlgebra.single n c) = monomial n c := by
  rw [AlgEquiv.symm_apply_eq, toFinsuppIsoAlg_apply, toFinsupp_monomial]

/-- A monomial of the left chart face is a polynomial monomial. -/
theorem leftEquiv_single (m : FaceMonoid leftFace) (c : K) :
    leftEquiv K (AddMonoidAlgebra.single m c) = monomial (leftExponentEquiv m) c := by
  rw [leftEquiv, AlgEquiv.trans_apply, AddMonoidAlgebra.domCongr_single, toFinsuppIsoAlg_symm_single]

/-- A monomial of the right chart face is a polynomial monomial. -/
theorem rightEquiv_single (m : FaceMonoid rightFace) (c : K) :
    rightEquiv K (AddMonoidAlgebra.single m c) = monomial (rightExponentEquiv m) c := by
  rw [rightEquiv, AlgEquiv.trans_apply, AddMonoidAlgebra.domCongr_single, toFinsuppIsoAlg_symm_single]

/-- The overlap exponent is the integer at the vertex. -/
theorem overlapExponentEquiv_apply (m : FaceMonoid overlapFace) :
    overlapExponentEquiv m = m () := rfl

/-- Integer exponents of the overlap face. -/
theorem faceToInt_overlap (m : FaceMonoid overlapFace) :
    faceToInt overlapFace m () = overlapExponentEquiv m := rfl

/-- Integer exponents of the left chart face. -/
theorem faceToInt_left (m : FaceMonoid leftFace) :
    faceToInt leftFace m () = (leftExponentEquiv m : ℤ) := rfl

/-- Integer exponents of the right chart face. -/
theorem faceToInt_right (m : FaceMonoid rightFace) :
    faceToInt rightFace m () = (rightExponentEquiv m : ℤ) := rfl

/-- The frame transition from the left chart to the overlap is trivial. -/
theorem multiTwistTransition_left (h : FaceRefines leftFace overlapFace) (a : Unit → ℤ) :
    multiTwistTransition K h a = 1 := by
  simp [multiTwistTransition, faceTransitionUnit]

/-- Left chart exponents restrict to the same overlap exponents. -/
theorem refinementExponent_left (h : FaceRefines leftFace overlapFace) (m : FaceMonoid leftFace) :
    overlapExponentEquiv (refinementExponent h m) = (leftExponentEquiv m : ℤ) := by
  rw [← faceToInt_overlap, faceToInt_refinement, faceToInt_left]
  simp

/-- Right chart exponents restrict to their negatives on the overlap. -/
theorem refinementExponent_right (h : FaceRefines rightFace overlapFace) (m : FaceMonoid rightFace) :
    overlapExponentEquiv (refinementExponent h m) = -(rightExponentEquiv m : ℤ) := by
  rw [← faceToInt_overlap, faceToInt_refinement, faceToInt_right]
  simp

/-- Restriction from the left chart to the overlap is the inclusion K[z] → K[z, z⁻¹]. -/
theorem overlapEquiv_restrict_left (h : FaceRefines leftFace overlapFace) (a : Unit → ℤ)
    (x : FaceRing K leftFace) :
    overlapEquiv K (multiTwistFaceRestriction K h a x) = toLaurent (leftEquiv K x) := by
  rw [multiTwistFaceRestriction_apply, multiTwistTransition_left, inv_one, Units.val_one, mul_one]
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single m c =>
    rw [faceRefinementMap_single, overlapEquiv_single, leftEquiv_single, toLaurent_C_mul_T,
      ← refinementExponent_left h]
    rfl

/-- The overlap variable is the Laurent variable z. -/
theorem overlapEquiv_faceVariable :
    overlapEquiv K (faceVariable K overlapFace ()) = T 1 := by
  rw [faceVariable, overlapEquiv_single, map_one, one_mul]
  rfl

/-- The inverse frame transition of the twist s from the right chart to the overlap is z^s. -/
theorem multiTwistTransition_right_inv (h : FaceRefines rightFace overlapFace) (s : ℕ) :
    overlapEquiv K (↑((multiTwistTransition K h (fun _ => (s : ℤ)))⁻¹) : FaceRing K overlapFace) =
      T s := by
  have hu : multiTwistTransition K h (fun _ => (s : ℤ)) =
      (faceLaurentUnit K overlapFace () rfl)⁻¹ ^ (s : ℤ) := by
    simp [multiTwistTransition, faceTransitionUnit]
  rw [hu, ← zpow_neg, inv_zpow', neg_neg, zpow_natCast, Units.val_pow_eq_pow_val, map_pow,
    faceLaurentUnit_val, overlapEquiv_faceVariable, T_pow, mul_one]

/-- Restriction from the right chart to the overlap, in the frame of the left chart, for the twist
s ≥ 0: u ↦ z⁻¹ followed by multiplication by z^s. -/
theorem overlapEquiv_restrict_right (h : FaceRefines rightFace overlapFace) (s : ℕ)
    (x : FaceRing K rightFace) :
    overlapEquiv K (multiTwistFaceRestriction K h (fun _ => (s : ℤ)) x) =
      T s * invert (toLaurent (rightEquiv K x)) := by
  rw [multiTwistFaceRestriction_apply, map_mul, multiTwistTransition_right_inv, mul_comm]
  congr 1
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | single m c =>
    rw [faceRefinementMap_single, overlapEquiv_single, rightEquiv_single, toLaurent_C_mul_T,
      map_mul, invert_C, invert_T, ← refinementExponent_right h]
    rfl


/-- Coefficients of a polynomial in nonnegative Laurent degrees. -/
theorem coeff_toLaurent_natCast (f : K[X]) (n : ℕ) : (toLaurent f).coeff (n : ℤ) = f.coeff n := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding (R := ℤ)).injective _ n

/-- A polynomial has no coefficients in negative Laurent degrees. -/
theorem coeff_toLaurent_of_neg (f : K[X]) {m : ℤ} (hm : m < 0) : (toLaurent f).coeff m = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n, rfl⟩
  have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  simp at hm
  omega

/-- Multiplication by T^s shifts coefficients. -/
theorem coeff_T_mul (f : K[T;T⁻¹]) (s n : ℤ) : (T s * f).coeff n = f.coeff (n - s) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_eq_sub]

/-- **Degree bound.** If z ↦ L(z) and u ↦ R(u) are the left and right coefficients of a section of
O(s), that is L(z) = z^s R(1/z), then L has degree at most s. -/
theorem natDegree_le_of_toLaurent_eq (s : ℕ) {L R : K[X]}
    (h : toLaurent L = T s * invert (toLaurent R)) : L.natDegree ≤ s := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hc : (toLaurent L).coeff (n : ℤ) = (T s * invert (toLaurent R)).coeff (n : ℤ) := by rw [h]
  rw [coeff_toLaurent_natCast, coeff_T_mul, invert_apply, coeff_toLaurent_of_neg K R (by omega)] at hc
  exact hc

/-- The right coefficient of a section of O(s) vanishes when its left coefficient does. -/
theorem eq_zero_of_toLaurent_eq_zero (s : ℕ) {R : K[X]}
    (h : (0 : K[T;T⁻¹]) = T s * invert (toLaurent R)) : R = 0 := by
  rw [eq_comm, (isUnit_T (s : ℤ)).mul_right_eq_zero, map_eq_zero_iff _ (invert).injective,
    toLaurent_eq_zero] at h
  exact h

/-- z^j ↦ u^{s−j}: the right chart coefficient of the section z ↦ P(z) of O(s). -/
noncomputable def reversePoly (s : ℕ) (P : K[X]) : K[X] :=
  ∑ n ∈ Finset.range (s + 1), monomial (s - n) (P.coeff n)

/-- On the overlap, the reversed polynomial is the original one: z^s P̃(1/z) = P(z). -/
theorem toLaurent_reversePoly (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    T s * invert (toLaurent (reversePoly K s P)) = toLaurent P := by
  conv_rhs => rw [P.as_sum_range' (s + 1) (by omega)]
  simp only [reversePoly, map_sum, Finset.mul_sum, toLaurent_C_mul_T, map_mul, invert_C, invert_T]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [mul_left_comm, ← T_add]
  congr 2
  rw [Nat.cast_sub (by omega : n ≤ s)]
  ring

section Cells
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open SheafTools SheafTools.BinaryCells ProjectiveLine CechCubicalCell ExtResolutionTools

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

/-- The overlap face of one vertex as a cell of degree one. -/
def overlapIndex : FaceIndex (V := Unit) 1 :=
  ⟨overlapFace, by simp [cellDegree, faceDegree]⟩

/-- The only cell of degree one for a single vertex is the overlap. -/
theorem faceIndex_one_eq (q : FaceIndex (V := Unit) 1) : q = overlapIndex := by
  apply Subtype.ext
  funext v
  have h := q.property
  simp only [cellDegree, faceDegree, Finset.univ_unique, Finset.sum_singleton] at h
  change q.val () = 2
  split_ifs at h with hq
  · exact hq
  · simp at h

/-- The left endpoint of the overlap cell is the left chart. -/
theorem endpoint_overlap_zero :
    (endpoint overlapIndex () rfl 0).val = leftFace := by
  funext v
  simp [endpoint, overlapIndex]

/-- The right endpoint of the overlap cell is the right chart. -/
theorem endpoint_overlap_one :
    (endpoint overlapIndex () rfl 1).val = rightFace := by
  funext v
  simp [endpoint, overlapIndex]

/-- A cochain evaluated on an open inside one of its faces is the restricted face section. -/
theorem cellCochainValue_index {F : Sheaf (Opens.grothendieckTopology (vertexScheme K Unit)) AddCommGrpCat.{0}}
    (i : ℕ) (f : (sheafComplex (vertexCoordinateOpen K Unit)).X i ⟶ F) (q : FaceIndex (V := Unit) i)
    (W : (vertexScheme K Unit).Opens) (hq : W ≤ binaryCoverFaceOpen (vertexCoordinateOpen K Unit) q.val) :
    cellCochainValue (vertexCoordinateOpen K Unit) i f W q.val hq =
      F.obj.map (homOfLE hq).op (sectionsEquiv (vertexCoordinateOpen K Unit) F i f q) := by
  have hd : faceDegree q.val = i := by
    have h := q.property
    change -(faceDegree q.val : ℤ) = -(i : ℤ) at h
    omega
  rw [cellCochainValue, dite_eq_left hd]
  exact cellSheafSection_cochain (vertexCoordinateOpen K Unit) F i f q W hq


/-- Restriction of a face coefficient along an equality of faces. -/
theorem multiTwistFaceRestriction_congr {a : Unit → ℤ} {p p' r : Unit → Fin 3} (hp : p = p')
    (h : FaceRefines p r) (h' : FaceRefines p' r) (x : (q : Unit → Fin 3) → FaceRing K q) :
    multiTwistFaceRestriction K h a (x p) = multiTwistFaceRestriction K h' a (x p') := by
  subst hp
  rfl

/-- The overlap coordinate of the coboundary of a degree-zero cochain is the signed difference of
the restrictions of its two chart coefficients. -/
theorem zeroCochain_boundary_overlap (b : Unit → ℤ)
    (g : sheafTerm (vertexCoordinateOpen K Unit) 0 ⟶ vertexTwistAbelianSheaf K Unit b)
    (hl : FaceRefines leftFace overlapFace) (hr : FaceRefines rightFace overlapFace) :
    vertexTwistSheafFaceSectionsEquiv K Unit b overlapFace
      (sectionsEquiv (vertexCoordinateOpen K Unit) (vertexTwistAbelianSheaf K Unit b) 1
        ((sheafComplex (vertexCoordinateOpen K Unit)).d 1 0 ≫ g) overlapIndex) =
      (-1 : ℤ) ^ faceBoundaryPrefix overlapIndex.val () •
        (multiTwistFaceRestriction K hl b (vertexTwistCellFaceCoefficient K Unit b 0 g leftFace) -
          multiTwistFaceRestriction K hr b (vertexTwistCellFaceCoefficient K Unit b 0 g rightFace)) := by
  let U := vertexCoordinateOpen K Unit
  let F := vertexTwistAbelianSheaf K Unit b
  rw [sectionsEquiv_boundary, Finset.sum_eq_single_of_mem () (Finset.mem_univ _)
    (fun v _ hv => absurd (Subsingleton.elim v ()) hv),
    dite_eq_left (show overlapIndex.val () = 2 from rfl), map_zsmul, map_sub]
  have h00 : FaceRefines (endpoint overlapIndex () rfl 0).val overlapFace :=
    endpoint_refines (faceRefines_refl overlapIndex.val) () rfl _
  have h01 : FaceRefines (endpoint overlapIndex () rfl 1).val overlapFace :=
    endpoint_refines (faceRefines_refl overlapIndex.val) () rfl _
  have e0 : vertexTwistSheafFaceSectionsEquiv K Unit b overlapFace
      (F.obj.map (homOfLE (endpointOpenLE U overlapIndex () rfl 0)).op
        (sectionsEquiv U F 0 g (endpoint overlapIndex () rfl 0))) =
      multiTwistFaceRestriction K h00 b
        (vertexTwistCellFaceCoefficient K Unit b 0 g (endpoint overlapIndex () rfl 0).val) := by
    rw [← cellCochainValue_index K 0 g]
    exact vertexTwistCellFaceCoefficient_restrict K Unit b 0 g h00
  have e1 : vertexTwistSheafFaceSectionsEquiv K Unit b overlapFace
      (F.obj.map (homOfLE (endpointOpenLE U overlapIndex () rfl 1)).op
        (sectionsEquiv U F 0 g (endpoint overlapIndex () rfl 1))) =
      multiTwistFaceRestriction K h01 b
        (vertexTwistCellFaceCoefficient K Unit b 0 g (endpoint overlapIndex () rfl 1).val) := by
    rw [← cellCochainValue_index K 0 g]
    exact vertexTwistCellFaceCoefficient_restrict K Unit b 0 g h01
  rw [← multiTwistFaceRestriction_congr K endpoint_overlap_zero h00 hl,
    ← multiTwistFaceRestriction_congr K endpoint_overlap_one h01 hr, ← e0, ← e1]

/-- **Degree-zero cycles.** For a single vertex, a degree-zero cell cochain is a cocycle iff its
left and right chart coefficients have the same restriction to the overlap. -/
theorem mem_zeroCycles_iff (b : Unit → ℤ)
    (g : sheafTerm (vertexCoordinateOpen K Unit) 0 ⟶ vertexTwistAbelianSheaf K Unit b)
    (hl : FaceRefines leftFace overlapFace) (hr : FaceRefines rightFace overlapFace) :
    g ∈ (cubicalTower (vertexCoordinateOpen K Unit)).cycles (vertexTwistAbelianSheaf K Unit b) 0 ↔
      multiTwistFaceRestriction K hl b (vertexTwistCellFaceCoefficient K Unit b 0 g leftFace) =
        multiTwistFaceRestriction K hr b (vertexTwistCellFaceCoefficient K Unit b 0 g rightFace) := by
  let U := vertexCoordinateOpen K Unit
  let F := vertexTwistAbelianSheaf K Unit b
  have hc : g ∈ (cubicalTower U).cycles F 0 ↔ (sheafComplex U).d 1 0 ≫ g = 0 := by
    change (cubicalTower U).differential 0 ≫ g = 0 ↔ _
    rw [complexTower_differential]
  have hs : (sheafComplex U).d 1 0 ≫ g = 0 ↔
      sectionsEquiv U F 1 ((sheafComplex U).d 1 0 ≫ g) overlapIndex = 0 := by
    constructor
    · intro h
      rw [h, map_zero]
      rfl
    · intro h
      apply (sectionsEquiv U F 1).injective
      rw [map_zero]
      funext q
      rw [faceIndex_one_eq q]
      exact h
  rw [hc, hs, ← (vertexTwistSheafFaceSectionsEquiv K Unit b overlapFace).map_eq_zero_iff,
    zeroCochain_boundary_overlap K b g hl hr]
  constructor
  · intro h
    have h2 := congrArg (fun z => ((-1 : ℤ) ^ faceBoundaryPrefix overlapIndex.val ()) • z) h
    simp only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul,
      smul_zero] at h2
    exact sub_eq_zero.mp h2
  · intro h
    rw [h, sub_self, smul_zero]


/-- The twist s ≥ 0 of the single vertex. -/
abbrev posTwist (s : ℕ) : Unit → ℤ := fun _ => (s : ℤ)

/-- The overlap refines the left chart. -/
theorem leftFace_refines : FaceRefines leftFace overlapFace := fun _ => Or.inr rfl
/-- The overlap refines the right chart. -/
theorem rightFace_refines : FaceRefines rightFace overlapFace := fun _ => Or.inr rfl

/-- The left chart as a cell of degree zero. -/
def leftIndex : FaceIndex (V := Unit) 0 := ⟨leftFace, by simp [cellDegree, faceDegree]⟩
/-- The right chart as a cell of degree zero. -/
def rightIndex : FaceIndex (V := Unit) 0 := ⟨rightFace, by simp [cellDegree, faceDegree]⟩

/-- The cells of degree zero are the two charts. -/
theorem faceIndex_zero_cases (q : FaceIndex (V := Unit) 0) : q = leftIndex ∨ q = rightIndex := by
  have h := q.property
  simp only [cellDegree, faceDegree, Finset.univ_unique, Finset.sum_singleton] at h
  have h2 : q.val () ≠ 2 := by
    intro h2
    rw [ite_eq_left h2] at h
    simp at h
  have hv : q.val = fun _ => q.val () := rfl
  generalize hc : q.val () = c at h2 hv
  fin_cases c
  · left
    exact Subtype.ext hv
  · right
    exact Subtype.ext hv
  · exact absurd rfl h2

/-- **Laurent form of the cycle condition.** A degree-zero cochain of O(s) is a cocycle iff its
chart polynomials satisfy L(z) = z^s R(1/z). -/
theorem mem_zeroCycles_iff_laurent (s : ℕ)
    (g : sheafTerm (vertexCoordinateOpen K Unit) 0 ⟶ vertexTwistAbelianSheaf K Unit (posTwist s)) :
    g ∈ (cubicalTower (vertexCoordinateOpen K Unit)).cycles
        (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 ↔
      toLaurent (leftEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 g leftFace)) =
        T s * invert (toLaurent
          (rightEquiv K (vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 g rightFace))) := by
  rw [mem_zeroCycles_iff K _ g leftFace_refines rightFace_refines, ← (overlapEquiv K).injective.eq_iff,
    overlapEquiv_restrict_left, overlapEquiv_restrict_right]

/-- A degree-zero cochain is determined by its two chart coefficients. -/
theorem zeroCochain_ext (b : Unit → ℤ)
    {g g' : sheafTerm (vertexCoordinateOpen K Unit) 0 ⟶ vertexTwistAbelianSheaf K Unit b}
    (hl : vertexTwistCellFaceCoefficient K Unit b 0 g leftFace =
      vertexTwistCellFaceCoefficient K Unit b 0 g' leftFace)
    (hr : vertexTwistCellFaceCoefficient K Unit b 0 g rightFace =
      vertexTwistCellFaceCoefficient K Unit b 0 g' rightFace) : g = g' := by
  apply (sectionsEquiv (vertexCoordinateOpen K Unit) (vertexTwistAbelianSheaf K Unit b) 0).injective
  funext q
  apply (vertexTwistSheafFaceSectionsEquiv K Unit b q.val).injective
  rw [← vertexTwistCellFaceCoefficient_sections, ← vertexTwistCellFaceCoefficient_sections]
  rcases faceIndex_zero_cases q with rfl | rfl
  · exact hl
  · exact hr

/-- Chart coefficients are additive in the cochain. -/
theorem vertexTwistCellFaceCoefficient_add (b : Unit → ℤ) (n : ℕ)
    (g g' : sheafTerm (vertexCoordinateOpen K Unit) n ⟶ vertexTwistAbelianSheaf K Unit b)
    (q : FaceIndex (V := Unit) n) :
    vertexTwistCellFaceCoefficient K Unit b n (g + g') q.val =
      vertexTwistCellFaceCoefficient K Unit b n g q.val +
        vertexTwistCellFaceCoefficient K Unit b n g' q.val := by
  rw [vertexTwistCellFaceCoefficient_sections, vertexTwistCellFaceCoefficient_sections,
    vertexTwistCellFaceCoefficient_sections, map_add, Pi.add_apply, map_add]

/-- The chart coefficients of the section z ↦ P(z) of O(s): P on the left chart and the reversed
polynomial on the right chart. -/
noncomputable def chartCoefficient (s : ℕ) (P : K[X]) (q : Unit → Fin 3) : FaceRing K q :=
  if h : q = leftFace then h ▸ (leftEquiv K).symm P
  else if h' : q = rightFace then h' ▸ (rightEquiv K).symm (reversePoly K s P) else 0

/-- The left chart coefficient of z ↦ P(z) is P. -/
theorem chartCoefficient_left (s : ℕ) (P : K[X]) :
    chartCoefficient K s P leftFace = (leftEquiv K).symm P := by
  rw [chartCoefficient, dite_eq_left rfl]

/-- The right chart coefficient of z ↦ P(z) is the reversed polynomial. -/
theorem chartCoefficient_right (s : ℕ) (P : K[X]) :
    chartCoefficient K s P rightFace = (rightEquiv K).symm (reversePoly K s P) := by
  have h : rightFace ≠ leftFace := fun h => by simpa using congrFun h ()
  rw [chartCoefficient, dite_eq_right h, dite_eq_left rfl]

/-- The degree-zero cochain of the section z ↦ P(z) of O(s). -/
noncomputable def polyCochain (s : ℕ) (P : K[X]) :
    sheafTerm (vertexCoordinateOpen K Unit) 0 ⟶ vertexTwistAbelianSheaf K Unit (posTwist s) :=
  (sectionsEquiv (vertexCoordinateOpen K Unit) (vertexTwistAbelianSheaf K Unit (posTwist s)) 0).symm
    fun q => (vertexTwistSheafFaceSectionsEquiv K Unit (posTwist s) q.val).symm
      (chartCoefficient K s P q.val)

/-- The chart coefficients of `polyCochain` are the specified ones. -/
theorem polyCochain_coefficient (s : ℕ) (P : K[X]) (q : FaceIndex (V := Unit) 0) :
    vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s P) q.val =
      chartCoefficient K s P q.val := by
  rw [vertexTwistCellFaceCoefficient_sections, polyCochain, AddEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The left chart coefficient of `polyCochain` is P. -/
theorem polyCochain_left (s : ℕ) (P : K[X]) :
    vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s P) leftFace =
      (leftEquiv K).symm P :=
  (polyCochain_coefficient K s P leftIndex).trans (chartCoefficient_left K s P)

/-- The right chart coefficient of `polyCochain` is the reversed polynomial. -/
theorem polyCochain_right (s : ℕ) (P : K[X]) :
    vertexTwistCellFaceCoefficient K Unit (posTwist s) 0 (polyCochain K s P) rightFace =
      (rightEquiv K).symm (reversePoly K s P) :=
  (polyCochain_coefficient K s P rightIndex).trans (chartCoefficient_right K s P)

/-- For deg P ≤ s, the cochain of z ↦ P(z) is a cocycle. -/
theorem polyCochain_mem (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    polyCochain K s P ∈ (cubicalTower (vertexCoordinateOpen K Unit)).cycles
      (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 := by
  rw [mem_zeroCycles_iff_laurent, polyCochain_left, polyCochain_right, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply, toLaurent_reversePoly K s P hP]


/-- The diagonal pairs on the overlap: (left, overlap) and (overlap, right). -/
theorem diagonalShape_overlap_iff (p q : Unit → Fin 3) :
    DiagonalShape overlapFace p q ↔ (p = leftFace ∧ q = overlapFace) ∨ (p = overlapFace ∧ q = rightFace) := by
  have hp : p = fun _ => p () := rfl
  have hq : q = fun _ => q () := rfl
  constructor
  · intro h
    have h1 := h ()
    simp only [intervalDiagonalShape] at h1
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by rw [hp, h1], by rw [hq, h2]⟩
    · right
      exact ⟨by rw [hp, h1], by rw [hq, h2]⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) v
    · change intervalDiagonalShape 2 0 2
      simp [intervalDiagonalShape]
    · change intervalDiagonalShape 2 2 1
      simp [intervalDiagonalShape]

/-- The diagonal term (overlap, right) carries no crossing sign. -/
theorem diagonalCross_overlap_right : diagonalCross overlapFace rightFace = 0 := by
  simp [diagonalCross, finDiagonalCross, Function.comp_def, rightFace]

/-- **One-vertex cup of degrees one and zero.** On the overlap, the cup of a degree-one cochain f
and a degree-zero cochain g is f times the restriction of the right chart coefficient of g. -/
theorem cellCup_overlap (a b : Unit → ℤ)
    (f : (vertexTwistCupSource K Unit).X 1 ⟶ vertexTwistAbelianSheaf K Unit a)
    (g : (vertexTwistCupSource K Unit).X 0 ⟶ vertexTwistAbelianSheaf K Unit b) :
    vertexTwistCellFaceCoefficient K Unit (a + b) 1 (vertexTwistCellCupAt K Unit a b 1 1 0 f g)
        overlapFace =
      vertexTwistCellFaceCoefficient K Unit a 1 f overlapFace *
        multiTwistFaceRestriction K rightFace_refines b
          (vertexTwistCellFaceCoefficient K Unit b 0 g rightFace) := by
  classical
  let U := vertexCoordinateOpen K Unit
  have hface := vertexTwistCellFaceCoefficient_sections K Unit (a + b) 1
    (vertexTwistCellCupAt K Unit a b 1 1 0 f g) overlapIndex
  refine hface.trans ?_
  rw [vertexTwistCellCupAt_face]
  have hov : binaryCoverFaceOpen U overlapIndex.val ≤ binaryCoverFaceOpen U overlapFace := le_rfl
  have hrt : binaryCoverFaceOpen U overlapIndex.val ≤ binaryCoverFaceOpen U rightFace :=
    faceOpen_refinement_le U rightFace_refines
  let z₀ : PairCellIndex U (binaryCoverFaceOpen U overlapIndex.val) 1 :=
    ⟨(overlapFace, rightFace), hov, hrt, by simp [faceDegree]⟩
  rw [Finset.sum_eq_single_of_mem z₀ (Finset.mem_univ _)]
  · have hz : DiagonalShape overlapIndex.val z₀.val.1 z₀.val.2 :=
      (diagonalShape_overlap_iff overlapFace rightFace).2 (Or.inr ⟨rfl, rfl⟩)
    rw [dite_eq_left hz]
    change (-1 : ℤ) ^ diagonalCross overlapFace rightFace • _ = _
    rw [diagonalCross_overlap_right, pow_zero, one_smul]
    congr 1
    exact multiTwistFaceRestriction_refl K Unit a overlapFace _
  · intro z _ hne
    by_cases hz : DiagonalShape overlapIndex.val z.val.1 z.val.2
    · rw [dite_eq_left hz]
      rcases (diagonalShape_overlap_iff _ _).1 hz with ⟨h1, _⟩ | ⟨h1, h2⟩
      · have hd : faceDegree z.val.1 ≠ 1 := by rw [h1]; simp [faceDegree]
        rw [vertexTwistCellFaceCoefficient_zero_degree K Unit a 1 f _ hd, map_zero, zero_mul,
          smul_zero]
      · exact absurd (Subtype.ext (Prod.ext h1 h2)) hne
    · rw [dite_eq_right hz]

end Cells


/-- Coefficients on the overlap face in Laurent coordinates. -/
theorem overlapEquiv_coeff (x : FaceRing K overlapFace) (n : ℤ) :
    (overlapEquiv K x).coeff n = x.coeff (fun _ => n) := by
  rw [overlapEquiv, AddMonoidAlgebra.coeff_domCongr]
  rfl

/-- The twist −(s+2) of the single vertex as a degree vector. -/
abbrev negTwist (s : ℕ) : Unit → ℕ := fun _ => s + 2

/-- The state coordinate j of twist −(s+2) reads the Laurent monomial z^{−j−1}. -/
theorem lineProjectionMonomial_gap (s : ℕ) (j : Fin (s + 1)) :
    lineProjectionMonomial (s + 2) j = Sum.inr (Sum.inr (-(j : ℤ) - 1)) := by
  have h : (lineStateIndexEquiv (s + 2)).symm j = Sum.inr ⟨j.val, by have := j.isLt; omega⟩ := by
    apply (lineStateIndexEquiv (s + 2)).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [lineStateIndexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [finSumFinEquiv_apply_right, Fin.val_natAdd]
    simp
  unfold lineProjectionMonomial
  rw [h]

section Gap
open ProjectiveLine

/-- **State coordinates of H^1(O(−(s+2))).** The state coordinate j of a degree-one cell cocycle is
minus the coefficient of z^{−j−1} of its overlap coefficient. -/
theorem cycleProjection_gap (s : ℕ) (f : vertexTwistCellCycles K Unit (negTwist s) 1)
    (j : Fin (s + 1)) :
    (vertexTwistCellCycleProjection K Unit (negTwist s) 1 f).val (fun _ => j) =
      -(overlapEquiv K (vertexTwistCellFaceCoefficient K Unit (fun v => -((negTwist s v : ℕ) : ℤ)) 1
        f.val overlapFace)).coeff (-(j : ℤ) - 1) := by
  rw [vertexTwistCellCycleProjection_val, contraction_p_coefficient]
  have hm : stateProjectionMonomial (negTwist s) (fun _ => j) =
      embedFace overlapFace (fun _ => (-(j : ℤ) - 1)) := by
    funext v
    simp only [stateProjectionMonomial]
    rw [lineProjectionMonomial_gap]
    rfl
  have hd : faceDegree overlapFace = 1 := by simp [faceDegree]
  rw [hm, ← faceEquiv_coeff, vertexTwistCellCoefficientEquiv_face, hd, pow_one, neg_one_smul,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, overlapEquiv_coeff]

end Gap

end BPFixedPoints.SerreComparison
