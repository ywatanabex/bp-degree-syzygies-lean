import BPFixedPoints.Incidence.VertexMapTwistStateFaces
import BPFixedPoints.Incidence.VertexMapCellRelabel
import BPFixedPoints.Incidence.VertexMapPullbackCech
import BPFixedPoints.Incidence.VertexPermutationTwistStateCoefficients

/-!
# Coefficient chains of cochains with pulled back face coordinates

The signed coefficient chain `vertexTwistCellCoefficientEquiv` of a cubical cochain of `(P¹)^W`
records, on every face `q`, the face coordinates of its face section, times the parity of the
overlap degree. Let `j : I → W` be injective. On product Čech chains, the pullback along the
coordinate projection `(P¹)^W → (P¹)^I` is `cechExtend R j` (`VertexMapPullbackCech`).

Proved here (`vertexTwistCellCoefficientEquiv_eq_cechExtend`): if a cochain `y` of `(P¹)^W` has,
on every face whose overlap directions lie in the image of `j`, the face coordinates
`relabelCoefficient ℤ j q • facePull j q R c` where `c` are the face coordinates of a cochain `z` of
`(P¹)^I` at the restricted face, and zero face coordinates on all other faces, then the coefficient
chain of `y` is `cechExtend R j` of the coefficient chain of `z`. The sign of the forgetful chain
map of cells is the Koszul sign of `cechExtend` (`relabelInversions_eq_vertexMapInversions`), and
the face-ring comparison `facePull` of an injective map is the extension of exponents by zero
(`facePull_coeff_faceMonoidPull`, `facePull_coeff_of_notMem`).

This is pure bookkeeping on coefficients; no sheaf cohomology is involved.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open SheafTools.BinaryCells ProjectiveLine CechProduct Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

section FacePull

variable {V W : Type} [Fintype V] [DecidableEq W] (f : V → W) (q : W → Fin 3) (R : Type)
  [CommRing R]

/-- Coefficients of a pulled back face element outside the image of the exponent map vanish. -/
theorem facePull_coeff_of_notMem (x : FaceRing R (fun v => q (f v))) (m : FaceMonoid q)
    (hm : ∀ m', faceMonoidPull f q m' ≠ m) : (facePull f q R x).coeff m = 0 := by
  change (Finsupp.mapDomain (faceMonoidPull f q) x.coeff) m = 0
  exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨m', hm'⟩; exact hm m' hm')

/-- For an injective function, coefficients of a pulled back face element at pulled back exponents
are the coefficients. -/
theorem facePull_coeff_faceMonoidPull [DecidableEq V] (hf : Function.Injective f)
    (x : FaceRing R (fun v => q (f v))) (m : FaceMonoid (fun v => q (f v))) :
    (facePull f q R x).coeff (faceMonoidPull f q m) = x.coeff m := by
  change (Finsupp.mapDomain (faceMonoidPull f q) x.coeff) (faceMonoidPull f q m) = _
  refine Finsupp.mapDomain_apply_of_injective ?_ x.coeff m
  intro m₁ m₂ h
  funext v
  have := congrFun h (f v)
  simp only [faceMonoidPull, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, Pi.evalAddMonoidHom_apply, Finset.sum_apply] at this
  rw [Finset.sum_eq_single v, Finset.sum_eq_single v] at this
  · simpa using this
  · intro u _ hu
    exact Pi.single_eq_of_ne (hf.ne hu).symm _
  · simp
  · intro u _ hu
    exact Pi.single_eq_of_ne (hf.ne hu).symm _
  · simp

/-- For an injective function, an exponent vector vanishing off the image is the pulled back
exponent vector of its restriction. -/
theorem faceMonoidPull_restrict [DecidableEq V] (hf : Function.Injective f) (m : FaceMonoid q)
    (hm : ∀ w, (∀ v, f v ≠ w) → m w = 0) : faceMonoidPull f q (fun v => m (f v)) = m := by
  funext w
  simp only [faceMonoidPull, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, Pi.evalAddMonoidHom_apply, Finset.sum_apply]
  by_cases hw : ∃ v, f v = w
  · obtain ⟨v, rfl⟩ := hw
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      exact Pi.single_eq_of_ne (hf.ne hu).symm _
    · simp
  · push Not at hw
    rw [hm w hw]
    refine Finset.sum_eq_zero fun u _ => ?_
    exact Pi.single_eq_of_ne (hw u).symm _

/-- Pulled back exponent vectors vanish off the image. -/
theorem faceMonoidPull_apply_of_notMem (m : FaceMonoid (fun v => q (f v))) {w : W}
    (hw : ∀ v, f v ≠ w) : faceMonoidPull f q m w = 0 := by
  simp only [faceMonoidPull, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, Pi.evalAddMonoidHom_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  exact Pi.single_eq_of_ne (hw u).symm _

end FacePull

section FacePullComp

variable {U V W : Type} [Fintype U] [Fintype V] [DecidableEq V] [DecidableEq W] (g : U → V)
  (f : V → W) (q : W → Fin 3) (R : Type) [CommRing R]

/-- Pulled back exponent vectors compose. -/
theorem faceMonoidPull_comp (m : FaceMonoid (fun u => q (f (g u)))) :
    faceMonoidPull f q (faceMonoidPull g (fun v => q (f v)) m) =
      faceMonoidPull (fun u => f (g u)) q m := by
  have hr : faceMonoidPull (fun u => f (g u)) q m =
      ∑ u, Pi.single (M := fun w => FaceExponent (q w)) (f (g u)) (m u) := by
    simp [faceMonoidPull, AddMonoidHom.finsetSum_apply]
  have hl : faceMonoidPull f q (faceMonoidPull g (fun v => q (f v)) m) =
      ∑ u, ∑ v, Pi.single (M := fun w => FaceExponent (q w)) (f v)
        (Pi.single (M := fun v => FaceExponent (q (f v))) (g u) (m u) v) := by
    simp [faceMonoidPull, AddMonoidHom.finsetSum_apply, map_sum]
  rw [hl, hr]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single (g u)]
  · simp
  · intro v _ hv
    rw [Pi.single_eq_of_ne hv, Pi.single_zero]
  · simp

/-- **The comorphisms of face rings compose.** -/
theorem facePull_comp (x : FaceRing R (fun u => q (f (g u)))) :
    facePull f q R (facePull g (fun v => q (f v)) R x) = facePull (fun u => f (g u)) q R x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r => rw [facePull_single, facePull_single, facePull_single, faceMonoidPull_comp]

end FacePullComp

section Signs

variable {I K : Type} [Fintype I] [Fintype K] (ι : I → K)

/-- The inversion count of the restriction of cells is the vertex-map inversion count of the
overlap directions. -/
theorem relabelInversions_eq_vertexMapInversions [DecidableEq I] [DecidableEq K] (p : I → Fin 3) :
    CechCubicalCell.relabelInversions ι p = vertexMapInversions ι (faceOverlap p) := by
  unfold CechCubicalCell.relabelInversions vertexMapInversions
  rfl

end Signs

section Coefficients

/-- A one-vertex monomial is a chart constant exactly when it lies on a chart with exponent zero. -/
theorem faceExp_unitBasis_iff (k : Fin 3) (x : FaceExponent k) :
    (∃ t, vertexFaceEquiv.symm ⟨k, x⟩ = unitBasis t) ↔ k ≠ 2 ∧ x = 0 := by
  fin_cases k
  · change (∃ t, (Sum.inl x : Basis) = unitBasis t) ↔ _ ∧ (x : ℕ) = 0
    constructor
    · rintro ⟨t, ht⟩
      cases t
      · simp [unitBasis] at ht
      · exact ⟨by decide, Sum.inl_injective ht⟩
    · rintro ⟨-, rfl⟩
      exact ⟨true, rfl⟩
  · change (∃ t, (Sum.inr (Sum.inl x) : Basis) = unitBasis t) ↔ _ ∧ (x : ℕ) = 0
    constructor
    · rintro ⟨t, ht⟩
      cases t
      · exact ⟨by decide, Sum.inl_injective (Sum.inr_injective ht)⟩
      · simp [unitBasis] at ht
    · rintro ⟨-, rfl⟩
      exact ⟨false, rfl⟩
  · change (∃ t, (Sum.inr (Sum.inr x) : Basis) = unitBasis t) ↔ _ ∧ (x : ℤ) = 0
    constructor
    · rintro ⟨t, ht⟩
      cases t <;> simp_all [unitBasis]
    · rintro ⟨h, -⟩
      exact absurd rfl h

/-- A product monomial is a chart constant at a vertex exactly when its face is a chart there and
its exponent vanishes there. -/
theorem embedFace_unitBasis_iff {W : Type} (q : W → Fin 3) (m : FaceMonoid q) (w : W) :
    (∃ t, embedFace q m w = unitBasis t) ↔ q w ≠ 2 ∧ m w = 0 :=
  faceExp_unitBasis_iff (q w) (m w)


variable (R : Type) [CommRing R] {I W : Type} [Fintype I] [DecidableEq I] [Fintype W]
  [DecidableEq W] {j : I → W} (hj : Function.Injective j)

/-- **Coefficient chains of extended cochains.** If the face coordinates of a cochain `y` of the
cell complex of `(P¹)^W` are, on every face whose overlap directions lie in the image of an
injective `j : I → W`, the cell sign times the pulled back face coordinates of a cochain `z` of
`(P¹)^I` at the restricted face, and zero on the other faces, then the signed coefficient chain of
`y` is the extension `cechExtend R j` of the signed coefficient chain of `z`. -/
theorem vertexTwistCellCoefficientEquiv_eq_cechExtend (dI : I → ℕ) (d : W → ℕ) (n : ℕ)
    (z : sheafTerm (vertexCoordinateOpen R I) n ⟶ vertexTwistAbelianSheaf R I (fun i => -(dI i : ℤ)))
    (y : sheafTerm (vertexCoordinateOpen R W) n ⟶ vertexTwistAbelianSheaf R W (fun w => -(d w : ℤ)))
    (hy : ∀ q : FaceIndex (V := W) n,
      vertexTwistSheafFaceSectionsEquiv R W (fun w => -(d w : ℤ)) q.val
          (sectionsEquiv (vertexCoordinateOpen R W) _ n y q) =
        if h : ∀ w, q.val w = 2 → ∃ i, j i = w then
          CechCubicalCell.relabelCoefficient ℤ j q.val • facePull j q.val R
            (vertexTwistSheafFaceSectionsEquiv R I (fun i => -(dI i : ℤ)) (fun i => q.val (j i))
              (sectionsEquiv (vertexCoordinateOpen R I) _ n z (relabelFace hj q h)))
        else 0) :
    (vertexTwistCellCoefficientEquiv R W d n y).val =
      cechExtend R j (vertexTwistCellCoefficientEquiv R I dI n z).val := by
  ext b
  obtain ⟨⟨q, m⟩, rfl⟩ := faceBasisEquiv.symm.surjective b
  change (vertexTwistCellCoefficientEquiv R W d n y).val (embedFace q m) =
    cechExtend R j (vertexTwistCellCoefficientEquiv R I dI n z).val (embedFace q m)
  have hL : (vertexTwistCellCoefficientEquiv R W d n y).val (embedFace q m) =
      ((-1 : R) ^ faceDegree q • vertexTwistSheafFaceSectionsEquiv R W (fun w => -(d w : ℤ)) q
        ((vertexTwistCellNativeEquiv R W _ n y).val q)).coeff m := by
    rw [← faceEquiv_coeff]
    change (faceEquiv R (vertexTwistCubicalChainEquiv R W d
      (vertexTwistCellNativeEquiv R W _ n y).val) q).coeff m = _
    rw [vertexTwistCubicalChainEquiv_face]
  have hI : ∀ (p : I → Fin 3) (m' : FaceMonoid p),
      (vertexTwistCellCoefficientEquiv R I dI n z).val (embedFace p m') =
      ((-1 : R) ^ faceDegree p • vertexTwistSheafFaceSectionsEquiv R I (fun i => -(dI i : ℤ)) p
        ((vertexTwistCellNativeEquiv R I _ n z).val p)).coeff m' := by
    intro p m'
    rw [← faceEquiv_coeff]
    change (faceEquiv R (vertexTwistCubicalChainEquiv R I dI
      (vertexTwistCellNativeEquiv R I _ n z).val) p).coeff m' = _
    rw [vertexTwistCubicalChainEquiv_face]
  rw [hL]
  by_cases hu : UnitOff j (embedFace q m)
  · have hoff : ∀ w, (∀ i, j i ≠ w) → q w ≠ 2 ∧ m w = 0 := fun w hw =>
      (embedFace_unitBasis_iff q m w).1 (hu w hw)
    have h : ∀ w, q w = 2 → ∃ i, j i = w := by
      intro w hw
      by_contra hn
      push Not at hn
      exact (hoff w hn).1 hw
    rw [cechExtend_apply_of_unitOff R hj _ hu]
    change _ = vertexMapSign R j (overlapVertices (embedFace (fun i => q (j i)) (fun i => m (j i)))) *
      (vertexTwistCellCoefficientEquiv R I dI n z).val
        (embedFace (fun i => q (j i)) (fun i => m (j i)))
    rw [hI, overlapVertices_embedFace]
    have hdeg : faceDegree (fun i => q (j i)) = faceDegree q :=
      CechCubicalCell.faceDegree_comp_of_image j hj q h
    by_cases hq : (faceDegree q : ℤ) = n
    · let q' : FaceIndex (V := W) n := faceIndexOfDegree W n q hq
      have hq'' : (faceDegree (fun i => q (j i)) : ℤ) = n := by rw [hdeg]; exact hq
      have e1 := vertexTwistCellNativeEquiv_apply R W _ n y q'
      have e2 := vertexTwistCellNativeEquiv_apply R I _ n z (relabelFace hj q' h)
      erw [e1, e2, hy q', dite_eq_left h]
      rw [hdeg]
      have hc : CechCubicalCell.relabelCoefficient ℤ j q =
          (-1 : ℤ) ^ vertexMapInversions j (faceOverlap (fun i => q (j i))) := by
        rw [CechCubicalCell.relabelCoefficient, ite_eq_left h, relabelInversions_eq_vertexMapInversions]
        rfl
      have hm : faceMonoidPull j q (fun i => m (j i)) = m :=
        faceMonoidPull_restrict j q hj m (fun w hw => (hoff w hw).2)
      change ((-1 : R) ^ faceDegree q • CechCubicalCell.relabelCoefficient ℤ j q • facePull j q R
        (vertexTwistSheafFaceSectionsEquiv R I (fun i => -(dI i : ℤ)) (fun i => q (j i))
          (sectionsEquiv (vertexCoordinateOpen R I) _ n z (relabelFace hj q' h)))).coeff m = _
      rw [hc, ← hm, AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply,
        facePull_coeff_faceMonoidPull j q R hj, AddMonoidAlgebra.coeff_smul_apply, vertexMapSign,
        smul_eq_mul, smul_eq_mul, zsmul_eq_mul]
      simp only [hm]
      push_cast
      ring
    · have hq' : (faceDegree (fun i => q (j i)) : ℤ) ≠ n := by rw [hdeg]; exact hq
      rw [vertexTwistCellNativeEquiv_apply_ne R W _ n y q hq,
        vertexTwistCellNativeEquiv_apply_ne R I _ n z _ hq']
      simp
  · rw [cechExtend_apply_of_not_unitOff R _ hu]
    have hw : ∃ w, (∀ i, j i ≠ w) ∧ ¬ (q w ≠ 2 ∧ m w = 0) := by
      by_contra hn
      push Not at hn
      exact hu (fun w hw => (embedFace_unitBasis_iff q m w).2 (hn w hw))
    obtain ⟨w, hwj, hwn⟩ := hw
    by_cases hq : (faceDegree q : ℤ) = n
    · let q' : FaceIndex (V := W) n := faceIndexOfDegree W n q hq
      have e1 := vertexTwistCellNativeEquiv_apply R W _ n y q'
      erw [e1, hy q']
      by_cases h : ∀ w, q'.val w = 2 → ∃ i, j i = w
      · rw [dite_eq_left h]
        have hq2 : q w ≠ 2 := fun h2 => by
          obtain ⟨i, hi⟩ := h w h2
          exact hwj i hi
        have hmw : m w ≠ 0 := fun h0 => hwn ⟨hq2, h0⟩
        have hz : (facePull j q R (vertexTwistSheafFaceSectionsEquiv R I (fun i => -(dI i : ℤ))
            (fun i => q (j i)) (sectionsEquiv (vertexCoordinateOpen R I) _ n z
              (relabelFace hj q' h)))).coeff m = 0 := by
          apply facePull_coeff_of_notMem
          intro m' hm'
          apply hmw
          rw [← hm']
          exact faceMonoidPull_apply_of_notMem j q m' hwj
        change ((-1 : R) ^ faceDegree q • CechCubicalCell.relabelCoefficient ℤ j q • facePull j q R
          (vertexTwistSheafFaceSectionsEquiv R I (fun i => -(dI i : ℤ)) (fun i => q (j i))
            (sectionsEquiv (vertexCoordinateOpen R I) _ n z (relabelFace hj q' h)))).coeff m = 0
        rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply, hz, smul_zero,
          smul_zero]
      · rw [dite_eq_right h]
        simp
    · rw [vertexTwistCellNativeEquiv_apply_ne R W _ n y q hq]
      simp

end Coefficients

end BPFixedPoints.Multigraph
