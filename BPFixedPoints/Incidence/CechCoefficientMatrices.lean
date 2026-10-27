import BPFixedPoints.Incidence.CoefficientMatrices
import BPFixedPoints.Incidence.CechProductDegree

/-!
# The actual Čech contraction has constant matrix entries

The statement holds over every subring of the coefficient ring. It is
proved from the one-vertex formulas and propagated through the actual
finite tensor construction, not assumed of the resulting contraction.
-/

namespace BPFixedPoints.CechProduct

open Finsupp ResolutionTools
open scoped TensorProduct

variable (R : Type*) [CommRing R] (A : Subring R)

private def LineCoeffs (x : LineC R) : Prop :=
  AllCoeffsIn A x.1.1 ∧ AllCoeffsIn A x.1.2 ∧ AllCoeffsIn A x.2

private def HCoeffs {d : ℕ} (x : LineH R d) : Prop :=
  AllCoeffsIn A x.1 ∧ AllCoeffsIn A x.2

private theorem lineBasis_coeffs {x : Basis →₀ R} (hx : AllCoeffsIn A x) :
    LineCoeffs R A (lineBasisEquiv R x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k; exact hx (Sum.inl k)
  · intro k; exact hx (Sum.inr (Sum.inl k))
  · intro k; exact hx (Sum.inr (Sum.inr k))

private theorem lineBasis_symm_coeffs {x : LineC R} (hx : LineCoeffs R A x) :
    AllCoeffsIn A ((lineBasisEquiv R).symm x) := by
  rintro (k | k | k)
  · exact hx.1 k
  · exact hx.2.1 k
  · exact hx.2.2 k

private theorem lineHBasis_coeffs (d : ℕ) {x : LineH R d} (hx : HCoeffs R A x) :
    AllCoeffsIn A (lineHBasisEquiv R d x) := by
  let e := finSumFinEquiv.trans
    (finCongr (show (if d = 0 then 1 else 0) + (d - 1) = phi d by
      cases d <;> simp [phi]))
  change AllCoeffsIn A
    (Finsupp.mapDomain e ((Finsupp.sumFinsuppLEquivProdFinsupp R).symm x))
  apply (MatrixOver.mapDomain (A := A) e).apply
  rintro (i | j)
  · exact hx.1 i
  · exact hx.2 j

private theorem lineHBasis_symm_coeffs (d : ℕ) {x : Fin (phi d) →₀ R}
    (hx : AllCoeffsIn A x) : HCoeffs R A ((lineHBasisEquiv R d).symm x) := by
  let e := finSumFinEquiv.trans
    (finCongr (show (if d = 0 then 1 else 0) + (d - 1) = phi d by
      cases d <;> simp [phi]))
  have hy := (MatrixOver.mapDomain (A := A) e.symm).apply hx
  constructor
  · intro k
    change (Finsupp.mapDomain e.symm x) (Sum.inl k) ∈ A
    exact hy _
  · intro k
    change (Finsupp.mapDomain e.symm x) (Sum.inr k) ∈ A
    exact hy _

private theorem inclusionZero_fst_matrix (d : ℕ) :
    MatrixOver A ((LinearMap.fst R _ _).comp (CechLine.inclusionZero R d)) := by
  intro k
  change AllCoeffsIn A ((CechLine.inclusionZero R d (single k 1)).1)
  rw [CechLine.inclusionZero_single]
  exact AllCoeffsIn.single _ A.one_mem

private theorem inclusionZero_snd_matrix (d : ℕ) :
    MatrixOver A ((LinearMap.snd R _ _).comp (CechLine.inclusionZero R d)) := by
  intro k
  change AllCoeffsIn A ((CechLine.inclusionZero R d (single k 1)).2)
  rw [CechLine.inclusionZero_single]
  exact AllCoeffsIn.single _ A.one_mem

private theorem projectionOne_matrix (d : ℕ) :
    MatrixOver A (CechLine.projectionOne R d) := by
  intro z
  simp only [CechLine.projectionOne, Finsupp.lsum_single]
  split_ifs
  · exact AllCoeffsIn.single _ A.one_mem
  · exact AllCoeffsIn.zero

private theorem homotopy_fst_matrix (d : ℕ) :
    MatrixOver A ((LinearMap.fst R _ _).comp (CechLine.homotopy R d)) := by
  intro z
  change AllCoeffsIn A ((CechLine.homotopy R d (single z 1)).1)
  rw [CechLine.homotopy_single]
  split_ifs
  · exact (AllCoeffsIn.single _ A.one_mem).neg
  · exact AllCoeffsIn.zero
  · exact AllCoeffsIn.zero

private theorem homotopy_snd_matrix (d : ℕ) :
    MatrixOver A ((LinearMap.snd R _ _).comp (CechLine.homotopy R d)) := by
  intro z
  change AllCoeffsIn A ((CechLine.homotopy R d (single z 1)).2)
  rw [CechLine.homotopy_single]
  split_ifs
  · exact AllCoeffsIn.zero
  · exact AllCoeffsIn.single _ A.one_mem
  · exact AllCoeffsIn.zero

private theorem lineD_coeffs (d : ℕ) {x : LineC R} (hx : LineCoeffs R A x) :
    LineCoeffs R A (lineD R d x) := by
  refine ⟨AllCoeffsIn.zero, AllCoeffsIn.zero, ?_⟩
  change AllCoeffsIn A
    (CechLine.rightRestriction R d x.1.2 - CechLine.leftRestriction R x.1.1)
  have hl := (MatrixOver.mapDomain (A := A) (fun k : ℕ => (k : ℤ))).apply hx.1
  have hr := (MatrixOver.mapDomain (A := A) (fun k : ℕ => -(d : ℤ) - k)).apply hx.2.1
  simpa only [CechLine.rightRestriction, CechLine.leftRestriction, sub_eq_add_neg] using hr.add hl.neg

private theorem lineH_coeffs (d : ℕ) {x : LineC R} (hx : LineCoeffs R A x) :
    LineCoeffs R A (lineH R d x) :=
  ⟨(homotopy_fst_matrix R A d).apply hx.2.2,
    (homotopy_snd_matrix R A d).apply hx.2.2, AllCoeffsIn.zero⟩

private theorem lineI_coeffs (d : ℕ) {x : LineH R d} (hx : HCoeffs R A x) :
    LineCoeffs R A (lineI R d x) :=
  ⟨(inclusionZero_fst_matrix R A d).apply hx.1,
    (inclusionZero_snd_matrix R A d).apply hx.1,
    (MatrixOver.mapDomain (A := A) (fun k : CechLine.H1Index d => -(k : ℤ) - 1)).apply hx.2⟩

private theorem lineP_coeffs (d : ℕ) {x : LineC R} (hx : LineCoeffs R A x) :
    HCoeffs R A (lineP R d x) := by
  constructor
  · change AllCoeffsIn A (CechLine.projectionZero R d x.1)
    unfold CechLine.projectionZero
    split_ifs
    · exact AllCoeffsIn.single _ (hx.2.1 0)
    · exact AllCoeffsIn.zero
  · exact (projectionOne_matrix R A d).apply hx.2.2

/-- The five maps of a concrete graded contraction have entries in `A`. -/
structure ContractionMatrices {I J : Type*}
    (C : GradedContraction R (I →₀ R) (J →₀ R)) : Prop where
  d : MatrixOver A C.d
  h : MatrixOver A C.h
  i : MatrixOver A C.i
  p : MatrixOver A C.p
  sign : MatrixOver A C.sign

theorem lineFree_matrices (d : ℕ) : ContractionMatrices R A (lineFree R d) := by
  constructor
  · intro b
    change AllCoeffsIn A ((lineBasisEquiv R).symm
      (lineD R d (lineBasisEquiv R (single b 1))))
    exact lineBasis_symm_coeffs R A
      (lineD_coeffs R A d (lineBasis_coeffs R A (AllCoeffsIn.single b A.one_mem)))
  · intro b
    change AllCoeffsIn A ((lineBasisEquiv R).symm
      (lineH R d (lineBasisEquiv R (single b 1))))
    exact lineBasis_symm_coeffs R A
      (lineH_coeffs R A d (lineBasis_coeffs R A (AllCoeffsIn.single b A.one_mem)))
  · intro b
    change AllCoeffsIn A ((lineBasisEquiv R).symm
      (lineI R d ((lineHBasisEquiv R d).symm (single b 1))))
    exact lineBasis_symm_coeffs R A
      (lineI_coeffs R A d (lineHBasis_symm_coeffs R A d (AllCoeffsIn.single b A.one_mem)))
  · intro b
    change AllCoeffsIn A (lineHBasisEquiv R d
      (lineP R d (lineBasisEquiv R (single b 1))))
    exact lineHBasis_coeffs R A d
      (lineP_coeffs R A d (lineBasis_coeffs R A (AllCoeffsIn.single b A.one_mem)))
  · intro b
    change AllCoeffsIn A ((lineBasisEquiv R).symm
      (lineSign R (lineBasisEquiv R (single b 1))))
    have hx := lineBasis_coeffs R A (AllCoeffsIn.single b A.one_mem)
    exact lineBasis_symm_coeffs R A ⟨hx.1, hx.2.1, hx.2.2.neg⟩

namespace ContractionMatrices

variable {R A} {I J K L I' J' : Type*}
  {C : GradedContraction R (I →₀ R) (J →₀ R)}
  {D : GradedContraction R (K →₀ R) (L →₀ R)}

theorem congr (hC : ContractionMatrices R A C) (u : I ≃ I') (v : J ≃ J') :
    ContractionMatrices R A
      (C.congr (Finsupp.mapDomain.linearEquiv R R u)
        (Finsupp.mapDomain.linearEquiv R R v)) where
  d := hC.d.congr_mapDomain u u
  h := hC.h.congr_mapDomain u u
  i := hC.i.congr_mapDomain v u
  p := hC.p.congr_mapDomain u v
  sign := hC.sign.congr_mapDomain u u

theorem tensor_congr (hC : ContractionMatrices R A C) (hD : ContractionMatrices R A D)
    (u : I × K ≃ I') (v : J × L ≃ J') :
    ContractionMatrices R A
      ((C.tensor D).congr
        ((finsuppTensorFinsupp' R I K).trans (Finsupp.mapDomain.linearEquiv R R u))
        ((finsuppTensorFinsupp' R J L).trans (Finsupp.mapDomain.linearEquiv R R v))) := by
  constructor
  · intro b
    rw [GradedContraction.congr_d_apply, tensor_d_apply, map_add]
    exact ((hC.d.tensor_congr MatrixOver.id u u) b).add
      ((hC.sign.tensor_congr hD.d u u) b)
  · intro b
    rw [GradedContraction.congr_h_apply, tensor_h_apply, map_add]
    have hps : MatrixOver A (C.projection * C.sign) := by
      simpa only [GradedContraction.projection, Module.End.mul_eq_comp] using
        (hC.i.comp hC.p).comp hC.sign
    exact ((hC.h.tensor_congr MatrixOver.id u u) b).add
      ((hps.tensor_congr hD.h u u) b)
  · intro b
    rw [GradedContraction.congr_i_apply, tensor_i_apply]
    exact (hC.i.tensor_congr hD.i v u) b
  · intro b
    rw [GradedContraction.congr_p_apply, tensor_p_apply]
    exact (hC.p.tensor_congr hD.p u v) b
  · intro b
    rw [GradedContraction.congr_sign_apply, tensor_sign_apply]
    exact (hC.sign.tensor_congr hD.sign u u) b

end ContractionMatrices

theorem finProduct_matrices (n : ℕ) (d : Fin n → ℕ) :
    ContractionMatrices R A (finProduct R n d) := by
  classical
  induction n with
  | zero =>
    let e : (Fin 0 → Basis) ≃ HBasis d := Equiv.ofUnique _ _
    constructor
    · exact MatrixOver.zero
    · exact MatrixOver.zero
    · change MatrixOver A (Finsupp.mapDomain.linearEquiv R R e).symm.toLinearMap
      simpa only [Finsupp.mapDomain.linearEquiv_symm,
        Finsupp.mapDomain.toLinearMap_linearEquiv] using
          (MatrixOver.mapDomain (A := A) e.symm)
    · exact MatrixOver.mapDomain e
    · exact MatrixOver.id
  | succ n ih =>
    rw [finProduct]
    exact (lineFree_matrices R A (d 0)).tensor_congr (ih (Fin.tail d))
      (Fin.consEquiv fun _ : Fin (n + 1) => Basis)
      (Fin.consEquiv fun i => Fin (phi (d i)))

/-- Every matrix entry of the actual product Čech contraction is constant,
indeed it belongs to every subring of the coefficient ring. -/
theorem contraction_matrices {V : Type*} [Fintype V] (d : V → ℕ) :
    ContractionMatrices R A (contraction R d) := by
  classical
  let e := (Fintype.equivFin V).symm
  exact (finProduct_matrices R A (Fintype.card V) (fun i => d (e i))).congr
    (e.arrowCongr (Equiv.refl Basis))
    (Equiv.piCongrLeft (fun v => Fin (phi (d v))) e)

end BPFixedPoints.CechProduct
