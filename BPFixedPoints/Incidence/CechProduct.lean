import BPFixedPoints.Incidence.CechTensor
import BPFixedPoints.StateSum.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Product two-chart Čech complex and free state-cohomology bases

Tensor finitely many one-vertex contractions and express all terms as free
modules on Laurent monomials. The underlying total module is independent of
the degree vector. The contraction target has basis ∀v,Fin(phi(d v)), empty
when a vertex has degree one.
-/

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

variable (R : Type*) [CommRing R]

abbrev LineC := CechLine.C0 R × CechLine.C1 R
abbrev LineH (d : ℕ) := CechLine.H0 R d × CechLine.H1 R d

noncomputable def lineD (d : ℕ) : Module.End R (LineC R) :=
  (0 : LineC R →ₗ[R] CechLine.C0 R).prod
    ((CechLine.differential R d).comp (LinearMap.fst R _ _))

noncomputable def lineH (d : ℕ) : Module.End R (LineC R) :=
  ((CechLine.homotopy R d).comp (LinearMap.snd R _ _)).prod 0

noncomputable def lineI (d : ℕ) : LineH R d →ₗ[R] LineC R :=
  (CechLine.inclusionZero R d).prodMap (CechLine.inclusionOne R d)

noncomputable def lineP (d : ℕ) : LineC R →ₗ[R] LineH R d :=
  (CechLine.projectionZero R d).prodMap (CechLine.projectionOne R d)

noncomputable def lineSign : Module.End R (LineC R) := LinearMap.id.prodMap (-LinearMap.id)
noncomputable def lineSignH (d : ℕ) : Module.End R (LineH R d) := LinearMap.id.prodMap (-LinearMap.id)

@[simp] theorem lineD_apply (d : ℕ) (x : LineC R) :
    lineD R d x = (0, CechLine.differential R d x.1) := rfl
@[simp] theorem lineH_apply (d : ℕ) (x : LineC R) :
    lineH R d x = (CechLine.homotopy R d x.2, 0) := rfl
@[simp] theorem lineI_apply (d : ℕ) (x : LineH R d) :
    lineI R d x = (CechLine.inclusionZero R d x.1, CechLine.inclusionOne R d x.2) := rfl
@[simp] theorem lineP_apply (d : ℕ) (x : LineC R) :
    lineP R d x = (CechLine.projectionZero R d x.1, CechLine.projectionOne R d x.2) := rfl
@[simp] theorem lineSign_apply (x : LineC R) : lineSign R x = (x.1, -x.2) := rfl
@[simp] theorem lineSignH_apply (d : ℕ) (x : LineH R d) :
    lineSignH R d x = (x.1, -x.2) := rfl

/-- One-vertex Čech strong contraction assembled on the total graded module. -/
noncomputable def line (d : ℕ) : GradedContraction R (LineC R) (LineH R d) where
  d := lineD R d
  h := lineH R d
  i := lineI R d
  p := lineP R d
  sign := lineSign R
  signH := lineSignH R d
  d_sq := by ext x <;> simp
  h_sq := by ext x <;> simp
  d_i := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have h := LinearMap.congr_fun (CechLine.differential_inclusionZero R d) a
    exact Prod.ext rfl h
  p_d := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have h := LinearMap.congr_fun (CechLine.projectionOne_differential R d) a
    exact Prod.ext (map_zero (CechLine.projectionZero R d)) h
  p_i := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    exact Prod.ext
      (LinearMap.congr_fun (CechLine.projectionZero_inclusionZero R d) a)
      (LinearMap.congr_fun (CechLine.projectionOne_inclusionOne R d) b)
  h_i := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have h := LinearMap.congr_fun (CechLine.homotopy_inclusionOne R d) b
    exact Prod.ext h rfl
  p_h := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have h := LinearMap.congr_fun (CechLine.projectionZero_homotopy R d) b
    exact Prod.ext h (map_zero (CechLine.projectionOne R d))
  homotopy := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have ha := LinearMap.congr_fun (CechLine.homotopy_differential R d) a
    have hb := LinearMap.congr_fun (CechLine.differential_homotopy R d) b
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at ha hb
    simp only [Module.End.mul_apply, LinearMap.add_apply, lineD_apply, lineH_apply,
      lineI_apply, lineP_apply, LinearMap.comp_apply, Module.End.one_apply, ha, hb]
    ext <;> simp
  sign_sq := by ext x <;> simp
  signH_sq := by ext x <;> simp
  sign_d := by ext x <;> simp
  sign_h := by ext x <;> simp
  sign_i := by ext x <;> simp
  p_sign := by ext x <;> simp

/-- One-vertex Čech basis; the final summand is degree one. -/
abbrev Basis := ℕ ⊕ ℕ ⊕ ℤ

abbrev C (V : Type*) := (V → Basis) →₀ R
abbrev HBasis {V : Type*} (d : V → ℕ) := (v : V) → Fin (phi (d v))
abbrev H {V : Type*} (d : V → ℕ) := HBasis d →₀ R

/-- Isomorphism between the monomial free basis and the three one-vertex terms. -/
noncomputable def lineBasisEquiv : (Basis →₀ R) ≃ₗ[R] LineC R :=
  (Finsupp.sumFinsuppLEquivProdFinsupp R).trans
    ((LinearEquiv.refl R (ℕ →₀ R)).prodCongr (Finsupp.sumFinsuppLEquivProdFinsupp R)) |>.trans
    (LinearEquiv.prodAssoc R (ℕ →₀ R) (ℕ →₀ R) (ℤ →₀ R)).symm

noncomputable def lineHBasisEquiv (d : ℕ) : LineH R d ≃ₗ[R] (Fin (phi d) →₀ R) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp R).symm.trans
    (Finsupp.mapDomain.linearEquiv R R
      (finSumFinEquiv.trans (finCongr (by cases d <;> simp [phi]))))

/-- One-vertex contraction entirely in free-basis coordinates. -/
noncomputable def lineFree (d : ℕ) :
    GradedContraction R (Basis →₀ R) (Fin (phi d) →₀ R) :=
  (line R d).congr (lineBasisEquiv R).symm (lineHBasisEquiv R d)

/-- Free-module isomorphism tensoring the head of a finite sequence with its tail. -/
noncomputable def consEquiv {n : ℕ} (B : Fin (n + 1) → Type*) :
    (B 0 →₀ R) ⊗[R] (((i : Fin n) → B i.succ) →₀ R) ≃ₗ[R]
      (((i : Fin (n + 1)) → B i) →₀ R) :=
  (finsuppTensorFinsupp' R _ _).trans
    (Finsupp.mapDomain.linearEquiv R R (Fin.consEquiv B))

/-- Empty product: identify two singleton bases; differential and homotopy are zero. -/
noncomputable def empty (d : Fin 0 → ℕ) : GradedContraction R (C R (Fin 0)) (H R d) := by
  let e : C R (Fin 0) ≃ₗ[R] H R d :=
    Finsupp.mapDomain.linearEquiv R R (Equiv.ofUnique _ _)
  exact
    { d := 0
      h := 0
      i := e.symm.toLinearMap
      p := e.toLinearMap
      sign := 1
      signH := 1
      d_sq := by simp
      d_i := by simp
      p_d := by simp
      p_i := by ext; simp
      homotopy := by ext; simp
      h_sq := by simp
      h_i := by simp
      p_h := by simp
      sign_sq := by simp
      signH_sq := by simp
      sign_d := by ext; simp
      sign_h := by ext; simp
      sign_i := by ext; simp
      p_sign := by ext; simp }

/-- Tensor vertices successively, returning to free-basis coordinates at each step. -/
noncomputable def finProduct : (n : ℕ) → (d : Fin n → ℕ) →
    GradedContraction R (C R (Fin n)) (H R d)
  | 0, d => empty R d
  | n + 1, d =>
    ((lineFree R (d 0)).tensor (finProduct n (fun i => d i.succ))).congr
      (consEquiv R fun _ => Basis)
      (consEquiv R fun i => Fin (phi (d i)))

/-- Product Čech contraction on an arbitrary finite vertex set. -/
noncomputable def contraction {V : Type*} [Fintype V] (d : V → ℕ) :
    GradedContraction R (C R V) (H R d) :=
  let e := (Fintype.equivFin V).symm
  (finProduct R (Fintype.card V) (fun i => d (e i))).congr
    (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl Basis)))
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun v => Fin (phi (d v))) e))

end BPFixedPoints.CechProduct
