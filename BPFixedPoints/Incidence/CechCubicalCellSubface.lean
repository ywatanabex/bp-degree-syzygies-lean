import BPFixedPoints.Incidence.CechCubicalCellDegree
import BPFixedPoints.Incidence.CechCubicalCellBoundary
import BPFixedPoints.Incidence.CechFaceRefinement

/-! # The specified original prism stays inside its original face

The base vertex is required to belong to the original face. Under precisely
that condition the existing tensor prism fills positive cycles without using
any cells outside the face. This is the local support needed for free-open
cubical resolutions and their comparison with tuple Čech resolutions.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type*) [CommRing R]

/-- Chains on the original subfaces of one specified original face. -/
def subfaces {V : Type*} (p : V → Fin 3) : Submodule R (Cells R V) :=
  supported R R {q | FaceRefines q p}

/-- The original prism vanishes at its specified base endpoint. -/
theorem prismCoefficient_self (b : Fin 2) : prismCoefficient R b b.castSucc = 0 := by
  fin_cases b <;> simp [prismCoefficient]

private theorem cons_subfaces {n : ℕ} {p : Fin n → Fin 3} {k a : Fin 3}
    (hk : k = a ∨ a = 2) {x : Cells R (Fin n)} (hx : x ∈ subfaces R p) :
    mapDomain (Fin.cons k) x ∈ subfaces R (Fin.cons a p) := by
  intro q hq
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
  have hp : FaceRefines s p := hx hs
  intro v
  refine Fin.cases ?_ (fun j => ?_) v
  · exact hk
  · exact hp j

/-- In finite tensor coordinates the specified prism uses only original subfaces. -/
theorem finContraction_h_single_subfaces (n : ℕ) (b : Fin n → Fin 2)
    (p q : Fin n → Fin 3) (r : R)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (hq : FaceRefines q p) :
    (finContraction R n b).h (single q r) ∈ subfaces R p := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    rw [finContraction_h_single]
    apply Submodule.add_mem
    · by_cases hc : prismCoefficient R (b 0) (q 0) = 0
      · rw [hc,zero_mul,Finsupp.single_zero]
        exact Submodule.zero_mem _
      · apply single_mem_supported R _
        intro v
        refine Fin.cases ?_ (fun j => ?_) v
        · have hp : p 0 = 2 := by
            by_contra hp
            have heq : q 0 = (b 0).castSucc :=
              ((hq 0).resolve_right hp).trans ((hb 0).resolve_right hp).symm
            exact hc (heq ▸ prismCoefficient_self R (b 0))
          exact Or.inr hp
        · exact hq j.succ
    · by_cases h₀ : q 0 = 2
      · rw [ite_eq_left h₀]
        exact Submodule.zero_mem _
      · rw [ite_eq_right h₀]
        have hh := ih (Fin.tail b) (Fin.tail p) (Fin.tail q)
          (fun j => hb j.succ) (fun j => hq j.succ)
        simpa only [Fin.cons_self_tail] using cons_subfaces R (hb 0) hh

/-- Relabelling carries original subfaces to precisely the relabelled original subfaces. -/
theorem mapDomain_subfaces {V W : Type*} (e : V ≃ W) {p : V → Fin 3} {x : Cells R V}
    (hx : x ∈ subfaces R p) :
    mapDomain (e.arrowCongr (Equiv.refl (Fin 3))) x ∈
      subfaces R (e.arrowCongr (Equiv.refl (Fin 3)) p) := by
  classical
  intro q hq
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
  have hp : FaceRefines s p := hx hs
  intro w
  simpa using hp (e.symm w)

/-- The labelled original prism retains the original specified face on every original cell generator. -/
theorem contraction_h_single_subfaces {V : Type*} [Fintype V]
    (b : V → Fin 2) (p q : V → Fin 3) (r : R)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (hq : FaceRefines q p) :
    (contraction R b).h (single q r) ∈ subfaces R p := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  change (Finsupp.mapDomain.linearEquiv R R ep)
    ((finContraction R (Fintype.card V) (fun i => b (e i))).h
      ((Finsupp.mapDomain.linearEquiv R R ep).symm (single q r))) ∈ _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain ep ((finContraction R (Fintype.card V) (fun i => b (e i))).h
    (mapDomain ep.symm (single q r))) ∈ _
  rw [mapDomain_single]
  have hh := finContraction_h_single_subfaces R (Fintype.card V) (fun i => b (e i))
    (ep.symm p) (ep.symm q) r (fun j => hb (e j)) (fun j => hq (e j))
  simpa only [← show e.arrowCongr (Equiv.refl (Fin 3)) = ep from rfl,
    Equiv.apply_symm_apply] using mapDomain_subfaces R e hh

/-- The specified original prism preserves every original face-supported chain. -/
theorem contraction_h_subfaces {V : Type*} [Fintype V]
    (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (x : Cells R V) (hx : x ∈ subfaces R p) :
    (contraction R b).h x ∈ subfaces R p := by
  rw [← x.sum_single,map_finsuppSum]
  apply Submodule.sum_mem
  intro q hq
  exact contraction_h_single_subfaces R b p q (x q) hb (hx hq)

/-- The original component inclusion uses the base vertex inside the same original face. -/
theorem contraction_i_subfaces {V : Type*} [Fintype V]
    (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (y : Components R V) :
    (contraction R b).i y ∈ subfaces R p := by
  rw [← y.sum_single,map_finsuppSum]
  apply Submodule.sum_mem
  intro q _
  change (contraction R b).i (single q (y q)) ∈ subfaces R p
  rw [contraction_i_single]
  exact single_mem_supported R _ hb

/-- Every original endpoint boundary stays inside the same original face. -/
theorem endpoint_refines {V : Type*} [DecidableEq V] {q p : V → Fin 3}
    (hq : FaceRefines q p) (v : V) (hv : q v = 2) (k : Fin 3) :
    FaceRefines (Function.update q v k) p := by
  intro w
  by_cases hw : w = v
  · subst w
    exact Or.inr (by rcases hq v with h | h; exact h.symm.trans hv; exact h)
  · simpa only [Function.update_of_ne hw] using hq w

/-- The original boundary preserves original face support on every original generator. -/
theorem contraction_d_single_subfaces {V : Type} [Fintype V] [DecidableEq V]
    (b : V → Fin 2) (p q : V → Fin 3) (r : R) (hq : FaceRefines q p) :
    (contraction R b).d (single q r) ∈ subfaces R p := by
  rw [contraction_d_single]
  apply Submodule.sum_mem
  intro v _
  by_cases hv : q v = 2
  · apply Submodule.sub_mem
    · exact single_mem_supported R _ (endpoint_refines hq v hv 0)
    · exact single_mem_supported R _ (endpoint_refines hq v hv 1)
  · simp only [hv,ite_false,zero_mul,mul_zero,Finsupp.single_zero,sub_self]
    exact Submodule.zero_mem _

/-- The original boundary preserves every original face-supported chain. -/
theorem contraction_d_subfaces {V : Type} [Fintype V] [DecidableEq V]
    (b : V → Fin 2) (p : V → Fin 3) (x : Cells R V) (hx : x ∈ subfaces R p) :
    (contraction R b).d x ∈ subfaces R p := by
  rw [← x.sum_single,map_finsuppSum]
  apply Submodule.sum_mem
  intro q hq
  exact contraction_d_single_subfaces R b p q (x q) (hx hq)

/-- Positive original cycles have the specified next-degree primitive inside the same original face. -/
theorem contraction_positive_primitive_in_face {V : Type*} [Fintype V]
    (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (n : ℕ) (hn : 0 < n)
    (x : Cells R V) (hx : x ∈ subfaces R p)
    (hdeg : x ∈ supported R R {q | cellDegree q = -(n : ℤ)})
    (hd : (contraction R b).d x = 0) :
    (contraction R b).h x ∈ subfaces R p ∧
      (contraction R b).h x ∈ supported R R {q | cellDegree q = -((n+1 : ℕ) : ℤ)} ∧
        (contraction R b).d ((contraction R b).h x) = x :=
  ⟨contraction_h_subfaces R b p hb x hx,contraction_positive_primitive R b n hn x hdeg hd⟩

end BPFixedPoints.CechCubicalCell
