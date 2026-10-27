import BPFixedPoints.Incidence.CechCupNaturality
import BPFixedPoints.Incidence.CechProductDegree

/-! # Integer grading of the full Čech product -/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.CechProduct

open Finsupp ResolutionTools

theorem finCupBasis_degree (n : ℕ) (e : Fin n → ℕ) (x y z : Fin n → Basis)
    (h : finCupBasis n e x y = some z) : cechDegree z = cechDegree x + cechDegree y := by
  induction n with
  | zero => simp [cechDegree]
  | succ n ih =>
    simp only [finCupBasis, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [cechDegree_cons, ih _ _ _ _ hb, lineCupBasis_degree _ ha]
    have hx := cechDegree_cons (x 0) (Fin.tail x)
    have hy := cechDegree_cons (y 0) (Fin.tail y)
    rw [Fin.cons_self_tail] at hx hy
    omega

variable (R : Type*) [CommRing R]

theorem finChainPairing_mul_single_degree (n : ℕ) (d e : Fin n → ℕ)
    (x y : Fin n → Basis) (r s : R) :
    (finChainPairing R n d e).mul (single x r) (single y s) ∈
      supported R R {z | (cechDegree z : ℤ) = (cechDegree x : ℤ) + cechDegree y} := by
  rw [finChainPairing_mul_single]
  cases h : finCupBasis n e x y with
  | none => exact Submodule.zero_mem _
  | some z => exact single_mem_supported R _ (by
      change (cechDegree z : ℤ) = _
      rw [finCupBasis_degree n e x y z h, Nat.cast_add])

theorem chainCup_single_degree {V : Type*} [Fintype V] (d e : V → ℕ)
    (x y : V → Basis) (r s : R) :
    chainCup R d e (single x r) (single y s) ∈
      supported R R {z | (cechDegree z : ℤ) = (cechDegree x : ℤ) + cechDegree y} := by
  let v := (Fintype.equivFin V).symm
  let b := v.arrowCongr (Equiv.refl Basis)
  have hsingle (z : V → Basis) (t : R) :
      single z t = vertexReindex R (single (b.symm z) t) := by
    change single z t = mapDomain b (single (b.symm z) t)
    rw [mapDomain_single, Equiv.apply_symm_apply]
  rw [hsingle x r, hsingle y s, chainCup_reindex]
  have hmap := HasDegree.mapDomain (R := R) (M := R) b
    (fun z => (cechDegree z : ℤ)) (fun z => (cechDegree z : ℤ))
    (fun z => by rw [cechDegree_arrowCongr])
  have h := hmap _ _ (finChainPairing_mul_single_degree R (Fintype.card V) (d ∘ v) (e ∘ v) (b.symm x) (b.symm y) r s)
  have hx : cechDegree (b.symm x) = cechDegree x := by
    simpa only [b, Equiv.apply_symm_apply] using (cechDegree_arrowCongr v (b.symm x)).symm
  have hy : cechDegree (b.symm y) = cechDegree y := by
    simpa only [b, Equiv.apply_symm_apply] using (cechDegree_arrowCongr v (b.symm y)).symm
  simpa only [hx, hy, add_zero, vertexReindex, b, v, lmapDomain_apply,
    mapDomain.coe_linearEquiv] using h

theorem chainCup_degree {V : Type*} [Fintype V] (d e : V → ℕ) (p q : ℤ)
    {x y : C R V} (hx : x ∈ supported R R {b | (cechDegree b : ℤ) = p})
    (hy : y ∈ supported R R {b | (cechDegree b : ℤ) = q}) :
    chainCup R d e x y ∈ supported R R {b | (cechDegree b : ℤ) = p + q} := by
  rw [← x.sum_single, map_finsuppSum, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro a ha
  rw [← y.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro b hb
  have ha' : (cechDegree a : ℤ) = p := (mem_supported R x).mp hx ha
  have hb' : (cechDegree b : ℤ) = q := (mem_supported R y).mp hy hb
  simpa only [ha', hb'] using chainCup_single_degree R d e a b (x a) (y b)

end BPFixedPoints.CechProduct
