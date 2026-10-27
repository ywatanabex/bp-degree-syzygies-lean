import BPFixedPoints.Incidence.KoszulCechCup
import BPFixedPoints.Incidence.Generators

/-! # Leibniz rule for the exterior Čech product and the total differential -/

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incKoszulPerturbation_eq :
    G.incKoszulPerturbation = Koszul.differentialLinear
      (fun e => (parity (IncCoeffRing E)).comp (G.incEdgeAction e)) := by
  apply Finsupp.lhom_ext
  intro S x
  rw [G.incKoszulPerturbation_single, Koszul.differentialLinear_single]
  apply Finset.sum_congr rfl
  intro e he
  rw [← parity_eq (IncCoeffRing E) (G.deg (S.erase e)), map_smul]
  rfl

theorem incTotalCup_edge_leibniz_single (e : E) (S T : Finset E)
    (x y : IncCechModule (V := V) (E := E)) :
    Koszul.linearTerm e ((parity (IncCoeffRing E)).comp (G.incEdgeAction e))
        (G.incTotalCup (single S x) (single T y)) =
      G.incTotalCup (Koszul.linearTerm e ((parity (IncCoeffRing E)).comp
          (G.incEdgeAction e)) (single S x)) (single T y) +
      G.incTotalCup (incTotalSign (single S x))
        (Koszul.linearTerm e ((parity (IncCoeffRing E)).comp
          (G.incEdgeAction e)) (single T y)) := by
  rw [G.incTotalCup_single, Koszul.linearTerm_wedgeSingle, Koszul.erase_wedgeSingle]
  simp only [LinearMap.comp_apply, Koszul.linearTerm_single, incTotalSign_single]
  by_cases heS : e ∈ S <;> by_cases heT : e ∈ T <;>
    simp only [heS, heT, ↓reduceIte, map_zero, LinearMap.zero_apply, add_zero, zero_add,
      ← Finsupp.smul_single, map_smul, LinearMap.smul_apply, G.incTotalCup_single,
      map_smul, LinearMap.smul_apply, smul_smul]
  · rw [G.incCupCoefficient_edge_left T heS, G.incCupCoefficient_edge_right S heT, mul_comm (Koszul.sign (A := IncCoeffRing E) T e)]
  · rw [G.incCupCoefficient_edge_left T heS]
  · rw [G.incCupCoefficient_edge_right S heT, mul_comm (Koszul.sign (A := IncCoeffRing E) T e)]

theorem incTotalCup_edge_leibniz (e : E) (x y : IncTotalModule (V := V) (E := E)) :
    Koszul.linearTerm e ((parity (IncCoeffRing E)).comp (G.incEdgeAction e))
        (G.incTotalCup x y) =
      G.incTotalCup (Koszul.linearTerm e ((parity (IncCoeffRing E)).comp
          (G.incEdgeAction e)) x) y +
      G.incTotalCup (incTotalSign x)
        (Koszul.linearTerm e ((parity (IncCoeffRing E)).comp
          (G.incEdgeAction e)) y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; abel
  | single S x =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']; abel
    | single T y => exact G.incTotalCup_edge_leibniz_single e S T x y

theorem incTotalCup_koszul_leibniz (x y : IncTotalModule (V := V) (E := E)) :
    G.incKoszulPerturbation (G.incTotalCup x y) =
      G.incTotalCup (G.incKoszulPerturbation x) y +
      G.incTotalCup (incTotalSign x) (G.incKoszulPerturbation y) := by
  simp only [G.incKoszulPerturbation_eq, Koszul.differentialLinear,
    LinearMap.sum_apply, map_sum, G.incTotalCup_edge_leibniz, Finset.sum_add_distrib]

theorem incCupCoefficient_cech_leibniz {S T : Finset E} (h : Disjoint S T)
    (x y : IncCechModule (V := V) (E := E)) :
    (contraction (IncCoeffRing E) (G.deg (S ∪ T))).d (G.incCupCoefficient S T x y) =
      G.incCupCoefficient S T ((contraction (IncCoeffRing E) (G.deg S)).d x) y +
      (-1 : IncCoeffRing E) ^ S.card • G.incCupCoefficient S T
        (parity (IncCoeffRing E) x) ((contraction (IncCoeffRing E) (G.deg T)).d y) := by
  have hdeg : G.deg (S ∪ T) = G.deg S + G.deg T :=
    funext (G.deg_union_of_disjoint h)
  change (contraction _ _).d (chainCup _ _ _ x ((parity _ ^ S.card) y)) = _
  rw [hdeg, chainCup_leibniz, d_parity_pow, map_smul,
    ← parity_eq (IncCoeffRing E) (G.deg S)]
  rfl

theorem incTotalCup_cech_leibniz_single (S T : Finset E)
    (x y : IncCechModule (V := V) (E := E)) :
    G.incCechContraction.d (G.incTotalCup (single S x) (single T y)) =
      G.incTotalCup (G.incCechContraction.d (single S x)) (single T y) +
      G.incTotalCup (incTotalSign (single S x)) (G.incCechContraction.d (single T y)) := by
  simp only [G.incCechContraction_d, Koszul.diagonal_single, incTotalSign_single,
    G.incTotalCup_single]
  simp only [G.incTotalCup_single, Koszul.wedgeSingle_apply]
  by_cases h : Disjoint S T
  · simp only [h, ↓reduceIte, Koszul.diagonal_single, map_smul,
      G.incCupCoefficient_cech_leibniz h, smul_add, Finsupp.single_add,
      LinearMap.smul_apply, smul_smul]
  · simp [h]

theorem incTotalCup_cech_leibniz (x y : IncTotalModule (V := V) (E := E)) :
    G.incCechContraction.d (G.incTotalCup x y) =
      G.incTotalCup (G.incCechContraction.d x) y +
      G.incTotalCup (incTotalSign x) (G.incCechContraction.d y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; abel
  | single S x =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']; abel
    | single T y => exact G.incTotalCup_cech_leibniz_single S T x y

theorem incTotalCup_leibniz (x y : IncTotalModule (V := V) (E := E)) :
    G.incTotalDifferential (G.incTotalCup x y) =
      G.incTotalCup (G.incTotalDifferential x) y +
      G.incTotalCup (incTotalSign x) (G.incTotalDifferential y) := by
  simp only [incTotalDifferential, LinearMap.add_apply, G.incTotalCup_cech_leibniz,
    G.incTotalCup_koszul_leibniz, map_add, LinearMap.add_apply]
  abel

theorem incTotalCup_cycles {x y : IncTotalModule (V := V) (E := E)}
    (hx : G.incTotalDifferential x = 0) (hy : G.incTotalDifferential y = 0) :
    G.incTotalDifferential (G.incTotalCup x y) = 0 := by
  rw [G.incTotalCup_leibniz, hx, hy]
  simp

end BPFixedPoints.Multigraph
