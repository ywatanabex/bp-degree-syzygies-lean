import BPFixedPoints.Incidence.CechCupSigns
import BPFixedPoints.Incidence.ExteriorProduct
import BPFixedPoints.Incidence.KoszulCech

/-!
# Product on the Koszul–Čech total complex with edge exterior factors

Since the existing total differential places Čech first, insert the sign
interchanging the left exterior degree and right Čech degree. Define the
product as a coefficient-bilinear map on the actual total module.
-/

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable def incCupCoefficient (S T : Finset E) :
    IncCechModule (V := V) (E := E) →ₗ[IncCoeffRing E]
      IncCechModule (V := V) (E := E) →ₗ[IncCoeffRing E]
        IncCechModule (V := V) (E := E) :=
  (chainCup (IncCoeffRing E) (G.deg S) (G.deg T)).compl₂
    (parity (IncCoeffRing E) ^ S.card)

noncomputable def incTotalCup : IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E]
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E]
      IncTotalModule (V := V) (E := E) :=
  Finsupp.lsum (IncCoeffRing E) fun S => (Finsupp.lsum (IncCoeffRing E)).comp
    (LinearMap.pi fun T => (G.incCupCoefficient S T).compr₂
      (Koszul.wedgeSingle (R := IncCoeffRing E) S T))

theorem incTotalCup_single (S T : Finset E) (x y : IncCechModule (V := V) (E := E)) :
    G.incTotalCup (single S x) (single T y) =
      Koszul.wedgeSingle (R := IncCoeffRing E) S T (G.incCupCoefficient S T x y) := by
  simp [incTotalCup]

noncomputable def incTotalSign :
    Module.End (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) :=
  Koszul.diagonal (fun S => (-1 : IncCoeffRing E) ^ S.card • parity (IncCoeffRing E))

@[simp] theorem incTotalSign_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    incTotalSign (single S x) =
      single S ((-1 : IncCoeffRing E) ^ S.card • parity (IncCoeffRing E) x) := by
  simp [incTotalSign]

theorem incEdgeAction_cup_left (S S' T : Finset E) (e : E)
    (x y : IncCechModule (V := V) (E := E)) :
    chainCup (IncCoeffRing E) (G.deg S') (G.deg T) (G.incEdgeAction e x) y =
      G.incEdgeAction e (chainCup (IncCoeffRing E) (G.deg S) (G.deg T) x y) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, chainCup_multiply_left (IncCoeffRing E) (G.deg S) (G.deg S') (G.deg T)]

theorem incEdgeAction_cup_right (S : Finset E) {T : Finset E} {e : E} (he : e ∈ T)
    (x y : IncCechModule (V := V) (E := E)) :
    chainCup (IncCoeffRing E) (G.deg S) (G.deg (T.erase e)) x (G.incEdgeAction e y) =
      G.incEdgeAction e (chainCup (IncCoeffRing E) (G.deg S) (G.deg T) x y) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  have h := chainCup_multiply_right (IncCoeffRing E) (G.deg S) (G.deg T)
    (G.incSectionLeft e α β) (G.incSectionRight e α β)
    (G.incSection_sum_le_degree he α β) x y
  rw [G.degree_sub_incSection he α β] at h
  exact h

theorem incEdgeAction_parity (e : E) (x : IncCechModule (V := V) (E := E)) :
    G.incEdgeAction e (parity (IncCoeffRing E) x) =
      parity (IncCoeffRing E) (G.incEdgeAction e x) := by
  rw [parity_eq (IncCoeffRing E) (G.deg ∅)]
  exact (LinearMap.congr_fun (G.incEdgeAction_sign ∅ ∅ e) x).symm

theorem incEdgeAction_parity_pow (e : E) (n : ℕ) (x : IncCechModule (V := V) (E := E)) :
    G.incEdgeAction e ((parity (IncCoeffRing E) ^ n) x) =
      (parity (IncCoeffRing E) ^ n) (G.incEdgeAction e x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [parity_pow_succ_apply, parity_pow_succ_apply,
      G.incEdgeAction_parity, ih]

theorem incCupCoefficient_edge_left {S : Finset E} (T : Finset E) {e : E} (he : e ∈ S)
    (x y : IncCechModule (V := V) (E := E)) :
    G.incCupCoefficient (S.erase e) T (parity (IncCoeffRing E) (G.incEdgeAction e x)) y =
      parity (IncCoeffRing E) (G.incEdgeAction e (G.incCupCoefficient S T x y)) := by
  change chainCup _ _ _ (parity _ (G.incEdgeAction e x)) ((parity _ ^ (S.erase e).card) y) =
    parity _ (G.incEdgeAction e (chainCup _ _ _ x ((parity _ ^ S.card) y)))
  rw [← G.incEdgeAction_cup_left S (S.erase e) T e, parity_cup]
  have hn : S.card = (S.erase e).card + 1 := (Finset.card_erase_add_one he).symm
  rw [hn, parity_pow_succ_apply, parity_twice]

theorem incCupCoefficient_edge_right (S : Finset E) {T : Finset E} {e : E} (he : e ∈ T)
    (x y : IncCechModule (V := V) (E := E)) :
    G.incCupCoefficient S (T.erase e) (parity (IncCoeffRing E) x)
        (parity (IncCoeffRing E) (G.incEdgeAction e y)) =
      parity (IncCoeffRing E) (G.incEdgeAction e (G.incCupCoefficient S T x y)) := by
  change chainCup _ _ _ (parity _ x) ((parity _ ^ S.card) (parity _ (G.incEdgeAction e y))) =
    parity _ (G.incEdgeAction e (chainCup _ _ _ x ((parity _ ^ S.card) y)))
  rw [← G.incEdgeAction_cup_right S he, parity_cup,
    G.incEdgeAction_parity_pow, parity_pow_comm]

end BPFixedPoints.Multigraph
