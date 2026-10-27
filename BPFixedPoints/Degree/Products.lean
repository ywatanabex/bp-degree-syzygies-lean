import BPFixedPoints.Degree.GenericDegree
import BPFixedPoints.Incidence.Rows

/-!
# Elementary properties of generic degree (remaining `cor:elementary-degree`)

For the disjoint union G₁⊔G₂ on V₁⊕V₂ and E₁⊕E₂, Q is multiplicative
(`Q_disjUnion`), hence so is generic degree (`hasGenericDegree_disjUnion`).
A loopless graph with no nonempty Eulerian edge set has N=1
(`hasGenericDegree_one_of_forest`). Connected trees and unicyclic graphs are
in `Degree/SmallRank.lean`; leaf/subdivision invariance is in `Degree/GenericDegree.lean`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

section DisjUnion

variable {V₁ E₁ V₂ E₂ : Type*}

/-- Disjoint union G₁⊔G₂. -/
def disjUnion (G₁ : Multigraph V₁ E₁) (G₂ : Multigraph V₂ E₂) :
    Multigraph (V₁ ⊕ V₂) (E₁ ⊕ E₂) where
  fst := Sum.elim (fun e => Sum.inl (G₁.fst e)) (fun e => Sum.inr (G₂.fst e))
  snd := Sum.elim (fun e => Sum.inl (G₁.snd e)) (fun e => Sum.inr (G₂.snd e))

variable [DecidableEq V₁] [DecidableEq V₂] [Fintype V₁] [Fintype V₂]
  [DecidableEq E₁] [DecidableEq E₂] [Fintype E₁] [Fintype E₂]
  (G₁ : Multigraph V₁ E₁) (G₂ : Multigraph V₂ E₂)

theorem loopless_disjUnion (h1 : G₁.Loopless) (h2 : G₂.Loopless) :
    (G₁.disjUnion G₂).Loopless := by
  rintro (e | e)
  · simpa [disjUnion] using h1 e
  · simpa [disjUnion] using h2 e

theorem deg_disjUnion_inl (S : Finset (E₁ ⊕ E₂)) (v : V₁) :
    (G₁.disjUnion G₂).deg S (Sum.inl v) = G₁.deg S.toLeft v := by
  unfold deg
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := S)]
  rw [Finset.sum_disjSum]
  simp [endCount, disjUnion]

theorem deg_disjUnion_inr (S : Finset (E₁ ⊕ E₂)) (v : V₂) :
    (G₁.disjUnion G₂).deg S (Sum.inr v) = G₂.deg S.toRight v := by
  unfold deg
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := S)]
  rw [Finset.sum_disjSum]
  simp [endCount, disjUnion]

theorem wt_disjUnion (g : ℕ → ℕ) (S : Finset (E₁ ⊕ E₂)) :
    (G₁.disjUnion G₂).wt g S = G₁.wt g S.toLeft * G₂.wt g S.toRight := by
  rw [wt, Fintype.prod_sum_type]
  simp only [deg_disjUnion_inl, deg_disjUnion_inr, wt]

/-- **Q is multiplicative on disjoint unions.** -/
theorem Q_disjUnion : (G₁.disjUnion G₂).Q = G₁.Q * G₂.Q := by
  simp only [Q, QOn, Finset.powerset_univ]
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  exact Fintype.sum_equiv Finset.sumEquiv.toEquiv _ _ fun S => by
    simp [wt_disjUnion, Finset.sumEquiv]

/-- **Generic degree is multiplicative on disjoint unions.** -/
theorem hasGenericDegree_disjUnion (h1 : G₁.Loopless) (h2 : G₂.Loopless) {n₁ n₂ : ℕ}
    (hn₁ : G₁.HasGenericDegree n₁) (hn₂ : G₂.HasGenericDegree n₂) :
    (G₁.disjUnion G₂).HasGenericDegree (n₁ * n₂) := by
  rw [hasGenericDegree_iff _ (G₁.loopless_disjUnion G₂ h1 h2), Q_disjUnion,
    (hasGenericDegree_iff _ h1).1 hn₁, (hasGenericDegree_iff _ h2).1 hn₂]

end DisjUnion

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- **Forests have generic degree one.** A loopless graph with no nonempty Eulerian edge set has N=1. -/
theorem hasGenericDegree_one_of_forest (hG : G.Loopless) (hF : ∀ S, G.IsEvenSet S → S = ∅) :
    G.HasGenericDegree 1 := by
  rw [hasGenericDegree_iff _ hG, G.Q_eq_one_of_forest hF]

end Multigraph

end BPFixedPoints
