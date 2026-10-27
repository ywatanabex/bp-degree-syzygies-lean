import BPFixedPoints.Incidence.LinearParameterFamily
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.List.OfFn

/-! # Coordinates for arbitrary tuples of homogeneous linear forms -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {k σ A : Type*} [Field k] [Fintype σ]

theorem exists_linearParameterForm_list (rs : List (MvPolynomial σ k)) (n : ℕ)
    (hlen : rs.length = n) (hh : ∀ r ∈ rs, r ∈ homogeneousSubmodule σ k 1) :
    ∃ a : Fin n × σ → k, List.ofFn (linearParameterForm X a) = rs := by
  classical
  subst n
  have he (i : Fin rs.length) : ∃ a : σ → k, ∑ j, a j • X j = rs.get i := by
    apply (Submodule.mem_span_range_iff_exists_fun k).mp
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hh _ (List.get_mem _ _)
  choose a ha using he
  refine ⟨fun t => a t.1 t.2, ?_⟩
  have h : linearParameterForm X (fun t : Fin rs.length × σ => a t.1 t.2) = rs.get :=
    funext ha
  rw [h]
  exact List.ofFn_get rs

theorem ideal_ofList_ofFn [CommRing A] {ι : ℕ} (x : Fin ι → A) :
    Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x) := by
  apply congrArg Ideal.span
  exact Set.ext (List.mem_ofFn' x)

end BPFixedPoints.ResolutionTools
