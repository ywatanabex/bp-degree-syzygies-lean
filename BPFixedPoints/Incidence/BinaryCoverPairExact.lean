import BPFixedPoints.Incidence.BinaryCoverPairPrism
import BPFixedPoints.Incidence.BinaryCoverCellActualTensorComplex

/-! # The original pair and actual tensor cell complexes are positively exact -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

/-- The original tensor pair chain complex on an actual open has the original signed pair differential. -/
def pairedOpenComplex (W : Opens T) : ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => pairedChains U R W n) (pairedDifferential U R W) (pairedDifferential_square U R W)

/-- Positive exactness of the original actual-open pair complex, by its specified same-open tensor prism. -/
theorem pairedOpenComplex_exact (W : Opens T) (n : ℕ) : (pairedOpenComplex U R W).ExactAt (n+1) :=
  linearChainComplex_exactAt_succ _ _ _ (pairedDifferential_range_eq_ker U R W) n

/-- Positive exactness of the original pair presheaf complex on all actual opens, without a cover assumption. -/
theorem pairedPresheafComplex_exact (n : ℕ) : (pairedPresheafComplex U R).ExactAt (n+1) := by
  let S := ShortComplex.mk (pairedPresheafDifferential U R (n+1)) (pairedPresheafDifferential U R n)
    (pairedPresheafDifferential_square U R n)
  have hs : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology,IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext W
    let E := (evaluation (Opens T)ᵒᵖ (ModuleCat R)).obj W
    have hW : (S.map E).Exact := by
      apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      exact pairedDifferential_range_eq_ker U R W.unop n
    exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp hW)
      (S.mapHomologyIso E).symm).eq_of_src _ _
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  change (ShortComplex.mk ((pairedPresheafComplex U R).d (n+2) (n+1))
    ((pairedPresheafComplex U R).d (n+1) n) _).Exact
  dsimp only [pairedPresheafComplex]
  have hd : ChainComplex.of.d (pairedPresheaf U R) (pairedPresheafDifferential U R) (n+2) (n+1) =
      pairedPresheafDifferential U R (n+1) := ChainComplex.of_d _ _ (n+1)
  simpa only [hd,ChainComplex.of_d] using hs

/-- Original integer forgetting retains positive exactness of the same original pair presheaf complex. -/
theorem pairedAbelianPresheafComplex_exact (n : ℕ) : (pairedAbelianPresheafComplex U).ExactAt (n+1) := by
  change (((pairedPresheafComplex U ℤ).sc (n+1)).map (toAbelianPresheaf (T := T))).Exact
  exact (pairedPresheafComplex_exact U ℤ n).map _

/-- Exact native sheafification retains positive exactness of the same actual original pair complex. -/
theorem pairedSheafComplex_exact (n : ℕ) : (pairedSheafComplex U).ExactAt (n+1) := by
  change (((pairedAbelianPresheafComplex U).sc (n+1)).map
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})).Exact
  exact (pairedAbelianPresheafComplex_exact U n).map _

/-- The original actual standard tensor totalization is positively exact by its original specified pair comparison. -/
theorem actualTensorSheafComplex_exact (n : ℕ) : (actualTensorSheafComplex U).ExactAt (n+1) :=
  (pairedSheafComplex_exact U n).of_iso (actualTensorPairComplexIso U).symm

end
end BPFixedPoints.SheafTools.BinaryCells
