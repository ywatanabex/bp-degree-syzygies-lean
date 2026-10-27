import BPFixedPoints.Incidence.BinaryCoverCellTensorProjection
import BPFixedPoints.Incidence.AbelianSheafTensorEvaluation

/-! # The original cell diagonal evaluates actual sheaf products on cochains

Tensor cochains use the native bidegree projections and the specified
actual sheaf pairing. Their evaluation on the original diagonal satisfies
the native Leibniz rule, before any cohomology or state comparison.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)
local instance sheafCupSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The original actual tensor cochain evaluates the specified section pairing in its original bidegree. -/
def actualTensorCochain (n i j : ℕ) (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (actualTensorSheafComplex U).X n ⟶ H :=
  actualTensorProjection U n i j ≫ (f ⊗ₘ g) ≫ b.sheafMap

/-- Evaluation on the originally specified actual cell diagonal defines the actual cup cochain. -/
def actualCellCupAt (n i j : ℕ) (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (sheafComplex U).X n ⟶ H :=
  (actualTensorDiagonalMap U).f n ≫ actualTensorCochain U b n i j f g

/-- The original homogeneous cup has precisely the sum of the two original cochain degrees. -/
def actualCellCup (i j : ℕ) (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (sheafComplex U).X (i+j) ⟶ H :=
  actualCellCupAt U b (i+j) i j f g

/-- No component outside the original total degree is introduced by the actual cup. -/
theorem actualCellCupAt_zero_degree (n i j : ℕ) (hne : i+j≠n)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b n i j f g = 0 := by
  rw [actualCellCupAt,actualTensorCochain,actualTensorProjection_zero_degree U n i j hne,
    zero_comp,comp_zero]

/-- In the original bidegree the tensor cochain is precisely the original tensor pairing of cochains. -/
@[reassoc] theorem actualTensorCochain_inclusion (n i j : ℕ) (h : i+j=n)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    actualTensorInclusion U i j n h ≫ actualTensorCochain U b n i j f g = (f ⊗ₘ g) ≫ b.sheafMap := by
  rw [actualTensorCochain,← Category.assoc,actualTensorProjection_same,Category.id_comp]

/-- Every original pure-section representative evaluates by the original section product itself. -/
theorem actualTensorCochain_pure (n i j : ℕ) (h : i+j=n)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) (W : Opens T)
    (x : ((sheafComplex U).X i).obj.obj (op W)) (y : ((sheafComplex U).X j).obj.obj (op W)) :
    (actualTensorInclusion U i j n h ≫ actualTensorCochain U b n i j f g).hom.app (op W)
      (sheafPureSection _ _ W x y) = b.pairing W (f.hom.app (op W) x) (g.hom.app (op W) y) := by
  rw [actualTensorCochain_inclusion]
  change b.sheafMap.hom.app (op W) ((f ⊗ₘ g).hom.app (op W) (sheafPureSection _ _ W x y)) = _
  rw [sheafPureSection_map,b.sheafMap_pure]

/-- The independently specified actual standard tensor differential gives the original Leibniz components. -/
theorem actualTensorCochain_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (actualTensorSheafComplex U).d (n+1) n ≫ actualTensorCochain U b n i j f g =
      actualTensorCochain U b (n+1) (i+1) j ((sheafComplex U).d (i+1) i ≫ f) g +
        ((-1 : ℤˣ)^i) • actualTensorCochain U b (n+1) i (j+1) f ((sheafComplex U).d (j+1) j ≫ g) := by
  simp only [actualTensorCochain]
  rw [← Category.assoc,actualTensorProjection_boundary,Preadditive.add_comp,
    Linear.units_smul_comp,Category.assoc,Category.assoc]
  congr 1
  · have e : ((sheafComplex U).d (i+1) i ▷ (sheafComplex U).X j) ≫ (f ⊗ₘ g) =
        ((sheafComplex U).d (i+1) i ≫ f) ⊗ₘ g := by
      rw [← tensorHom_id,tensorHom_comp_tensorHom,Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun k => actualTensorProjection U (n+1) (i+1) j ≫ k ≫ b.sheafMap) e
  · congr 1
    have e : ((sheafComplex U).X i ◁ (sheafComplex U).d (j+1) j) ≫ (f ⊗ₘ g) =
        f ⊗ₘ ((sheafComplex U).d (j+1) j ≫ g) := by
      rw [← id_tensorHom,tensorHom_comp_tensorHom,Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun k => actualTensorProjection U (n+1) i (j+1) ≫ k ≫ b.sheafMap) e

/-- The actual cup on the original cell cochains has the original signed Leibniz differential. -/
theorem actualCellCupAt_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    (sheafComplex U).d (n+1) n ≫ actualCellCupAt U b n i j f g =
      actualCellCupAt U b (n+1) (i+1) j ((sheafComplex U).d (i+1) i ≫ f) g +
        ((-1 : ℤˣ)^i) • actualCellCupAt U b (n+1) i (j+1) f ((sheafComplex U).d (j+1) j ≫ g) := by
  rw [actualCellCupAt,← Category.assoc,← (actualTensorDiagonalMap U).comm,Category.assoc,
    actualTensorCochain_boundary,Preadditive.comp_add,Linear.comp_units_smul]
  rfl

/-- A zero original left cochain evaluates to zero. -/
theorem actualCellCupAt_zero_left (n i j : ℕ) (g : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b n i j 0 g = 0 := by
  simp only [actualCellCupAt,actualTensorCochain,MonoidalPreadditive.zero_tensor,zero_comp,comp_zero]

/-- A zero original right cochain evaluates to zero. -/
theorem actualCellCupAt_zero_right (n i j : ℕ) (f : (sheafComplex U).X i ⟶ F) :
    actualCellCupAt U b n i j f 0 = 0 := by
  simp only [actualCellCupAt,actualTensorCochain,MonoidalPreadditive.tensor_zero,zero_comp,comp_zero]

/-- The original actual cup is additive in its left cochain. -/
theorem actualCellCupAt_add_left (n i j : ℕ)
    (f f' : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b n i j (f+f') g = actualCellCupAt U b n i j f g + actualCellCupAt U b n i j f' g := by
  simp only [actualCellCupAt,actualTensorCochain,MonoidalPreadditive.add_tensor,
    Preadditive.add_comp,Preadditive.comp_add]

/-- The original actual cup is additive in its right cochain. -/
theorem actualCellCupAt_add_right (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g g' : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b n i j f (g+g') = actualCellCupAt U b n i j f g + actualCellCupAt U b n i j f g' := by
  simp only [actualCellCupAt,actualTensorCochain,MonoidalPreadditive.tensor_add,
    Preadditive.add_comp,Preadditive.comp_add]

/-- The actual cup is biadditive on the original Hom cochains, with no transported action. -/
def actualCellCupBiadditive (n i j : ℕ) :
    ((sheafComplex U).X i ⟶ F) →+ ((sheafComplex U).X j ⟶ G) →+ ((sheafComplex U).X n ⟶ H) where
  toFun f :=
    { toFun := actualCellCupAt U b n i j f
      map_zero' := actualCellCupAt_zero_right U b n i j f
      map_add' := actualCellCupAt_add_right U b n i j f }
  map_zero' := by apply AddMonoidHom.ext; intro g; exact actualCellCupAt_zero_left U b n i j g
  map_add' := by intro f f'; apply AddMonoidHom.ext; intro g; exact actualCellCupAt_add_left U b n i j f f' g

/-- Actual closed original cochains multiply to a closed original cochain. -/
theorem actualCellCupAt_closed (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G)
    (hf : (sheafComplex U).d (i+1) i ≫ f = 0) (hg : (sheafComplex U).d (j+1) j ≫ g = 0) :
    (sheafComplex U).d (n+1) n ≫ actualCellCupAt U b n i j f g = 0 := by
  rw [actualCellCupAt_boundary,hf,hg,actualCellCupAt_zero_left,actualCellCupAt_zero_right,smul_zero,zero_add]

/-- A left boundary times a closed original cochain is its specified original cup boundary. -/
theorem actualCellCupAt_left_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G)
    (hg : (sheafComplex U).d (j+1) j ≫ g = 0) :
    (sheafComplex U).d (n+1) n ≫ actualCellCupAt U b n i j f g =
      actualCellCupAt U b (n+1) (i+1) j ((sheafComplex U).d (i+1) i ≫ f) g := by
  rw [actualCellCupAt_boundary,hg,actualCellCupAt_zero_right,smul_zero,add_zero]

/-- A closed original cochain times a right boundary retains the original Koszul-signed cup boundary. -/
theorem actualCellCupAt_right_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G)
    (hf : (sheafComplex U).d (i+1) i ≫ f = 0) :
    (sheafComplex U).d (n+1) n ≫ actualCellCupAt U b n i j f g =
      ((-1 : ℤˣ)^i) • actualCellCupAt U b (n+1) i (j+1) f ((sheafComplex U).d (j+1) j ≫ g) := by
  rw [actualCellCupAt_boundary,hf,actualCellCupAt_zero_left,zero_add]

end
end BPFixedPoints.SheafTools.BinaryCells
