import BPFixedPoints.Incidence.BinaryCoverCellActualTensorComplex

/-! # Original bidegree projections of the actual standard cell tensor

Use the native coproduct descent and zero morphisms. Every original
bidegree inclusion is sent to its original identity or its original zero;
no cohomology coordinates or splitting of a surjection are selected.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance tensorProjectionSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The original bidegree projection from the native actual tensor totalization. -/
def actualTensorProjection (n i j : ℕ) :
    (actualTensorSheafComplex U).X n ⟶ (sheafComplex U).X i ⊗ (sheafComplex U).X j :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ => by
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q; exact 𝟙 _
      · exact 0
    · exact 0)

/-- The original bidegree inclusion returns its original identity. -/
@[reassoc] theorem actualTensorProjection_same (n i j : ℕ) (h : i+j=n) :
    actualTensorInclusion U i j n h ≫ actualTensorProjection U n i j = 𝟙 _ := by
  rw [actualTensorProjection,HomologicalComplex.ι_mapBifunctorDesc]
  simp only [dite_true]
  rfl

/-- Every distinct original bidegree is sent to its original zero. -/
@[reassoc] theorem actualTensorProjection_other (n i j p q : ℕ) (h : p+q=n)
    (hne : p≠i ∨ q≠j) :
    actualTensorInclusion U p q n h ≫ actualTensorProjection U n i j = 0 := by
  rw [actualTensorProjection,HomologicalComplex.ι_mapBifunctorDesc]
  by_cases hp : p=i
  · subst p
    have hq : q≠j := hne.resolve_left (by simp)
    simp only [dite_true,dif_neg hq]
  · simp only [dif_neg hp]

/-- A bidegree outside its original total degree has zero native projection. -/
theorem actualTensorProjection_zero_degree (n i j : ℕ) (hne : i+j≠n) :
    actualTensorProjection U n i j = 0 := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p+q=n at h
  rw [actualTensorProjection_other U n i j p q h (by omega),comp_zero]

/-- The original left summand differential selects exactly the preceding original left degree. -/
theorem actualTensorLeft_projection (n i j p q : ℕ) (h : p+q=n+1) :
    actualTensorLeftDifferential U p q n ≫ actualTensorProjection U n i j =
      actualTensorInclusion U p q (n+1) h ≫ actualTensorProjection U (n+1) (i+1) j ≫
        ((sheafComplex U).d (i+1) i ▷ (sheafComplex U).X j) := by
  cases p with
  | zero =>
    rw [actualTensorLeft_zero,zero_comp,← Category.assoc,
      actualTensorProjection_other U (n+1) (i+1) j 0 q h (Or.inl (by omega)),zero_comp]
  | succ p =>
    have hpq : p+q=n := by omega
    rw [actualTensorLeft_succ U p q n hpq,Category.assoc]
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q
        rw [actualTensorProjection_same,← actualCellSheaf_d,← Category.assoc,actualTensorProjection_same]
        change ((sheafComplex U).d (i+1) i ▷ (sheafComplex U).X j) ≫ 𝟙 _ =
          𝟙 _ ≫ ((sheafComplex U).d (i+1) i ▷ (sheafComplex U).X j)
        simp only [Category.comp_id,Category.id_comp]
      · rw [actualTensorProjection_other U n i j i q hpq (Or.inr hq),comp_zero,
          ← Category.assoc,actualTensorProjection_other U (n+1) (i+1) j (i+1) q h (Or.inr hq),zero_comp]
    · rw [actualTensorProjection_other U n i j p q hpq (Or.inl hp),comp_zero,
        ← Category.assoc,actualTensorProjection_other U (n+1) (i+1) j (p+1) q h (Or.inl (by omega)),zero_comp]

/-- The original right summand retains its original left-degree Koszul sign. -/
theorem actualTensorRight_projection (n i j p q : ℕ) (h : p+q=n+1) :
    actualTensorRightDifferential U p q n ≫ actualTensorProjection U n i j =
      ((-1 : ℤˣ)^i) • (actualTensorInclusion U p q (n+1) h ≫
        actualTensorProjection U (n+1) i (j+1) ≫
          ((sheafComplex U).X i ◁ (sheafComplex U).d (j+1) j)) := by
  cases q with
  | zero =>
    rw [actualTensorRight_zero,zero_comp,← Category.assoc,
      actualTensorProjection_other U (n+1) i (j+1) p 0 h (Or.inr (by omega)),zero_comp,smul_zero]
  | succ q =>
    have hpq : p+q=n := by omega
    rw [actualTensorRight_succ U p q n hpq,Linear.units_smul_comp,Category.assoc]
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q
        rw [actualTensorProjection_same,← actualCellSheaf_d,← Category.assoc,actualTensorProjection_same]
        change ((-1 : ℤˣ)^i) • (((sheafComplex U).X i ◁ (sheafComplex U).d (j+1) j) ≫ 𝟙 _) =
          ((-1 : ℤˣ)^i) • (𝟙 _ ≫ ((sheafComplex U).X i ◁ (sheafComplex U).d (j+1) j))
        simp only [Category.comp_id,Category.id_comp]
      · rw [actualTensorProjection_other U n i j i q hpq (Or.inr hq),comp_zero,smul_zero,
          ← Category.assoc,actualTensorProjection_other U (n+1) i (j+1) i (q+1) h (Or.inr (by omega)),zero_comp,smul_zero]
    · rw [actualTensorProjection_other U n i j p q hpq (Or.inl hp),comp_zero,smul_zero,
        ← Category.assoc,actualTensorProjection_other U (n+1) i (j+1) p (q+1) h (Or.inl hp),zero_comp,smul_zero]

/-- The actual standard total differential has exactly the original bidegree Leibniz components. -/
theorem actualTensorProjection_boundary (n i j : ℕ) :
    (actualTensorSheafComplex U).d (n+1) n ≫ actualTensorProjection U n i j =
      actualTensorProjection U (n+1) (i+1) j ≫ ((sheafComplex U).d (i+1) i ▷ (sheafComplex U).X j) +
        ((-1 : ℤˣ)^i) • (actualTensorProjection U (n+1) i (j+1) ≫
          ((sheafComplex U).X i ◁ (sheafComplex U).d (j+1) j)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [← Category.assoc,HomologicalComplex.mapBifunctor.d_eq,Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁,HomologicalComplex.mapBifunctor.ι_D₂,
    Preadditive.add_comp,actualTensorLeft_projection U n i j p q h,
    actualTensorRight_projection U n i j p q h,Preadditive.comp_add,
    Linear.comp_units_smul]

end
end BPFixedPoints.SheafTools.BinaryCells
