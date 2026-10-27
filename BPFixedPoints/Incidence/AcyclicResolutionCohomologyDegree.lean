import BPFixedPoints.Incidence.AcyclicResolutionComplex

/-! # The original resolution cohomology with its actual cochain degree

Positive degrees are exactly the existing quotient by the original
boundary image. Degree zero is the original closed-cochain group, with
no incoming differential. The original representative and quotient maps
are retained rather than replaced by Ext or state coordinates.
-/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ExactTower C) (Y : C)

/-- Actual cochain degree zero uses original cycles; every positive degree is the original quotient. -/
def cohomologyAt : ℕ → Type v
  | 0 => T.cycles Y 0
  | n+1 => T.cohomology Y n

noncomputable instance cohomologyAtAddCommGroup (n : ℕ) : AddCommGroup (T.cohomologyAt Y n) := by
  cases n <;> dsimp only [cohomologyAt] <;> infer_instance

/-- The original representative map in every actual cochain degree. -/
noncomputable def classAt (n : ℕ) : T.cycles Y n →+ T.cohomologyAt Y n := by
  cases n with
  | zero => exact AddMonoidHom.id _
  | succ n => exact QuotientAddGroup.mk' (T.boundary Y n).range

/-- Degree zero retains exactly its original closed representative. -/
theorem classAt_zero (x : T.cycles Y 0) : T.classAt Y 0 x = x := rfl

/-- Positive degree retains exactly its original quotient representative. -/
theorem classAt_succ (n : ℕ) (x : T.cycles Y (n+1)) :
    T.classAt Y (n+1) x = (QuotientAddGroup.mk x : T.cohomology Y n) := rfl

/-- Every original cohomology class has an original closed-cochain representative. -/
theorem classAt_surjective (n : ℕ) : Function.Surjective (T.classAt Y n) := by
  cases n with
  | zero => exact Function.surjective_id
  | succ n => exact QuotientAddGroup.mk_surjective

/-- The original preceding boundary has zero original class. -/
theorem classAt_boundary (n : ℕ) (x : T.P n ⟶ Y) :
    T.classAt Y (n+1) (T.boundary Y n x) = 0 := by
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨x,rfl⟩

variable {Y} {A : Type*} [AddCommGroup A]

/-- There is no incoming boundary in degree zero; positive degrees use the original boundary map. -/
def KillsBoundariesAt : (n : ℕ) → (T.cycles Y n →+ A) → Prop
  | 0, _ => True
  | n+1, f => ∀ x : T.P n ⟶ Y, f (T.boundary Y n x) = 0

/-- Descend an additive map that kills the original preceding boundaries, including actual degree zero. -/
noncomputable def liftAt (n : ℕ) (f : T.cycles Y n →+ A)
    (hf : T.KillsBoundariesAt n f) :
    T.cohomologyAt Y n →+ A := by
  cases n with
  | zero => exact f
  | succ n =>
    exact QuotientAddGroup.lift (T.boundary Y n).range f (by
      rintro x ⟨a,rfl⟩
      exact hf a)

/-- Quotient descent retains the original map on every original representative. -/
theorem liftAt_class (n : ℕ) (f : T.cycles Y n →+ A)
    (hf : T.KillsBoundariesAt n f)
    (x : T.cycles Y n) : T.liftAt n f hf (T.classAt Y n x) = f x := by
  cases n <;> rfl

variable {Z : C}

/-- Every degree retains original postcomposition, with the existing positive quotient map. -/
noncomputable def mapAt (f : Y ⟶ Z) (n : ℕ) : T.cohomologyAt Y n →+ T.cohomologyAt Z n := by
  cases n with
  | zero => exact T.mapCycles f 0
  | succ n => exact T.mapCohomology f n

/-- Postcomposition retains every original closed-cochain representative. -/
theorem mapAt_class (f : Y ⟶ Z) (n : ℕ) (x : T.cycles Y n) :
    T.mapAt f n (T.classAt Y n x) = T.classAt Z n (T.mapCycles f n x) := by
  cases n <;> rfl

variable (Y) [HasExt.{w} C]

/-- The existing original Yoneda comparison in every actual cochain degree, including zero. -/
noncomputable def cohomologyAtExtEquiv (h : T.AcyclicAgainst Y) :
    (n : ℕ) → T.cohomologyAt Y n ≃+ Ext.{w} (T.K 0) Y n
  | 0 => (T.cycleEquiv Y 0).trans Ext.addEquiv₀.symm
  | n+1 => T.cohomologyEquiv Y n h

/-- All degrees retain the same original cocycle factorization and iterated connecting representative. -/
theorem cohomologyAtExtEquiv_class (h : T.AcyclicAgainst Y) (n : ℕ) (x : T.cycles Y n) :
    T.cohomologyAtExtEquiv Y h n (T.classAt Y n x) = T.cocycleComparison Y n x := by
  cases n <;> rfl

/-- The same original Yoneda comparison is target-natural in every actual cochain degree. -/
theorem cohomologyAtExtEquiv_postcomp (f : Y ⟶ Z) (n : ℕ)
    (hY : T.AcyclicAgainst Y) (hZ : T.AcyclicAgainst Z) (x : T.cohomologyAt Y n) :
    T.cohomologyAtExtEquiv Z hZ n (T.mapAt f n x) =
      (T.cohomologyAtExtEquiv Y hY n x).comp (Ext.mk₀ f) (add_zero n) := by
  obtain ⟨x,rfl⟩ := T.classAt_surjective Y n x
  rw [mapAt_class,cohomologyAtExtEquiv_class,cohomologyAtExtEquiv_class]
  exact T.cocycleComparison_postcomp f n x

end BPFixedPoints.ExtResolutionTools.ExactTower
