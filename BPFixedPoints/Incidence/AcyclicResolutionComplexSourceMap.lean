import BPFixedPoints.Incidence.AcyclicResolutionSourceNaturality

/-! # Original chain maps induce the original syzygy and augmentation maps

Native cokernel maps preserve the independently specified differentials.
No projectivity, lifting choice or extra exactness is assumed of a map.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P Q : ChainComplex C ℕ} (f : P ⟶ Q)

/-- The original chain map induces the native map of the original differential cokernels. -/
noncomputable def complexSyzygyMap (n : ℕ) : complexSyzygy P n ⟶ complexSyzygy Q n :=
  cokernel.map (P.d (n+1) n) (Q.d (n+1) n) (f.f (n+1)) (f.f n) (f.comm _ _).symm

/-- The syzygy source map retains the original term map and native cokernel projections. -/
theorem complexSyzygyMap_projection (n : ℕ) :
    cokernel.π (P.d (n+1) n) ≫ complexSyzygyMap f n = f.f n ≫ cokernel.π (Q.d (n+1) n) :=
  cokernel.π_desc _ _ _

/-- The same original chain map preserves the original descended syzygy inclusions. -/
theorem complexSyzygyMap_inclusion (n : ℕ) :
    complexSyzygyInclusion P n ≫ f.f n = complexSyzygyMap f (n+1) ≫ complexSyzygyInclusion Q n := by
  apply (cancel_epi (cokernel.π (P.d (n+2) (n+1)))).mp
  rw [← Category.assoc,complexSyzygy_factor,← Category.assoc,complexSyzygyMap_projection,
    Category.assoc,complexSyzygy_factor]
  exact (f.comm (n+1) n).symm

/-- Any original chain map of positively exact complexes gives a map of their original exact towers. -/
noncomputable def complexSourceMap (hP : ∀ n, P.ExactAt (n+1)) (hQ : ∀ n, Q.ExactAt (n+1)) :
    ExactTower.SourceMap (complexTower P hP) (complexTower Q hQ) where
  syzygy n := complexSyzygyMap f n
  term n := f.f n
  inclusion n := complexSyzygyMap_inclusion f n
  projection n := complexSyzygyMap_projection f n

variable {A B : C} (πP : P.X 0 ⟶ A) (πQ : Q.X 0 ⟶ B)
variable (zP : P.d 1 0 ≫ πP=0) (zQ : Q.d 1 0 ≫ πQ=0)
variable (eP : (ShortComplex.mk (P.d 1 0) πP zP).Exact)
variable (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πP] [Epi πQ]

/-- An original augmentation-preserving chain map retains the native augmentation identifications. -/
theorem complexAugmentationIso_source (a : A ⟶ B) (ha : f.f 0 ≫ πQ=πP ≫ a) :
    (complexAugmentationIso P πP zP eP).hom ≫ a =
      complexSyzygyMap f 0 ≫ (complexAugmentationIso Q πQ zQ eQ).hom := by
  apply (cancel_epi (cokernel.π (P.d 1 0))).mp
  rw [← Category.assoc,complexAugmentationIso_projection,← Category.assoc,complexSyzygyMap_projection,
    Category.assoc,complexAugmentationIso_projection]
  exact ha.symm

/-- The same original augmentation square is retained on the inverse syzygy identifications. -/
theorem complexAugmentationIso_source_inv (a : A ⟶ B) (ha : f.f 0 ≫ πQ=πP ≫ a) :
    (complexAugmentationIso P πP zP eP).inv ≫ complexSyzygyMap f 0 =
      a ≫ (complexAugmentationIso Q πQ zQ eQ).inv := by
  apply (cancel_mono (complexAugmentationIso Q πQ zQ eQ).hom).mp
  rw [Category.assoc,← complexAugmentationIso_source f πP πQ zP zQ eP eQ a ha,
    Iso.inv_hom_id_assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]

end BPFixedPoints.ExtResolutionTools
