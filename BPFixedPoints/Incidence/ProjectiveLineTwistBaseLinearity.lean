import BPFixedPoints.Incidence.ProjectiveLineBaseSections
import BPFixedPoints.Incidence.ProjectiveLineTwistH0
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Original geometric base linearity of the genuine twist section comparisons

The base module structure restricts the original structure-ring action along
the actual projection to Spec R. The original additive polynomial comparison
preserves these independent scalars and therefore upgrades to a linear one.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original geometric base action on actual global sections of the integral twist. -/
@[instance_reducible] noncomputable def twistSheafBaseModule (n : ℤ) :
    Module R Γ(twistSheaf R n, ⊤) :=
  SchemeTools.schemeBaseModuleSections (toSpecBase R) (twistSheaf R n)

/-- The actual polynomial-kernel section comparison is linear for the original geometric base action. -/
noncomputable def twistSheafGlobalSectionsPolynomialLinearEquiv (n : ℤ) :
    letI := twistSheafBaseModule R n
    Γ(twistSheaf R n, ⊤) ≃ₗ[R] LinearMap.ker (polynomialTwistDifference R n) := by
  letI := twistSheafBaseModule R n
  refine { twistSheafGlobalSectionsPolynomialEquiv R n with map_smul' := ?_ }
  intro r s
  apply Subtype.ext
  change (twistSheafGlobalSectionsPolynomialEquiv R n (r • s)).val =
    r • (twistSheafGlobalSectionsPolynomialEquiv R n s).val
  rw [twistSheafGlobalSectionsPolynomialEquiv_val, twistSheafGlobalSectionsPolynomialEquiv_val]
  apply Prod.ext
  · change chartGlobalSectionsEquiv R 0
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.fst).app ⊤ (r • s)) =
      r • chartGlobalSectionsEquiv R 0
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.fst).app ⊤ s)
    erw [SchemeTools.openUnitProjection_base_smul]
    erw [map_mul, chartGlobalSectionsEquiv_coefficient]
    exact (Algebra.smul_def r _).symm
  · change chartGlobalSectionsEquiv R 1
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.snd).app ⊤ (r • s)) =
      r • chartGlobalSectionsEquiv R 1
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.snd).app ⊤ s)
    erw [SchemeTools.openUnitProjection_base_smul]
    erw [map_mul, chartGlobalSectionsEquiv_coefficient]
    exact (Algebra.smul_def r _).symm

/-- The new base-linear comparison retains exactly the original actual section coordinate map. -/
theorem twistSheafGlobalSectionsPolynomialLinearEquiv_apply (n : ℤ)
    (s : Γ(twistSheaf R n, ⊤)) :
    letI := twistSheafBaseModule R n
    twistSheafGlobalSectionsPolynomialLinearEquiv R n s =
      twistSheafGlobalSectionsPolynomialEquiv R n s := rfl

/-- The actual nonpositive-twist global section comparison with the original state module is base-linear. -/
noncomputable def twistSheafGlobalSectionsH0LinearEquiv (d : ℕ) :
    letI := twistSheafBaseModule R (-(d : ℤ))
    Γ(twistSheaf R (-(d : ℤ)), ⊤) ≃ₗ[R] CechLine.H0 R d := by
  letI := twistSheafBaseModule R (-(d : ℤ))
  exact (twistSheafGlobalSectionsPolynomialLinearEquiv R _).trans
    ((polynomialTwistKernelCechEquiv R d).trans (cechLineKernelH0Equiv R d))

/-- Genuine global twist sections have the original polynomial kernel over the original geometric coefficient ring. -/
theorem twistSheafGlobalSectionsPolynomialLinear_comparison (n : ℤ) :
    letI := twistSheafBaseModule R n
    Nonempty (Γ(twistSheaf R n, ⊤) ≃ₗ[R] LinearMap.ker (polynomialTwistDifference R n)) :=
  ⟨twistSheafGlobalSectionsPolynomialLinearEquiv R n⟩

/-- Genuine nonpositive-twist global sections equal the original H0 state module over the original geometric base. -/
theorem twistSheafGlobalSectionsH0Linear_comparison (d : ℕ) :
    letI := twistSheafBaseModule R (-(d : ℤ))
    Nonempty (Γ(twistSheaf R (-(d : ℤ)), ⊤) ≃ₗ[R] CechLine.H0 R d) :=
  ⟨twistSheafGlobalSectionsH0LinearEquiv R d⟩

/-- Genuine nonpositive-twist global sections are free over the original geometric coefficient ring. -/
theorem twistSheafGlobalSectionsH0_free (d : ℕ) :
    letI := twistSheafBaseModule R (-(d : ℤ))
    Module.Free R Γ(twistSheaf R (-(d : ℤ)), ⊤) := by
  letI := twistSheafBaseModule R (-(d : ℤ))
  exact Module.Free.of_equiv (twistSheafGlobalSectionsH0LinearEquiv R d).symm

/-- Genuine nonpositive-twist global sections are finite over the original geometric coefficient ring. -/
theorem twistSheafGlobalSectionsH0_finite (d : ℕ) :
    letI := twistSheafBaseModule R (-(d : ℤ))
    Module.Finite R Γ(twistSheaf R (-(d : ℤ)), ⊤) := by
  letI := twistSheafBaseModule R (-(d : ℤ))
  exact Module.Finite.equiv (twistSheafGlobalSectionsH0LinearEquiv R d).symm

/-- Over every nontrivial original coefficient ring, genuine H0 has the original zero-or-one rank. -/
theorem twistSheafGlobalSectionsH0_finrank [Nontrivial R] (d : ℕ) :
    letI := twistSheafBaseModule R (-(d : ℤ))
    Module.finrank R Γ(twistSheaf R (-(d : ℤ)), ⊤) = if d = 0 then 1 else 0 := by
  letI := twistSheafBaseModule R (-(d : ℤ))
  rw [(twistSheafGlobalSectionsH0LinearEquiv R d).finrank_eq]
  simp only [CechLine.H0, Module.finrank_finsupp_self, CechLine.H0Index, Fintype.card_fin]

end BPFixedPoints.ProjectiveLine
