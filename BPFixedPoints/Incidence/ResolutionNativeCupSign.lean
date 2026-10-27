import BPFixedPoints.Incidence.ResolutionNativeYonedaSignFormula

/-! # The native Yoneda normalization retains its exact product sign -/

namespace BPFixedPoints.ExtResolutionTools

/-- The ratio of the original native degree normalizations is precisely the original Koszul crossing sign. -/
theorem nativeYonedaSign_add (i j : ℕ) :
    nativeYonedaSign (i+j) = ((i*j : ℕ) : ℤ).negOnePow * nativeYonedaSign i * nativeYonedaSign j := by
  induction j with
  | zero => simp [nativeYonedaSign]
  | succ j ih =>
    rw [show i+(j+1)=i+j+1 by omega,nativeYonedaSign,ih,nativeYonedaSign]
    simp only [Int.natCast_add,Int.natCast_mul,Int.negOnePow_add,
      mul_add,mul_one]
    ac_rfl

end BPFixedPoints.ExtResolutionTools
