import BPFixedPoints.Incidence.IncidenceRelabelRings

/-!
# Edge signs act on the coefficient ring and on the incidence ring

An edge sign `ε : EdgeSign E` assigns an integer unit `ε e ∈ {±1}` to every edge. It acts on the
coefficient ring by `c_{e,α,β} ↦ ε_e c_{e,α,β}` (`edgeSignCoeff`), a `ℂ`-algebra automorphism
preserving the constant coefficient. This is the per-edge sign change of the orientation lines of
the functoriality proposition; it is not the endpoint transposition of an `EdgeRelabel`, which
exchanges the coefficient indices of a reversed edge without a sign.

Fixing the vertex variables and scaling the coefficient variables, every chart equation of an edge
`e` goes to `ε_e` times itself (`varSignHom_incChartEq`) and every torus relation goes to its sign
times itself (`varSignHom_incTorusRel`). Hence the scaling descends to automorphisms of the chart
rings (`edgeSignChart`), of the common torus ring (`edgeSignTorus`), compatible with the chart
restrictions, and of the actual incidence ring (`edgeSignIncidence`), intertwining the coefficient
maps (`edgeSignIncidence_coeffHom`). The coefficient, torus and incidence sign changes are
involutions; for the coefficient and torus sign changes it is also proved that the trivial sign
gives the identity and that products of signs give composites.

The scaling of variables of a polynomial ring by integer units (`varSignHom`, `varSignEquiv`) is
developed in general first.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

/-! ## Scaling polynomial variables by integer units -/

section VarSign

variable {ι : Type*}

/-- An integer unit squares to one in any ring. -/
theorem units_intCast_mul_self {A : Type*} [Ring A] (u : ℤˣ) : ((u : ℤ) : A) * ((u : ℤ) : A) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- The algebra endomorphism scaling every variable `X i` by the integer unit `s i`. -/
noncomputable def varSignHom (s : ι → ℤˣ) : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  aeval fun i => ((s i : ℤ) : MvPolynomial ι ℂ) * X i

@[simp] theorem varSignHom_X (s : ι → ℤˣ) (i : ι) :
    varSignHom s (X i) = ((s i : ℤ) : MvPolynomial ι ℂ) * X i :=
  aeval_X _ _

/-- Composites of variable scalings multiply the units. -/
theorem varSignHom_comp (s t : ι → ℤˣ) :
    (varSignHom s).comp (varSignHom t) = varSignHom (s * t) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, varSignHom_X, map_mul, map_intCast, Pi.mul_apply, Units.val_mul,
    Int.cast_mul]
  ring

/-- The trivial scaling is the identity. -/
theorem varSignHom_one : varSignHom (1 : ι → ℤˣ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- A variable scaling is an involution. -/
theorem varSignHom_comp_self (s : ι → ℤˣ) : (varSignHom s).comp (varSignHom s) = AlgHom.id ℂ _ := by
  rw [varSignHom_comp]
  have h : s * s = 1 := funext fun i => Int.units_mul_self (s i)
  rw [h, varSignHom_one]

theorem varSignHom_varSignHom (s : ι → ℤˣ) (p : MvPolynomial ι ℂ) :
    varSignHom s (varSignHom s p) = p :=
  AlgHom.congr_fun (varSignHom_comp_self s) p

/-- The variable scaling as an algebra automorphism; it is its own inverse. -/
noncomputable def varSignEquiv (s : ι → ℤˣ) : MvPolynomial ι ℂ ≃ₐ[ℂ] MvPolynomial ι ℂ :=
  AlgEquiv.ofAlgHom (varSignHom s) (varSignHom s) (varSignHom_comp_self s) (varSignHom_comp_self s)

@[simp] theorem varSignEquiv_apply (s : ι → ℤˣ) (p : MvPolynomial ι ℂ) :
    varSignEquiv s p = varSignHom s p := rfl

@[simp] theorem varSignEquiv_symm_apply (s : ι → ℤˣ) (p : MvPolynomial ι ℂ) :
    (varSignEquiv s).symm p = varSignHom s p := rfl

/-- Variable scaling preserves the constant coefficient. -/
@[simp] theorem constantCoeff_varSignHom (s : ι → ℤˣ) (p : MvPolynomial ι ℂ) :
    constantCoeff (varSignHom s p) = constantCoeff p := by
  have h : (constantCoeff : MvPolynomial ι ℂ →+* ℂ).comp (varSignHom s).toRingHom =
      constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  exact RingHom.congr_fun h p

/-- Variable scaling commutes with renaming along a map compatible with the units. -/
theorem rename_varSignHom {κ : Type*} (f : ι → κ) (s : ι → ℤˣ) (t : κ → ℤˣ)
    (h : ∀ i, t (f i) = s i) (p : MvPolynomial ι ℂ) :
    rename f (varSignHom s p) = varSignHom t (rename f p) := by
  have hc : (rename f).comp (varSignHom s) = (varSignHom t).comp (rename f) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h]
  exact AlgHom.congr_fun hc p

end VarSign

/-- An ideal spanned by a family is invariant under a ring endomorphism multiplying every generator
by an integer unit. -/
theorem map_span_range_eq_of_units {A ι : Type*} [CommRing A] (f : A →+* A) (g : ι → A)
    (u : ι → ℤˣ) (h : ∀ i, f (g i) = ((u i : ℤ) : A) * g i) :
    (Ideal.span (Set.range g)).map f = Ideal.span (Set.range g) := by
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g i = ((u i : ℤ) : A) * f (g i) := by
      rw [h, ← mul_assoc, units_intCast_mul_self, one_mul]
    rw [hg]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g i, ⟨i, rfl⟩, rfl⟩)

/-! ## Edge signs -/

/-- An edge sign: an integer unit `ε e ∈ {±1}` on every edge, the sign of the orientation-line
isomorphism at that edge. Edge signs form a group under pointwise multiplication. -/
abbrev EdgeSign (E : Type) := E → ℤˣ

namespace EdgeSign

variable {E : Type} (ε : EdgeSign E)

/-- An edge sign squares to the trivial sign. -/
@[simp] theorem mul_self : ε * ε = 1 := funext fun e => Int.units_mul_self (ε e)

/-- The units by which the coefficient variables are scaled: the sign of their edge. -/
def coeffVarSign : IncCoeffIdx E → ℤˣ := fun c => ε c.1

/-- The units by which the chart variables are scaled: vertex coordinates are fixed. -/
def chartVarSign {V : Type} : IncChartVar V E → ℤˣ
  | Sum.inl _ => 1
  | Sum.inr c => ε c.1

/-- The units by which the torus variables are scaled: vertex coordinates are fixed. -/
def torusVarSign {V : Type} : IncTorusVar V E → ℤˣ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr c) => ε c.1

/-- The unit of a torus relation: one for a vertex relation, the edge sign for an edge equation. -/
def relSign {V : Type} : V ⊕ E → ℤˣ
  | Sum.inl _ => 1
  | Sum.inr e => ε e

@[simp] theorem coeffVarSign_apply (c : IncCoeffIdx E) : ε.coeffVarSign c = ε c.1 := rfl

@[simp] theorem chartVarSign_inl {V : Type} (v : V) : ε.chartVarSign (Sum.inl v) = 1 := rfl

@[simp] theorem chartVarSign_inr {V : Type} (c : IncCoeffIdx E) :
    ε.chartVarSign (V := V) (Sum.inr c) = ε c.1 := rfl

@[simp] theorem torusVarSign_inl {V : Type} (v : V) : ε.torusVarSign (E := E) (Sum.inl v) = 1 := rfl

@[simp] theorem torusVarSign_inr_inl {V : Type} (v : V) :
    ε.torusVarSign (E := E) (Sum.inr (Sum.inl v)) = 1 := rfl

@[simp] theorem torusVarSign_inr_inr {V : Type} (c : IncCoeffIdx E) :
    ε.torusVarSign (V := V) (Sum.inr (Sum.inr c)) = ε c.1 := rfl

@[simp] theorem relSign_inl {V : Type} (v : V) : ε.relSign (Sum.inl v) = 1 := rfl

@[simp] theorem relSign_inr {V : Type} (e : E) : ε.relSign (V := V) (Sum.inr e) = ε e := rfl

end EdgeSign

/-! ## The coefficient ring automorphism -/

section Coefficients

variable {E : Type} (ε : EdgeSign E)

/-- The coefficient ring automorphism of an edge sign: `c_{e,α,β} ↦ ε_e c_{e,α,β}`. -/
noncomputable def edgeSignCoeff : IncCoeffRing E ≃ₐ[ℂ] IncCoeffRing E :=
  varSignEquiv ε.coeffVarSign

theorem edgeSignCoeff_apply (p : IncCoeffRing E) : edgeSignCoeff ε p = varSignHom ε.coeffVarSign p :=
  rfl

@[simp] theorem edgeSignCoeff_X (c : IncCoeffIdx E) :
    edgeSignCoeff ε (X c) = ((ε c.1 : ℤ) : IncCoeffRing E) * X c := by
  simp [edgeSignCoeff]

/-- The coefficient sign change is an involution. -/
@[simp] theorem edgeSignCoeff_edgeSignCoeff (p : IncCoeffRing E) :
    edgeSignCoeff ε (edgeSignCoeff ε p) = p :=
  varSignHom_varSignHom _ p

theorem edgeSignCoeff_symm_apply (p : IncCoeffRing E) :
    (edgeSignCoeff ε).symm p = edgeSignCoeff ε p := rfl

/-- The coefficient sign change preserves the coefficient origin. -/
@[simp] theorem constantCoeff_edgeSignCoeff (p : IncCoeffRing E) :
    constantCoeff (edgeSignCoeff ε p) = constantCoeff p :=
  constantCoeff_varSignHom _ p

/-- The trivial sign acts trivially on coefficients. -/
theorem edgeSignCoeff_one (p : IncCoeffRing E) : edgeSignCoeff (1 : EdgeSign E) p = p := by
  have h : (1 : EdgeSign E).coeffVarSign = 1 := rfl
  rw [edgeSignCoeff_apply, h, varSignHom_one, AlgHom.id_apply]

/-- The coefficient sign change of a product of signs is the composite. -/
theorem edgeSignCoeff_mul (ε' : EdgeSign E) (p : IncCoeffRing E) :
    edgeSignCoeff (ε * ε') p = edgeSignCoeff ε (edgeSignCoeff ε' p) := by
  have h : (ε * ε').coeffVarSign = ε.coeffVarSign * ε'.coeffVarSign := rfl
  rw [edgeSignCoeff_apply, h, ← varSignHom_comp]
  rfl

end Coefficients

/-! ## Chart equations, torus relations and the induced ring automorphisms -/

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E) (ε : EdgeSign E)

/-- The sign change of an edge equation on any chart is the edge sign times the equation. -/
theorem varSignHom_incChartEq (σ : V → Bool) (e : E) :
    varSignHom ε.chartVarSign (G.incChartEq σ e) =
      ((ε e : ℤ) : MvPolynomial (IncChartVar V E) ℂ) * G.incChartEq σ e := by
  unfold incChartEq
  simp only [map_sum, map_mul, varSignHom_X, map_incCoord, EdgeSign.chartVarSign_inl,
    EdgeSign.chartVarSign_inr, Units.val_one, Int.cast_one, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- The sign change of a torus relation is its sign times the relation. -/
theorem varSignHom_incTorusRel (i : V ⊕ E) :
    varSignHom ε.torusVarSign (G.incTorusRel i) =
      ((ε.relSign i : ℤ) : MvPolynomial (IncTorusVar V E) ℂ) * G.incTorusRel i := by
  rcases i with v | e
  · simp [incTorusRel]
  · simp only [incTorusRel, EdgeSign.relSign_inr]
    rw [← rename_varSignHom _ ε.chartVarSign ε.torusVarSign (fun w => by rcases w with v | c <;> rfl),
      varSignHom_incChartEq, map_mul, map_intCast]

/-- The ideal of chart equations is invariant under the chart sign change. -/
theorem map_chartIdeal_edgeSign (σ : V → Bool) :
    Ideal.span (Set.range (G.incChartEq σ)) =
      (Ideal.span (Set.range (G.incChartEq σ))).map
        ((varSignEquiv (ε.chartVarSign (V := V)) : _ ≃ₐ[ℂ] _) : _ →+* _) :=
  (map_span_range_eq_of_units _ _ ε fun e => G.varSignHom_incChartEq ε σ e).symm

/-- The ideal of torus relations is invariant under the torus sign change. -/
theorem map_torusIdeal_edgeSign :
    Ideal.span (Set.range G.incTorusRel) =
      (Ideal.span (Set.range G.incTorusRel)).map
        ((varSignEquiv (ε.torusVarSign (V := V)) : _ ≃ₐ[ℂ] _) : _ →+* _) :=
  (map_span_range_eq_of_units _ _ ε.relSign fun i => G.varSignHom_incTorusRel ε i).symm

/-- The chart ring automorphism of an edge sign. -/
noncomputable def edgeSignChart (σ : V → Bool) : G.IncChartRing σ ≃ₐ[ℂ] G.IncChartRing σ :=
  Ideal.quotientEquivAlg _ _ (varSignEquiv ε.chartVarSign) (G.map_chartIdeal_edgeSign ε σ)

theorem edgeSignChart_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.edgeSignChart ε σ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (varSignHom ε.chartVarSign p) :=
  rfl

/-- The common torus ring automorphism of an edge sign. -/
noncomputable def edgeSignTorus : G.IncTorusRing ≃ₐ[ℂ] G.IncTorusRing :=
  Ideal.quotientEquivAlg _ _ (varSignEquiv ε.torusVarSign) (G.map_torusIdeal_edgeSign ε)

theorem edgeSignTorus_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    G.edgeSignTorus ε (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (varSignHom ε.torusVarSign p) :=
  rfl

/-- The torus sign change fixes the vertex coordinates `t_v`. -/
@[simp] theorem edgeSignTorus_vertex (v : V) :
    G.edgeSignTorus ε (Ideal.Quotient.mk _ (X (Sum.inl v))) = Ideal.Quotient.mk _ (X (Sum.inl v)) := by
  simp [edgeSignTorus_mk]

/-- The torus sign change fixes the inverse vertex coordinates `s_v = t_v⁻¹`. -/
@[simp] theorem edgeSignTorus_vertexInv (v : V) :
    G.edgeSignTorus ε (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))) := by
  simp [edgeSignTorus_mk]

/-- The torus sign change multiplies the coefficient `c_{e,α,β}` by `ε_e`. -/
@[simp] theorem edgeSignTorus_coeff (c : IncCoeffIdx E) :
    G.edgeSignTorus ε (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c)))) =
      ((ε c.1 : ℤ) : G.IncTorusRing) * Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c))) := by
  simp [edgeSignTorus_mk]

/-- The chart sign change fixes the vertex coordinates. -/
@[simp] theorem edgeSignChart_vertex (σ : V → Bool) (v : V) :
    G.edgeSignChart ε σ (Ideal.Quotient.mk _ (X (Sum.inl v))) = Ideal.Quotient.mk _ (X (Sum.inl v)) := by
  simp [edgeSignChart_mk]

/-- The torus sign change is an involution. -/
@[simp] theorem edgeSignTorus_edgeSignTorus (x : G.IncTorusRing) :
    G.edgeSignTorus ε (G.edgeSignTorus ε x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [edgeSignTorus_mk, edgeSignTorus_mk, varSignHom_varSignHom]

theorem edgeSignTorus_symm_apply (x : G.IncTorusRing) :
    (G.edgeSignTorus ε).symm x = G.edgeSignTorus ε x := by
  rw [AlgEquiv.symm_apply_eq, edgeSignTorus_edgeSignTorus]

/-- The torus sign change on the torus values of chart variables. -/
theorem edgeSignTorus_incChartVal (σ : V → Bool) (w : IncChartVar V E) :
    G.edgeSignTorus ε (G.incChartVal σ w) =
      ((ε.chartVarSign w : ℤ) : G.IncTorusRing) * G.incChartVal σ w := by
  rcases w with v | c
  · simp only [incChartVal, EdgeSign.chartVarSign_inl, Units.val_one, Int.cast_one, one_mul]
    split_ifs <;> simp [edgeSignTorus_mk]
  · simp [incChartVal, edgeSignTorus_mk]

/-- The torus sign change intertwines the chart restrictions. -/
theorem edgeSignTorus_comp_incChartMap (σ : V → Bool) :
    (G.edgeSignTorus ε).toAlgHom.comp (G.incChartMap σ) =
      (G.incChartMap σ).comp (G.edgeSignChart ε σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro w
  change G.edgeSignTorus ε (G.incChartMap σ (Ideal.Quotient.mk _ (X w))) =
    G.incChartMap σ (Ideal.Quotient.mk _ (varSignHom ε.chartVarSign (X w)))
  rw [incChartMap_mk, aeval_X, edgeSignTorus_incChartVal, varSignHom_X, incChartMap_mk, map_mul,
    aeval_X, map_intCast]

theorem edgeSignTorus_incChartMap (σ : V → Bool) (y : G.IncChartRing σ) :
    G.edgeSignTorus ε (G.incChartMap σ y) = G.incChartMap σ (G.edgeSignChart ε σ y) :=
  AlgHom.congr_fun (G.edgeSignTorus_comp_incChartMap ε σ) y

/-- The torus sign change preserves the incidence ring. -/
theorem edgeSignTorus_mem_incidenceRing_iff (x : G.IncTorusRing) :
    G.edgeSignTorus ε x ∈ G.IncidenceRing ↔ x ∈ G.IncidenceRing := by
  simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range]
  constructor
  · intro h σ
    obtain ⟨y, hy⟩ := h σ
    refine ⟨(G.edgeSignChart ε σ).symm y, (G.edgeSignTorus ε).injective ?_⟩
    rw [edgeSignTorus_incChartMap, AlgEquiv.apply_symm_apply, hy]
  · rintro h σ
    obtain ⟨y, rfl⟩ := h σ
    exact ⟨G.edgeSignChart ε σ y, (G.edgeSignTorus_incChartMap ε σ y).symm⟩

/-- The automorphism of the actual incidence ring induced by an edge sign; vertex variables are
fixed and coefficients change sign with their edge. -/
noncomputable def edgeSignIncidence : G.IncidenceRing ≃ₐ[ℂ] G.IncidenceRing where
  toFun x := ⟨G.edgeSignTorus ε x.val, (G.edgeSignTorus_mem_incidenceRing_iff ε x.val).mpr x.property⟩
  invFun y := ⟨(G.edgeSignTorus ε).symm y.val, (G.edgeSignTorus_mem_incidenceRing_iff ε _).mp
    (by rw [AlgEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext ((G.edgeSignTorus ε).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((G.edgeSignTorus ε).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul (G.edgeSignTorus ε) x.val y.val)
  map_add' x y := Subtype.ext (map_add (G.edgeSignTorus ε) x.val y.val)
  commutes' r := Subtype.ext ((G.edgeSignTorus ε).commutes r)

@[simp] theorem edgeSignIncidence_val (x : G.IncidenceRing) :
    (G.edgeSignIncidence ε x : G.IncTorusRing) = G.edgeSignTorus ε x.val := rfl

@[simp] theorem edgeSignIncidence_symm_val (y : G.IncidenceRing) :
    ((G.edgeSignIncidence ε).symm y : G.IncTorusRing) = (G.edgeSignTorus ε).symm y.val := rfl

/-- The incidence sign change is an involution. -/
@[simp] theorem edgeSignIncidence_edgeSignIncidence (x : G.IncidenceRing) :
    G.edgeSignIncidence ε (G.edgeSignIncidence ε x) = x :=
  Subtype.ext (G.edgeSignTorus_edgeSignTorus ε x.val)

/-- The incidence sign change intertwines the coefficient maps. -/
theorem edgeSignIncidence_coeffHom (r : IncCoeffRing E) :
    G.edgeSignIncidence ε (G.coeffHom r) = G.coeffHom (edgeSignCoeff ε r) := by
  have h : (G.edgeSignIncidence ε).toAlgHom.comp G.coeffHom =
      G.coeffHom.comp (edgeSignCoeff ε).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro c
    apply Subtype.ext
    change G.edgeSignTorus ε (G.coeffHom (X c)).val = (G.coeffHom (edgeSignCoeff ε (X c))).val
    rw [edgeSignCoeff_X, map_mul, map_intCast]
    simp only [coeffHom, aeval_X]
    rw [edgeSignTorus_mk, varSignHom_X, map_mul, map_intCast]
    rfl
  exact AlgHom.congr_fun h r

/-- The torus sign change intertwines the coefficient actions on the common torus. -/
theorem edgeSignTorus_incTorusCoeffHom (r : IncCoeffRing E) :
    G.edgeSignTorus ε (G.incTorusCoeffHom r) = G.incTorusCoeffHom (edgeSignCoeff ε r) := by
  rw [incTorusCoeffHom_apply, incTorusCoeffHom_apply, ← edgeSignIncidence_coeffHom]
  rfl

/-- The trivial sign acts trivially on the torus ring. -/
theorem edgeSignTorus_one (x : G.IncTorusRing) : G.edgeSignTorus (1 : EdgeSign E) x = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : (1 : EdgeSign E).torusVarSign (V := V) = 1 := by
    funext w
    rcases w with v | v | c <;> rfl
  rw [edgeSignTorus_mk, h, varSignHom_one, AlgHom.id_apply]

/-- The torus sign change of a product of signs is the composite. -/
theorem edgeSignTorus_mul (ε' : EdgeSign E) (x : G.IncTorusRing) :
    G.edgeSignTorus (ε * ε') x = G.edgeSignTorus ε (G.edgeSignTorus ε' x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : (ε * ε').torusVarSign (V := V) = ε.torusVarSign * ε'.torusVarSign := by
    funext w
    rcases w with v | v | c <;> rfl
  rw [edgeSignTorus_mk, edgeSignTorus_mk, edgeSignTorus_mk, h, ← varSignHom_comp]
  rfl

end BPFixedPoints.Multigraph
