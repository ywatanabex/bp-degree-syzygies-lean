import BPFixedPoints.Family.Points

/-!
# Normalized belief coordinates

Write the four edge beliefs as q, r=uᵢ−q, s=uⱼ−q, d=1−uᵢ−uⱼ+q.
The edge relation is a²rs=qd. Make all edge beliefs and both states of every
vertex belief units.
-/

namespace BPFixedPoints.Multigraph

open BP
open scoped Ring
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {G : Multigraph V E}
variable {R : Type*} [CommRing R]

theorem unit_ringInverse {x : R} (h : IsUnit x) : IsUnit x⁻¹ʳ := by
  rw [Ring.inverse_of_isUnit h]
  exact Units.isUnit _

@[ext] structure BeliefPoint (G : Multigraph V E) (R : Type*) [CommRing R] where
  a : E → R
  u : V → R
  q : E → R
  a_unit : ∀ e, IsUnit (a e)
  u_unit : ∀ i, IsUnit (u i)
  uc_unit : ∀ i, IsUnit (1 - u i)
  q_unit : ∀ e, IsUnit (q e)
  r_unit : ∀ e, IsUnit (u (G.fst e) - q e)
  s_unit : ∀ e, IsUnit (u (G.snd e) - q e)
  d_unit : ∀ e, IsUnit (1 - u (G.fst e) - u (G.snd e) + q e)
  equation : ∀ e, a e ^ 2 * (u (G.fst e) - q e) * (u (G.snd e) - q e) =
    q e * (1 - u (G.fst e) - u (G.snd e) + q e)

namespace FamilyPoint

variable (p : G.FamilyPoint R)

noncomputable def beliefU (i : V) : R := p.F i * (1 + p.F i)⁻¹ʳ

def edgeZ (e : E) : R :=
  p.a e * p.X (e, true) * p.X (e, false) + p.X (e, true) + p.X (e, false) + p.a e

theorem edgeZ_eq (e : E) :
    p.edgeZ e = (1 + p.F (G.fst e)) * (p.X (e, false) + p.a e) := by
  have h := p.equation (e, false)
  have hF := G.ringField_tail p.b p.y (e, true)
  change p.F (G.fst e) = p.X (e, true) * p.y (e, false) at hF
  dsimp only [edgeZ]
  change p.y (e, false) * (p.X (e, false) + p.a e) = _ at h
  linear_combination -p.X (e, true) * h - (p.X (e, false) + p.a e) * hF

theorem edgeZ_eq' (e : E) :
    p.edgeZ e = (1 + p.F (G.snd e)) * (p.X (e, true) + p.a e) := by
  have h := p.equation (e, true)
  have hF := G.ringField_tail p.b p.y (e, false)
  change p.F (G.snd e) = p.X (e, false) * p.y (e, true) at hF
  dsimp only [edgeZ]
  change p.y (e, true) * (p.X (e, true) + p.a e) = _ at h
  linear_combination -p.X (e, false) * h - (p.X (e, true) + p.a e) * hF

theorem edgeZ_unit (e : E) : IsUnit (p.edgeZ e) := by
  rw [p.edgeZ_eq]
  exact (p.field_unit _).mul (p.den_unit (e, false))

noncomputable def beliefQ (e : E) : R :=
  p.a e * p.X (e, true) * p.X (e, false) * (p.edgeZ e)⁻¹ʳ

theorem beliefU_compl (i : V) : 1 - p.beliefU i = (1 + p.F i)⁻¹ʳ := by
  have h := Ring.mul_inverse_cancel _ (p.field_unit i)
  dsimp only [beliefU]
  linear_combination -h

theorem beliefR (e : E) :
    p.beliefU (G.fst e) - p.beliefQ e = p.X (e, true) * (p.edgeZ e)⁻¹ʳ := by
  have hz := Ring.mul_inverse_cancel _ (p.edgeZ_unit e)
  have hu := Ring.mul_inverse_cancel _ (p.field_unit (G.fst e))
  have he := p.equation (e, false)
  have hf := G.ringField_tail p.b p.y (e, true)
  have hZ := p.edgeZ_eq e
  change p.F (G.fst e) = p.X (e, true) * p.y (e, false) at hf
  change p.y (e, false) * (p.X (e, false) + p.a e) = _ at he
  dsimp only [beliefU, beliefQ]
  grind only

theorem beliefS (e : E) :
    p.beliefU (G.snd e) - p.beliefQ e = p.X (e, false) * (p.edgeZ e)⁻¹ʳ := by
  have hz := Ring.mul_inverse_cancel _ (p.edgeZ_unit e)
  have hu := Ring.mul_inverse_cancel _ (p.field_unit (G.snd e))
  have he := p.equation (e, true)
  have hf := G.ringField_tail p.b p.y (e, false)
  have hZ := p.edgeZ_eq' e
  change p.F (G.snd e) = p.X (e, false) * p.y (e, true) at hf
  change p.y (e, true) * (p.X (e, true) + p.a e) = _ at he
  dsimp only [beliefU, beliefQ]
  grind only

theorem beliefD (e : E) :
    1 - p.beliefU (G.fst e) - p.beliefU (G.snd e) + p.beliefQ e =
      p.a e * (p.edgeZ e)⁻¹ʳ := by
  have hr := p.beliefR e
  have hs := p.beliefS e
  have hz := Ring.mul_inverse_cancel _ (p.edgeZ_unit e)
  change (p.a e * p.X (e, true) * p.X (e, false) + p.X (e, true) +
    p.X (e, false) + p.a e) * (p.edgeZ e)⁻¹ʳ = 1 at hz
  dsimp only [beliefQ] at hr hs ⊢
  linear_combination -hr - hs - hz

noncomputable def toBelief : BeliefPoint G R where
  a := p.a
  u := p.beliefU
  q := p.beliefQ
  a_unit := p.a_unit
  u_unit i := (p.F_unit i).mul (unit_ringInverse (p.field_unit i))
  uc_unit i := by rw [p.beliefU_compl]; exact unit_ringInverse (p.field_unit i)
  q_unit e := ((p.a_unit e).mul (p.X_unit _)).mul (p.X_unit _) |>.mul
    (unit_ringInverse (p.edgeZ_unit e))
  r_unit e := by rw [p.beliefR]; exact (p.X_unit _).mul (unit_ringInverse (p.edgeZ_unit e))
  s_unit e := by rw [p.beliefS]; exact (p.X_unit _).mul (unit_ringInverse (p.edgeZ_unit e))
  d_unit e := by rw [p.beliefD]; exact (p.a_unit _).mul (unit_ringInverse (p.edgeZ_unit e))
  equation e := by rw [p.beliefR, p.beliefS, p.beliefD]; dsimp [beliefQ]; ring

end FamilyPoint

namespace BeliefPoint

variable (p : BeliefPoint G R)

def d (e : E) : R := 1 - p.u (G.fst e) - p.u (G.snd e) + p.q e
def t (α : Dart E) : R := p.u (G.tail α) - p.q α.1

theorem t_unit (α : Dart E) : IsUnit (p.t α) := by
  rcases α with ⟨e, _ | _⟩
  · exact p.s_unit e
  · exact p.r_unit e

theorem t_add_d (α : Dart E) : p.t α + p.d α.1 = 1 - p.u (G.head α) := by
  rcases α with ⟨e, _ | _⟩ <;> simp only [t, d, tail, head, Bool.cond_false, Bool.cond_true] <;> ring

theorem edge_eq (α : Dart E) :
    p.a α.1 ^ 2 * p.t α * p.t (rev α) = p.q α.1 * p.d α.1 := by
  rcases α with ⟨e, _ | _⟩
  · simpa only [t, d, tail, rev, Bool.not_false, Bool.cond_false, Bool.cond_true,
      mul_assoc, mul_comm, mul_left_comm] using p.equation e
  · exact p.equation e

noncomputable def field (i : V) : R := p.u i * (1 - p.u i)⁻¹ʳ
noncomputable def cavity (α : Dart E) : R := p.a α.1 * p.t α * (p.d α.1)⁻¹ʳ
noncomputable def message (α : Dart E) : R := p.field (G.head α) * (p.cavity (rev α))⁻¹ʳ
noncomputable def parameter (i : V) : R := p.field i * (∏ α ∈ G.inDarts i, p.message α)⁻¹ʳ

theorem field_isUnit (i : V) : IsUnit (p.field i) :=
  (p.u_unit i).mul (unit_ringInverse (p.uc_unit i))
theorem cavity_isUnit (α : Dart E) : IsUnit (p.cavity α) :=
  ((p.a_unit α.1).mul (p.t_unit α)).mul (unit_ringInverse (p.d_unit α.1))
theorem message_isUnit (α : Dart E) : IsUnit (p.message α) :=
  (p.field_isUnit _).mul (unit_ringInverse (p.cavity_isUnit _))
theorem message_prod_isUnit (i : V) : IsUnit (∏ α ∈ G.inDarts i, p.message α) :=
  IsUnit.prod_iff.mpr fun α _ => p.message_isUnit α
theorem parameter_isUnit (i : V) : IsUnit (p.parameter i) :=
  (p.field_isUnit _).mul (unit_ringInverse (p.message_prod_isUnit i))

theorem field_mul_compl (i : V) : p.field i * (1 - p.u i) = p.u i := by
  exact Ring.inverse_mul_cancel_right _ _ (p.uc_unit i)

theorem one_add_field (i : V) : 1 + p.field i = (1 - p.u i)⁻¹ʳ := by
  have h := Ring.mul_inverse_cancel _ (p.uc_unit i)
  dsimp only [field]
  linear_combination -h

theorem cavity_add_a (α : Dart E) :
    p.cavity α + p.a α.1 = p.a α.1 * (1 - p.u (G.head α)) * (p.d α.1)⁻¹ʳ := by
  have h := p.t_add_d α
  have hd := Ring.mul_inverse_cancel _ (p.d_unit α.1)
  change p.d α.1 * (p.d α.1)⁻¹ʳ = 1 at hd
  dsimp only [cavity]
  linear_combination p.a α.1 * (p.d α.1)⁻¹ʳ * h - p.a α.1 * hd

theorem message_mul_cavity (α : Dart E) :
    p.message α * p.cavity (rev α) = p.field (G.head α) := by
  exact Ring.inverse_mul_cancel_right _ _ (p.cavity_isUnit _)

theorem message_equation (α : Dart E) :
    p.message α * (p.cavity α + p.a α.1) = p.a α.1 * p.cavity α + 1 := by
  apply (p.cavity_isUnit (rev α)).mul_right_cancel
  have hm := p.message_mul_cavity α
  have hf := p.field_mul_compl (G.head α)
  have ht : p.t (rev α) = p.u (G.head α) - p.q α.1 := by simp [t]
  have he := p.edge_eq α
  have hd := Ring.mul_inverse_cancel _ (p.d_unit α.1)
  change p.d α.1 * (p.d α.1)⁻¹ʳ = 1 at hd
  rw [mul_assoc, mul_comm (p.cavity α + _), ← mul_assoc, hm, p.cavity_add_a]
  change p.field (G.head α) * (p.a α.1 * (1 - p.u (G.head α)) * (p.d α.1)⁻¹ʳ) =
    (p.a α.1 * (p.a α.1 * p.t α * (p.d α.1)⁻¹ʳ) + 1) *
      (p.a α.1 * p.t (rev α) * (p.d α.1)⁻¹ʳ)
  grind only

theorem reconstructed_field (i : V) :
    G.ringField p.parameter p.message i = p.field i := by
  exact Ring.inverse_mul_cancel_right _ _ (p.message_prod_isUnit i)

theorem reconstructed_cavity (α : Dart E) :
    G.ringCavity p.parameter p.message α = p.cavity α := by
  apply (p.message_isUnit (rev α)).mul_right_cancel
  rw [← G.ringField_tail, p.reconstructed_field, mul_comm]
  simpa using (p.message_mul_cavity (rev α)).symm

noncomputable def toFamily : G.FamilyPoint R where
  a := p.a
  b := p.parameter
  y := p.message
  a_unit := p.a_unit
  b_unit := p.parameter_isUnit
  y_unit := p.message_isUnit
  den_unit α := by
    rw [p.reconstructed_cavity, p.cavity_add_a]
    exact ((p.a_unit _).mul (p.uc_unit _)).mul (unit_ringInverse (p.d_unit _))
  field_unit i := by
    rw [p.reconstructed_field, p.one_add_field]
    exact unit_ringInverse (p.uc_unit i)
  equation α := by rw [p.reconstructed_cavity]; exact p.message_equation α

variable {S : Type*} [CommRing S]

def map (φ : R →+* S) : BeliefPoint G S where
  a := φ ∘ p.a
  u := φ ∘ p.u
  q := φ ∘ p.q
  a_unit e := (p.a_unit e).map φ
  u_unit i := (p.u_unit i).map φ
  uc_unit i := by simpa using (p.uc_unit i).map φ
  q_unit e := (p.q_unit e).map φ
  r_unit e := by simpa using (p.r_unit e).map φ
  s_unit e := by simpa using (p.s_unit e).map φ
  d_unit e := by simpa using (p.d_unit e).map φ
  equation e := by simpa using congrArg φ (p.equation e)

@[simp] theorem map_d (φ : R →+* S) (e : E) : (p.map φ).d e = φ (p.d e) := by
  simp [d, map]
@[simp] theorem map_t (φ : R →+* S) (α : Dart E) : (p.map φ).t α = φ (p.t α) := by
  simp [t, map]
@[simp] theorem map_field (φ : R →+* S) (i : V) : (p.map φ).field i = φ (p.field i) := by
  simp [field, map, (p.uc_unit i).map_ringInverse φ]
@[simp] theorem map_cavity (φ : R →+* S) (α : Dart E) :
    (p.map φ).cavity α = φ (p.cavity α) := by
  change φ (p.a α.1) * (p.map φ).t α * ((p.map φ).d α.1)⁻¹ʳ =
    φ (p.a α.1 * p.t α * (p.d α.1)⁻¹ʳ)
  rw [map_t, map_d, map_mul, map_mul]
  congr 1
  exact ((p.d_unit α.1).map_ringInverse φ).symm
@[simp] theorem map_message (φ : R →+* S) (α : Dart E) :
    (p.map φ).message α = φ (p.message α) := by
  simp [message, (p.cavity_isUnit (rev α)).map_ringInverse φ]
@[simp] theorem map_parameter (φ : R →+* S) (i : V) :
    (p.map φ).parameter i = φ (p.parameter i) := by
  simp [parameter, (p.message_prod_isUnit i).map_ringInverse φ]

theorem toFamily_map (φ : R →+* S) : (p.map φ).toFamily = p.toFamily.map φ := by
  ext i
  · rfl
  · exact p.map_parameter φ i
  · exact p.map_message φ i

end BeliefPoint

namespace FamilyPoint

variable (p : G.FamilyPoint R)

@[simp] theorem toBelief_field (i : V) : p.toBelief.field i = p.F i := by
  change p.beliefU i * (1 - p.beliefU i)⁻¹ʳ = p.F i
  rw [p.beliefU_compl, Ring.inverse_inverse (p.field_unit i)]
  exact Ring.inverse_mul_cancel_right _ _ (p.field_unit i)

@[simp] theorem toBelief_cavity (α : Dart E) : p.toBelief.cavity α = p.X α := by
  have hd : p.toBelief.d α.1 = p.a α.1 * (p.edgeZ α.1)⁻¹ʳ := p.beliefD α.1
  have ht : p.toBelief.t α = p.X α * (p.edgeZ α.1)⁻¹ʳ := by
    rcases α with ⟨e, _ | _⟩
    · exact p.beliefS e
    · exact p.beliefR e
  apply (p.toBelief.d_unit α.1).mul_right_cancel
  change p.toBelief.cavity α * p.toBelief.d α.1 = p.X α * p.toBelief.d α.1
  dsimp only [BeliefPoint.cavity]
  rw [Ring.inverse_mul_cancel_right (p.toBelief.d α.1) _ (p.toBelief.d_unit α.1), hd, ht]
  change p.a α.1 * (p.X α * (p.edgeZ α.1)⁻¹ʳ) = p.X α * (p.a α.1 * (p.edgeZ α.1)⁻¹ʳ)
  ring

@[simp] theorem toBelief_message (α : Dart E) : p.toBelief.message α = p.y α := by
  change p.toBelief.field (G.head α) * (p.toBelief.cavity (rev α))⁻¹ʳ = p.y α
  rw [p.toBelief_field, p.toBelief_cavity]
  have h := G.ringField_tail p.b p.y (rev α)
  simp only [tail_rev, rev_rev] at h
  change p.F (G.head α) = p.X (rev α) * p.y α at h
  rw [h, mul_comm, Ring.inverse_mul_cancel_left _ _ (p.X_unit _)]

@[simp] theorem toBelief_parameter (i : V) : p.toBelief.parameter i = p.b i := by
  simp only [BeliefPoint.parameter, p.toBelief_field, p.toBelief_message]
  exact Ring.mul_inverse_cancel_right _ _ (IsUnit.prod_iff.mpr fun α _ => p.y_unit α)

theorem toFamily_toBelief : p.toBelief.toFamily = p := by
  ext i
  · rfl
  · exact p.toBelief_parameter i
  · exact p.toBelief_message i

end FamilyPoint

namespace BeliefPoint

variable (p : BeliefPoint G R)

@[simp] theorem toFamily_beliefU (i : V) : p.toFamily.beliefU i = p.u i := by
  change G.ringField p.parameter p.message i *
    (1 + G.ringField p.parameter p.message i)⁻¹ʳ = p.u i
  rw [p.reconstructed_field, p.one_add_field, Ring.inverse_inverse (p.uc_unit i)]
  exact p.field_mul_compl i

theorem toFamily_edgeZ (e : E) : p.toFamily.edgeZ e = p.a e * (p.d e)⁻¹ʳ := by
  rw [p.toFamily.edgeZ_eq]
  change (1 + G.ringField p.parameter p.message (G.fst e)) *
    (G.ringCavity p.parameter p.message (e, false) + p.a e) = _
  rw [p.reconstructed_field, p.reconstructed_cavity, p.cavity_add_a (e, false),
    p.one_add_field]
  change (1 - p.u (G.fst e))⁻¹ʳ *
    (p.a e * (1 - p.u (G.fst e)) * (p.d e)⁻¹ʳ) = _
  have h := Ring.inverse_mul_cancel _ (p.uc_unit (G.fst e))
  linear_combination p.a e * (p.d e)⁻¹ʳ * h

@[simp] theorem toFamily_beliefQ (e : E) : p.toFamily.beliefQ e = p.q e := by
  apply (p.toFamily.edgeZ_unit e).mul_right_cancel
  change (p.a e * G.ringCavity p.parameter p.message (e, true) *
    G.ringCavity p.parameter p.message (e, false) * (p.toFamily.edgeZ e)⁻¹ʳ) *
    p.toFamily.edgeZ e = p.q e * p.toFamily.edgeZ e
  rw [Ring.inverse_mul_cancel_right _ _ (p.toFamily.edgeZ_unit e),
    p.reconstructed_cavity, p.reconstructed_cavity, p.toFamily_edgeZ]
  have he := p.edge_eq (e, true)
  have hd := Ring.mul_inverse_cancel (p.d e) (p.d_unit e)
  change p.a e ^ 2 * p.t (e, true) * p.t (e, false) = p.q e * p.d e at he
  change p.a e * (p.a e * p.t (e, true) * (p.d e)⁻¹ʳ) *
    (p.a e * p.t (e, false) * (p.d e)⁻¹ʳ) = p.q e * (p.a e * (p.d e)⁻¹ʳ)
  grind only

theorem toBelief_toFamily : p.toFamily.toBelief = p := by
  ext i
  · rfl
  · exact p.toFamily_beliefU i
  · exact p.toFamily_beliefQ i

end BeliefPoint

/-- Natural bijection over commutative rings between admissible BP points and normalized-belief points. -/
noncomputable def familyPointEquivBelief : G.FamilyPoint R ≃ BeliefPoint G R where
  toFun := FamilyPoint.toBelief
  invFun := BeliefPoint.toFamily
  left_inv := FamilyPoint.toFamily_toBelief
  right_inv := BeliefPoint.toBelief_toFamily

end BPFixedPoints.Multigraph
