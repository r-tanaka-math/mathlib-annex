/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Basic
import MathlibAnnex.Algebra.Star.ProjectionEquivalence

/-!
# Corners and transport by internal partial isometries

The carrier of `corner M p hp` is `{x : M | p * x = x ∧ x * p = x}`.
It is a norm-closed nonunital star subalgebra. Its distinguished two-sided
identity is the element `p`; the ambient identity is not used as the unit
of a proper corner. Conjugation by a partial isometry in `M` gives an actual
star-algebra equivalence between its initial and final corners.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The algebraic corner with its inherited nonunital star-algebra structure. -/
def corner (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ M.toStarSubalgebra where
  carrier := {x | p * x = x ∧ x * p = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨by rw [← mul_assoc, hx.1], by rw [mul_assoc, hy.2]⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2]⟩
  star_mem' := by
    intro x hx
    constructor
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hx.2
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hx.1

@[simp]
theorem mem_corner (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (x : M.toStarSubalgebra) :
    x ∈ corner M p hp ↔ p * x = x ∧ x * p = x := Iff.rfl

/-- The two absorption equations are equivalent to the usual sandwich
description of the corner. -/
theorem mem_corner_iff_sandwich (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (x : M.toStarSubalgebra) :
    x ∈ corner M p hp ↔ p * x * p = x := by
  constructor
  · intro hx
    rw [hx.1, hx.2]
  · intro hx
    constructor
    · calc
        p * x = p * (p * x * p) := by rw [hx]
        _ = (p * p) * x * p := by simp only [mul_assoc]
        _ = x := by rw [hp.isIdempotentElem.eq, hx]
    · calc
        x * p = (p * x * p) * p := by rw [hx]
        _ = p * x * (p * p) := by simp only [mul_assoc]
        _ = x := by rw [hp.isIdempotentElem.eq, hx]

/-- Corners are norm closed, as intersections of two equalizers of
continuous multiplication maps. -/
theorem isClosed_corner (M : VonNeumannAlgebra H)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    IsClosed (corner M p hp : Set M.toStarSubalgebra) := by
  change IsClosed ({x : M.toStarSubalgebra | p * x = x} ∩
    {x : M.toStarSubalgebra | x * p = x})
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

-- Reuse Mathlib's closed nonunital star-subalgebra C*-algebra instance.
attribute [instance] isClosed_corner

/-- The corner identity, represented by its projection. -/
def cornerUnit (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) : corner M p hp :=
  ⟨p, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq⟩

@[simp]
theorem coe_cornerUnit (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) : (cornerUnit M p hp : M.toStarSubalgebra) = p := rfl

@[simp]
theorem cornerUnit_mul (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (x : corner M p hp) : cornerUnit M p hp * x = x :=
  Subtype.ext x.property.1

@[simp]
theorem mul_cornerUnit (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (x : corner M p hp) : x * cornerUnit M p hp = x :=
  Subtype.ext x.property.2

/-- Even a left identity for the corner must be its projection. -/
theorem cornerUnit_unique (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (e : corner M p hp)
    (he : ∀ x : corner M p hp, e * x = x) : e = cornerUnit M p hp := by
  calc
    e = e * cornerUnit M p hp := (mul_cornerUnit M p hp e).symm
    _ = cornerUnit M p hp := he _

/-- The zero projection has the zero corner. -/
@[simp]
theorem corner_zero (M : VonNeumannAlgebra H) :
    corner M 0 (IsStarProjection.zero _) = ⊥ := by
  ext x
  simp [mem_corner, NonUnitalStarAlgebra.mem_bot, eq_comm]

/-- The unit projection has the whole algebra as its corner. -/
@[simp]
theorem corner_one (M : VonNeumannAlgebra H) :
    corner M 1 (IsStarProjection.one _) = ⊤ := by
  ext x
  simp [mem_corner]

/-- For projections, membership in a corner is exactly being a
subprojection. -/
theorem projection_mem_corner_iff_le (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    q ∈ corner M p hp ↔ q ≤ p := by
  constructor
  · intro h
    exact (hq.le_iff_mul_eq_left hp).2 h.2
  · intro h
    exact ⟨(hq.le_iff_mul_eq_right hp).1 h, (hq.le_iff_mul_eq_left hp).1 h⟩

/-- Smaller projections give smaller corners. -/
theorem corner_le_of_projection_le (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p ≤ q) : corner M p hp ≤ corner M q hq := by
  have hqp : q * p = p := (hp.le_iff_mul_eq_right hq).1 hpq
  have hpq' : p * q = p := (hp.le_iff_mul_eq_left hq).1 hpq
  intro x hx
  constructor
  · calc
      q * x = q * (p * x) := by rw [hx.1]
      _ = (q * p) * x := (mul_assoc _ _ _).symm
      _ = x := by rw [hqp, hx.1]
  · calc
      x * q = (x * p) * q := by rw [hx.2]
      _ = x * (p * q) := mul_assoc _ _ _
      _ = x := by rw [hpq', hx.2]

/-- Compression is linear. No multiplicativity is asserted for a
noncentral projection. -/
def cornerCompression (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) : M.toStarSubalgebra →ₗ[ℂ] corner M p hp where
  toFun x := ⟨p * x * p, by
    constructor
    · calc
        p * (p * x * p) = (p * p) * x * p := by simp only [mul_assoc]
        _ = p * x * p := by rw [hp.isIdempotentElem.eq]
    · calc
        (p * x * p) * p = p * x * (p * p) := by simp only [mul_assoc]
        _ = p * x * p := by rw [hp.isIdempotentElem.eq]⟩
  map_add' x y := by
    apply Subtype.ext
    change p * (x+y) * p = p*x*p + p*y*p
    rw [mul_add, add_mul]
  map_smul' c x := by
    apply Subtype.ext
    change p * (c • x) * p = c • (p * x * p)
    rw [mul_smul_comm, smul_mul_assoc]

@[simp]
theorem coe_cornerCompression (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (x : M.toStarSubalgebra) :
    (cornerCompression M p hp x : M.toStarSubalgebra) = p * x * p := rfl

/-- Compression restricts to the identity on the corner. -/
@[simp]
theorem cornerCompression_coe (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (x : corner M p hp) :
    cornerCompression M p hp x = x := by
  apply Subtype.ext
  exact (mem_corner_iff_sandwich M p hp x).1 x.property

private def conjugateCorner (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v)
    (hfinal : v * star v = q) (x : corner M p hp) : corner M q hq :=
  ⟨v * (x : M.toStarSubalgebra) * star v, by
    constructor
    · calc
        q * (v * (x : M.toStarSubalgebra) * star v) =
            (v * star v * v) * (x : M.toStarSubalgebra) * star v := by
          rw [← hfinal]
          simp only [mul_assoc]
        _ = v * (x : M.toStarSubalgebra) * star v := by rw [hv.mul_star_self_mul]
    · calc
        (v * (x : M.toStarSubalgebra) * star v) * q =
            v * (x : M.toStarSubalgebra) * (star v * (v * star v)) := by
          rw [← hfinal]
          simp only [mul_assoc]
        _ = v * (x : M.toStarSubalgebra) * star v := by rw [hv.star_mul_final]⟩

/-- Conjugation by an internal partial isometry is an actual star-algebra
equivalence between its initial and final corners. -/
def cornerEquiv (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v)
    (hinitial : star v * v = p) (hfinal : v * star v = q) :
    corner M p hp ≃⋆ₐ[ℂ] corner M q hq where
  toFun := conjugateCorner M hp hq v hv hfinal
  invFun := conjugateCorner M hq hp (star v) hv.star
    (by simpa only [star_star] using hinitial)
  left_inv x := by
    apply Subtype.ext
    change star v * (v * (x : M.toStarSubalgebra) * star v) * star (star v) =
      (x : M.toStarSubalgebra)
    rw [star_star]
    calc
      star v * (v * (x : M.toStarSubalgebra) * star v) * v =
          (star v * v) * (x : M.toStarSubalgebra) * (star v * v) := by
        simp only [mul_assoc]
      _ = (x : M.toStarSubalgebra) := by rw [hinitial, x.property.1, x.property.2]
  right_inv x := by
    apply Subtype.ext
    change v * (star v * (x : M.toStarSubalgebra) * star (star v)) * star v =
      (x : M.toStarSubalgebra)
    rw [star_star]
    calc
      v * (star v * (x : M.toStarSubalgebra) * v) * star v =
          (v * star v) * (x : M.toStarSubalgebra) * (v * star v) := by
        simp only [mul_assoc]
      _ = (x : M.toStarSubalgebra) := by rw [hfinal, x.property.1, x.property.2]
  map_mul' x y := by
    apply Subtype.ext
    change v * ((x : M.toStarSubalgebra) * (y : M.toStarSubalgebra)) * star v =
      (v * (x : M.toStarSubalgebra) * star v) *
        (v * (y : M.toStarSubalgebra) * star v)
    symm
    calc
      (v * (x : M.toStarSubalgebra) * star v) *
          (v * (y : M.toStarSubalgebra) * star v) =
          v * (x : M.toStarSubalgebra) * (star v * v) *
            (y : M.toStarSubalgebra) * star v := by simp only [mul_assoc]
      _ = v * ((x : M.toStarSubalgebra) * p) *
            (y : M.toStarSubalgebra) * star v := by rw [hinitial, mul_assoc v _ p]
      _ = v * ((x : M.toStarSubalgebra) * (y : M.toStarSubalgebra)) * star v := by
        rw [x.property.2, mul_assoc v]
  map_add' x y := by
    apply Subtype.ext
    change v * ((x : M.toStarSubalgebra) + (y : M.toStarSubalgebra)) * star v =
      v * (x : M.toStarSubalgebra) * star v + v * (y : M.toStarSubalgebra) * star v
    simp only [mul_add, add_mul]
  map_star' x := by
    apply Subtype.ext
    change v * star (x : M.toStarSubalgebra) * star v =
      star (v * (x : M.toStarSubalgebra) * star v)
    simp only [star_mul, star_star, mul_assoc]
  map_smul' c x := by
    apply Subtype.ext
    change v * (c • (x : M.toStarSubalgebra)) * star v =
      c • (v * (x : M.toStarSubalgebra) * star v)
    simp only [mul_smul_comm, smul_mul_assoc]

@[simp]
theorem coe_cornerEquiv (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v)
    (hinitial : star v * v = p) (hfinal : v * star v = q)
    (x : corner M p hp) :
    (cornerEquiv M hp hq v hv hinitial hfinal x : M.toStarSubalgebra) =
      v * (x : M.toStarSubalgebra) * star v := rfl

/-- The corner equivalence carries its actual unit `p` to the actual unit
`q`. This equality does not identify either projection with the ambient `1`. -/
theorem cornerEquiv_unit (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v)
    (hinitial : star v * v = p) (hfinal : v * star v = q) :
    cornerEquiv M hp hq v hv hinitial hfinal (cornerUnit M p hp) =
      cornerUnit M q hq := by
  apply Subtype.ext
  change v * p * star v = q
  rw [← hinitial, hv.mul_initial, hfinal]

/-- Internal Murray-von Neumann equivalence gives equivalent corners. -/
theorem nonempty_cornerEquiv_of_equivalent (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (h : MurrayVonNeumannEquivalent p q) :
    Nonempty (corner M p h.1 ≃⋆ₐ[ℂ] corner M q h.2.1) := by
  obtain ⟨v, hv, hinitial, hfinal⟩ := h.2.2
  exact ⟨cornerEquiv M h.1 h.2.1 v hv hinitial hfinal⟩

/-- The inherited corner projection predicate is reflected by its
inclusion. This is a property of the existing predicate. -/
theorem isStarProjection_corner_iff (M : VonNeumannAlgebra H)
    (e : M.toStarSubalgebra) (he : IsStarProjection e) (p : corner M e he) :
    IsStarProjection p ↔ IsStarProjection (p : M.toStarSubalgebra) := by
  constructor
  · intro hp
    exact hp.map (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (corner M e he))
  · intro hp
    exact ⟨Subtype.ext hp.isIdempotentElem.eq,
      Subtype.ext hp.isSelfAdjoint.star_eq⟩

/-- Equivalence between two corner projections can be checked in the
containing algebra: the endpoint absorption equations force the same
partial-isometry witness to lie in the corner. -/
theorem murrayVonNeumannEquivalent_corner_iff (M : VonNeumannAlgebra H)
    (e : M.toStarSubalgebra) (he : IsStarProjection e)
    (p q : corner M e he) :
    MurrayVonNeumannEquivalent p q ↔
      MurrayVonNeumannEquivalent (p : M.toStarSubalgebra) (q : M.toStarSubalgebra) := by
  constructor
  · intro h
    exact h.map (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (corner M e he))
  · intro h
    obtain ⟨v, hv, hi, hf, hev, hve⟩ :=
      h.exists_partial_isometry_with_absorption he p.property.2 q.property.2
    let w : corner M e he := ⟨v, hev, hve⟩
    refine ⟨(isStarProjection_corner_iff M e he p).2 h.1,
      (isStarProjection_corner_iff M e he q).2 h.2.1, w, ?_, ?_, ?_⟩
    · change w * star w * w = w
      exact Subtype.ext hv
    · exact Subtype.ext hi
    · exact Subtype.ext hf

/-- Subequivalence between corner projections is also reflected by the
corner inclusion, including an actual subprojection and witness in the
corner. -/
theorem murrayVonNeumannSubequivalent_corner_iff (M : VonNeumannAlgebra H)
    (e : M.toStarSubalgebra) (he : IsStarProjection e)
    (p q : corner M e he) :
    MurrayVonNeumannSubequivalent p q ↔
      MurrayVonNeumannSubequivalent
        (p : M.toStarSubalgebra) (q : M.toStarSubalgebra) := by
  constructor
  · intro h
    exact h.map (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (corner M e he))
  · rintro ⟨hq, r, hpr, hrq⟩
    have hre : r * e = r := by
      calc
        r * e = (r * (q : M.toStarSubalgebra)) * e := by rw [hrq]
        _ = r * ((q : M.toStarSubalgebra) * e) := mul_assoc _ _ _
        _ = r := by rw [q.property.2, hrq]
    have her : e * r = r := by
      simpa only [star_mul, he.isSelfAdjoint.star_eq,
        hpr.2.1.isSelfAdjoint.star_eq] using congrArg star hre
    let s : corner M e he := ⟨r, her, hre⟩
    refine ⟨(isStarProjection_corner_iff M e he q).2 hq, s, ?_, ?_⟩
    · exact (murrayVonNeumannEquivalent_corner_iff M e he p s).2 hpr
    · exact Subtype.ext hrq

end VonNeumannAlgebra
