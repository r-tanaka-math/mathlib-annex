/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Algebra.Star.PartialIsometry

/-!
# Murray-von Neumann equivalence in a specified star ring

All witnesses belong to the carrier `R`. In particular, applying these
relations to a star-subalgebra subtype gives equivalence inside that
subalgebra, rather than ambient equivalence. Reflexivity is proved only
for star projections; no setoid is placed on arbitrary elements.

Subequivalence uses the algebraic subprojection equation `r * q = r`.
Its equivalence with C-star order is established in the analytic module.
The partial-isometry clause is essential over general star rings; under
the existing proper-star assumption it follows from either star-square
being a projection, and the usual two-equation witness is recovered.
-/

set_option autoImplicit false

universe u v

/-- Equivalence of star projections, witnessed inside the same carrier. -/
def MurrayVonNeumannEquivalent {R : Type u} [Mul R] [Star R] (p q : R) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : R, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q

/-- Equivalence to a subprojection of `q`, expressed without assuming an
order on all of the star ring. -/
def MurrayVonNeumannSubequivalent {R : Type u} [Mul R] [Star R] (p q : R) : Prop :=
  IsStarProjection q ∧ ∃ r : R, MurrayVonNeumannEquivalent p r ∧ r * q = r

namespace MurrayVonNeumannEquivalent

section Semigroup

variable {R : Type u} [Semigroup R] [StarMul R] {p q r : R}

theorem isStarProjection_left (h : MurrayVonNeumannEquivalent p q) :
    IsStarProjection p := h.1

theorem isStarProjection_right (h : MurrayVonNeumannEquivalent p q) :
    IsStarProjection q := h.2.1

theorem exists_partial_isometry (h : MurrayVonNeumannEquivalent p q) :
    ∃ v : R, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := h.2.2

theorem of_partial_isometry {v : R} (hv : IsPartialIsometry v) :
    MurrayVonNeumannEquivalent (star v * v) (v * star v) :=
  ⟨hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self,
    v, hv, rfl, rfl⟩

@[refl] protected theorem refl (hp : IsStarProjection p) :
    MurrayVonNeumannEquivalent p p := by
  refine ⟨hp, hp, p, hp.isPartialIsometry, ?_, ?_⟩ <;>
    rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

@[symm] protected theorem symm (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent q p := by
  obtain ⟨v, hv, hvp, hvq⟩ := h.exists_partial_isometry
  refine ⟨h.isStarProjection_right, h.isStarProjection_left, star v, hv.star, ?_, ?_⟩
  · simpa only [star_star] using hvq
  · simpa only [star_star] using hvp

@[trans] protected theorem trans (hpq : MurrayVonNeumannEquivalent p q)
    (hqr : MurrayVonNeumannEquivalent q r) : MurrayVonNeumannEquivalent p r := by
  obtain ⟨v, hv, hvp, hvq⟩ := hpq.exists_partial_isometry
  obtain ⟨w, hw, hwq, hwr⟩ := hqr.exists_partial_isometry
  have hqv : q * v = v := by
    rw [← hvq]
    exact hv.mul_star_self_mul
  have hwq' : w * q = w := by
    rw [← hwq]
    exact hw.mul_initial
  have hwv : IsPartialIsometry (w * v) :=
    hv.mul_of_initial_mul_eq w (by rw [hwq, hqv])
  refine ⟨hpq.isStarProjection_left, hqr.isStarProjection_right, w * v, hwv, ?_, ?_⟩
  · calc
      star (w * v) * (w * v) = star v * (star w * w) * v := by
        simp only [star_mul, mul_assoc]
      _ = star v * (q * v) := by rw [hwq, mul_assoc]
      _ = p := by rw [hqv, hvp]
  · calc
      (w * v) * star (w * v) = w * (v * star v) * star w := by
        simp only [star_mul, mul_assoc]
      _ = w * star w := by rw [hvq, hwq']
      _ = r := hwr

theorem subequivalent (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannSubequivalent p q :=
  ⟨h.isStarProjection_right, q, h, h.isStarProjection_right.isIdempotentElem.eq⟩

/-- Equivalence transports every subprojection, retaining its witness. -/
theorem subprojection (h : MurrayVonNeumannEquivalent p q) (hr : IsStarProjection r)
    (hrp : r * p = r) :
    ∃ s : R, MurrayVonNeumannEquivalent r s ∧ s * q = s := by
  obtain ⟨v, hv, hvp, hvq⟩ := h.exists_partial_isometry
  have hpr : p * r = r := by
    simpa only [star_mul, hr.isSelfAdjoint.star_eq,
      h.isStarProjection_left.isSelfAdjoint.star_eq] using congrArg star hrp
  have hvr : IsPartialIsometry (v * r) :=
    hr.isPartialIsometry.mul_of_initial_mul_eq v (by rw [hvp, hpr])
  have hinit : star (v * r) * (v * r) = r := by
    calc
      star (v * r) * (v * r) = r * (star v * v) * r := by
        simp only [star_mul, hr.isSelfAdjoint.star_eq, mul_assoc]
      _ = r := by rw [hvp, hrp, hr.isIdempotentElem.eq]
  have hfinal : (v * r) * star (v * r) = v * r * star v := by
    calc
      (v * r) * star (v * r) = v * (r * r) * star v := by
        simp only [star_mul, hr.isSelfAdjoint.star_eq, mul_assoc]
      _ = v * r * star v := by rw [hr.isIdempotentElem.eq]
  refine ⟨v * r * star v, ?_, ?_⟩
  · refine ⟨hr, ?_, v * r, hvr, hinit, hfinal⟩
    rw [← hfinal]
    exact hvr.isStarProjection_mul_star_self
  · calc
      (v * r * star v) * q = (v * r * star v) * (v * star v) := by rw [hvq]
      _ = v * (r * p) * star v := by rw [← hvp]; simp only [mul_assoc]
      _ = v * r * star v := by rw [hrp]

/-- If the endpoint projections lie in a corner, the same witness lies in
that corner. These absorption equations can be used to build a subtype
witness without assuming ambient equivalence reflects along an inclusion. -/
theorem exists_partial_isometry_with_absorption (h : MurrayVonNeumannEquivalent p q)
    {e : R} (he : IsStarProjection e) (hpe : p * e = p) (hqe : q * e = q) :
    ∃ v : R, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧
      e * v = v ∧ v * e = v := by
  obtain ⟨v, hv, hvp, hvq⟩ := h.exists_partial_isometry
  have heq : e * q = q := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq,
      h.isStarProjection_right.isSelfAdjoint.star_eq] using congrArg star hqe
  have hqv : q * v = v := by rw [← hvq]; exact hv.mul_star_self_mul
  have hvp' : v * p = v := by rw [← hvp]; exact hv.mul_initial
  refine ⟨v, hv, hvp, hvq, ?_, ?_⟩
  · calc
      e * v = e * (q * v) := by rw [hqv]
      _ = (e * q) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [heq, hqv]
  · calc
      v * e = (v * p) * e := by rw [hvp']
      _ = v * (p * e) := mul_assoc _ _ _
      _ = v := by rw [hpe, hvp']

theorem eq_of_commutative (h : MurrayVonNeumannEquivalent p q)
    (hcomm : ∀ a b : R, a * b = b * a) : p = q := by
  obtain ⟨v, _, hvp, hvq⟩ := h.exists_partial_isometry
  exact hvp.symm.trans ((hcomm (star v) v).trans hvq)

end Semigroup

section Maps

variable {R : Type u} {S : Type v} [Semigroup R] [StarMul R]
  [Semigroup S] [StarMul S] {F : Type*} [FunLike F R S]
  [MulHomClass F R S] [StarHomClass F R S] {p q : R}

protected theorem map (h : MurrayVonNeumannEquivalent p q) (f : F) :
    MurrayVonNeumannEquivalent (f p) (f q) := by
  obtain ⟨v, hv, hvp, hvq⟩ := h.exists_partial_isometry
  refine ⟨h.isStarProjection_left.map f, h.isStarProjection_right.map f,
    f v, hv.map f, ?_, ?_⟩
  · simpa only [map_mul, map_star] using congrArg f hvp
  · simpa only [map_mul, map_star] using congrArg f hvq

/-- Surjectivity is required for pulling back an arbitrary target witness.
Injectivity alone does not reflect equivalence in a star subalgebra. -/
theorem of_map (f : F) (hf : Function.Bijective f)
    (h : MurrayVonNeumannEquivalent (f p) (f q)) : MurrayVonNeumannEquivalent p q := by
  obtain ⟨w, hw, hwp, hwq⟩ := h.exists_partial_isometry
  obtain ⟨v, rfl⟩ := hf.2 w
  have hv : IsPartialIsometry v := IsPartialIsometry.of_map f hf.1 hw
  have hvp : star v * v = p := hf.1 (by simpa only [map_mul, map_star] using hwp)
  have hvq : v * star v = q := hf.1 (by simpa only [map_mul, map_star] using hwq)
  refine ⟨?_, ?_, v, hv, hvp, hvq⟩
  · rw [← hvp]
    exact hv.isStarProjection_star_mul_self
  · rw [← hvq]
    exact hv.isStarProjection_mul_star_self

theorem map_iff (f : F) (hf : Function.Bijective f) :
    MurrayVonNeumannEquivalent (f p) (f q) ↔ MurrayVonNeumannEquivalent p q :=
  ⟨of_map f hf, fun h => h.map f⟩

end Maps

section Zero

variable {R : Type u} [NonUnitalSemiring R] [StarRing R] {p q : R}

@[simp] protected theorem zero : MurrayVonNeumannEquivalent (0 : R) 0 :=
  .refl (IsStarProjection.zero R)

theorem eq_zero_iff (h : MurrayVonNeumannEquivalent p q) : p = 0 ↔ q = 0 := by
  obtain ⟨v, hv, hvp, hvq⟩ := h.exists_partial_isometry
  constructor
  · intro hp
    have hv0 := hv.eq_zero_of_initial_eq_zero (hvp.trans hp)
    simpa only [hv0, star_zero, zero_mul] using hvq.symm
  · intro hq
    have hv0 := hv.eq_zero_of_final_eq_zero (hvq.trans hq)
    simpa only [hv0, star_zero, zero_mul] using hvp.symm

theorem ne_zero_iff (h : MurrayVonNeumannEquivalent p q) : p ≠ 0 ↔ q ≠ 0 :=
  not_congr h.eq_zero_iff

/-- Orthogonal sums are compatible with equivalence, with orthogonality
required on both the initial and the final families. -/
protected theorem add {p' q' : R} (hp : MurrayVonNeumannEquivalent p p')
    (hq : MurrayVonNeumannEquivalent q q') (hpq : p * q = 0) (hpq' : p' * q' = 0) :
    MurrayVonNeumannEquivalent (p + q) (p' + q') := by
  obtain ⟨v, hv, hvp, hvp'⟩ := hp.exists_partial_isometry
  obtain ⟨w, hw, hwq, hwq'⟩ := hq.exists_partial_isometry
  have hi : star v * w = 0 := hv.star_mul_eq_zero_of_final_mul_final_eq_zero hw (by
    rw [hvp', hwq']; exact hpq')
  have hf : v * star w = 0 := hv.mul_star_eq_zero_of_initial_mul_initial_eq_zero hw (by
    rw [hvp, hwq]; exact hpq)
  have hi' : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hi
  have hf' : w * star v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hf
  refine ⟨hp.isStarProjection_left.add hq.isStarProjection_left hpq,
    hp.isStarProjection_right.add hq.isStarProjection_right hpq',
    v + w, hv.add hw hi hf, ?_, ?_⟩
  · simp only [star_add, add_mul, mul_add, hi, hi', add_zero, zero_add, hvp, hwq]
  · simp only [star_add, add_mul, mul_add, hf, hf', add_zero, zero_add, hvp', hwq']

open scoped BigOperators

/-- Equivalence of arbitrary finite orthogonal sums. -/
protected theorem sum {ι : Type*} (s : Finset ι) (p q : ι → R)
    (h : ∀ i ∈ s, MurrayVonNeumannEquivalent (p i) (q i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → q i * q j = 0) :
    MurrayVonNeumannEquivalent (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  classical
  revert h hp hq
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _
    simpa only [Finset.sum_empty] using (MurrayVonNeumannEquivalent.zero (R := R))
  · intro i t hit ih h hp hq
    have ht : ∀ j ∈ t, MurrayVonNeumannEquivalent (p j) (q j) :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hpt : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → p j * p k = 0 :=
      fun j hj k hk hjk => hp j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    have hqt : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → q j * q k = 0 :=
      fun j hj k hk hjk => hq j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    rw [Finset.sum_insert hit, Finset.sum_insert hit]
    apply (h i (Finset.mem_insert_self i t)).add (ih ht hpt hqt)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hp i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj)
        (by intro hij; exact hit (hij.symm ▸ hj))
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hq i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj)
        (by intro hij; exact hit (hij.symm ▸ hj))

end Zero

end MurrayVonNeumannEquivalent

namespace MurrayVonNeumannSubequivalent

section Semigroup

variable {R : Type u} [Semigroup R] [StarMul R] {p q r : R}

theorem isStarProjection_left (h : MurrayVonNeumannSubequivalent p q) :
    IsStarProjection p := by
  obtain ⟨_, s, hps, _⟩ := h
  exact hps.isStarProjection_left

theorem isStarProjection_right (h : MurrayVonNeumannSubequivalent p q) :
    IsStarProjection q := h.1

@[refl] protected theorem refl (hp : IsStarProjection p) :
    MurrayVonNeumannSubequivalent p p := (MurrayVonNeumannEquivalent.refl hp).subequivalent

theorem of_mul_eq_left (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = p) : MurrayVonNeumannSubequivalent p q :=
  ⟨hq, p, MurrayVonNeumannEquivalent.refl hp, hpq⟩

@[trans] protected theorem trans (hpq : MurrayVonNeumannSubequivalent p q)
    (hqr : MurrayVonNeumannSubequivalent q r) : MurrayVonNeumannSubequivalent p r := by
  obtain ⟨_, p', hpp', hp'q⟩ := hpq
  obtain ⟨hr, q', hqq', hq'r⟩ := hqr
  obtain ⟨s, hp's, hsq'⟩ := hqq'.subprojection hpp'.isStarProjection_right hp'q
  refine ⟨hr, s, hpp'.trans hp's, ?_⟩
  calc
    s * r = (s * q') * r := by rw [hsq']
    _ = s * (q' * r) := mul_assoc _ _ _
    _ = s := by rw [hq'r, hsq']

theorem trans_equivalent (hpq : MurrayVonNeumannSubequivalent p q)
    (hqr : MurrayVonNeumannEquivalent q r) : MurrayVonNeumannSubequivalent p r :=
  hpq.trans hqr.subequivalent

theorem equivalent_trans (hpq : MurrayVonNeumannEquivalent p q)
    (hqr : MurrayVonNeumannSubequivalent q r) : MurrayVonNeumannSubequivalent p r :=
  hpq.subequivalent.trans hqr

end Semigroup

section Maps

variable {R : Type u} {S : Type v} [Semigroup R] [StarMul R]
  [Semigroup S] [StarMul S] {F : Type*} [FunLike F R S]
  [MulHomClass F R S] [StarHomClass F R S] {p q : R}

protected theorem map (h : MurrayVonNeumannSubequivalent p q) (f : F) :
    MurrayVonNeumannSubequivalent (f p) (f q) := by
  obtain ⟨hq, r, hpr, hrq⟩ := h
  refine ⟨hq.map f, f r, hpr.map f, ?_⟩
  simpa only [map_mul] using congrArg f hrq

theorem of_map (f : F) (hf : Function.Bijective f)
    (h : MurrayVonNeumannSubequivalent (f p) (f q)) :
    MurrayVonNeumannSubequivalent p q := by
  obtain ⟨hq, s, hps, hsq⟩ := h
  obtain ⟨r, rfl⟩ := hf.2 s
  have hq' : IsStarProjection q := by
    refine ⟨?_, ?_⟩
    · apply hf.1
      simpa only [map_mul] using hq.isIdempotentElem.eq
    · apply hf.1
      simpa only [map_star] using hq.isSelfAdjoint.star_eq
  refine ⟨hq', r, MurrayVonNeumannEquivalent.of_map f hf hps, ?_⟩
  apply hf.1
  simpa only [map_mul] using hsq

theorem map_iff (f : F) (hf : Function.Bijective f) :
    MurrayVonNeumannSubequivalent (f p) (f q) ↔ MurrayVonNeumannSubequivalent p q :=
  ⟨of_map f hf, fun h => h.map f⟩

end Maps

section Zero

variable {R : Type u} [NonUnitalSemiring R] [StarRing R] {p q : R}

theorem zero_left (hq : IsStarProjection q) : MurrayVonNeumannSubequivalent (0 : R) q :=
  ⟨hq, 0, MurrayVonNeumannEquivalent.zero, zero_mul q⟩

theorem eq_zero_of_right_eq_zero (h : MurrayVonNeumannSubequivalent p q)
    (hq : q = 0) : p = 0 := by
  obtain ⟨_, r, hpr, hrq⟩ := h
  have hr : r = 0 := by simpa only [hq, mul_zero] using hrq.symm
  exact hpr.eq_zero_iff.mpr hr

end Zero

end MurrayVonNeumannSubequivalent

/-- In proper-star rings the additional algebraic partial-isometry clause
can be omitted. This includes C-star algebras with their existing instance. -/
theorem murrayVonNeumannEquivalent_iff_exists
    {R : Type u} [NonUnitalRing R] [StarRing R] [IsProperStar R] {p q : R} :
    MurrayVonNeumannEquivalent p q ↔
      IsStarProjection p ∧ IsStarProjection q ∧ ∃ v : R, star v * v = p ∧ v * star v = q := by
  constructor
  · rintro ⟨hp, hq, v, _, hvp, hvq⟩
    exact ⟨hp, hq, v, hvp, hvq⟩
  · rintro ⟨hp, hq, v, hvp, hvq⟩
    refine ⟨hp, hq, v, ?_, hvp, hvq⟩
    apply IsPartialIsometry.of_isStarProjection_star_mul_self
    rw [hvp]
    exact hp
