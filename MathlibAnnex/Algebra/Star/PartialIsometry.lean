/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Algebraic partial isometries

A partial isometry satisfies `v * star v * v = v`. The algebraic results do
not require a norm or a unit. The converse from a projected star-square
requires the existing `IsProperStar` assumption; it is not valid in an
arbitrary star ring. No alternative projection predicate is introduced.
-/

set_option autoImplicit false

universe u v

/-- The algebraic partial-isometry identity. -/
def IsPartialIsometry {R : Type u} [Mul R] [Star R] (v : R) : Prop :=
  v * star v * v = v

namespace IsPartialIsometry

section Semigroup

variable {R : Type u} [Semigroup R] [StarMul R] {v w : R}

theorem mul_star_self_mul (hv : IsPartialIsometry v) : v * star v * v = v := hv

theorem mul_initial (hv : IsPartialIsometry v) : v * (star v * v) = v := by
  simpa only [mul_assoc] using hv.mul_star_self_mul

protected theorem star (hv : IsPartialIsometry v) : IsPartialIsometry (star v) := by
  have h := congrArg star hv.mul_star_self_mul
  simpa only [IsPartialIsometry, star_mul, star_star, mul_assoc] using h

theorem initial_mul_star (hv : IsPartialIsometry v) : (star v * v) * star v = star v := by
  simpa only [star_star] using hv.star.mul_star_self_mul

theorem star_mul_final (hv : IsPartialIsometry v) : star v * (v * star v) = star v := by
  simpa only [mul_assoc] using hv.initial_mul_star

theorem isStarProjection_star_mul_self (hv : IsPartialIsometry v) :
    IsStarProjection (star v * v) := by
  refine ⟨?_, IsSelfAdjoint.star_mul_self v⟩
  change (star v * v) * (star v * v) = star v * v
  calc
    (star v * v) * (star v * v) = star v * (v * star v * v) := by
      simp only [mul_assoc]
    _ = star v * v := by rw [hv.mul_star_self_mul]

theorem isStarProjection_mul_star_self (hv : IsPartialIsometry v) :
    IsStarProjection (v * star v) := by
  simpa only [star_star] using hv.star.isStarProjection_star_mul_self

/-- Left multiplication preserves the partial-isometry identity when its
initial star-square acts as the identity on the given element. -/
theorem mul_of_initial_mul_eq (hv : IsPartialIsometry v) (w : R)
    (hwv : star w * w * v = v) : IsPartialIsometry (w * v) := by
  change (w * v) * star (w * v) * (w * v) = w * v
  calc
    (w * v) * star (w * v) * (w * v) =
        w * (v * star v * (star w * w * v)) := by
      simp only [star_mul, mul_assoc]
    _ = w * (v * star v * v) := by rw [hwv]
    _ = w * v := by rw [hv.mul_star_self_mul]

theorem _root_.IsStarProjection.isPartialIsometry {p : R} (hp : IsStarProjection p) :
    IsPartialIsometry p := by
  change p * star p * p = p
  rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]

end Semigroup

section Maps

variable {R : Type u} {S : Type v} [Mul R] [Star R] [Mul S] [Star S]
  {F : Type*} [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S] {v : R}

protected theorem map (hv : IsPartialIsometry v) (f : F) : IsPartialIsometry (f v) := by
  change f v * star (f v) * f v = f v
  simpa only [map_mul, map_star] using congrArg f hv

theorem of_map (f : F) (hf : Function.Injective f) (hv : IsPartialIsometry (f v)) :
    IsPartialIsometry v := by
  apply hf
  simpa only [IsPartialIsometry, map_mul, map_star] using hv

theorem map_iff (f : F) (hf : Function.Injective f) :
    IsPartialIsometry (f v) ↔ IsPartialIsometry v :=
  ⟨of_map f hf, fun hv => hv.map f⟩

end Maps

section Zero

variable {R : Type u} [NonUnitalSemiring R] [StarRing R] {v : R}

@[simp] protected theorem zero : IsPartialIsometry (0 : R) := by
  simp only [IsPartialIsometry, star_zero, zero_mul]

theorem eq_zero_of_initial_eq_zero (hv : IsPartialIsometry v)
    (h : star v * v = 0) : v = 0 := by
  calc
    v = v * (star v * v) := hv.mul_initial.symm
    _ = 0 := by rw [h, mul_zero]

theorem eq_zero_of_final_eq_zero (hv : IsPartialIsometry v)
    (h : v * star v = 0) : v = 0 := by
  calc
    v = (v * star v) * v := hv.mul_star_self_mul.symm
    _ = 0 := by rw [h, zero_mul]

/-- Orthogonality of the final projections annihilates the corresponding
initial cross-product. -/
theorem star_mul_eq_zero_of_final_mul_final_eq_zero {w : R}
    (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : (v * star v) * (w * star w) = 0) : star v * w = 0 := by
  calc
    star v * w = (star v * (v * star v)) * ((w * star w) * w) := by
      rw [hv.star_mul_final, hw.mul_star_self_mul]
    _ = star v * ((v * star v) * (w * star w)) * w := by
      simp only [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

/-- Orthogonality of the initial projections annihilates the corresponding
final cross-product. -/
theorem mul_star_eq_zero_of_initial_mul_initial_eq_zero {w : R}
    (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : (star v * v) * (star w * w) = 0) : v * star w = 0 := by
  calc
    v * star w = (v * (star v * v)) * ((star w * w) * star w) := by
      rw [hv.mul_initial, hw.initial_mul_star]
    _ = v * ((star v * v) * (star w * w)) * star w := by
      simp only [mul_assoc]
    _ = 0 := by rw [h, mul_zero, zero_mul]

/-- Both cross-products must vanish. Orthogonality of only the initial or
only the final projections does not suffice. -/
protected theorem add {w : R} (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (hinitial : star v * w = 0) (hfinal : v * star w = 0) :
    IsPartialIsometry (v + w) := by
  have hinitial' : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hinitial
  have hfinal' : w * star v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hfinal
  change (v + w) * star (v + w) * (v + w) = v + w
  calc
    (v + w) * star (v + w) * (v + w) =
        (v * star v + w * star w) * (v + w) := by
      simp only [star_add, add_mul, mul_add, hfinal, hfinal', add_zero, zero_add]
    _ = v * star v * v + w * star w * w := by
      simp only [add_mul, mul_add, mul_assoc, hinitial, hinitial',
        mul_zero, add_zero, zero_add]
    _ = v + w := by rw [hv.mul_star_self_mul, hw.mul_star_self_mul]

open scoped BigOperators

/-- The initial star-square of a finite orthogonal sum. -/
theorem star_sum_mul_sum {ι : Type*} (s : Finset ι) (v : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (v i) * v j = 0) :
    star (∑ i ∈ s, v i) * (∑ i ∈ s, v i) = ∑ i ∈ s, star (v i) * v i := by
  classical
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  exact Finset.sum_eq_single i
    (fun j hj hji => h i hi j hj hji.symm)
    (fun hnot => (hnot hi).elim)

/-- The final star-square of a finite orthogonal sum. -/
theorem sum_mul_star_sum {ι : Type*} (s : Finset ι) (v : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i * star (v j) = 0) :
    (∑ i ∈ s, v i) * star (∑ i ∈ s, v i) = ∑ i ∈ s, v i * star (v i) := by
  simpa only [star_star, star_sum] using
    star_sum_mul_sum s (fun i => star (v i)) (by simpa only [star_star] using h)

/-- An arbitrary finite subfamily can be summed; the indexing type need
not be countable. -/
protected theorem sum {ι : Type*} (s : Finset ι) (v : ι → R)
    (hv : ∀ i ∈ s, IsPartialIsometry (v i))
    (hinitial : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (v i) * v j = 0)
    (hfinal : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i * star (v j) = 0) :
    IsPartialIsometry (∑ i ∈ s, v i) := by
  classical
  revert hv hinitial hfinal
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _
    simpa only [Finset.sum_empty] using (IsPartialIsometry.zero (R := R))
  · intro i t hit ih hv hi hf
    have hvt : ∀ j ∈ t, IsPartialIsometry (v j) := fun j hj =>
      hv j (Finset.mem_insert_of_mem hj)
    have hit' : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → star (v j) * v k = 0 :=
      fun j hj k hk hjk => hi j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    have hft : ∀ j ∈ t, ∀ k ∈ t, j ≠ k → v j * star (v k) = 0 :=
      fun j hj k hk hjk => hf j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    rw [Finset.sum_insert hit]
    apply (hv i (Finset.mem_insert_self i t)).add (ih hvt hit' hft)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hi i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj)
        (by intro hij; exact hit (hij.symm ▸ hj))
    · rw [star_sum, Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact hf i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj)
        (by intro hij; exact hit (hij.symm ▸ hj))

end Zero

section One

variable {R : Type u} [Monoid R] [StarMul R] {v : R}

@[simp] protected theorem one : IsPartialIsometry (1 : R) := by
  simp only [IsPartialIsometry, star_one, one_mul]

theorem of_star_mul_self_eq_one (h : star v * v = 1) : IsPartialIsometry v := by
  change v * star v * v = v
  rw [mul_assoc, h, mul_one]

theorem of_mul_star_self_eq_one (h : v * star v = 1) : IsPartialIsometry v := by
  change v * star v * v = v
  rw [h, one_mul]

end One

section ProperStar

variable {R : Type u} [NonUnitalRing R] [StarRing R] [IsProperStar R] {v : R}

/-- In a ring with proper star, an idempotent initial star-square already
forces the partial-isometry identity. -/
theorem of_isIdempotentElem_star_mul_self (h : IsIdempotentElem (star v * v)) :
    IsPartialIsometry v := by
  let p : R := star v * v
  have hp : p * p = p := h
  let d : R := v * p - v
  have hd : star d * d = 0 := by
    calc
      star d * d = (p * p * p - p * p) - (p * p - p) := by
        dsimp [d, p]
        simp only [star_sub, star_mul, star_star, sub_mul, mul_sub, mul_assoc]
      _ = 0 := by simp only [hp, sub_self]
  have hd0 : d = 0 := star_mul_self_eq_zero.mp hd
  change v * star v * v = v
  simpa only [d, p, mul_assoc] using sub_eq_zero.mp hd0

theorem of_isStarProjection_star_mul_self
    (h : IsStarProjection (star v * v)) : IsPartialIsometry v :=
  of_isIdempotentElem_star_mul_self h.isIdempotentElem

end ProperStar

end IsPartialIsometry

theorem isPartialIsometry_iff_isStarProjection_star_mul_self
    {R : Type u} [NonUnitalRing R] [StarRing R] [IsProperStar R] {v : R} :
    IsPartialIsometry v ↔ IsStarProjection (star v * v) :=
  ⟨IsPartialIsometry.isStarProjection_star_mul_self,
    IsPartialIsometry.of_isStarProjection_star_mul_self⟩

theorem isPartialIsometry_iff_isStarProjection_mul_star_self
    {R : Type u} [NonUnitalRing R] [StarRing R] [IsProperStar R] {v : R} :
    IsPartialIsometry v ↔ IsStarProjection (v * star v) := by
  constructor
  · exact IsPartialIsometry.isStarProjection_mul_star_self
  · intro h
    have hstar : IsPartialIsometry (star v) :=
      IsPartialIsometry.of_isStarProjection_star_mul_self
        (by simpa only [star_star] using h)
    simpa only [star_star] using hstar.star
