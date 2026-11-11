import MathlibAnnex.Analysis.CStarAlgebra.ProjectionEquivalence

/-! Typed consumers of the actual algebraic and ordered statements. -/

set_option autoImplicit false

open scoped BigOperators

section Algebra

variable {R : Type*} [NonUnitalRing R] [StarRing R] {p q r : R}

example (hpq : MurrayVonNeumannEquivalent p q) (hqr : MurrayVonNeumannEquivalent q r) :
    ∃ v : R, v * star v * v = v ∧ star v * v = p ∧ v * star v = r := by
  obtain ⟨v, hv, hvi, hvf⟩ := (hpq.trans hqr).exists_partial_isometry
  exact ⟨v, hv.mul_star_self_mul, hvi, hvf⟩

example (h : MurrayVonNeumannEquivalent (p := p) (q := q)) : p = 0 ↔ q = 0 :=
  h.eq_zero_iff

example (hpq : MurrayVonNeumannSubequivalent p q)
    (hqr : MurrayVonNeumannSubequivalent q r) :
    IsStarProjection r ∧ ∃ s : R, MurrayVonNeumannEquivalent p s ∧ s * r = s :=
  hpq.trans hqr

example {e : R} (h : MurrayVonNeumannEquivalent p q) (he : IsStarProjection e)
    (hpe : p * e = p) (hqe : q * e = q) :
    ∃ v : R, v * star v * v = v ∧ star v * v = p ∧ v * star v = q ∧
      e * v = v ∧ v * e = v := by
  obtain ⟨v, hv, hvi, hvf, hev, hve⟩ :=
    h.exists_partial_isometry_with_absorption (e := e) he hpe hqe
  exact ⟨v, hv.mul_star_self_mul, hvi, hvf, hev, hve⟩

example {ι : Type*} (s : Finset ι) (v : ι → R)
    (hv : ∀ i ∈ s, IsPartialIsometry (v i))
    (hi : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (v i) * v j = 0)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i * star (v j) = 0) :
    (∑ i ∈ s, v i) * star (∑ i ∈ s, v i) * (∑ i ∈ s, v i) = ∑ i ∈ s, v i :=
  (IsPartialIsometry.sum (s := s) (v := v) hv hi hf).mul_star_self_mul

end Algebra

section ProperStar

variable {R : Type*} [NonUnitalRing R] [StarRing R] [IsProperStar R] {p q : R}

example (hp : IsStarProjection p) (hq : IsStarProjection q) (v : R)
    (hi : star v * v = p) (hf : v * star v = q) :
    MurrayVonNeumannEquivalent p q :=
  murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp, hq, v, hi, hf⟩

end ProperStar

section Unital

variable {R : Type*} [Ring R] [StarRing R]

example (v : R) (h : star v * v = 1) :
    MurrayVonNeumannEquivalent (1 : R) (v * star v) := by
  have hv := IsPartialIsometry.of_star_mul_self_eq_one h
  simpa only [h] using MurrayVonNeumannEquivalent.of_partial_isometry hv

end Unital

section CStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

example {p q : A} (h : MurrayVonNeumannSubequivalent p q) :
    ∃ r : A, IsStarProjection r ∧ r ≤ q ∧
      ∃ v : A, star v * v = p ∧ v * star v = r := by
  obtain ⟨r, hpr, hrq⟩ := h.exists_le
  obtain ⟨v, _, hvp, hvr⟩ := hpr.exists_partial_isometry
  exact ⟨r, hpr.isStarProjection_right, hrq, v, hvp, hvr⟩

example {ι : Type*} (s : Finset ι) (v : ι → A)
    (hv : ∀ i ∈ s, IsPartialIsometry (v i))
    (hi : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (v i) * v j = 0)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i * star (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ≤ 1 :=
  (IsPartialIsometry.sum s v hv hi hf).norm_le_one

end CStar

section Subalgebra

variable {A : Type*} [CStarAlgebra A]

/-- The witness in this consumer is a subtype element, with its membership
proof available; the ambient witness alone would not inhabit this type. -/
example (S : StarSubalgebra ℂ A) {p q : S} (h : MurrayVonNeumannEquivalent p q) :
    ∃ v : S, (v : A) ∈ S ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨v, _, hvp, hvq⟩ := h.exists_partial_isometry
  exact ⟨v, v.property, hvp, hvq⟩

example (S : StarSubalgebra ℂ A) {p q : S} (h : MurrayVonNeumannEquivalent p q) :
    MurrayVonNeumannEquivalent (p : A) (q : A) :=
  h.map S.subtype

end Subalgebra
