import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Finite
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1

set_option autoImplicit false

universe u v

section Algebra

variable {R : Type u} [Ring R] [StarRing R]

example : IsFiniteProjection (0 : R) := IsFiniteProjection.zero

example {p q : R} (hp : IsFiniteProjection p) (hq : IsStarProjection q)
    (hqp : q * p = q) :
    ∀ r : R, IsStarProjection r →
      (∃ v : R, v * star v * v = v ∧ star v * v = q ∧ v * star v = r) →
      r * q = r → r = q := by
  intro r hr hvr hrq
  exact (hp.of_mul_eq_left hq hqp).2 r ⟨hq, hr, hvr⟩ hrq

example {p : R} (hp : IsProperlyInfiniteProjection p) :
    p ≠ 0 ∧ ¬ IsFiniteProjection p := ⟨hp.ne_zero, hp.not_isFiniteProjection⟩

end Algebra

section Maps

variable {R : Type u} {S : Type v} [NonUnitalRing R] [StarRing R]
  [NonUnitalRing S] [StarRing S]

/-- An injective map reflects finiteness without any surjectivity premise. -/
example {F : Type*} [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S]
    (f : F) (hf : Function.Injective f) {p : R} (hp : IsFiniteProjection (f p)) :
    IsFiniteProjection p :=
  IsFiniteProjection.of_map f hf hp

/-- Preservation uses an actual equivalence, with both directions available. -/
example (e : R ≃⋆+* S) (p : R) :
    IsFiniteProjection (e p) ↔ IsFiniteProjection p :=
  IsFiniteProjection.map_iff e (EquivLike.bijective e)

end Maps

section Concrete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The witness in the expanded consumer belongs to the same algebra. -/
example (M : VonNeumannAlgebra H) (hM : M.IsFinite)
    (p q : M.toStarSubalgebra) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hvi : star v * v = p) (hvf : v * star v = q)
    (hqp : q * p = q) : q = p := by
  apply (hM.isFiniteProjection hp).eq_of_equivalent_of_mul_eq _ hqp
  exact murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp, hq, v, hvi, hvf⟩

/-- The accepted factor-only II₁ predicate supplies algebra finiteness
without being redefined as a general type-II predicate. -/
example (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : IsFiniteProjection p :=
  hM.2.1.isFiniteProjection hp

example (M : VonNeumannAlgebra H) :
    (∀ v : H →L[ℂ] H, v ∈ M → star v * v = 1 → v * star v = 1) ↔
      IsFiniteProjection (1 : M.toStarSubalgebra) :=
  VonNeumannAlgebra.isFinite_iff_isFiniteProjection_one M

/-- The corner unit is the projection itself, as an actual corner element. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) :
    IsFiniteProjection
      (⟨p, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq⟩ :
        VonNeumannAlgebra.corner M p hp) ↔ IsFiniteProjection p :=
  VonNeumannAlgebra.isFiniteProjection_cornerUnit_iff M p hp

/-- An internal partial-isometry witness transfers finiteness, with the
initial finite projection and the final projection both explicitly typed. -/
example (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hp : IsFiniteProjection p) (hq : IsStarProjection q)
    (v : M.toStarSubalgebra) (hvi : star v * v = p) (hvf : v * star v = q) :
    IsFiniteProjection q := by
  apply VonNeumannAlgebra.isFiniteProjection_of_equivalent M hp
  exact murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp.1, hq, v, hvi, hvf⟩

/-- The transported conclusion rules out a proper equivalent subprojection;
both witnesses belong to `M`, and no ambient operator witness is used. -/
example (M : VonNeumannAlgebra H) {p q r : M.toStarSubalgebra}
    (hp : IsFiniteProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (v w : M.toStarSubalgebra)
    (hvi : star v * v = p) (hvf : v * star v = q)
    (hwi : star w * w = q) (hwf : w * star w = r) (hrq : r * q = r) : r = q := by
  have hpq : MurrayVonNeumannEquivalent p q :=
    murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp.1, hq, v, hvi, hvf⟩
  have hqr : MurrayVonNeumannEquivalent q r :=
    murrayVonNeumannEquivalent_iff_exists.mpr ⟨hq, hr, w, hwi, hwf⟩
  exact (VonNeumannAlgebra.isFiniteProjection_of_equivalent M hp hpq).2 r hqr hrq

end Concrete
