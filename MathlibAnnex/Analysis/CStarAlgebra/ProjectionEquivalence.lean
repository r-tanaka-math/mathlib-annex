/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Algebra.Star.ProjectionEquivalence
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic.Linarith

/-!
# C-star algebra interpretations of projection equivalence

The witness remains in the specified carrier. The algebraic absorption
relation is identified with the existing C-star order; partial isometries
are contractions by the C-star identity and the existing projection bound.
-/

set_option autoImplicit false

universe u

namespace IsPartialIsometry

variable {A : Type u} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] {v : A}

theorem norm_le_one (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have h : ‖v‖ * ‖v‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self]
    exact IsStarProjection.norm_le _ hv.isStarProjection_star_mul_self
  nlinarith [norm_nonneg v]

end IsPartialIsometry

section Ordered

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {p q : A}

/-- The order-free absorption equation in the core is exactly projection
order in a C-star algebra. -/
theorem murrayVonNeumannSubequivalent_iff_exists_le :
    MurrayVonNeumannSubequivalent p q ↔
      IsStarProjection q ∧ ∃ r : A, MurrayVonNeumannEquivalent p r ∧ r ≤ q := by
  constructor
  · rintro ⟨hq, r, hpr, hrq⟩
    exact ⟨hq, r, hpr, (hpr.isStarProjection_right.le_iff_mul_eq_left hq).2 hrq⟩
  · rintro ⟨hq, r, hpr, hrq⟩
    exact ⟨hq, r, hpr, (hpr.isStarProjection_right.le_iff_mul_eq_left hq).1 hrq⟩

theorem MurrayVonNeumannSubequivalent.of_le (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) : MurrayVonNeumannSubequivalent p q :=
  ⟨hq, p, MurrayVonNeumannEquivalent.refl hp, (hp.le_iff_mul_eq_left hq).1 hpq⟩

theorem MurrayVonNeumannSubequivalent.exists_le
    (h : MurrayVonNeumannSubequivalent p q) :
    ∃ r : A, MurrayVonNeumannEquivalent p r ∧ r ≤ q :=
  (murrayVonNeumannSubequivalent_iff_exists_le.mp h).2

end Ordered
