import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.MinimalProjection
import MathlibAnnex.Analysis.CStarAlgebra.Representation.RankOneProjection

/-!
# Rank-one images of non-unital minimal projections
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A scalar corner in a non-unital algebra remains a scalar corner after
passing to the minimal unitization. -/
theorem scalar_corner_unitization {p : A} (hp : IsStarProjection p)
    (hcorner : ∀ a : A, ∃ c : ℂ, p * a * p = c • p) :
    ∀ z : Unitization ℂ A, ∃ c : ℂ,
      (p : Unitization ℂ A) * z * (p : Unitization ℂ A) =
        c • (p : Unitization ℂ A) := by
  intro z
  induction z using Unitization.ind with
  | inl_add_inr c a =>
      obtain ⟨d, hd⟩ := hcorner a
      refine ⟨c + d, ?_⟩
      calc
        (p : Unitization ℂ A) *
              (Unitization.inl c + (a : Unitization ℂ A)) *
              (p : Unitization ℂ A) =
            (((c • p) * p : A) : Unitization ℂ A) +
              ((p * a * p : A) : Unitization ℂ A) := by
          rw [mul_add, add_mul, Unitization.inr_mul_inl]
          simp only [← Unitization.inr_mul]
        _ = ((c • p + d • p : A) : Unitization ℂ A) := by
          rw [smul_mul_assoc, hp.isIdempotentElem.eq, hd]
          exact (Unitization.inr_add ℂ (c • p) (d • p)).symm
        _ = (((c + d) • p : A) : Unitization ℂ A) := by rw [add_smul]
        _ = (c + d) • (p : Unitization ℂ A) := Unitization.inr_smul ℂ (c + d) p

/-- A nonzero scalar corner is represented by a rank-one projection in an
irreducible non-unital representation. -/
theorem exists_unitVector_map_eq_rankOne_of_scalar_corner
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    {p : A} (hp : IsStarProjection p) (hpmap : pi p ≠ 0)
    (hcorner : ∀ a : A, ∃ c : ℂ, p * a * p = c • p) :
    ∃ e : H, ‖e‖ = 1 ∧
      pi p = InnerProductSpace.rankOne ℂ e e := by
  have hirrU := isIrreducible_unitization pi hirr
  have hpU : IsStarProjection (p : Unitization ℂ A) := hp.inr
  have hpmapU : pi.unitization (p : Unitization ℂ A) ≠ 0 := by
    simpa using hpmap
  obtain ⟨e, he, hmap⟩ :=
    Representation.exists_unitVector_map_eq_rankOne_of_scalar_corner
      pi.unitization hirrU hpU hpmapU
        (scalar_corner_unitization hp hcorner)
  exact ⟨e, he, by simpa using hmap⟩

/-- A nonzero scalar corner has compact image in an irreducible non-unital
representation. -/
theorem isCompactOperator_map_of_scalar_corner
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    {p : A} (hp : IsStarProjection p) (hpmap : pi p ≠ 0)
    (hcorner : ∀ a : A, ∃ c : ℂ, p * a * p = c • p) :
    IsCompactOperator (pi p) := by
  obtain ⟨e, _he, hmap⟩ :=
    exists_unitVector_map_eq_rankOne_of_scalar_corner pi hirr hp hpmap hcorner
  rw [hmap]
  exact isCompactOperator_rankOne e e

/-- A separable singleton model contains a nonzero minimal projection whose
represented image is rank one and compact. -/
theorem exists_nonzero_projection_rankOne_map [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      (∃ e : H, ‖e‖ = 1 ∧ pi p = InnerProductSpace.rankOne ℂ e e) ∧
      IsCompactOperator (pi p) := by
  obtain ⟨p, hp, hpne, hcorner⟩ :=
    exists_nonzero_projection_scalar_corner pi hsingle
  have hpinj := injective_of_singleton pi hsingle
  have hpmap : pi p ≠ 0 := by
    intro hzero
    apply hpne
    apply hpinj
    simpa using hzero
  obtain ⟨e, he, hmap⟩ :=
    exists_unitVector_map_eq_rankOne_of_scalar_corner
      pi hsingle.1 hp hpmap hcorner
  refine ⟨p, hp, hpne, ⟨e, he, hmap⟩, ?_⟩
  rw [hmap]
  exact isCompactOperator_rankOne e e

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
