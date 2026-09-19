import MathlibAnnex.Analysis.CStarAlgebra.CompactModel
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.MinimalProjection
import MathlibAnnex.Analysis.InnerProductSpace.RankOne

/-!
# Scalar corners act as rank-one projections

In an irreducible representation, a nonzero projection whose algebraic corner
is one-dimensional is represented by a rank-one orthogonal projection.  The
argument uses only density of the orbit of a nonzero vector in the range of the
projection and closedness of a one-dimensional subspace.
-/

set_option autoImplicit false

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- A nonzero scalar corner is represented by a rank-one projection in an
irreducible representation. -/
theorem exists_unitVector_map_eq_rankOne_of_scalar_corner
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    {p : A} (hp : IsStarProjection p) (hpmap : pi p ≠ 0)
    (hcorner : ∀ a : A, ∃ c : ℂ, p * a * p = c • p) :
    ∃ e : H, ‖e‖ = 1 ∧
      pi p = InnerProductSpace.rankOne ℂ e e := by
  classical
  let P : H →L[ℂ] H := pi p
  have hPstar : IsStarProjection P := hp.map pi
  obtain ⟨xi, hxi⟩ : ∃ xi : H, P xi ≠ 0 := by
    by_contra h
    push_neg at h
    apply hpmap
    apply ContinuousLinearMap.ext
    intro x
    simpa [P] using h x
  let v : H := P xi
  have hv : v ≠ 0 := hxi
  have horbit : DenseRange (StarAlgHom.orbitMap pi v) :=
    denseRange_orbitMap_of_isIrreducible pi hirr hv
  have hPrange : P.range = ℂ ∙ v := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x ∈ closure (Set.range (StarAlgHom.orbitMap pi v)) := by
        rw [horbit.closure_range]
        trivial
      apply (Set.MapsTo.closure_left (f := P)
        (s := Set.range (StarAlgHom.orbitMap pi v))
        (t := (ℂ ∙ v : Submodule ℂ H)) ?_
        P.continuous (Submodule.closed_of_finiteDimensional (ℂ ∙ v))) hx
      rintro _ ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := hcorner a
      have hcalc : P (pi a v) = c • v := by
        calc
          P (pi a v) = (P * pi a * P) xi := rfl
          _ = pi (p * a * p) xi := by simp [P]
          _ = pi (c • p) xi := by rw [hc]
          _ = c • v := by simp [P, v]
      change P (pi a v) ∈ (ℂ ∙ v : Submodule ℂ H)
      rw [hcalc]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨xi, rfl⟩
  let e : H := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he : ‖e‖ = 1 := by
    simp [e, norm_smul, hvnorm]
  have hspan : ℂ ∙ v = ℂ ∙ e := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Submodule.mem_span_singleton.mpr
      refine ⟨((‖v‖ : ℝ) : ℂ), ?_⟩
      simp [e, hvnorm]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  letI : P.range.HasOrthogonalProjection :=
    Classical.choose (isStarProjection_iff_eq_starProjection_range.mp hPstar)
  have hPeq : P = P.range.starProjection :=
    Classical.choose_spec (isStarProjection_iff_eq_starProjection_range.mp hPstar)
  refine ⟨e, he, ?_⟩
  change P = InnerProductSpace.rankOne ℂ e e
  calc
    P = P.range.starProjection := hPeq
    _ = InnerProductSpace.rankOne ℂ e e :=
      MathlibAnnex.Analysis.InnerProductSpace.starProjection_eq_rankOne_of_eq_span
        P.range e he (hPrange.trans hspan)

/-- A nonzero scalar corner has compact image in an irreducible
representation. -/
theorem isCompactOperator_map_of_scalar_corner
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    {p : A} (hp : IsStarProjection p) (hpmap : pi p ≠ 0)
    (hcorner : ∀ a : A, ∃ c : ℂ, p * a * p = c • p) :
    IsCompactOperator (pi p) := by
  obtain ⟨e, _he, hmap⟩ :=
    exists_unitVector_map_eq_rankOne_of_scalar_corner pi hirr hp hpmap hcorner
  rw [hmap]
  exact isCompactOperator_rankOne e e

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
