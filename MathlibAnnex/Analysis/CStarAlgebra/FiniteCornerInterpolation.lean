import MathlibAnnex.Analysis.CStarAlgebra.TwoSidedInterpolation

/-!
# Simultaneous sharp interpolation on both sides of a finite corner

The *same* source witness controls the right and left finite-projection
compressions of a general operator.  This is the form needed when a source
witness must carry both support identities through a later construction.
-/
set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Both multiplication identities hold for one sharp-norm algebra element. -/
theorem exists_norm_le_and_both_finiteCorner
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      pi a * E.starProjection = T * E.starProjection ∧
      E.starProjection * pi a = E.starProjection * T := by
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_on pi hpi E T
  have hright : pi a * E.starProjection = T * E.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact hf (E.starProjection x) (E.starProjection_apply_mem x)
  have hstarRight : pi (star a) * E.starProjection =
      star T * E.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    exact hs (E.starProjection x) (E.starProjection_apply_mem x)
  have hqstar : star E.starProjection = E.starProjection := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact E.starProjection_isSymmetric.clm_adjoint_eq
  have hleft := congrArg star hstarRight
  simp only [star_mul, hqstar, map_star, star_star] at hleft
  exact ⟨a, ha, hright, hleft⟩

/-- A finite-dimensional supported target is matched on both sides with the
original norm; no support equality of the source element itself is asserted. -/
theorem exists_norm_le_and_supported_target
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H)
    (hr : T * E.starProjection = T) (hl : E.starProjection * T = T) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧
      pi a * E.starProjection = T ∧ E.starProjection * pi a = T := by
  obtain ⟨a, ha, har, hal⟩ := exists_norm_le_and_both_finiteCorner pi hpi E T
  exact ⟨a, ha, har.trans hr, hal.trans hl⟩

end MathlibAnnex.Analysis.CStarAlgebra
