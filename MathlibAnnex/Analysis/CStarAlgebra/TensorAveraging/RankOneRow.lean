import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.ExactRow

/-!
# Exact finite row on the span of a fixed vector

This specializes the projection result to a genuine nonzero rank-one
projection. The Ω input remains explicit; this is an interface check, not
an existence proof for Ω.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.FiniteApproximation

universe uA uH

theorem exists_finiteRow_exact_on_unit_vector
    (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (ρ : NonUnitalCStarRepresentation A H) (hρ : ρ.IsIrreducible)
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ v : H, omega (vectorMoment A H ρ v) = (‖v‖ ^ 2 : ℂ))
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (y : Fin n → A),
      0 ≤ rowSquare A y ∧ ‖rowSquare A y‖ ≤ 1 ∧
      ρ (rowSquare A y) ξ = ξ ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * rowMap A y z - rowMap A y z * a‖ ≤ ε * ‖z‖ := by
  let U : Submodule ℂ H := ℂ ∙ ξ
  letI : FiniteDimensional ℂ U :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton ξ)
  let P : H →L[ℂ] H := U.starProjection
  haveI : FiniteDimensional ℂ P.range := by
    rw [show P.range = U from Submodule.range_starProjection U]
    infer_instance
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hPξ : P ξ = ξ :=
    U.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self ξ)
  obtain ⟨n, y, hpos, hnorm, hfixed, hcomm⟩ :=
    exists_finiteRow_exact_on_projection A H ρ hρ omega homega hcentral
      hmoment F P hP hε
  refine ⟨n, y, hpos, hnorm, ?_, hcomm⟩
  have h := congrArg (fun T : H →L[ℂ] H => T ξ) hfixed
  simpa [P, ContinuousLinearMap.mul_apply, hPξ] using h

/-- The same rank-one row interface for an ordinary unital representation.
The Ω data is still a hypothesis, not a supplied mean. -/
theorem exists_finiteRow_exact_on_unital_vector
    (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ v : H,
      omega (vectorMoment A H pi.toNonUnitalStarAlgHom v) = (‖v‖ ^ 2 : ℂ))
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (y : Fin n → A),
      0 ≤ rowSquare A y ∧ ‖rowSquare A y‖ ≤ 1 ∧
      pi (rowSquare A y) ξ = ξ ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * rowMap A y z - rowMap A y z * a‖ ≤ ε * ‖z‖ := by
  let ρ : NonUnitalCStarRepresentation A H := pi.toNonUnitalStarAlgHom
  have hρ : ρ.IsIrreducible := ⟨hpi.1, hpi.2⟩
  exact exists_finiteRow_exact_on_unit_vector A H ρ hρ omega homega
    hcentral hmoment ξ hξ F hε

end MathlibAnnex.CStarAlgebra.TensorAveraging
