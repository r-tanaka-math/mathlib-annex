import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRankBridge

/-!
# The tensor row bridge for a finite-rank orthogonal projection

The projection need not come from a projection in the represented algebra.
-/

set_option autoImplicit false

open scoped CStarAlgebra InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.FiniteApproximation

universe uA uH

variable (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_finiteRow_approximate_on_projection
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ ξ : H, omega (vectorMoment A H ρ ξ) = (‖ξ‖ ^ 2 : ℂ))
    (F : Finset A) (P : H →L[ℂ] H) (hP : IsStarProjection P)
    [FiniteDimensional ℂ P.range]
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ (n : ℕ) (y : Fin n → A),
      (∑ i, ‖y i‖ ^ 2 ≤ 1) ∧
      0 ≤ rowSquare A y ∧ ‖rowSquare A y‖ ≤ 1 ∧
      ‖(ρ (rowSquare A y)).comp P - P‖ < τ ∧
      ∀ a ∈ F, ∀ b : A,
        ‖a * rowMap A y b - rowMap A y b * a‖ ≤ ε * ‖b‖ := by
  obtain ⟨hU, hPU⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  letI := hU
  obtain ⟨n, y, hbudget, hpositive, hnorm, happrox, hcomm⟩ :=
    exists_finiteRow_approximate_on_subspace A H ρ omega homega hcentral
      hmoment F P.range hε hτ
  refine ⟨n, y, hbudget, hpositive, hnorm, ?_, hcomm⟩
  simpa only [← hPU] using happrox

end MathlibAnnex.CStarAlgebra.TensorAveraging
