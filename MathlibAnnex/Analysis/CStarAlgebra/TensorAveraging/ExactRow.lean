import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.ProjectionBridge
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.RowPerturbation
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.ProjectionNormalization

/-!
# Finite rows exactly normalized on an arbitrary Hilbert projection

The approximate row is supplied by the actual tensor Ω theorem.  A single
unitization multiplier then corrects that row, with all commutators protected
by a budget chosen before the row.
-/

set_option autoImplicit false

open scoped CStarAlgebra InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.FiniteApproximation
open MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

theorem exists_finiteRow_exact_on_projection
    (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (ρ : NonUnitalCStarRepresentation A H) (hρ : ρ.IsIrreducible)
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ ξ : H, omega (vectorMoment A H ρ ξ) = (‖ξ‖ ^ 2 : ℂ))
    (F : Finset A) (P : H →L[ℂ] H) (hP : IsStarProjection P)
    [FiniteDimensional ℂ P.range]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (y : Fin n → A),
      0 ≤ rowSquare A y ∧ ‖rowSquare A y‖ ≤ 1 ∧
      ρ (rowSquare A y) * P = P ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * rowMap A y z - rowMap A y z * a‖ ≤ ε * ‖z‖ := by
  let M : ℝ := 1 + ∑ a ∈ F, ‖a‖
  have hM : 0 < M := by
    dsimp [M]
    have hsum : 0 ≤ ∑ a ∈ F, ‖a‖ := by positivity
    linarith
  let r : ℝ := min (1 / 2) (ε / (24 * M))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrbudget : r ≤ ε / (24 * M) := min_le_right _ _
  obtain ⟨δ, hδ, hnormalize⟩ :=
    NonUnitalCStarRepresentation.exists_near_one_positive_normalizer_on_projection
      ρ hρ P hP hr
  obtain ⟨n, x, hxbudget, hxpos, hxnorm, hxapprox, hxcomm⟩ :=
    exists_finiteRow_approximate_on_projection A H ρ omega homega hcentral
      hmoment F P hP (by linarith : 0 < ε / 2) hδ
  have hxresidual : ‖(1 - ρ (rowSquare A x)) * P‖ < δ := by
    have hcomp : (ρ (rowSquare A x)).comp P = ρ (rowSquare A x) * P := rfl
    rw [hcomp] at hxapprox
    simpa [sub_mul, norm_sub_rev] using hxapprox
  obtain ⟨b, hbnear, d, hdpos, hdnorm, hdexact, hdeq⟩ :=
    hnormalize (rowSquare A x) hxpos hxnorm hxresidual
  let y : Fin n → A := fun i => unitizationLeftMul A b (x i)
  have hySquare : rowSquare A y = d := by
    apply Unitization.inr_injective (R := ℂ)
    calc
      ((rowSquare A y : A) : Unitization ℂ A) =
          b * (rowSquare A x : Unitization ℂ A) * star b := by
            exact rowSquare_unitizationLeftMul A b x
      _ = (d : Unitization ℂ A) := hdeq.symm
  refine ⟨n, y, by rw [hySquare]; exact hdpos,
    by rw [hySquare]; exact hdnorm,
    by rw [hySquare]; exact hdexact, ?_⟩
  intro a ha z
  have haM : ‖a‖ ≤ M := by
    have hsum : ‖a‖ ≤ ∑ a ∈ F, ‖a‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg j) ha
    dsimp [M]
    linarith
  have hbone : ‖b‖ ≤ 1 + ‖b - 1‖ := by
    have h := norm_add_le (b - 1) (1 : Unitization ℂ A)
    have heq : (b - 1) + 1 = b := by simp
    rw [heq, norm_one] at h
    linarith
  have hbone' : ‖b‖ ≤ 1 + r := by linarith
  have hpert : ‖b - 1‖ * ‖b‖ + ‖b - 1‖ ≤ 3 * r := by
    have hmul : ‖b - 1‖ * ‖b‖ ≤ r * (1 + r) := by
      calc
        ‖b - 1‖ * ‖b‖ ≤ r * ‖b‖ :=
          mul_le_mul_of_nonneg_right hbnear.le (norm_nonneg _)
        _ ≤ r * (1 + r) := mul_le_mul_of_nonneg_left hbone' hr.le
    nlinarith
  have hcomm0 := norm_commutator_rowMap_unitizationLeftMul_le_budget
    A b x a z hxbudget
  have hcommx := hxcomm a ha z
  have hbudget : 24 * M * r ≤ ε := by
    have hdv : 0 < 24 * M := by positivity
    have h := (le_div_iff₀ hdv).mp hrbudget
    nlinarith
  calc
    ‖a * rowMap A y z - rowMap A y z * a‖ ≤
        ‖a * rowMap A x z - rowMap A x z * a‖ +
          2 * ‖a‖ * ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖) := hcomm0
    _ ≤ ε / 2 * ‖z‖ + 2 * M * (3 * r * ‖z‖) := by
      gcongr
    _ ≤ ε * ‖z‖ := by
      have hcoef : ε / 2 + 2 * M * (3 * r) ≤ ε := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef (norm_nonneg z)]

end MathlibAnnex.CStarAlgebra.TensorAveraging
