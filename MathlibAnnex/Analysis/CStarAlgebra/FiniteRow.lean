import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Finite-row averaging

This is the source-independent averaging interface shared by the CAR first
endpoint and a later general-simple-algebra proof.  It records exact row
normalization and a simultaneous finite-set commutator estimate.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The completely positive finite-row expression `b ↦ Σ xᵢ b xᵢ*`. -/
def finiteRowAverage {n : ℕ} (x : Fin n → A) (b : A) : A :=
  ∑ i, x i * b * star (x i)

theorem finiteRowAverage_nonneg {n : ℕ} (x : Fin n → A)
    {b : A} (hb : 0 ≤ b) : 0 ≤ finiteRowAverage x b := by
  unfold finiteRowAverage
  apply Finset.sum_nonneg
  intro i _
  exact star_right_conjugate_nonneg hb (x i)

@[simp] theorem finiteRowAverage_one {n : ℕ} (x : Fin n → A) :
    finiteRowAverage x 1 = ∑ i, x i * star (x i) := by
  simp [finiteRowAverage]

/-- Exact normalization and dimension-free approximate centrality supplied
by finite rows.  The row and its cardinality may depend on the finite set and
tolerance, while the estimate holds for every test element `b`. -/
def HasFiniteRowAveraging (A : Type u)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Prop :=
  ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
    ∃ (n : ℕ) (x : Fin n → A),
      (∑ i, x i * star (x i) = 1) ∧
      ∀ a ∈ F, ∀ b : A,
        ‖a * finiteRowAverage x b - finiteRowAverage x b * a‖ ≤
          epsilon * ‖b‖

end MathlibAnnex.CStarAlgebra
