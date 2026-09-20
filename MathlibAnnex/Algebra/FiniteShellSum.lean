import Mathlib.Algebra.Star.BigOperators

/-!
Finite algebraic identities behind orthogonal shell sums.  The analytic strong
convergence step is intentionally separate.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MathlibAnnex.Algebra

variable {A ι : Type*} [Semiring A] [StarRing A]

/-- Initial-support identity for a finite orthogonal family of links. -/
theorem star_sum_mul_sum_eq_sum_initial [DecidableEq ι] (s : Finset ι)
    (W F : ι → A)
    (hdiag : ∀ i ∈ s, star (W i) * W i = F i)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (W i) * W j = 0) :
    star (∑ i ∈ s, W i) * (∑ i ∈ s, W i) = ∑ i ∈ s, F i := by
  classical
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    ∑ i ∈ s, ∑ j ∈ s, star (W i) * W j =
        ∑ i ∈ s, star (W i) * W i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_eq_single i
          · intro j hj hji
            exact hcross i hi j hj hji.symm
          · exact fun hnot ↦ (hnot hi).elim
    _ = ∑ i ∈ s, F i := by
      apply Finset.sum_congr rfl
      exact fun i hi ↦ hdiag i hi

/-- Final-support identity for a finite orthogonal family of links. -/
theorem sum_mul_star_sum_eq_sum_final [DecidableEq ι] (s : Finset ι)
    (W G : ι → A)
    (hdiag : ∀ i ∈ s, W i * star (W i) = G i)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → W i * star (W j) = 0) :
    (∑ i ∈ s, W i) * star (∑ i ∈ s, W i) = ∑ i ∈ s, G i := by
  classical
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    ∑ i ∈ s, ∑ j ∈ s, W i * star (W j) =
        ∑ i ∈ s, W i * star (W i) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_eq_single i
          · intro j hj hji
            exact hcross i hi j hj hji.symm
          · exact fun hnot ↦ (hnot hi).elim
    _ = ∑ i ∈ s, G i := by
      apply Finset.sum_congr rfl
      exact fun i hi ↦ hdiag i hi

end MathlibAnnex.Algebra
