/- Discharge the comparison budget using the actual smaller-tail point bound and
full dyadic energy theorem. This does not discharge defect locality.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.PointBounds
import BanachGeometry.HilbertSums.Nonlinear.DistanceBounds

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums.Nonlinear
open Clock

theorem comparisonWeight_of_smaller_tail (c : ℝ) (hc : 0 < c) (q q' : GradedHilbert) (n : ℕ)
    (horder : ‖blockTail n q‖ ≤ ‖blockTail n q'‖) :
    comparisonWeight (pointDirection c hc q) (pointDirection c hc q') (fun j => q j) n ≤
      weightedGammaEnergy c q n * ‖q - q'‖ ^ 2 := by
  by_cases hz : ‖blockTail n q‖ = 0
  · have h₁ := apply_eq_zero_of_norm_blockTail_eq_zero q hz (le_refl n)
    have h₂ := apply_eq_zero_of_norm_blockTail_eq_zero q hz (show n ≤ 2 * n + 1 by omega)
    simp [comparisonWeight, weightedGammaEnergy, h₁, h₂]
  · have hq : 0 < ‖blockTail n q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hq' := hq.trans_le horder
    have hd := pointDirection_difference_bound c hc q q' n hq hq'
    rw [min_eq_left horder] at hd
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (gamma_nonneg hc.le _) (norm_nonneg _))).2 hd
    have hmul := mul_le_mul_of_nonneg_left hsq
      (add_nonneg (sq_nonneg ‖q n‖) (sq_nonneg ‖q (2 * n + 1)‖))
    simpa only [comparisonWeight, weightedGammaEnergy, mul_pow, mul_assoc] using hmul

theorem y_comparisonWeight_le (c : ℝ) (hc : 0 < c) (y z : GradedHilbert) (n : ℕ) :
    comparisonWeight (pointDirection c hc y) (comparisonDirection c hc y z) (fun j => y j) n ≤
      weightedGammaEnergy c y n * ‖y - z‖ ^ 2 := by
  by_cases hn : ‖blockTail n y‖ ≤ ‖blockTail n z‖
  · simpa only [comparisonWeight, comparisonDirection, if_pos hn] using
      comparisonWeight_of_smaller_tail c hc y z n hn
  · simp only [comparisonWeight, comparisonDirection, if_neg hn, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    unfold weightedGammaEnergy
    positivity

theorem z_comparisonWeight_le (c : ℝ) (hc : 0 < c) (y z : GradedHilbert) (n : ℕ) :
    comparisonWeight (pointDirection c hc z) (comparisonDirection c hc y z) (fun j => z j) n ≤
      weightedGammaEnergy c z n * ‖y - z‖ ^ 2 := by
  by_cases hn : ‖blockTail n y‖ ≤ ‖blockTail n z‖
  · simp only [comparisonWeight, comparisonDirection, if_pos hn, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    unfold weightedGammaEnergy
    positivity
  · simpa only [comparisonWeight, comparisonDirection, if_neg hn, norm_sub_rev z y] using
      comparisonWeight_of_smaller_tail c hc z y n (le_of_not_ge hn)

/-- The concrete comparison budget, no longer an analytic premise in this module. -/
theorem comparisonBudget_bound (c : ℝ) (hc : 0 < c) : ComparisonBudget c hc := by
  intro y z q hq
  have pointwise : ∀ n, comparisonWeight (pointDirection c hc q) (comparisonDirection c hc y z)
      (fun j => q j) n ≤ weightedGammaEnergy c q n * ‖y - z‖ ^ 2 := by
    rcases Set.mem_insert_iff.mp hq with h | h
    · subst q; exact y_comparisonWeight_le c hc y z
    · have h' : q = z := Set.mem_singleton_iff.mp h
      subst q; exact z_comparisonWeight_le c hc y z
  have hsum := comparisonWeight_summable (pointDirection c hc q) (comparisonDirection c hc y z)
    (norm_pointDirection c hc q) (norm_comparisonDirection c hc y z) q
  calc
    (∑' n, comparisonWeight (pointDirection c hc q) (comparisonDirection c hc y z) (fun j => q j) n) ≤
        ∑' n, weightedGammaEnergy c q n * ‖y - z‖ ^ 2 :=
      hsum.tsum_le_tsum pointwise ((weightedGammaEnergy_summable hc.le q).mul_right _)
    _ = (∑' n, weightedGammaEnergy c q n) * ‖y - z‖ ^ 2 := tsum_mul_right
    _ ≤ (c ^ 2 / 16) * ‖y - z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (tsum_weightedGammaEnergy_le hc.le q) (sq_nonneg _)

/-- The concrete norm-preserving Hilbert equivalence for 0 < c < 1/4,
using comparisonBudget_bound to obtain both distance estimates.
Local execution evidence is recorded in the external qualification receipts;
Annex, hosted and release status are recorded separately. -/
def hilbertEquiv (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) : HilbertPair GradedHilbert ≃ GradedHilbert :=
  hEquiv c hc (by linarith) (comparisonBudget_bound c hc)

@[simp] theorem hilbertEquiv_zero (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) : hilbertEquiv c hc hc' 0 = 0 :=
  recursiveHilbertMap_zero c hc

theorem norm_hilbertEquiv (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) (z : HilbertPair GradedHilbert) :
    ‖hilbertEquiv c hc hc' z‖ = ‖z‖ := norm_recursiveHilbertMap c hc z

theorem hilbertEquiv_bounds (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) (z z' : HilbertPair GradedHilbert) :
    (1 - 4 * c) * ‖z - z'‖ ≤ ‖hilbertEquiv c hc hc' z - hilbertEquiv c hc hc' z'‖ ∧
    ‖hilbertEquiv c hc hc' z - hilbertEquiv c hc hc' z'‖ ≤ (1 + 4 * c) * ‖z - z'‖ :=
  hEquiv_distance_bounds c hc hc' (comparisonBudget_bound c hc) z z'

end BanachGeometry.HilbertSums.Nonlinear
