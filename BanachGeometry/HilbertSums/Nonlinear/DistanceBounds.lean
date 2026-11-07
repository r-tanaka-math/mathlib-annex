/- Distance estimates for the inverse Hilbert map under an explicit comparison-series
budget. This local theorem retains that budget in its type; Nonlinear/Equivalence
proves the budget for the concrete clock/directions and constructs the equivalence.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.RecursiveInverse
import BanachGeometry.HilbertSums.InverseComparison

noncomputable section
open scoped BigOperators InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear

/-- The exact larger-tail comparison family in R6, in the frozen zero-based convention. -/
def comparisonDirection (c : ℝ) (hc : 0 < c) (y z : GradedHilbert) (n : ℕ) : GradedBlock n :=
  if ‖blockTail n y‖ ≤ ‖blockTail n z‖ then pointDirection c hc z n else pointDirection c hc y n

theorem norm_comparisonDirection (c : ℝ) (hc : 0 < c) (y z : GradedHilbert) (n : ℕ) :
    ‖comparisonDirection c hc y z n‖ = 1 := by
  unfold comparisonDirection
  split_ifs <;> exact norm_pointDirection _ _ _ _

/-- The comparison-series bound for the actual larger-tail directions,
with constant c²/16 and no existential replacement of the map. The estimates
below take hbudget explicitly; Equivalence.comparisonBudget_bound proves it
for these directions and the concrete dyadic clock. -/
def ComparisonBudget (c : ℝ) (hc : 0 < c) : Prop :=
  ∀ y z : GradedHilbert, ∀ q ∈ ({y, z} : Set GradedHilbert),
    (∑' n, comparisonWeight (pointDirection c hc q) (comparisonDirection c hc y z)
      (fun j => q j) n) ≤ c ^ 2 / 16 * ‖y - z‖ ^ 2

theorem comparison_error_le (c : ℝ) (hc : 0 < c) (hbudget : ComparisonBudget c hc)
    (y z q : GradedHilbert) (hq : q ∈ ({y, z} : Set GradedHilbert)) :
    ‖inverseHilbertMap c hc q - (frozenLinearIsometryEquiv (comparisonDirection c hc y z)
      (norm_comparisonDirection c hc y z)).symm q‖ ≤ c * ‖y - z‖ := by
  have he := frozenInverse_comparison (pointDirection c hc q) (comparisonDirection c hc y z)
    (norm_pointDirection c hc q) (norm_comparisonDirection c hc y z) q
  have hs := comparisonEnergy_sq (pointDirection c hc q) (comparisonDirection c hc y z)
    (norm_pointDirection c hc q) (norm_comparisonDirection c hc y z) q
  have hb := hbudget y z q hq
  have hn : 0 ≤ comparisonEnergy (pointDirection c hc q) (comparisonDirection c hc y z)
      (fun j => q j) := Real.sqrt_nonneg _
  have hscaled : 4 * comparisonEnergy (pointDirection c hc q) (comparisonDirection c hc y z)
      (fun j => q j) ≤ c * ‖y - z‖ := by
    apply (sq_le_sq₀ (by positivity)
      (mul_nonneg hc.le (norm_nonneg (y - z)))).1
    nlinarith
  exact he.trans hscaled

theorem inverseHilbertMap_fixed_isometry_error (c : ℝ) (hc : 0 < c) (hbudget : ComparisonBudget c hc)
    (y z : GradedHilbert) :
    ‖inverseHilbertMap c hc y - inverseHilbertMap c hc z -
      (frozenLinearIsometryEquiv (comparisonDirection c hc y z)
        (norm_comparisonDirection c hc y z)).symm (y - z)‖ ≤ 2 * c * ‖y - z‖ := by
  let e := (frozenLinearIsometryEquiv (comparisonDirection c hc y z)
    (norm_comparisonDirection c hc y z)).symm
  have hy := comparison_error_le c hc hbudget y z y (by simp)
  have hz := comparison_error_le c hc hbudget y z z (by simp)
  have hid : inverseHilbertMap c hc y - inverseHilbertMap c hc z - e (y - z) =
      (inverseHilbertMap c hc y - e y) - (inverseHilbertMap c hc z - e z) := by rw [e.map_sub]; module
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

theorem inverseHilbertMap_distance_bounds (c : ℝ) (hc : 0 < c) (hbudget : ComparisonBudget c hc)
    (y z : GradedHilbert) :
    (1 - 2 * c) * ‖y - z‖ ≤ ‖inverseHilbertMap c hc y - inverseHilbertMap c hc z‖ ∧
      ‖inverseHilbertMap c hc y - inverseHilbertMap c hc z‖ ≤ (1 + 2 * c) * ‖y - z‖ := by
  let e := (frozenLinearIsometryEquiv (comparisonDirection c hc y z)
    (norm_comparisonDirection c hc y z)).symm
  have he := inverseHilbertMap_fixed_isometry_error c hc hbudget y z
  have hn : ‖e (y - z)‖ = ‖y - z‖ := e.norm_map _
  have hlo := norm_sub_norm_le (e (y - z)) (inverseHilbertMap c hc y - inverseHilbertMap c hc z)
  have hhi := norm_sub_norm_le (inverseHilbertMap c hc y - inverseHilbertMap c hc z) (e (y - z))
  rw [norm_sub_rev (e (y - z)) (inverseHilbertMap c hc y - inverseHilbertMap c hc z)] at hlo
  constructor <;> linarith

theorem inverseHilbertMap_injective (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 2)
    (hbudget : ComparisonBudget c hc) : Function.Injective (inverseHilbertMap c hc) := by
  intro y z h
  have hlow := (inverseHilbertMap_distance_bounds c hc hbudget y z).1
  rw [h, sub_self, norm_zero] at hlow
  have hz : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Actual right inverse upgraded using the lower estimate, not choice of an unrelated inverse. -/
def hEquiv (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 2) (hbudget : ComparisonBudget c hc) :
    HilbertPair GradedHilbert ≃ GradedHilbert where
  toFun := recursiveHilbertMap c hc
  invFun := inverseHilbertMap c hc
  left_inv := inverseHilbertMap_recursiveHilbertMap c hc
  right_inv y := inverseHilbertMap_injective c hc hc' hbudget (inverseHilbertMap_recursiveHilbertMap c hc (inverseHilbertMap c hc y))

@[simp] theorem hEquiv_zero (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 2)
    (hbudget : ComparisonBudget c hc) : hEquiv c hc hc' hbudget 0 = 0 := recursiveHilbertMap_zero c hc

theorem norm_hEquiv (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 2)
    (hbudget : ComparisonBudget c hc) (z : HilbertPair GradedHilbert) :
    ‖hEquiv c hc hc' hbudget z‖ = ‖z‖ := norm_recursiveHilbertMap c hc z

/-- The contract constants follow by elementary arithmetic from the sharper Phi constants. -/
theorem hEquiv_distance_bounds (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4)
    (hbudget : ComparisonBudget c hc) (z z' : HilbertPair GradedHilbert) :
    (1 - 4 * c) * ‖z - z'‖ ≤ ‖hEquiv c hc (by linarith) hbudget z - hEquiv c hc (by linarith) hbudget z'‖ ∧
    ‖hEquiv c hc (by linarith) hbudget z - hEquiv c hc (by linarith) hbudget z'‖ ≤ (1 + 4 * c) * ‖z - z'‖ := by
  let h := hEquiv c hc (by linarith) hbudget
  have hb := inverseHilbertMap_distance_bounds c hc hbudget (h z) (h z')
  have he : inverseHilbertMap c hc (h z) - inverseHilbertMap c hc (h z') = z - z' := by simp [h, hEquiv, inverseHilbertMap_recursiveHilbertMap]
  rw [he] at hb
  have hD := norm_nonneg (z - z')
  have hd := norm_nonneg (h z - h z')
  have h₁ : 0 < 1 - 2 * c := by linarith
  have h₂ : 0 ≤ 1 - 4 * c := by linarith
  have h₃ := mul_le_mul_of_nonneg_left hb.2 h₂
  have h₄ := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0 ≤ 1 + 4 * c)
  have hfac : 0 ≤ 2 * c - 8 * c ^ 2 := by nlinarith
  have hprod := mul_nonneg hfac hd
  have hprod' := mul_nonneg (by positivity : 0 ≤ 2 * c + 8 * c ^ 2) hd
  constructor <;> dsimp [h] at * <;> nlinarith

end BanachGeometry.HilbertSums.Nonlinear
