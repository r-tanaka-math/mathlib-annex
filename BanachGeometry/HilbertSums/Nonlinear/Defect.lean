/- Actual output defect lies on the actual direction line in each block.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.Equivalence
import BanachGeometry.HilbertSums.Graded.CoordinateIsometry

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear

def hilbertDefect (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) (z : HilbertPair GradedHilbert) : GradedHilbert :=
  hilbertEquiv c hc hc' z - (WithLp.ofLp z).1

def beta (c : ℝ) (hc : 0 < c) (y : GradedHilbert) (n : ℕ) : ℝ :=
  coefficient (pointDirection c hc y) (fun j => y j) n

theorem hilbertDefect_apply (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4)
    (z : HilbertPair GradedHilbert) (n : ℕ) :
    hilbertDefect c hc hc' z n =
      (beta c hc (hilbertEquiv c hc hc' z) n - beta c hc (hilbertEquiv c hc hc' z) (2 * n + 1)) •
        pointDirection c hc (hilbertEquiv c hc hc' z) n := by
  have he := congrArg (fun t : HilbertPair GradedHilbert => (WithLp.ofLp t).1 n)
    (inverseHilbertMap_recursiveHilbertMap c hc z)
  change frozenInverseU (pointDirection c hc (hilbertEquiv c hc hc' z))
    (fun j => hilbertEquiv c hc hc' z j) n = (WithLp.ofLp z).1 n at he
  change hilbertEquiv c hc hc' z n - (WithLp.ofLp z).1 n = _
  rw [← he]
  unfold frozenInverseU beta
  module

theorem defect_scalar_zero_of_direction_zero (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4)
    (z : HilbertPair GradedHilbert) (n : ℕ) (a : BlockCoordinate n)
    (hz : pointDirection c hc (hilbertEquiv c hc hc' z) n a.1 a.2 = 0) :
    flattenEquiv (hilbertDefect c hc hc' z) n a = 0 := by
  rw [flattenEquiv_apply, hilbertDefect_apply]
  simp [hz]

end BanachGeometry.HilbertSums.Nonlinear
