/- Separability from the countable union of the actual coordinate ranges.
This fills the concrete Hilbert bundle; it is not assumed in a predicate.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Graded.Basic
import BanachGeometry.HilbertSums.L2Separable
import Mathlib.Topology.Algebra.Module.Basic

open scoped ENNReal

noncomputable section
open scoped BigOperators Topology
namespace BanachGeometry.HilbertSums.Nonlinear

instance gradedHilbert_separable : TopologicalSpace.SeparableSpace GradedHilbert := lp_two_separable
instance scalarL2_separable : TopologicalSpace.SeparableSpace ScalarL2 := lp_two_separable

/-- The actual separable complete real Hilbert space used in the common boundary. -/
def hilbertBundle : SeparableRealHilbert where
  Carrier := GradedHilbert
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  completeSpace := inferInstance
  separableSpace := inferInstance
  nontrivial := inferInstance

end BanachGeometry.HilbertSums.Nonlinear
