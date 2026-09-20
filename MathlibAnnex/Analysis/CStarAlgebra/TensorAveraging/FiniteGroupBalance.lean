import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteIsometryAverage
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Exact finite-group balance before approximation

For s = w U(g), the range projection is independent of g. Right translation
of g (not left translation of the source test) makes the average balance
on the complex linear span of U(G). This algebraic result requires no Haar
measure, no amenability of a discrete unitary group, and no normality.
The existence of suitable finite-dimensional unitary groups is a separate
geometric source task. C04 unbuilt.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.TensorAveraging
universe u v
variable {M : Type u} [CStarAlgebra M] [Nontrivial M]
variable {G : Type v} [Group G] [Fintype G]

def orbitSum (U : G → M) (w : M) (B : ContinuousBilinearForm M) : ℂ :=
  ∑ g, B (star (w * U g)) (w * U g)

/-- Raw sums suffice for the exact identity; normalization is done once
when building a FiniteIsometryAverage. -/
theorem orbitSum_balance_generator (U : G → M)
    (hmul : ∀ g h, U (g * h) = U g * U h)
    (hunit : ∀ g, U g * star (U g) = 1)
    (w : M) (B : ContinuousBilinearForm M) (v : G) :
    orbitSum U w (leftForm M (U v) B) =
      orbitSum U w (rightForm M (U v) B) := by
  classical
  let e : G ≃ G :=
    { toFun := fun g => g * v
      invFun := fun g => g * v⁻¹
      left_inv := by intro g; simp only [mul_assoc, mul_inv_cancel, mul_one]
      right_inv := by intro g; simp only [mul_assoc, inv_mul_cancel, mul_one] }
  have he (g : G) :
      (leftForm M (U v) B) (star (w * U (g * v))) (w * U (g * v)) =
      (rightForm M (U v) B) (star (w * U g)) (w * U g) := by
    change B (U v * star (w * U (g * v))) (w * U (g * v)) =
      B (star (w * U g)) ((w * U g) * U v)
    rw [hmul, star_mul, star_mul]
    have hleft : U v * ((star (U v) * star (U g)) * star w) =
        star (U g) * star w := by rw [← mul_assoc, ← mul_assoc, hunit, one_mul]
    rw [hleft, ← mul_assoc]
    simp only [star_mul]
  calc
    orbitSum U w (leftForm M (U v) B) =
        ∑ g, (leftForm M (U v) B) (star (w * U (e g))) (w * U (e g)) := by
      exact (Equiv.sum_comp e (fun g =>
        (leftForm M (U v) B) (star (w * U g)) (w * U g))).symm
    _ = orbitSum U w (rightForm M (U v) B) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact he g

/-- Extend from group elements to their actual complex linear span. -/
theorem orbitSum_balance_span (U : G → M)
    (hmul : ∀ g h, U (g * h) = U g * U h)
    (hunit : ∀ g, U g * star (U g) = 1)
    (w : M) (B : ContinuousBilinearForm M) (a : M)
    (ha : a ∈ Submodule.span ℂ (Set.range U)) :
    orbitSum U w (leftForm M a B) = orbitSum U w (rightForm M a B) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨g, rfl⟩
      exact orbitSum_balance_generator U hmul hunit w B g
  | zero => simp [orbitSum, leftForm, rightForm]
  | add x y hx hy ihx ihy =>
      simpa only [orbitSum, leftForm_apply, rightForm_apply,
        add_mul, mul_add, map_add, ContinuousLinearMap.add_apply,
        Finset.sum_add_distrib] using congrArg₂ (· + ·) ihx ihy
  | smul c x hx ih =>
      simpa only [orbitSum, leftForm_apply, rightForm_apply,
        smul_mul_assoc, mul_smul_comm,
        map_smul, ContinuousLinearMap.smul_apply,
        Finset.smul_sum] using congrArg (c • ·) ih

/-- The range projection stays fixed under the finite right orbit. -/
theorem orbit_range_projection (U : G → M)
    (hunit : ∀ g, U g * star (U g) = 1) (w : M) (g : G) :
    (w * U g) * star (w * U g) = w * star w := by
  rw [star_mul]
  calc
    _ = w * (U g * star (U g)) * star w := by noncomm_ring
    _ = w * star w := by rw [hunit, mul_one]

/-- Each orbit element is an actual isometry, with no assumption ww*=1. -/
theorem orbit_isometry (U : G → M)
    (hunit : ∀ g, star (U g) * U g = 1)
    (w : M) (hw : star w * w = 1) (g : G) :
    star (w * U g) * (w * U g) = 1 := by
  rw [star_mul]
  calc
    _ = star (U g) * (star w * w) * U g := by noncomm_ring
    _ = 1 := by rw [hw, mul_one, hunit]

end MathlibAnnex.CStarAlgebra.TensorAveraging
