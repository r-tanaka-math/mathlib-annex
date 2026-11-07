/- Actual isometric flattening to the finite-coordinate Hilbert used by the
specialized upstream complete-continuity theorem.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Graded.Separable

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums.Nonlinear

abbrev FlatBlock (n : ℕ) := EuclideanSpace ℝ (BlockCoordinate n)
abbrev FlatHilbert := lp FlatBlock 2

def flattenBlock (n : ℕ) : GradedBlock n ≃ₗᵢ[ℝ] FlatBlock n where
  toFun x := WithLp.toLp 2 (fun a => x a.1 a.2)
  invFun x := WithLp.toLp 2 (fun k => WithLp.toLp 2 (fun a => x ⟨k, a⟩))
  left_inv x := by apply PiLp.ext; intro k; apply PiLp.ext; intro a; rfl
  right_inv x := by apply PiLp.ext; rintro ⟨k, a⟩; rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [Fintype.sum_sigma]
    rfl

def flattenL2 (y : GradedHilbert) : FlatHilbert :=
  ⟨fun n => flattenBlock n (y n), mem_l2_of_summable_sq _ (by
    simpa only [(flattenBlock _).norm_map] using l2_summable_sq y)⟩

def unflattenL2 (y : FlatHilbert) : GradedHilbert :=
  ⟨fun n => (flattenBlock n).symm (y n), mem_l2_of_summable_sq _ (by
    simpa only [(flattenBlock _).symm.norm_map] using l2_summable_sq y)⟩

/-- No change of the concrete metric, enumeration, or causal order is hidden here. -/
def flattenEquiv : GradedHilbert ≃ₗᵢ[ℝ] FlatHilbert where
  toFun := flattenL2
  invFun := unflattenL2
  left_inv x := by apply lp.ext; funext n; exact (flattenBlock n).symm_apply_apply _
  right_inv x := by apply lp.ext; funext n; exact (flattenBlock n).apply_symm_apply _
  map_add' x y := by apply lp.ext; funext n; exact (flattenBlock n).map_add _ _
  map_smul' r x := by apply lp.ext; funext n; exact (flattenBlock n).map_smul _ _
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [l2_norm_sq, l2_norm_sq]
    apply tsum_congr
    intro n
    exact congrArg (fun r : ℝ => r ^ 2) ((flattenBlock n).norm_map (x n))

@[simp] theorem flattenEquiv_apply (y : GradedHilbert) (n : ℕ) (a : BlockCoordinate n) :
    flattenEquiv y n a = y n a.1 a.2 := rfl

end BanachGeometry.HilbertSums.Nonlinear
