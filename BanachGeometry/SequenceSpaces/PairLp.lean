import BanachGeometry.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Operator.Prod

open scoped ENNReal

/-! Explicit ℓp pair adapters. The source p=1 and output p=2 in the graph
construction retain their separate norm instances.
Execution evidence is recorded in the external receipts. -/

noncomputable section
namespace BanachGeometry
namespace PairLp
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (A B : Type*)
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

def first : WithLp p (A × B) →L[ℝ] A :=
  (ContinuousLinearMap.fst ℝ A B).comp (WithLp.prodContinuousLinearEquiv p ℝ A B).toContinuousLinearMap
def second : WithLp p (A × B) →L[ℝ] B :=
  (ContinuousLinearMap.snd ℝ A B).comp (WithLp.prodContinuousLinearEquiv p ℝ A B).toContinuousLinearMap
def left : A →L[ℝ] WithLp p (A × B) :=
  (WithLp.prodContinuousLinearEquiv p ℝ A B).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ A B)
def right : B →L[ℝ] WithLp p (A × B) :=
  (WithLp.prodContinuousLinearEquiv p ℝ A B).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ A B)

@[simp] theorem first_apply (z : WithLp p (A × B)) : first p A B z = (WithLp.ofLp z).1 := rfl
@[simp] theorem second_apply (z : WithLp p (A × B)) : second p A B z = (WithLp.ofLp z).2 := rfl
@[simp] theorem left_apply (x : A) : left p A B x = WithLp.toLp p (x, 0) := rfl
@[simp] theorem right_apply (y : B) : right p A B y = WithLp.toLp p (0, y) := rfl

@[simp] theorem first_left (x : A) : first p A B (left p A B x) = x := rfl
@[simp] theorem second_left (x : A) : second p A B (left p A B x) = 0 := rfl
@[simp] theorem first_right (y : B) : first p A B (right p A B y) = 0 := rfl
@[simp] theorem second_right (y : B) : second p A B (right p A B y) = y := rfl

theorem norm_first_le (z : WithLp p (A × B)) : ‖first p A B z‖ ≤ ‖z‖ := WithLp.norm_fst_le A z
theorem norm_second_le (z : WithLp p (A × B)) : ‖second p A B z‖ ≤ ‖z‖ := WithLp.norm_snd_le A z
theorem opNorm_first_le : ‖first p A B‖ ≤ 1 :=
  (first p A B).opNorm_le_bound zero_le_one (by intro z; simpa only [one_mul] using norm_first_le p A B z)
theorem opNorm_second_le : ‖second p A B‖ ≤ 1 :=
  (second p A B).opNorm_le_bound zero_le_one (by intro z; simpa only [one_mul] using norm_second_le p A B z)

@[simp] theorem norm_left (x : A) : ‖left p A B x‖ = ‖x‖ := WithLp.norm_toLp_fst p A B x
@[simp] theorem norm_right (y : B) : ‖right p A B y‖ = ‖y‖ := WithLp.norm_toLp_snd p A B y

theorem left_first_add_right_second (z : WithLp p (A × B)) :
    left p A B (first p A B z) + right p A B (second p A B z) = z := by
  apply WithLp.ofLp_injective p
  apply Prod.ext <;> simp [first, second, left, right]

theorem norm_toLp_le (x : A) (y : B) : ‖WithLp.toLp p (x, y)‖ ≤ ‖x‖ + ‖y‖ := by
  have hsplit : WithLp.toLp p (x, y) = left p A B x + right p A B y := by
    apply WithLp.ofLp_injective p
    apply Prod.ext <;> simp [left, right]
  rw [hsplit]
  exact (norm_add_le _ _).trans_eq (by rw [norm_left, norm_right])

end PairLp
end BanachGeometry
