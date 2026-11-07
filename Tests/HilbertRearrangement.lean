/- Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.AlmostIsometric.Consequences
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality
open BanachGeometry BanachGeometry.HilbertSums
open scoped InnerProductSpace
noncomputable section

section GeneralBlocks
variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]
variable (ξ ζ : ∀ n, G n) (hξ : ∀ n, ‖ξ n‖ = 1) (hζ : ∀ n, ‖ζ n‖ = 1)

example (u : ∀ n, G n) (v : ℕ → ℝ) :
    frozenForward ξ u v 0 = u 0 - coefficient ξ u 0 • ξ 0 + v 0 • ξ 0 := by
  simp [frozenForward, interleave]
example (u : ∀ n, G n) (v : ℕ → ℝ) :
    frozenForward ξ u v 1 = u 1 - coefficient ξ u 1 • ξ 1 + coefficient ξ u 0 • ξ 1 := by
  simp [frozenForward, interleave]
example (u : ∀ n, G n) (v : ℕ → ℝ) :
    frozenForward ξ u v 2 = u 2 - coefficient ξ u 2 • ξ 2 + v 1 • ξ 2 := by
  simp [frozenForward, interleave]
example : frozenLinearIsometryEquiv ξ hξ 0 = 0 := map_zero _
example (z : HilbertPair (lp G 2)) :
    (frozenLinearIsometryEquiv ξ hξ).symm (frozenLinearIsometryEquiv ξ hξ z) = z :=
  (frozenLinearIsometryEquiv ξ hξ).symm_apply_apply z
example (y : lp G 2) :
    frozenLinearIsometryEquiv ξ hξ ((frozenLinearIsometryEquiv ξ hξ).symm y) = y :=
  (frozenLinearIsometryEquiv ξ hξ).apply_symm_apply y
example (y : lp G 2) :
    ‖(frozenL2Equiv ξ hξ).symm y - (frozenL2Equiv ζ hζ).symm y‖ ≤
      4 * Real.sqrt (∑' n, (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * ‖ξ n - ζ n‖ ^ 2) :=
  frozenInverse_comparison ξ ζ hξ hζ y
end GeneralBlocks

example (u v : ℕ → ℝ) (n : ℕ) :
    frozenForward (fun _ => (1 : ℝ)) u v n = interleave u v n := by
  simp [frozenForward, coefficient, interleave]
example (y : ℕ → ℝ) (n : ℕ) :
    frozenInverseU (fun _ => (1 : ℝ)) y n = y (2 * n + 1) := by
  simp [frozenInverseU, coefficient]
example (y : ℕ → ℝ) (n : ℕ) :
    frozenInverseV (fun _ => (1 : ℝ)) y n = y (2 * n) := by
  simp [frozenInverseV, coefficient]

-- Explicit nonzero Euclidean blocks of dimensions 1, 2, 3.
def firstDirection (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.basisFun (Fin (d + 1)) ℝ) 0
lemma firstDirection_unit (d : ℕ) : ‖firstDirection d‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).norm_eq_one 0
example : HilbertPair (lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 1)) 2) ≃ₗᵢ[ℝ]
    lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 1)) 2 :=
  frozenLinearIsometryEquiv (fun _ => firstDirection 0) (fun _ => firstDirection_unit 0)
example : HilbertPair (lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2) ≃ₗᵢ[ℝ]
    lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2 :=
  frozenLinearIsometryEquiv (fun _ => firstDirection 1) (fun _ => firstDirection_unit 1)
example : HilbertPair (lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 3)) 2) ≃ₗᵢ[ℝ]
    lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 3)) 2 :=
  frozenLinearIsometryEquiv (fun _ => firstDirection 2) (fun _ => firstDirection_unit 2)
