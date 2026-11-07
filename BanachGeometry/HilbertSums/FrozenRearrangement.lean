/-
Fixed Pair R6, Lemma 9.2: the actual coordinate rearrangement and both inverses.
This is a new proof from the R6 formulas, not copied OpenAI proof code.
Zero-based convention: extra scalars occupy 2*n; old coefficients occupy 2*n+1.
No dimension or completeness assumption is needed for these algebraic identities.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace

namespace BanachGeometry.HilbertSums

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

/-- The direction coefficient in a block. -/
def coefficient (ξ u : ∀ n, G n) (n : ℕ) : ℝ := ⟪ξ n, u n⟫_ℝ

/-- Interleaving in the common zero-based indexing convention. -/
def interleave (a v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then v (n / 2) else a (n / 2)

@[simp] theorem interleave_even (a v : ℕ → ℝ) (n : ℕ) :
    interleave a v (2 * n) = v n := by simp [interleave]

@[simp] theorem interleave_odd (a v : ℕ → ℝ) (n : ℕ) :
    interleave a v (2 * n + 1) = a n := by
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [interleave, hd]

theorem interleave_split (b : ℕ → ℝ) :
    interleave (fun n => b (2 * n + 1)) (fun n => b (2 * n)) = b := by
  funext n
  have h := Nat.mod_add_div n 2
  have hm := Nat.mod_lt n (by omega : 0 < 2)
  by_cases hn : n % 2 = 0
  · simpa [interleave, hn] using congrArg b (show 2 * (n / 2) = n by omega)
  · simpa [interleave, hn] using congrArg b (show 2 * (n / 2) + 1 = n by omega)

/-- Formula (9.3) of R6, on all coordinate sequences before imposing ℓ₂ membership. -/
def frozenForward (ξ u : ∀ n, G n) (v : ℕ → ℝ) (n : ℕ) : G n :=
  u n - coefficient ξ u n • ξ n + interleave (coefficient ξ u) v n • ξ n

/-- The Hilbert component of the explicit inverse in R6 Lemma 9.2. -/
def frozenInverseU (ξ y : ∀ n, G n) (n : ℕ) : G n :=
  y n - coefficient ξ y n • ξ n + coefficient ξ y (2 * n + 1) • ξ n

/-- The extra scalar component of that inverse. -/
def frozenInverseV (ξ y : ∀ n, G n) (n : ℕ) : ℝ :=
  coefficient ξ y (2 * n)

variable (ξ : ∀ n, G n) (hξ : ∀ n, ‖ξ n‖ = 1)

include hξ

theorem inner_direction_self (n : ℕ) : ⟪ξ n, ξ n⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, hξ n]
  norm_num

theorem coefficient_frozenForward (u : ∀ n, G n) (v : ℕ → ℝ) (n : ℕ) :
    coefficient ξ (frozenForward ξ u v) n = interleave (coefficient ξ u) v n := by
  simp [coefficient, frozenForward, inner_sub_right, inner_add_right,
    real_inner_smul_right, hξ n]

theorem coefficient_frozenInverseU (y : ∀ n, G n) (n : ℕ) :
    coefficient ξ (frozenInverseU ξ y) n = coefficient ξ y (2 * n + 1) := by
  simp [coefficient, frozenInverseU, inner_sub_right, inner_add_right,
    real_inner_smul_right, hξ n]

theorem frozenInverseU_forward (u : ∀ n, G n) (v : ℕ → ℝ) :
    frozenInverseU ξ (frozenForward ξ u v) = u := by
  funext n
  simp only [frozenInverseU, coefficient_frozenForward ξ hξ, interleave_odd,
    frozenForward]
  module

theorem frozenInverseV_forward (u : ∀ n, G n) (v : ℕ → ℝ) :
    frozenInverseV ξ (frozenForward ξ u v) = v := by
  funext n
  simp [frozenInverseV, coefficient_frozenForward ξ hξ]

theorem frozenForward_inverse (y : ∀ n, G n) :
    frozenForward ξ (frozenInverseU ξ y) (frozenInverseV ξ y) = y := by
  funext n
  have hc : interleave (coefficient ξ (frozenInverseU ξ y))
      (frozenInverseV ξ y) = coefficient ξ y := by
    change interleave (coefficient ξ (frozenInverseU ξ y))
      (fun n => coefficient ξ y (2 * n)) = coefficient ξ y
    rw [funext (coefficient_frozenInverseU ξ hξ y)]
    exact interleave_split (coefficient ξ y)
  simp only [frozenForward, coefficient_frozenInverseU ξ hξ, hc, frozenInverseU]
  module

/-- The raw sequence equivalence has the actual inverse; ℓ₂ restriction is separate. -/
def frozenSequenceEquiv : ((∀ n, G n) × (ℕ → ℝ)) ≃ (∀ n, G n) where
  toFun p := frozenForward ξ p.1 p.2
  invFun y := (frozenInverseU ξ y, frozenInverseV ξ y)
  left_inv p := Prod.ext (frozenInverseU_forward ξ hξ p.1 p.2)
    (frozenInverseV_forward ξ hξ p.1 p.2)
  right_inv := frozenForward_inverse ξ hξ

theorem coefficient_abs_le (y : ∀ n, G n) (n : ℕ) :
    |coefficient ξ y n| ≤ ‖y n‖ := by
  simpa [coefficient, hξ n] using abs_real_inner_le_norm (ξ n) (y n)

/-- Orthogonal projection onto the line of a unit direction, with its norm identity. -/
theorem block_energy (y : ∀ n, G n) (a : ℝ) (n : ℕ) :
    ‖y n - coefficient ξ y n • ξ n + a • ξ n‖ ^ 2 =
      ‖y n‖ ^ 2 - (coefficient ξ y n) ^ 2 + a ^ 2 := by
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hξ n, one_pow, mul_one, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, inner_direction_self ξ hξ,
    real_inner_comm (y n) (ξ n)]
  unfold coefficient
  rw [real_inner_comm (y n) (ξ n)]
  ring

theorem frozenForward_energy (u : ∀ n, G n) (v : ℕ → ℝ) (n : ℕ) :
    ‖frozenForward ξ u v n‖ ^ 2 = ‖u n‖ ^ 2 - coefficient ξ u n ^ 2 +
      interleave (coefficient ξ u) v n ^ 2 :=
  block_energy ξ hξ u _ n

theorem frozenInverseU_energy (y : ∀ n, G n) (n : ℕ) :
    ‖frozenInverseU ξ y n‖ ^ 2 = ‖y n‖ ^ 2 - coefficient ξ y n ^ 2 +
      coefficient ξ y (2 * n + 1) ^ 2 :=
  block_energy ξ hξ y _ n

end BanachGeometry.HilbertSums
