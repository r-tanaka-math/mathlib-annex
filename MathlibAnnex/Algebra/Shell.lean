import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite shell bookkeeping for a decreasing source flag. -/

set_option autoImplicit false

open scoped BigOperators

namespace MathlibAnnex.Algebra

variable {A : Type*} [AddCommGroup A]

/-- Shells are indexed from zero: shell `n` is `q n - q (n+1)`. -/
def shell (q : ℕ → A) (n : ℕ) : A := q n - q (n + 1)

/-- The first `N` zero-indexed shells telescope to `q 0 - q N`. -/
theorem sum_shell_range (q : ℕ → A) (N : ℕ) :
    ∑ n ∈ Finset.range N, shell q n = q 0 - q N := by
  simpa [shell, Nat.add_comm] using Finset.sum_range_sub' q N

end MathlibAnnex.Algebra
