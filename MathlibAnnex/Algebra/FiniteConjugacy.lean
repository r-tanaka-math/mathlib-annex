import Mathlib.Algebra.Star.Unitary
import MathlibAnnex.Algebra.Shell

/-!
Finite algebraic part of unitary completion.  These statements stop before
any strong-operator limit and therefore remain valid in every represented
copy of the source algebra.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MathlibAnnex.Algebra

variable {A : Type*} [Ring A] [StarRing A]

/-- A shell relation and the final-support equation imply conjugacy of that
individual shell. -/
theorem unitary_conjugates_shell_of_relation (u : unitary A)
    (qi qo : ℕ → A) (w : ℕ → A) (n : ℕ)
    (hself : star (shell qi n) = shell qi n)
    (hidem : shell qi n * shell qi n = shell qi n)
    (hrel : (u : A) * shell qi n = w n)
    (hfinal : w n * star (w n) = shell qo n) :
    (u : A) * shell qi n * star (u : A) = shell qo n := by
  have hadj : shell qi n * star (u : A) = star (w n) := by
    have := congrArg star hrel
    simpa only [star_mul, hself] using this
  calc
    (u : A) * shell qi n * star (u : A) =
        (u : A) * (shell qi n * shell qi n) * star (u : A) := by rw [hidem]
    _ = ((u : A) * shell qi n) * (shell qi n * star (u : A)) := by
      simp only [mul_assoc]
    _ = w n * star (w n) := by rw [hrel, hadj]
    _ = shell qo n := hfinal

/-- Exact finite defect transport.  Index `n` denotes the zero-indexed shell
`q n - q (n+1)`, so summing `n < N` yields `q 0 - q N`. -/
theorem unitary_conjugates_flag_of_shell_relations (u : unitary A)
    (qi qo : ℕ → A) (w : ℕ → A)
    (hqi0 : qi 0 = 1) (hqo0 : qo 0 = 1)
    (hself : ∀ n, star (shell qi n) = shell qi n)
    (hidem : ∀ n, shell qi n * shell qi n = shell qi n)
    (hrel : ∀ n, (u : A) * shell qi n = w n)
    (hfinal : ∀ n, w n * star (w n) = shell qo n) (N : ℕ) :
    (u : A) * qi N * star (u : A) = qo N := by
  have hshell (n : ℕ) :
      (u : A) * shell qi n * star (u : A) = shell qo n :=
    unitary_conjugates_shell_of_relation u qi qo w n (hself n) (hidem n)
      (hrel n) (hfinal n)
  have hsum :
      (u : A) * (qi 0 - qi N) * star (u : A) = qo 0 - qo N := by
    rw [← sum_shell_range qi N, ← sum_shell_range qo N]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ ↦ hshell n
  rw [hqi0, hqo0, mul_sub, sub_mul] at hsum
  have hdiff : 1 - (u : A) * qi N * star (u : A) = 1 - qo N := by
    simpa only [mul_one, Unitary.mul_star_self_of_mem u.prop] using hsum
  exact sub_right_inj.mp hdiff

/-- Multiplying a unitary by a projection gives the exact partial-isometry
link between that projection and its unitary conjugate. -/
theorem unitaryProjectionLink_supports (u : unitary A) (p r : A)
    (hp_star : star p = p) (hp_idem : p * p = p)
    (hconj : (u : A) * p * star (u : A) = r) :
    star ((u : A) * p) * ((u : A) * p) = p ∧
      ((u : A) * p) * star ((u : A) * p) = r := by
  constructor
  · simp only [star_mul, hp_star, mul_assoc]
    rw [← mul_assoc (star (u : A)) (u : A) p,
      Unitary.star_mul_self_of_mem u.prop, one_mul, hp_idem]
  · simp only [star_mul, hp_star]
    rw [mul_assoc (u : A) p (p * star (u : A)),
      ← mul_assoc p p (star (u : A)), hp_idem]
    simpa only [mul_assoc] using hconj

end MathlibAnnex.Algebra
