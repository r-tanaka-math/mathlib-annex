import Mathlib.Algebra.Star.Unitary

/-!
The algebraic tail of exact shell matching. Existence of the unitaries is not
asserted here; when they are supplied, both support identities follow.
-/

set_option autoImplicit false

namespace MathlibAnnex.Algebra

variable {A : Type*} [Semiring A] [StarRing A]

/-- The partial-isometry link obtained after exact matching of two shells. -/
def matchedLink (g t : unitary A) (e : A) : A :=
  star (g : A) * (t : A) * e

/--
If `t` transports the initial shell `e` to the conjugate of `f` by `g`, then
`g⁺ t e` has initial support `e` and final support `f`.
-/
theorem matchedLink_supports (g t : unitary A) (e f : A)
    (he_star : star e = e) (he_idem : e * e = e)
    (hmatch : (t : A) * e * star (t : A) = (g : A) * f * star (g : A)) :
    star (matchedLink g t e) * matchedLink g t e = e ∧
      matchedLink g t e * star (matchedLink g t e) = f := by
  constructor
  · simp only [matchedLink, star_mul, star_star, he_star, mul_assoc]
    rw [← mul_assoc (g : A) (star (g : A)) ((t : A) * e),
      Unitary.mul_star_self_of_mem g.prop, one_mul,
      ← mul_assoc (star (t : A)) (t : A) e,
      Unitary.star_mul_self_of_mem t.prop, one_mul, he_idem]
  · calc
      matchedLink g t e * star (matchedLink g t e) =
          star (g : A) * ((t : A) * e * star (t : A)) * (g : A) := by
            simp only [matchedLink, star_mul, star_star, he_star]
            rw [mul_assoc (star (g : A) * (t : A)) e
              (e * (star (t : A) * (g : A)))]
            rw [← mul_assoc e e (star (t : A) * (g : A)), he_idem]
            simp only [mul_assoc]
      _ = star (g : A) * ((g : A) * f * star (g : A)) * (g : A) := by rw [hmatch]
      _ = f := by
        simp only [mul_assoc]
        rw [Unitary.star_mul_self_of_mem g.prop, mul_one,
          ← mul_assoc (star (g : A)) (g : A) f,
          Unitary.star_mul_self_of_mem g.prop, one_mul]

end MathlibAnnex.Algebra
