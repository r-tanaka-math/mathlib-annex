import Mathlib.Algebra.Star.Unitary

/-!
# Exact shell matching

The algebraic tail of shell matching.  Once two projection shells are exactly
unitarily matched after an auxiliary conjugation, the displayed link has both
required support identities.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra

variable {A : Type*} [Semiring A] [StarRing A]

/-- The partial-isometry link obtained after exact matching of two shells. -/
def matchedLink (g t : unitary A) (e : A) : A :=
  star (g : A) * (t : A) * e

/-- If `t` takes `e` to the conjugate of `f` by `g`, then `g⁺ t e` has initial
support `e` and final support `f`. -/
theorem matchedLink_supports (g t : unitary A) (e f : A)
    (he : IsStarProjection e)
    (hmatch : (t : A) * e * star (t : A) = (g : A) * f * star (g : A)) :
    star (matchedLink g t e) * matchedLink g t e = e ∧
      matchedLink g t e * star (matchedLink g t e) = f := by
  constructor
  · simp only [matchedLink, star_mul, star_star, he.isSelfAdjoint.star_eq, mul_assoc]
    rw [← mul_assoc (g : A) (star (g : A)) ((t : A) * e),
      Unitary.mul_star_self_of_mem g.prop, one_mul,
      ← mul_assoc (star (t : A)) (t : A) e,
      Unitary.star_mul_self_of_mem t.prop, one_mul, he.isIdempotentElem.eq]
  · calc
      matchedLink g t e * star (matchedLink g t e) =
          star (g : A) * ((t : A) * e * star (t : A)) * (g : A) := by
            simp only [matchedLink, star_mul, star_star, he.isSelfAdjoint.star_eq]
            rw [mul_assoc (star (g : A) * (t : A)) e
              (e * (star (t : A) * (g : A)))]
            rw [← mul_assoc e e (star (t : A) * (g : A)), he.isIdempotentElem.eq]
            simp only [mul_assoc]
      _ = star (g : A) * ((g : A) * f * star (g : A)) * (g : A) := by rw [hmatch]
      _ = f := by
        simp only [mul_assoc]
        rw [Unitary.star_mul_self_of_mem g.prop, mul_one,
          ← mul_assoc (star (g : A)) (g : A) f,
          Unitary.star_mul_self_of_mem g.prop, one_mul]

end MathlibAnnex.CStarAlgebra
