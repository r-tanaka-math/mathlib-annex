import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Schwarz and norm estimates for positive bimodule retractions

Positivity of the square of `a - E a`, together with the actual bimodule
identities and pointwise retraction equation, gives the Schwarz inequality.
The C-star identity then gives contractivity. No normality, complete
positivity, or norm bound is assumed.
-/

set_option autoImplicit false

open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Schwarz follows from positivity and bimodularity of a retraction onto
a closed star subalgebra. -/
theorem star_mul_le_of_positive_bimodule_retraction
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] (E : A →P[ℂ] D)
    (hfix : ∀ d : D, E (d : A) = d)
    (hbi : ∀ (d e : D) (a : A), E ((d : A) * a * (e : A)) = d * E a * e)
    (a : A) : star (E a) * E a ≤ E (star a * a) := by
  letI : StarOrderedRing D := Subtype.starOrderedRing (𝕜 := ℂ) D
  have hleft : E (star (E a : A) * a) = star (E a) * E a := by
    simpa only [OneMemClass.coe_one, StarMemClass.coe_star, mul_one] using hbi (star (E a)) 1 a
  have hright : E (star a * (E a : A)) = star (E a) * E a := by
    simpa only [OneMemClass.coe_one, one_mul, map_star] using hbi 1 (E a) (star a)
  have hsquare : E (star (E a : A) * (E a : A)) = star (E a) * E a :=
    hfix (star (E a) * E a)
  have hexpand : E (star (a - (E a : A)) * (a - (E a : A))) =
      E (star a * a) - star (E a) * E a := by
    simp only [star_sub, sub_mul, mul_sub, map_sub]
    rw [hleft, hright, hsquare]
    abel
  have hpositive := map_nonneg E (star_mul_self_nonneg (a - (E a : A)))
  rw [hexpand] at hpositive
  exact sub_nonneg.mp hpositive

/-- Contractivity is proved from the Schwarz estimate and the existing
positive-input norm bound. The trivial algebra is treated explicitly. -/
theorem norm_le_of_positive_bimodule_retraction
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] (E : A →P[ℂ] D)
    (hfix : ∀ d : D, E (d : A) = d)
    (hbi : ∀ (d e : D) (a : A), E ((d : A) * a * (e : A)) = d * E a * e)
    (a : A) : ‖E a‖ ≤ ‖a‖ := by
  letI : StarOrderedRing D := Subtype.starOrderedRing (𝕜 := ℂ) D
  rcases subsingleton_or_nontrivial D with h | h
  · letI := h
    rw [Subsingleton.elim (E a) 0, norm_zero]
    exact norm_nonneg a
  · letI := h
    have hone : E 1 = 1 := hfix 1
    have hsquare : ‖E a‖ * ‖E a‖ ≤ ‖a‖ * ‖a‖ := by
      calc
        ‖E a‖ * ‖E a‖ = ‖star (E a) * E a‖ :=
          (CStarRing.norm_star_mul_self (x := E a)).symm
        _ ≤ ‖E (star a * a)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (star_mul_le_of_positive_bimodule_retraction D E hfix hbi a)
          (star_mul_self_nonneg (E a))
        _ ≤ ‖E 1‖ * ‖star a * a‖ :=
          E.toPositiveLinearMap.norm_apply_le_of_nonneg _ (star_mul_self_nonneg a)
        _ = ‖a‖ * ‖a‖ := by rw [hone, norm_one, one_mul, CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (E a), norm_nonneg a]

end MathlibAnnex.Analysis.CStarAlgebra
