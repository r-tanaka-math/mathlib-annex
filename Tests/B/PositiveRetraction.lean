import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveRetraction

set_option autoImplicit false

open scoped CStarAlgebra ComplexOrder
open MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

example (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] (E : A →P[ℂ] D)
    (hfix : ∀ d : D, E (d : A) = d)
    (hbi : ∀ (d e : D) (a : A), E ((d : A) * a * (e : A)) = d * E a * e)
    (a : A) : star (E a) * E a ≤ E (star a * a) :=
  star_mul_le_of_positive_bimodule_retraction D E hfix hbi a

example (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] (E : A →P[ℂ] D)
    (hfix : ∀ d : D, E (d : A) = d)
    (hbi : ∀ (d e : D) (a : A), E ((d : A) * a * (e : A)) = d * E a * e)
    (a : A) : ‖E a‖ ≤ ‖a‖ :=
  norm_le_of_positive_bimodule_retraction D E hfix hbi a
