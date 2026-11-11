/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARSubquotient

set_option autoImplicit false
open MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example {x : A} (hx : x ≠ 0) (hxx : x * x = 0) :
    ∃ p q : A, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧ p * q = 0 ∧ q * p = 0 :=
  exists_nonzero_orthogonal_positive_elements_of_square_zero (A := A) hx hxx

example {a b x y : A} (hab : star a * b = 0)
    (hx : x ∈ hereditarySubalgebra a) (hy : y ∈ hereditarySubalgebra b) : x * y = 0 :=
  mul_eq_zero_of_mem_hereditary_subalgebras (A := A) hab hx hy

example {a x : A} (hx : x ≠ 0) (hxx : x * x = 0)
    (hxa : x ∈ hereditarySubalgebra a) :
    ∃ p q : A, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧
      hereditarySubalgebra p ≤ hereditarySubalgebra a ∧
      hereditarySubalgebra q ≤ hereditarySubalgebra a ∧
      (∀ u ∈ hereditarySubalgebra p, ∀ v ∈ hereditarySubalgebra q, u * v = 0) ∧
      (∀ v ∈ hereditarySubalgebra q, ∀ u ∈ hereditarySubalgebra p, v * u = 0) :=
  exists_orthogonal_hereditary_subalgebras_of_square_zero (A := A) hx hxx hxa
