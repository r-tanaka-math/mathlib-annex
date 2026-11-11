/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixAction

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {ι : Type v} [Fintype ι]
variable {B : NonUnitalStarSubalgebra ℂ A}

-- The actual finite matrix action equations define a norm-closed ambient set.
example (E : ι → ι → B →ₗ[ℂ] A) :
    IsClosed {a : A | ∃ M : CStarMatrix ι ι ℂ,
      (∀ i j b, a * E i j b = ∑ k, M k i • E k j b) ∧
      (∀ i j b, E i j b * a = ∑ k, M j k • E i k b)} :=
  isClosed_setOf_exists_actsOnMatrixCorners E

-- Passing to ambient norm closure preserves existence of an actual matrix coefficient.
example (E : ι → ι → B →ₗ[ℂ] A) {a : A}
    (ha : a ∈ closure {a : A | ∃ M : CStarMatrix ι ι ℂ, ActsOnMatrixCorners E a M}) :
    ∃ M : CStarMatrix ι ι ℂ, ActsOnMatrixCorners E a M := by
  rw [(isClosed_setOf_exists_actsOnMatrixCorners E).closure_eq] at ha
  exact ha

-- No injective/isometric entry-map hypothesis is hidden in the closedness statement.
example : IsClosed {a : A | ∃ M : CStarMatrix ι ι ℂ,
    ActsOnMatrixCorners (fun _ _ => (0 : B →ₗ[ℂ] A)) a M} :=
  isClosed_setOf_exists_actsOnMatrixCorners _

end MathlibAnnex.Analysis.CStarAlgebra
