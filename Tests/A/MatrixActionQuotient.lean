/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixActionQuotient

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators CStarAlgebra ComplexOrder
open MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {B : NonUnitalStarSubalgebra ℂ A}
variable (E : ι → ι → B →ₗ[ℂ] A)
variable (hstar : ∀ i j b, star (E i j b) = E j i (star b))
variable (hmul : ∀ i j k l b c,
  E i j b * E k l c = if j = k then E i l (b * c) else 0)
variable (hnorm : ∀ i j b, ‖E i j b‖ = ‖b‖)
variable (b : B) (hb : b ≠ 0)

-- The domain really is a closed subalgebra of the arbitrary original A.
example : IsClosed (matrixActionSubalgebra E hstar : Set A) := inferInstance

-- The selected matrix is identified by its actual action, not a chosen norm.
example (a : matrixActionSubalgebra E hstar) (M : CStarMatrix ι ι ℂ)
    (hM : ActsOnMatrixCorners E (a : A) M) :
    matrixActionQuotient E hstar hmul hnorm b hb a = M :=
  ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionQuotient E hstar hmul hnorm b hb a) hM

-- Contractivity follows from the existing C* hom theorem and the original norm.
example (a : matrixActionSubalgebra E hstar) :
    ‖matrixActionQuotient E hstar hmul hnorm b hb a‖ ≤ ‖(a : A)‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matrixActionQuotient E hstar hmul hnorm b hb) a

-- These u_ij only act as elementary matrices on the core; no u_ii^2=u_ii is assumed.
example (u : ι → ι → A)
    (hleft : ∀ i j k l z, u i j * E k l z = if j = k then E i l z else 0)
    (hright : ∀ i j k l z, E k l z * u i j = if l = i then E k j z else 0) :
    Function.Surjective (matrixActionQuotient E hstar hmul hnorm b hb) :=
  matrixActionQuotient_surjective E hstar hmul hnorm b hb u hleft hright

example (a c : matrixActionSubalgebra E hstar) :
    matrixActionQuotient E hstar hmul hnorm b hb (star a * c) =
      star (matrixActionQuotient E hstar hmul hnorm b hb a) *
        matrixActionQuotient E hstar hmul hnorm b hb c := by
  rw [map_mul, map_star]

