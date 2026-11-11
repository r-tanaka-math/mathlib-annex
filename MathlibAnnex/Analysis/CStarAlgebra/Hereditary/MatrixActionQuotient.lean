/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixAction
import Mathlib.Algebra.Star.BigOperators

/-!
# The actual finite matrix-action quotient

For a nonzero family of matrix corners, the ambient elements acting on both
sides by a scalar matrix form a norm-closed non-unital star subalgebra. The
matrix is unique, by multiplication against one nonzero corner coefficient.
Consequently the matrix-action map is an actual star homomorphism. Explicit
local-unit coefficients make it onto without requiring projections in the
ambient algebra.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {B : NonUnitalStarSubalgebra ℂ A}
variable (E : ι → ι → B →ₗ[ℂ] A)

theorem ActsOnMatrixCorners.zero : ActsOnMatrixCorners E 0 0 := by
  constructor <;> intro i j b <;> simp

theorem ActsOnMatrixCorners.add {a b : A} {M N : CStarMatrix ι ι ℂ}
    (ha : ActsOnMatrixCorners E a M) (hb : ActsOnMatrixCorners E b N) :
    ActsOnMatrixCorners E (a + b) (M + N) := by
  constructor
  · intro i j x
    simp only [add_mul, ha.1, hb.1, CStarMatrix.add_apply, add_smul,
      Finset.sum_add_distrib]
  · intro i j x
    simp only [mul_add, ha.2, hb.2, CStarMatrix.add_apply, add_smul,
      Finset.sum_add_distrib]

theorem ActsOnMatrixCorners.smul {a : A} {M : CStarMatrix ι ι ℂ}
    (ha : ActsOnMatrixCorners E a M) (z : ℂ) :
    ActsOnMatrixCorners E (z • a) (z • M) := by
  constructor
  · intro i j b
    simp only [smul_mul_assoc, ha.1, Finset.smul_sum, CStarMatrix.smul_apply,
      smul_eq_mul, smul_smul]
  · intro i j b
    simp only [mul_smul_comm, ha.2, Finset.smul_sum, CStarMatrix.smul_apply,
      smul_eq_mul, smul_smul]

theorem ActsOnMatrixCorners.mul {a b : A} {M N : CStarMatrix ι ι ℂ}
    (ha : ActsOnMatrixCorners E a M) (hb : ActsOnMatrixCorners E b N) :
    ActsOnMatrixCorners E (a * b) (M * N) := by
  constructor
  · intro i j x
    calc
      (a * b) * E i j x = a * (b * E i j x) := mul_assoc _ _ _
      _ = ∑ k, N k i • (a * E k j x) := by
        rw [hb.1]
        simp only [Finset.mul_sum, mul_smul_comm]
      _ = ∑ k, ∑ l, (N k i * M l k) • E l j x := by
        simp only [ha.1, Finset.smul_sum, smul_smul]
      _ = ∑ l, ∑ k, (M l k * N k i) • E l j x := by
        rw [Finset.sum_comm]
        simp only [mul_comm]
      _ = ∑ l, (M * N) l i • E l j x := by
        simp only [CStarMatrix.mul_apply, Finset.sum_smul]
  · intro i j x
    calc
      E i j x * (a * b) = (E i j x * a) * b := (mul_assoc _ _ _).symm
      _ = ∑ k, M j k • (E i k x * b) := by
        rw [ha.2]
        simp only [Finset.sum_mul, smul_mul_assoc]
      _ = ∑ k, ∑ l, (M j k * N k l) • E i l x := by
        simp only [hb.2, Finset.smul_sum, smul_smul]
      _ = ∑ l, ∑ k, (M j k * N k l) • E i l x := Finset.sum_comm
      _ = ∑ l, (M * N) j l • E i l x := by
        simp only [CStarMatrix.mul_apply, Finset.sum_smul]

theorem ActsOnMatrixCorners.star
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    {a : A} {M : CStarMatrix ι ι ℂ} (ha : ActsOnMatrixCorners E a M) :
    ActsOnMatrixCorners E (star a) (star M) := by
  constructor
  · intro i j b
    have h := congrArg Star.star (ha.2 j i (Star.star b))
    simpa only [star_mul, hstar, star_star, star_sum, star_smul,
      CStarMatrix.star_apply] using h
  · intro i j b
    have h := congrArg Star.star (ha.1 j i (Star.star b))
    simpa only [star_mul, hstar, star_star, star_sum, star_smul,
      CStarMatrix.star_apply] using h

/-- Ambient elements whose two-sided action on the actual corner family is a
scalar matrix. This is a subalgebra of the original `A`, not an abstract
algebra with a newly assigned norm. -/
def matrixActionSubalgebra
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b)) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a | ∃ M, ActsOnMatrixCorners E a M}
  zero_mem' := ⟨0, ActsOnMatrixCorners.zero E⟩
  add_mem' := by
    rintro a b ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨M + N, ActsOnMatrixCorners.add E hM hN⟩
  mul_mem' := by
    rintro a b ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨M * N, ActsOnMatrixCorners.mul E hM hN⟩
  smul_mem' := by
    rintro z a ⟨M, hM⟩
    exact ⟨z • M, ActsOnMatrixCorners.smul E hM z⟩
  star_mem' := by
    rintro a ⟨M, hM⟩
    exact ⟨star M, ActsOnMatrixCorners.star E hstar hM⟩

instance isClosed_matrixActionSubalgebra
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b)) :
    IsClosed (matrixActionSubalgebra E hstar : Set A) :=
  isClosed_setOf_exists_actsOnMatrixCorners E

/-- Multiplication by one column and one row recovers each matrix entry. -/
theorem ActsOnMatrixCorners.sandwich_eq
    (hmul : ∀ i j k l b c,
      E i j b * E k l c = if j = k then E i l (b * c) else 0)
    {a : A} {M : CStarMatrix ι ι ℂ} (ha : ActsOnMatrixCorners E a M)
    (r i j : ι) (b : B) :
    E r i (Star.star b) * a * E j r b = M i j • E r r (Star.star b * b) := by
  calc
    E r i (Star.star b) * a * E j r b =
        E r i (Star.star b) * (a * E j r b) := mul_assoc _ _ _
    _ = ∑ k, M k j • (E r i (Star.star b) * E k r b) := by
      rw [ha.1]
      simp only [Finset.mul_sum, mul_smul_comm]
    _ = M i j • E r r (Star.star b * b) := by
      simp only [hmul, smul_ite, smul_zero]
      simp

/-- A nonzero corner determines the scalar action matrix uniquely. -/
theorem ActsOnMatrixCorners.matrix_eq [Nonempty ι]
    (hmul : ∀ i j k l b c,
      E i j b * E k l c = if j = k then E i l (b * c) else 0)
    (hnorm : ∀ i j b, ‖E i j b‖ = ‖b‖)
    (b : B) (hb : b ≠ 0)
    {a : A} {M N : CStarMatrix ι ι ℂ}
    (hM : ActsOnMatrixCorners E a M) (hN : ActsOnMatrixCorners E a N) : M = N := by
  let r : ι := Classical.choice inferInstance
  have hd : E r r (Star.star b * b) ≠ 0 := by
    intro h
    have hbb : Star.star b * b = 0 := by
      apply norm_eq_zero.mp
      rw [← hnorm r r (Star.star b * b), h, norm_zero]
    have hbbA : Star.star (b : A) * (b : A) = 0 := congrArg Subtype.val hbb
    exact hb (Subtype.ext (star_mul_self_eq_zero.mp hbbA))
  apply CStarMatrix.ext
  intro i j
  have h : M i j • E r r (Star.star b * b) = N i j • E r r (Star.star b * b) :=
    (ActsOnMatrixCorners.sandwich_eq E hmul hM r i j b).symm.trans
      (ActsOnMatrixCorners.sandwich_eq E hmul hN r i j b)
  apply sub_eq_zero.mp
  have hz : (M i j - N i j) • E r r (Star.star b * b) = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_right hd

/-- Choose the uniquely determined matrix on the actual action subalgebra. -/
def matrixActionMatrix
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    (a : matrixActionSubalgebra E hstar) : CStarMatrix ι ι ℂ :=
  Classical.choose a.property

theorem actsOnMatrixCorners_matrixActionMatrix
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    (a : matrixActionSubalgebra E hstar) :
    ActsOnMatrixCorners E (a : A) (matrixActionMatrix E hstar a) :=
  Classical.choose_spec a.property

/-- The finite action quotient is an actual non-unital star hom. Its domain
has the inherited norm and the closedness proved above. -/
def matrixActionQuotient [Nonempty ι]
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    (hmul : ∀ i j k l b c,
      E i j b * E k l c = if j = k then E i l (b * c) else 0)
    (hnorm : ∀ i j b, ‖E i j b‖ = ‖b‖) (b : B) (hb : b ≠ 0) :
    matrixActionSubalgebra E hstar →⋆ₙₐ[ℂ] CStarMatrix ι ι ℂ where
  toFun := matrixActionMatrix E hstar
  map_zero' := ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionMatrix E hstar 0) (ActsOnMatrixCorners.zero E)
  map_add' a c := ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionMatrix E hstar (a + c))
    (ActsOnMatrixCorners.add E (actsOnMatrixCorners_matrixActionMatrix E hstar a)
      (actsOnMatrixCorners_matrixActionMatrix E hstar c))
  map_mul' a c := ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionMatrix E hstar (a * c))
    (ActsOnMatrixCorners.mul E (actsOnMatrixCorners_matrixActionMatrix E hstar a)
      (actsOnMatrixCorners_matrixActionMatrix E hstar c))
  map_smul' z a := ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionMatrix E hstar (z • a))
    (ActsOnMatrixCorners.smul E (actsOnMatrixCorners_matrixActionMatrix E hstar a) z)
  map_star' a := ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionMatrix E hstar (star a))
    (ActsOnMatrixCorners.star E hstar (actsOnMatrixCorners_matrixActionMatrix E hstar a))

theorem actsOnMatrixCorners_matrixActionQuotient [Nonempty ι]
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    (hmul : ∀ i j k l b c,
      E i j b * E k l c = if j = k then E i l (b * c) else 0)
    (hnorm : ∀ i j b, ‖E i j b‖ = ‖b‖) (b : B) (hb : b ≠ 0)
    (a : matrixActionSubalgebra E hstar) :
    ActsOnMatrixCorners E (a : A) (matrixActionQuotient E hstar hmul hnorm b hb a) :=
  actsOnMatrixCorners_matrixActionMatrix E hstar a

/-- A finite family of local-unit coefficients acts onto all scalar matrices.
The coefficients are not assumed idempotent and need not be matrix units in
the original algebra. Only their action on the smaller core is used. -/
theorem matrixActionQuotient_surjective [Nonempty ι]
    (hstar : ∀ i j b, star (E i j b) = E j i (Star.star b))
    (hmul : ∀ i j k l b c,
      E i j b * E k l c = if j = k then E i l (b * c) else 0)
    (hnorm : ∀ i j b, ‖E i j b‖ = ‖b‖) (b : B) (hb : b ≠ 0)
    (u : ι → ι → A)
    (hleft : ∀ i j k l z,
      u i j * E k l z = if j = k then E i l z else 0)
    (hright : ∀ i j k l z,
      E k l z * u i j = if l = i then E k j z else 0) :
    Function.Surjective (matrixActionQuotient E hstar hmul hnorm b hb) := by
  intro M
  let a : A := ∑ i, ∑ j, M i j • u i j
  have ha : ActsOnMatrixCorners E a M := by
    constructor
    · intro k l z
      simp [a, Finset.sum_mul, smul_mul_assoc, hleft]
    · intro k l z
      simp [a, Finset.mul_sum, mul_smul_comm, hright]
  refine ⟨⟨a, ⟨M, ha⟩⟩, ?_⟩
  exact ActsOnMatrixCorners.matrix_eq E hmul hnorm b hb
    (actsOnMatrixCorners_matrixActionQuotient E hstar hmul hnorm b hb _) ha

end MathlibAnnex.Analysis.CStarAlgebra
