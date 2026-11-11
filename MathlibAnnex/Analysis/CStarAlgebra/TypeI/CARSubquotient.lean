/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Basic

/-!
# Orthogonal hereditary corners from a square-zero element

The two positive elements are the actual products `x⋆x` and `xx⋆`. Their
orthogonality extends to the entire closed hereditary subalgebras, using two
norm-closure arguments with arbitrary ambient middle coefficients.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Orthogonality of the middle factors gives orthogonality of every pair of
elements of the two norm-closed sandwich algebras. -/
theorem mul_eq_zero_of_mem_hereditary_subalgebras {a b x y : A}
    (hab : star a * b = 0) (hx : x ∈ hereditarySubalgebra a)
    (hy : y ∈ hereditarySubalgebra b) : x * y = 0 := by
  have hraw (s : A) : (a * s * star a) * y = 0 := by
    apply closure_minimal
      (s := (sandwichSubalgebra b : Set A))
      (t := {z : A | (a * s * star a) * z = 0}) _ _ hy
    · rintro _ ⟨t, rfl⟩
      calc
        (a * s * star a) * (b * t * star b) =
            a * s * (star a * b) * t * star b := by simp only [mul_assoc]
        _ = 0 := by rw [hab]; simp only [mul_zero, zero_mul]
    · exact isClosed_eq (continuous_const.mul continuous_id) continuous_const
  apply closure_minimal
    (s := (sandwichSubalgebra a : Set A))
    (t := {z : A | z * y = 0}) _ _ hx
  · rintro _ ⟨s, rfl⟩
    exact hraw s
  · exact isClosed_eq (continuous_id.mul continuous_const) continuous_const

/-- A nonzero square-zero element supplies two nonzero positive orthogonal
elements by explicit multiplication, without any ambient unit. -/
theorem exists_nonzero_orthogonal_positive_elements_of_square_zero
    {x : A} (hx : x ≠ 0) (hxx : x * x = 0) :
    ∃ p q : A, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧ p * q = 0 ∧ q * p = 0 := by
  have hstar : star x * star x = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hxx
  refine ⟨star x * x, x * star x, star_mul_self_nonneg x,
    mul_star_self_nonneg x, ?_, ?_, ?_, ?_⟩
  · exact fun h => hx (star_mul_self_eq_zero.mp h)
  · exact fun h => hx (mul_star_self_eq_zero.mp h)
  · calc
      (star x * x) * (x * star x) = star x * (x * x) * star x := by
        simp only [mul_assoc]
      _ = 0 := by rw [hxx]; simp only [mul_zero, zero_mul]
  · calc
      (x * star x) * (star x * x) = x * (star x * star x) * x := by
        simp only [mul_assoc]
      _ = 0 := by rw [hstar]; simp only [mul_zero, zero_mul]

/-- A square-zero element already in a hereditary algebra splits off two
nonzero positive generators of smaller, mutually orthogonal hereditary
algebras. -/
theorem exists_orthogonal_hereditary_subalgebras_of_square_zero
    {a x : A} (hx : x ≠ 0) (hxx : x * x = 0)
    (hxa : x ∈ hereditarySubalgebra a) :
    ∃ p q : A, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧
      hereditarySubalgebra p ≤ hereditarySubalgebra a ∧
      hereditarySubalgebra q ≤ hereditarySubalgebra a ∧
      (∀ u ∈ hereditarySubalgebra p, ∀ v ∈ hereditarySubalgebra q, u * v = 0) ∧
      (∀ v ∈ hereditarySubalgebra q, ∀ u ∈ hereditarySubalgebra p, v * u = 0) := by
  have hp : 0 ≤ star x * x := star_mul_self_nonneg x
  have hq : 0 ≤ x * star x := mul_star_self_nonneg x
  have hpq : (star x * x) * (x * star x) = 0 := by
    calc
      _ = star x * (x * x) * star x := by simp only [mul_assoc]
      _ = 0 := by rw [hxx]; simp only [mul_zero, zero_mul]
  have hqp : (x * star x) * (star x * x) = 0 := by
    have h := congrArg star hpq
    rw [star_mul, hq.star_eq, hp.star_eq, star_zero] at h
    exact h
  have hstar : star x ∈ hereditarySubalgebra a := star_mem hxa
  refine ⟨star x * x, x * star x, hp, hq,
    (fun h => hx (star_mul_self_eq_zero.mp h)),
    (fun h => hx (mul_star_self_eq_zero.mp h)), ?_, ?_, ?_, ?_⟩
  · exact hereditarySubalgebra_le_of_mem
      ((hereditarySubalgebra a).mul_mem hstar hxa)
  · exact hereditarySubalgebra_le_of_mem
      ((hereditarySubalgebra a).mul_mem hxa hstar)
  · intro u hu v hv
    exact mul_eq_zero_of_mem_hereditary_subalgebras
      (by simpa only [hp.star_eq] using hpq) hu hv
  · intro v hv u hu
    exact mul_eq_zero_of_mem_hereditary_subalgebras
      (by simpa only [hq.star_eq] using hqp) hv hu

end MathlibAnnex.Analysis.CStarAlgebra
