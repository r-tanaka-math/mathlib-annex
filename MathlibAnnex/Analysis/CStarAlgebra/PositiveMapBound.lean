import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# A uniform elementary bound for unital positive maps

This file isolates the dimension-free estimate used by finite-row averaging.
It uses Mathlib's four-positive-parts decomposition and does not add a
contractivity hypothesis.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]

/-- A unital positive complex-linear map has the elementary uniform bound `4`.
This deliberately uses only the standard four-positive-parts decomposition. -/
theorem norm_apply_le_four (f : A →ₚ[ℂ] B) (hf : f 1 = 1) (a : A) :
    ‖f a‖ ≤ 4 * ‖a‖ := by
  obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul]
  apply (norm_sum_le _ _).trans
  have hI : ‖(Complex.I : ℂ)‖ = 1 := by norm_num
  simp only [norm_smul, norm_pow, hI, one_pow, one_mul]
  calc
    ∑ i : Fin 4, ‖f (y i)‖ ≤ ∑ _i : Fin 4, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖f (y i)‖ ≤ ‖f 1‖ * ‖y i‖ := f.norm_apply_le_of_nonneg _ (hy_nonneg i)
        _ ≤ 1 * ‖a‖ := by rw [hf, norm_one]; gcongr; exact hy_norm i
        _ = ‖a‖ := one_mul _
    _ = 4 * ‖a‖ := by simp

end MathlibAnnex.CStarAlgebra
