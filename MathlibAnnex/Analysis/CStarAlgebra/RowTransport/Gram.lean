import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Average
import MathlibAnnex.Analysis.CStarAlgebra.VectorGram
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! The transformed finite family obeys a Hilbert-space budget from the
represented row square, not from the sum of squared norms of row entries. -/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem sum_norm_sq_map_star_eq_rowSquare
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {n : ℕ} (x : Fin n → A) :
    ∑ i, ‖pi (star (x i)) ξ‖ ^ 2 =
      (Representation.vectorFunctional pi ξ
        (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)).re := by
  calc
    ∑ i, ‖pi (star (x i)) ξ‖ ^ 2 =
        ∑ i, (inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ)).re := by
          apply Finset.sum_congr rfl
          intro i _
          exact norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∑ i, inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ)).re := by
          simp only [Complex.re_sum]
    _ = _ := by
          rw [Representation.sum_inner_map_star_self]
          rfl

/-- A contractive row square gives the Gram theorem's total-squared-norm
budget for every unit vector, despite a potentially larger entry norm sum. -/
theorem sum_norm_sq_map_star_le_one
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {n : ℕ} (x : Fin n → A) (hξ : ‖ξ‖ = 1)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1) :
    ∑ i, ‖pi (star (x i)) ξ‖ ^ 2 ≤ 1 := by
  let q := MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x
  have hpiq : ‖pi q‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le pi q).trans hq
  have happly : ‖pi q ξ‖ ≤ ‖ξ‖ := by
    calc
      ‖pi q ξ‖ ≤ ‖pi q‖ * ‖ξ‖ := (pi q).le_opNorm ξ
      _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right hpiq (norm_nonneg ξ)
      _ = ‖ξ‖ := one_mul _
  rw [sum_norm_sq_map_star_eq_rowSquare]
  change (inner ℂ ξ (pi q ξ)).re ≤ 1
  calc
    (inner ℂ ξ (pi q ξ)).re ≤ ‖inner ℂ ξ (pi q ξ)‖ := Complex.re_le_norm _
    _ ≤ ‖ξ‖ * ‖pi q ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * ‖ξ‖ := mul_le_mul_of_nonneg_left happly (norm_nonneg ξ)
    _ = 1 := by rw [hξ]; norm_num

end MathlibAnnex.Analysis.CStarAlgebra
