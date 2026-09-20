import MathlibAnnex.Analysis.CStarAlgebra.RowPerturbation
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Finite rows corrected by a multiplier in the unitization

The correction may have nonzero scalar coordinate, but its product with a
row component lies in the original nonunital ideal.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

universe u

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def unitizationLeftMul (b : Unitization ℂ A) (x : A) : A :=
  b.fst • x + b.snd * x

@[simp] theorem inr_unitizationLeftMul (b : Unitization ℂ A) (x : A) :
    ((unitizationLeftMul A b x : A) : Unitization ℂ A) =
      b * (x : Unitization ℂ A) := by
  apply Unitization.ext
  · simp [unitizationLeftMul]
  · simp [unitizationLeftMul]

theorem rowSquare_unitizationLeftMul {n : ℕ}
    (b : Unitization ℂ A) (x : Fin n → A) :
    ((rowSquare A (fun i => unitizationLeftMul A b (x i)) : A) : Unitization ℂ A) =
      b * (rowSquare A x : Unitization ℂ A) * star b := by
  have hrow (y : Fin n → A) :
      ((rowSquare A y : A) : Unitization ℂ A) =
        rowSquare (Unitization ℂ A) (fun i => (y i : Unitization ℂ A)) := by
    change (Unitization.inrNonUnitalStarAlgHom ℂ A)
        (∑ i, y i * star (y i)) =
      ∑ i, (Unitization.inrNonUnitalStarAlgHom ℂ A) (y i) *
        star ((Unitization.inrNonUnitalStarAlgHom ℂ A) (y i))
    simp only [map_sum, map_mul, map_star]
  rw [hrow, hrow]
  simp only [inr_unitizationLeftMul]
  exact rowSquare_left_mul (Unitization ℂ A) (fun i => (x i : Unitization ℂ A)) b

theorem rowMap_unitizationLeftMul {n : ℕ}
    (b : Unitization ℂ A) (x : Fin n → A) (z : A) :
    ((rowMap A (fun i => unitizationLeftMul A b (x i)) z : A) : Unitization ℂ A) =
      b * (rowMap A x z : Unitization ℂ A) * star b := by
  have hmap (y : Fin n → A) :
      ((rowMap A y z : A) : Unitization ℂ A) =
        rowMap (Unitization ℂ A)
          (fun i => (y i : Unitization ℂ A)) (z : Unitization ℂ A) := by
    rw [rowMap_apply, rowMap_apply]
    change (Unitization.inrNonUnitalStarAlgHom ℂ A)
        (∑ i, y i * z * star (y i)) =
      ∑ i, (Unitization.inrNonUnitalStarAlgHom ℂ A) (y i) *
        (Unitization.inrNonUnitalStarAlgHom ℂ A) z *
        star ((Unitization.inrNonUnitalStarAlgHom ℂ A) (y i))
    simp only [map_sum, map_mul, map_star]
  rw [hmap, hmap]
  simp only [inr_unitizationLeftMul]
  exact rowMap_left_mul (Unitization ℂ A)
    (fun i => (x i : Unitization ℂ A)) b (z : Unitization ℂ A)

theorem norm_rowMap_unitizationLeftMul_sub_le {n : ℕ}
    (b : Unitization ℂ A) (x : Fin n → A) (z : A) :
    ‖rowMap A (fun i => unitizationLeftMul A b (x i)) z - rowMap A x z‖ ≤
      (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap A x z‖ := by
  calc
    ‖rowMap A (fun i => unitizationLeftMul A b (x i)) z - rowMap A x z‖ =
        ‖((rowMap A (fun i => unitizationLeftMul A b (x i)) z -
            rowMap A x z : A) : Unitization ℂ A)‖ :=
      (Unitization.norm_inr _).symm
    _ = ‖b * (rowMap A x z : Unitization ℂ A) * star b -
          (rowMap A x z : Unitization ℂ A)‖ := by
      rw [Unitization.inr_sub, rowMap_unitizationLeftMul]
    _ ≤ (‖b - 1‖ * ‖b‖ + ‖b - 1‖) *
          ‖(rowMap A x z : Unitization ℂ A)‖ :=
      norm_conjugate_sub_le (Unitization ℂ A) b _
    _ = (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap A x z‖ := by
      rw [Unitization.norm_inr]

theorem norm_commutator_rowMap_unitizationLeftMul_le_budget {n : ℕ}
    (b : Unitization ℂ A) (x : Fin n → A) (a z : A)
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖a * rowMap A (fun i => unitizationLeftMul A b (x i)) z -
        rowMap A (fun i => unitizationLeftMul A b (x i)) z * a‖ ≤
      ‖a * rowMap A x z - rowMap A x z * a‖ +
        2 * ‖a‖ * ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖) := by
  have hrow : ‖rowMap A x z‖ ≤ ‖z‖ := by
    calc
      ‖rowMap A x z‖ ≤ ‖rowMap A x‖ * ‖z‖ := (rowMap A x).le_opNorm z
      _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_rowMap_le_one A x hx) (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  calc
    _ ≤ ‖a * rowMap A x z - rowMap A x z * a‖ +
        2 * ‖a‖ *
          ‖rowMap A (fun i => unitizationLeftMul A b (x i)) z - rowMap A x z‖ :=
      norm_commutator_le_of_sub A a _ _
    _ ≤ ‖a * rowMap A x z - rowMap A x z * a‖ +
        2 * ‖a‖ *
          ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap A x z‖) := by
      gcongr
      exact norm_rowMap_unitizationLeftMul_sub_le A b x z
    _ ≤ ‖a * rowMap A x z - rowMap A x z * a‖ +
        2 * ‖a‖ * ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖) := by
      gcongr

end MathlibAnnex.CStarAlgebra.TensorAveraging
