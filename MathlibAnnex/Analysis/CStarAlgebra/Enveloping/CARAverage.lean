import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteAverage
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Finite matrix averages in an arbitrary representation of CAR

The existing continuous sandwich operator is applied to the represented
matrix column. Its argument is an arbitrary element of the target algebra,
not only an element of the represented CAR range. This distinction is needed
when constructing a retraction on all of `B(H)`.

The matrix-unit calculation adapts `CAR.limitMatrixUnit_commute_rowAverage`;
matrix units, their normalization, and the positive continuous row map are
reused from the public providers.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

universe u

variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Average an arbitrary target element with the represented matrix column. -/
def representedRowAverage (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) : B →P[ℂ] B :=
  PositiveContinuousLinearMap.mk₀
    (TensorAveraging.rowMap B (fun i : Fin (2 ^ n) => rho (limitMatrixUnit n i 0)))
    (fun b hb => TensorAveraging.rowMap_nonneg B _ hb)

@[simp]
theorem representedRowAverage_apply (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (b : B) :
    representedRowAverage rho n b =
      ∑ i : Fin (2 ^ n), rho (limitMatrixUnit n i 0) * b *
        rho (limitMatrixUnit n 0 i) := by
  simp only [representedRowAverage, PositiveContinuousLinearMap.mk₀_apply,
    TensorAveraging.rowMap_apply, ← map_star, star_limitMatrixUnit]

@[simp]
theorem representedRowAverage_one (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) :
    representedRowAverage rho n 1 = 1 := by
  simpa only [representedRowAverage_apply, mul_one, ← map_star,
    star_limitMatrixUnit] using map_row_isometry_sum rho n

/-- Every value of the average commutes with every represented matrix unit
at the stage used for averaging. -/
theorem limitMatrixUnit_commute_representedRowAverage
    (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (k l : Fin (2 ^ n)) (b : B) :
    rho (limitMatrixUnit n k l) * representedRowAverage rho n b =
      representedRowAverage rho n b * rho (limitMatrixUnit n k l) := by
  classical
  calc
    rho (limitMatrixUnit n k l) * representedRowAverage rho n b =
        ∑ i : Fin (2 ^ n), rho (limitMatrixUnit n k l) *
          (rho (limitMatrixUnit n i 0) * b * rho (limitMatrixUnit n 0 i)) := by
            rw [representedRowAverage_apply, Finset.mul_sum]
    _ = rho (limitMatrixUnit n k 0) * b * rho (limitMatrixUnit n 0 l) := by
      rw [Finset.sum_eq_single l]
      · simp [← mul_assoc, ← map_mul]
      · intro i _ hil
        have hli : l ≠ i := Ne.symm hil
        simp [← mul_assoc, ← map_mul, hli]
      · simp
    _ = ∑ i : Fin (2 ^ n),
        (rho (limitMatrixUnit n i 0) * b * rho (limitMatrixUnit n 0 i)) *
          rho (limitMatrixUnit n k l) := by
      rw [Finset.sum_eq_single k]
      · simp [mul_assoc, ← map_mul]
      · intro i _ hik
        simp [mul_assoc, ← map_mul, hik]
      · simp
    _ = representedRowAverage rho n b * rho (limitMatrixUnit n k l) := by
      rw [representedRowAverage_apply, Finset.sum_mul]

theorem ofStage_commute_representedRowAverage
    (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (c : Stage n) (b : B) :
    rho (ofStage n c) * representedRowAverage rho n b =
      representedRowAverage rho n b * rho (ofStage n c) := by
  rw [ofStage_eq_sum_smul_limitMatrixUnit]
  simp only [map_sum, map_smul]
  apply (Commute.sum_left Finset.univ _ _ fun i _ =>
    Commute.sum_left Finset.univ _ _ fun j _ => ?_).eq
  exact (show Commute (rho (limitMatrixUnit n i j)) (representedRowAverage rho n b)
    from limitMatrixUnit_commute_representedRowAverage rho n i j b).smul_left (c i j)

/-- Later finite averages also commute with every earlier finite stage. -/
theorem ofStage_commute_representedRowAverage_of_le
    (rho : Limit →⋆ₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (c : Stage n) (b : B) :
    rho (ofStage n c) * representedRowAverage rho m b =
      representedRowAverage rho m b * rho (ofStage n c) := by
  simpa only [ofStage_embed] using
    ofStage_commute_representedRowAverage rho m (embed n m h c) b

/-- Elements of the commutant can be pulled through the average on both
sides. This identity holds on the whole target algebra. -/
theorem representedRowAverage_mul_mul (rho : Limit →⋆ₐ[ℂ] B)
    (n : ℕ) (S T b : B)
    (hS : ∀ a : Limit, rho a * S = S * rho a)
    (hT : ∀ a : Limit, rho a * T = T * rho a) :
    representedRowAverage rho n (S * b * T) =
      S * representedRowAverage rho n b * T := by
  simp only [representedRowAverage_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    rho (limitMatrixUnit n i 0) * (S * b * T) * rho (limitMatrixUnit n 0 i) =
        (rho (limitMatrixUnit n i 0) * S) * b *
          (T * rho (limitMatrixUnit n 0 i)) := by simp only [mul_assoc]
    _ = (S * rho (limitMatrixUnit n i 0)) * b *
          (rho (limitMatrixUnit n 0 i) * T) := by rw [hS, ← hT]
    _ = S * (rho (limitMatrixUnit n i 0) * b * rho (limitMatrixUnit n 0 i)) * T := by
      simp only [mul_assoc]

/-- Every finite average fixes the commutant pointwise. -/
theorem representedRowAverage_eq_self (rho : Limit →⋆ₐ[ℂ] B)
    (n : ℕ) (S : B) (hS : ∀ a : Limit, rho a * S = S * rho a) :
    representedRowAverage rho n S = S := by
  simpa only [mul_one, representedRowAverage_one] using
    representedRowAverage_mul_mul rho n S 1 1 hS (by intro a; simp)

end MathlibAnnex.CStarAlgebra.CAR
