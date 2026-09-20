import MathlibAnnex.Analysis.CStarAlgebra.CAR.Trace
import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteAverage

/-!
# Uniqueness of the normalized CAR trace

The matrix-unit calculations are separated from the density argument.
Positivity is not an additional hypothesis: normalization and the trace
identity already determine any continuous linear functional on CAR.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.CAR

private theorem apply_limitMatrixUnit_diag_eq_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))
    (n : ℕ) (i : Fin (2 ^ n)) :
    f (limitMatrixUnit n i i) = f (limitMatrixUnit n 0 0) := by
  simpa only [limitMatrixUnit_mul, ↓reduceIte] using
    hf (limitMatrixUnit n i 0) (limitMatrixUnit n 0 i)

private theorem apply_limitMatrixUnit_eq_zero_of_ne_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))
    (n : ℕ) (i j : Fin (2 ^ n)) (hij : i ≠ j) :
    f (limitMatrixUnit n i j) = 0 := by
  simpa only [limitMatrixUnit_mul, ↓reduceIte, hij, Ne.symm hij, if_false, map_zero] using
    hf (limitMatrixUnit n i i) (limitMatrixUnit n i j)

private theorem apply_limitMatrixUnit_zero_zero_of_apply_one_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ∀ a b, f (a * b) = f (b * a)) (n : ℕ) :
    f (limitMatrixUnit n 0 0) = (2 ^ n : ℂ)⁻¹ := by
  have hmul : (2 ^ n : ℂ) * f (limitMatrixUnit n 0 0) = 1 := by
    calc
      (2 ^ n : ℂ) * f (limitMatrixUnit n 0 0) =
          ∑ _i : Fin (2 ^ n), f (limitMatrixUnit n 0 0) := by simp
      _ = ∑ i : Fin (2 ^ n), f (limitMatrixUnit n i i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (apply_limitMatrixUnit_diag_eq_of_mul_comm f hf n i).symm
      _ = f (∑ i : Fin (2 ^ n), limitMatrixUnit n i i) := by rw [map_sum]
      _ = 1 := by rw [sum_limitMatrixUnit_diag, hf1]
  have hn : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    f (limitMatrixUnit n 0 0) =
        ((2 ^ n : ℂ)⁻¹ * (2 ^ n : ℂ)) * f (limitMatrixUnit n 0 0) := by
      rw [inv_mul_cancel₀ hn, one_mul]
    _ = (2 ^ n : ℂ)⁻¹ * ((2 ^ n : ℂ) * f (limitMatrixUnit n 0 0)) :=
      mul_assoc _ _ _
    _ = (2 ^ n : ℂ)⁻¹ := by rw [hmul, mul_one]

/-- A normalized continuous trace agrees with the constructed trace on
all matrix units, including off-diagonal ones. -/
theorem apply_limitMatrixUnit_eq_trace_of_apply_one_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ∀ a b, f (a * b) = f (b * a))
    (n : ℕ) (i j : Fin (2 ^ n)) :
    f (limitMatrixUnit n i j) = trace (limitMatrixUnit n i j) := by
  by_cases hij : i = j
  · subst j
    rw [apply_limitMatrixUnit_diag_eq_of_mul_comm f hf n i,
      apply_limitMatrixUnit_diag_eq_of_mul_comm trace trace_mul_comm n i,
      apply_limitMatrixUnit_zero_zero_of_apply_one_of_mul_comm f hf1 hf n,
      apply_limitMatrixUnit_zero_zero_of_apply_one_of_mul_comm trace trace_one trace_mul_comm n]
  · rw [apply_limitMatrixUnit_eq_zero_of_ne_of_mul_comm f hf n i j hij,
      apply_limitMatrixUnit_eq_zero_of_ne_of_mul_comm trace trace_mul_comm n i j hij]

/-- Agreement on matrix units extends linearly to each complete finite stage. -/
theorem apply_ofStage_eq_trace_of_apply_one_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ∀ a b, f (a * b) = f (b * a)) (n : ℕ) (a : Stage n) :
    f (ofStage n a) = trace (ofStage n a) := by
  rw [ofStage_eq_sum_smul_limitMatrixUnit]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [apply_limitMatrixUnit_eq_trace_of_apply_one_of_mul_comm f hf1 hf n i j]

/-- The normalized trace is unique among continuous linear functionals
satisfying the trace identity. -/
theorem eq_trace_of_apply_one_of_mul_comm
    (f : Limit →L[ℂ] ℂ) (hf1 : f 1 = 1)
    (hf : ∀ a b, f (a * b) = f (b * a)) : f = trace := by
  apply ContinuousLinearMap.coeFn_injective
  apply f.continuous.ext_on dense_stageRange trace.continuous
  intro x hx
  obtain ⟨n, a, rfl⟩ := Set.mem_iUnion.mp hx
  exact apply_ofStage_eq_trace_of_apply_one_of_mul_comm f hf1 hf n a

end MathlibAnnex.CStarAlgebra.CAR
