import MathlibAnnex.Analysis.CStarAlgebra.CAR.RootCorner
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Normalized traces of the binary matrix stages

Every estimate is proved at a finite stage. The compatibility proof uses the
actual embedding `step`, including its coordinate reindexing.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The average of the diagonal entries of a binary matrix stage. -/
noncomputable def stageTraceLinear (n : ℕ) : Stage n →ₗ[ℂ] ℂ where
  toFun a := (2 ^ n : ℂ)⁻¹ * ∑ i, a i i
  map_add' a b := by simp only [CStarMatrix.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c a := by
    change (2 ^ n : ℂ)⁻¹ * (∑ i, c * a i i) =
      c * ((2 ^ n : ℂ)⁻¹ * ∑ i, a i i)
    rw [← Finset.mul_sum]
    ring

@[simp]
theorem stageTraceLinear_apply (n : ℕ) (a : Stage n) :
    stageTraceLinear n a = (2 ^ n : ℂ)⁻¹ * ∑ i, a i i := rfl

/-- The normalized matrix trace is contractive in the C⋆-norm. -/
theorem norm_stageTraceLinear_le (n : ℕ) (a : Stage n) :
    ‖stageTraceLinear n a‖ ≤ ‖a‖ := by
  have hpos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  calc
    ‖stageTraceLinear n a‖ = (2 ^ n : ℝ)⁻¹ * ‖∑ i, a i i‖ := by
      simp only [stageTraceLinear_apply, norm_mul, norm_inv, norm_pow, Complex.norm_two]
    _ ≤ (2 ^ n : ℝ)⁻¹ * ∑ i, ‖a i i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hpos.le)
    _ ≤ (2 ^ n : ℝ)⁻¹ * ∑ _i : Fin (2 ^ n), ‖a‖ := by
      gcongr with i
      exact CStarMatrix.norm_entry_le_norm
    _ = ‖a‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- The finite-stage trace, bundled as a continuous linear map. -/
noncomputable def stageTrace (n : ℕ) : Stage n →L[ℂ] ℂ :=
  (stageTraceLinear n).mkContinuous 1 fun a ↦ by
    simpa only [one_mul] using norm_stageTraceLinear_le n a

@[simp]
theorem stageTrace_apply (n : ℕ) (a : Stage n) :
    stageTrace n a = (2 ^ n : ℂ)⁻¹ * ∑ i, a i i := rfl

theorem norm_stageTrace_le (n : ℕ) (a : Stage n) :
    ‖stageTrace n a‖ ≤ ‖a‖ := norm_stageTraceLinear_le n a

@[simp]
theorem stageTrace_one (n : ℕ) : stageTrace n 1 = 1 := by
  rw [stageTrace_apply]
  simp only [CStarMatrix.one_apply_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num))

/-- Positivity is checked entrywise on a star square. -/
theorem stageTrace_star_mul_self_nonneg (n : ℕ) (a : Stage n) :
    0 ≤ stageTrace n (star a * a) := by
  rw [stageTrace_apply]
  have hcoef : (0 : ℂ) ≤ (2 ^ n : ℂ)⁻¹ := by
    have hr : (0 : ℝ) ≤ (2 ^ n : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
    simpa only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat] using
      (Complex.zero_le_real.mpr hr)
  apply mul_nonneg hcoef
  apply Finset.sum_nonneg
  intro i _
  rw [CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun k _ ↦ star_mul_self_nonneg (a k i)

/-- Traciality follows from interchanging the two finite sums. -/
theorem stageTrace_mul_comm (n : ℕ) (a b : Stage n) :
    stageTrace n (a * b) = stageTrace n (b * a) := by
  simp only [stageTrace_apply, CStarMatrix.mul_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

private theorem step_diagonal (n : ℕ) (a : Stage n)
    (i : Fin (2 ^ n)) (b : Fin 2) :
    step n a (stepIndexEquiv n (i, b)) (stepIndexEquiv n (i, b)) = a i i := by
  simp [step, amplify, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
    Matrix.kronecker_apply]

private theorem sum_step_diagonal (n : ℕ) (a : Stage n) :
    (∑ k : Fin (2 ^ (n + 1)), step n a k k) = 2 * ∑ i, a i i := by
  calc
    (∑ k : Fin (2 ^ (n + 1)), step n a k k) =
        ∑ z : Fin (2 ^ n) × Fin 2,
          step n a (stepIndexEquiv n z) (stepIndexEquiv n z) :=
      ((stepIndexEquiv n).sum_comp (fun k ↦ step n a k k)).symm
    _ = ∑ i : Fin (2 ^ n), ∑ b : Fin 2, a i i := by
      rw [Fintype.sum_prod_type]
      simp only [step_diagonal]
    _ = 2 * ∑ i, a i i := by simp [Fin.sum_univ_two, Finset.sum_add_distrib, two_mul]

@[simp]
theorem stageTrace_step (n : ℕ) (a : Stage n) :
    stageTrace (n + 1) (step n a) = stageTrace n a := by
  rw [stageTrace_apply, sum_step_diagonal, stageTrace_apply, pow_succ]
  field_simp <;> ring

@[simp]
theorem stageTrace_rootProjection (n : ℕ) :
    stageTrace n (rootProjection n) = (2 ^ n : ℂ)⁻¹ := by
  simp [stageTrace_apply, rootProjection, Matrix.single]

end MathlibAnnex.CStarAlgebra.CAR
