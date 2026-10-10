import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Matrix coefficients as continuous linear functionals

For `x : E` and `y : F`, `matrixCoefficient 𝕜 x y` sends an operator `T : E →L[𝕜] F`
to `inner 𝕜 y (T x)`. In particular, it is linear in `T` and `x`, and conjugate-linear
in `y`. The arguments are ordered as input vector, output vector.

The construction and its exact norm formula require neither completeness nor
finite dimension. The rank-one operators used below are Mathlib's `rankOne`;
there is no second definition of rank-one operators or of their kernels.
-/

set_option autoImplicit false

noncomputable section

namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The matrix coefficient with input vector `x` and output vector `y`. -/
def matrixCoefficient (𝕜 : Type*) [RCLike 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (x : E) (y : F) : (E →L[𝕜] F) →L[𝕜] 𝕜 :=
  ({ toFun := fun T : E →L[𝕜] F => inner 𝕜 y (T x)
     map_add' := by
       intro T S
       simp only [ContinuousLinearMap.add_apply, inner_add_right]
     map_smul' := by
       intro c T
       simp only [ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul,
         RingHom.id_apply] } :
    (E →L[𝕜] F) →ₗ[𝕜] 𝕜).mkContinuous (‖x‖ * ‖y‖) (by
      intro T
      calc
        ‖inner 𝕜 y (T x)‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖T‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg y)
        _ = (‖x‖ * ‖y‖) * ‖T‖ := by ring)

@[simp]
theorem matrixCoefficient_apply (x : E) (y : F) (T : E →L[𝕜] F) :
    matrixCoefficient 𝕜 x y T = inner 𝕜 y (T x) := rfl

@[simp]
theorem matrixCoefficient_zero_left (y : F) :
    matrixCoefficient 𝕜 (0 : E) y = 0 := by
  ext T
  simp only [matrixCoefficient_apply, map_zero, inner_zero_right,
    ContinuousLinearMap.zero_apply]

@[simp]
theorem matrixCoefficient_zero_right (x : E) :
    matrixCoefficient 𝕜 x (0 : F) = 0 := by
  ext T
  simp only [matrixCoefficient_apply, inner_zero_left, ContinuousLinearMap.zero_apply]

@[simp]
theorem matrixCoefficient_add_left (x u : E) (y : F) :
    matrixCoefficient 𝕜 (x + u) y =
      matrixCoefficient 𝕜 x y + matrixCoefficient 𝕜 u y := by
  ext T
  simp only [matrixCoefficient_apply, map_add, inner_add_right,
    ContinuousLinearMap.add_apply]

@[simp]
theorem matrixCoefficient_add_right (x : E) (y v : F) :
    matrixCoefficient 𝕜 x (y + v) =
      matrixCoefficient 𝕜 x y + matrixCoefficient 𝕜 x v := by
  ext T
  simp only [matrixCoefficient_apply, inner_add_left, ContinuousLinearMap.add_apply]

@[simp]
theorem matrixCoefficient_sub_left (x u : E) (y : F) :
    matrixCoefficient 𝕜 (x - u) y =
      matrixCoefficient 𝕜 x y - matrixCoefficient 𝕜 u y := by
  ext T
  simp only [matrixCoefficient_apply, map_sub, inner_sub_right,
    ContinuousLinearMap.sub_apply]

@[simp]
theorem matrixCoefficient_sub_right (x : E) (y v : F) :
    matrixCoefficient 𝕜 x (y - v) =
      matrixCoefficient 𝕜 x y - matrixCoefficient 𝕜 x v := by
  ext T
  simp only [matrixCoefficient_apply, inner_sub_left, ContinuousLinearMap.sub_apply]

@[simp]
theorem matrixCoefficient_smul_left (c : 𝕜) (x : E) (y : F) :
    matrixCoefficient 𝕜 (c • x) y = c • matrixCoefficient 𝕜 x y := by
  ext T
  simp only [matrixCoefficient_apply, map_smul, inner_smul_right,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

@[simp]
theorem matrixCoefficient_smul_right (c : 𝕜) (x : E) (y : F) :
    matrixCoefficient 𝕜 x (c • y) = star c • matrixCoefficient 𝕜 x y := by
  ext T
  simp [matrixCoefficient_apply, inner_smul_left, smul_eq_mul]

/-- Evaluation on a rank-one operator, with the scalar order written explicitly. -/
theorem matrixCoefficient_apply_rankOne (x u : E) (y v : F) :
    matrixCoefficient 𝕜 x y (rankOne 𝕜 v u) =
      inner 𝕜 u x * inner 𝕜 y v := by
  simp only [matrixCoefficient_apply, rankOne_apply, inner_smul_right]

theorem norm_matrixCoefficient_le (x : E) (y : F) :
    ‖matrixCoefficient 𝕜 x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  intro T
  calc
    ‖matrixCoefficient 𝕜 x y T‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg y)
    _ = (‖x‖ * ‖y‖) * ‖T‖ := by ring

/-- The exact norm follows by testing on `rankOne 𝕜 y x`, including zero-norm vectors. -/
@[simp]
theorem norm_matrixCoefficient (x : E) (y : F) :
    ‖matrixCoefficient 𝕜 x y‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm (norm_matrixCoefficient_le (𝕜 := 𝕜) x y)
  by_cases hzero : ‖x‖ * ‖y‖ = 0
  · rw [hzero]
    exact norm_nonneg (matrixCoefficient 𝕜 x y)
  · have hpos : 0 < ‖x‖ * ‖y‖ := by
      rcases lt_or_eq_of_le (mul_nonneg (norm_nonneg x) (norm_nonneg y)) with h | h
      · exact h
      · exact (hzero h.symm).elim
    have htest :
        ‖matrixCoefficient 𝕜 x y (rankOne 𝕜 y x)‖ =
          (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖) := by
      rw [matrixCoefficient_apply_rankOne, norm_mul,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      simp only [norm_pow, RCLike.norm_ofReal, abs_norm]
      ring
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖) =
          ‖matrixCoefficient 𝕜 x y (rankOne 𝕜 y x)‖ := htest.symm
      _ ≤ ‖matrixCoefficient 𝕜 x y‖ * ‖rankOne 𝕜 y x‖ :=
        (matrixCoefficient 𝕜 x y).le_opNorm _
      _ = ‖matrixCoefficient 𝕜 x y‖ * (‖x‖ * ‖y‖) := by
        rw [norm_rankOne (𝕜 := 𝕜), mul_comm ‖y‖ ‖x‖]

/-- Unit input and output vectors give a norm-one coefficient attaining one. -/
theorem exists_norm_eq_one_matrixCoefficient_eq_one
    {x : E} {y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ T : E →L[𝕜] F, ‖T‖ = 1 ∧ matrixCoefficient 𝕜 x y T = 1 := by
  refine ⟨rankOne 𝕜 y x, ?_, ?_⟩
  · simp only [norm_rankOne, hx, hy, one_mul]
  · simp [matrixCoefficient_apply_rankOne, inner_self_eq_norm_sq_to_K, hx, hy]

/-- A two-term expansion useful for norm-continuity estimates. -/
theorem matrixCoefficient_sub_eq (x u : E) (y v : F) :
    matrixCoefficient 𝕜 x y - matrixCoefficient 𝕜 u v =
      matrixCoefficient 𝕜 (x - u) y + matrixCoefficient 𝕜 u (y - v) := by
  rw [matrixCoefficient_sub_left, matrixCoefficient_sub_right, sub_add_sub_cancel]

theorem norm_matrixCoefficient_sub_le (x u : E) (y v : F) :
    ‖matrixCoefficient 𝕜 x y - matrixCoefficient 𝕜 u v‖ ≤
      ‖x - u‖ * ‖y‖ + ‖u‖ * ‖y - v‖ := by
  rw [matrixCoefficient_sub_eq]
  calc
    ‖matrixCoefficient 𝕜 (x - u) y + matrixCoefficient 𝕜 u (y - v)‖ ≤
        ‖matrixCoefficient 𝕜 (x - u) y‖ + ‖matrixCoefficient 𝕜 u (y - v)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ = ‖x - u‖ * ‖y‖ + ‖u‖ * ‖y - v‖ := by
      rw [norm_matrixCoefficient, norm_matrixCoefficient]

end Seminormed

section Normed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[simp]
theorem matrixCoefficient_eq_zero_iff {x : E} {y : F} :
    matrixCoefficient 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    have hnorm : ‖matrixCoefficient 𝕜 x y‖ = 0 := by
      rw [h, ContinuousLinearMap.opNorm_zero]
    rw [norm_matrixCoefficient, mul_eq_zero] at hnorm
    exact hnorm.elim (fun hx => Or.inl (norm_eq_zero.mp hx))
      (fun hy => Or.inr (norm_eq_zero.mp hy))
  · rintro (rfl | rfl)
    · exact matrixCoefficient_zero_left _
    · exact matrixCoefficient_zero_right _

theorem matrixCoefficient_ne_zero {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    matrixCoefficient 𝕜 x y ≠ 0 := by
  rw [ne_eq, matrixCoefficient_eq_zero_iff, not_or]
  exact ⟨hx, hy⟩

end Normed

end InnerProductSpace
