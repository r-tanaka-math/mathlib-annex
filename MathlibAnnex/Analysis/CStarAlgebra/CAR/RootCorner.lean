import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteStages
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The finite-stage root corner

The distinguished coordinate defines the product-vector functional at every binary
matrix stage.  Its rank-one corner has an exact compression formula for every stage
element, before any completion or limiting argument is used.
-/

set_option autoImplicit false

open scoped CStarAlgebra ComplexOrder Matrix

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The rank-one projection onto the distinguished zero coordinate. -/
noncomputable def rootProjection (n : ℕ) : Stage n :=
  CStarMatrix.ofMatrix (Matrix.single 0 0 (1 : ℂ))

/-- Exact finite-stage compression by the distinguished rank-one projection. -/
theorem rootProjection_mul_mul (n : ℕ) (x : Stage n) :
    rootProjection n * x * rootProjection n = (x 0 0) • rootProjection n := by
  classical
  apply CStarMatrix.ext
  intro i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i
    subst j
    simp [rootProjection, CStarMatrix.mul_apply, Matrix.single]
  · subst i
    simp [rootProjection, CStarMatrix.mul_apply, Matrix.single, Ne.symm hj]
  · simp [rootProjection, CStarMatrix.mul_apply, Matrix.single, Ne.symm hi]
  · simp [rootProjection, CStarMatrix.mul_apply, Matrix.single, Ne.symm hi,
      Ne.symm hj]

/-- The finite-stage compression error vanishes for every stage element. -/
@[simp]
theorem norm_rootProjection_compression_sub (n : ℕ) (x : Stage n) :
    ‖rootProjection n * x * rootProjection n - (x 0 0) • rootProjection n‖ = 0 := by
  rw [rootProjection_mul_mul, sub_self, norm_zero]

theorem isStarProjection_rootProjection (n : ℕ) :
    IsStarProjection (rootProjection n) := by
  constructor
  · rw [isIdempotentElem_iff]
    simpa using rootProjection_mul_mul n (1 : Stage n)
  · rw [isSelfAdjoint_iff]
    apply CStarMatrix.ext
    intro i j
    simp [rootProjection, CStarMatrix.star_apply, Matrix.single, and_comm]

/-- Evaluation at the distinguished diagonal coordinate. -/
def rootLinear (n : ℕ) : Stage n →ₗ[ℂ] ℂ where
  toFun x := x 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The distinguished-coordinate functional is continuous for the operator norm. -/
noncomputable def rootFunctional (n : ℕ) : Stage n →L[ℂ] ℂ :=
  (rootLinear n).mkContinuous 1 fun x => by
    simpa [rootLinear] using (CStarMatrix.norm_entry_le_norm (M := x) (i := (0 : Fin (2 ^ n)))
      (j := (0 : Fin (2 ^ n))))

@[simp]
theorem rootFunctional_apply (n : ℕ) (x : Stage n) : rootFunctional n x = x 0 0 :=
  rfl

/-- The root vector functionals are compatible with the standard CAR stage embeddings. -/
@[simp]
theorem rootFunctional_step (n : ℕ) (x : Stage n) :
    rootFunctional (n + 1) (step n x) = rootFunctional n x := by
  change step n x 0 0 = x 0 0
  simp [step, stepIndexEquiv, amplify, Matrix.reindex_apply, finProdFinEquiv]
  congr 1 <;> apply Fin.ext <;> simp

/-- One-step local compression is exact after embedding an arbitrary old-stage element. -/
theorem rootProjection_step_mul_mul (n : ℕ) (x : Stage n) :
    rootProjection (n + 1) * step n x * rootProjection (n + 1) =
      (x 0 0) • rootProjection (n + 1) := by
  rw [rootProjection_mul_mul]
  congr 1
  exact rootFunctional_step n x

@[simp]
theorem norm_rootProjection_step_compression_sub (n : ℕ) (x : Stage n) :
    ‖rootProjection (n + 1) * step n x * rootProjection (n + 1) -
      (x 0 0) • rootProjection (n + 1)‖ = 0 := by
  rw [rootProjection_step_mul_mul, sub_self, norm_zero]

/-- Positivity of the distinguished-coordinate functional. -/
theorem rootLinear_nonneg (n : ℕ) (x : Stage n) (hx : 0 ≤ x) :
    0 ≤ rootLinear n x := by
  letI : NonnegSpectrumClass ℝ (Stage n) :=
    CStarAlgebra.instNonnegSpectrumClass'
  letI : NonUnitalContinuousFunctionalCalculus ℂ (Stage n) IsStarNormal :=
    (IsStarNormal.instNonUnitalContinuousFunctionalCalculus
      (A := Stage n)).toNonUnitalContinuousFunctionalCalculus
  letI : NonUnitalContinuousFunctionalCalculus ℝ (Stage n) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx with ⟨y, rfl⟩
  change 0 ≤ (star y * y) 0 0
  rw [CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg (y k 0)

/-- The normalized positive functional at the root coordinate. -/
noncomputable def rootPositiveFunctional (n : ℕ) : Stage n →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (rootLinear n) (rootLinear_nonneg n)

@[simp]
theorem rootPositiveFunctional_apply (n : ℕ) (x : Stage n) :
    rootPositiveFunctional n x = x 0 0 := rfl

@[simp]
theorem rootPositiveFunctional_one (n : ℕ) : rootPositiveFunctional n 1 = 1 := by
  exact CStarMatrix.one_apply_eq 0

@[simp]
theorem rootPositiveFunctional_step (n : ℕ) (x : Stage n) :
    rootPositiveFunctional (n + 1) (step n x) = rootPositiveFunctional n x := by
  exact rootFunctional_step n x

end MathlibAnnex.CStarAlgebra.CAR
