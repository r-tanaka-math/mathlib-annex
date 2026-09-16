import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Output selection for maximal minors

Contractive output selection acts on continuous linear maps and their operator
spaces. Its determinant is the maximal minor in the canonical increasing row order.
-/

noncomputable section

namespace MathlibAnnex
namespace ContinuousLinearMap

universe u

/-- Select the output coordinates in the increasing order fixed by a
maximal-minor index. -/
def selectedOutputLinearMap {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) :
    (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun y i := y (s.orderedRows i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate selection is contractive for the finite Pi sup norms. -/
theorem norm_selectedOutputLinearMap_le
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) (y : ι → ℝ) :
    ‖selectedOutputLinearMap s y‖ ≤ ‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2
  intro i
  change ‖y (s.orderedRows i)‖ ≤ ‖y‖
  exact norm_le_pi_norm y _

/-- Output-coordinate selection as a continuous linear map. -/
noncomputable def selectedOutput
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) :
    (ι → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (selectedOutputLinearMap s).mkContinuous 1 fun y => by
    simpa using norm_selectedOutputLinearMap_le s y

@[simp] theorem selectedOutput_apply
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) (y : ι → ℝ) (i : Fin n) :
    selectedOutput s y i = y (s.orderedRows i) := rfl

/-- The square operator obtained by selecting `n` output coordinates. -/
noncomputable def selectedSquare
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι)
    (A : (Fin n → ℝ) →L[ℝ] (ι → ℝ)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (selectedOutput s).comp A

/-- Output selection bundled as a continuous linear map on operator spaces. -/
noncomputable def selectedSquareCLM
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) :
    ((Fin n → ℝ) →L[ℝ] (ι → ℝ)) →L[ℝ]
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
  (selectedOutput s).postcomp (Fin n → ℝ)

@[simp] theorem selectedSquareCLM_apply
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι)
    (A : (Fin n → ℝ) →L[ℝ] (ι → ℝ)) :
    selectedSquareCLM s A = selectedSquare s A := rfl

/-- The output selection has operator norm at most one. -/
theorem norm_selectedOutput_le_one
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι) :
    ‖selectedOutput s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  change ‖selectedOutputLinearMap s y‖ ≤ 1 * ‖y‖
  simpa only [one_mul] using norm_selectedOutputLinearMap_le s y

/-- Selection is contractive on operator spaces. -/
theorem norm_selectedSquare_le
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι)
    (A : (Fin n → ℝ) →L[ℝ] (ι → ℝ)) :
    ‖selectedSquare s A‖ ≤ ‖A‖ := by
  calc
    ‖selectedSquare s A‖ ≤ ‖selectedOutput s‖ * ‖A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖A‖ :=
      mul_le_mul_of_nonneg_right (norm_selectedOutput_le_one s) (norm_nonneg A)
    _ = ‖A‖ := one_mul _

@[simp] theorem selectedSquare_sub
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι)
    (P Q : (Fin n → ℝ) →L[ℝ] (ι → ℝ)) :
    selectedSquare s (P - Q) = selectedSquare s P - selectedSquare s Q := by
  change selectedSquareCLM s (P - Q) =
    selectedSquareCLM s P - selectedSquareCLM s Q
  exact map_sub (selectedSquareCLM s) P Q

/-- The determinant of the selected square operator is the maximal minor
of the standard-basis matrix of the original operator. -/
@[simp] theorem det_selectedSquare
    {n : ℕ} {ι : Type u} [Fintype ι] [LinearOrder ι]
    (s : Matrix.MaximalMinorIndex n ι)
    (A : (Fin n → ℝ) →L[ℝ] (ι → ℝ)) :
    LinearMap.det (selectedSquare s A :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      Matrix.maximalMinor
        (LinearMap.toMatrix' (A : (Fin n → ℝ) →ₗ[ℝ] (ι → ℝ))) s := by
  rw [← LinearMap.det_toMatrix'
    (selectedSquare s A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))]
  unfold Matrix.maximalMinor Matrix.maximalSubmatrix selectedSquare selectedOutput
  congr 1

end ContinuousLinearMap
end MathlibAnnex
