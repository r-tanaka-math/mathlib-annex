import BanachGeometry.SequenceSpaces.C0Operators
import BanachGeometry.SequenceSpaces.L1Separable
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped ENNReal

/-!
# Weighted heterogeneous graphs as closed subspaces

The first ambient coordinate is x_j=λ_j a_j in ℓ₁(A_j); the second is
b_j=Q_j a_j in c₀(B_j). The linear closed constraint is Q_j x_j=λ_j b_j.
Thus the ambient maximum norm is exactly the paper's graph norm when λ_j>0.
This representation avoids introducing a second global norm on a sequence type.
-/

noncomputable section
open TopologicalSpace
namespace BanachGeometry
namespace WeightedGraph

variable (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)

def submodule : Submodule ℝ (L1Sum A × C0Sum B) where
  carrier := {z | ∀ j, Q j (z.1 j) = «λ» j • z.2 j}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro x y hx hy j
    change Q j (x.1 j + y.1 j) = «λ» j • (x.2 j + y.2 j)
    rw [map_add, hx j, hy j, smul_add]
  smul_mem' := by
    intro a x hx j
    change Q j (a • x.1 j) = «λ» j • (a • x.2 j)
    rw [map_smul, hx j, smul_comm]

abbrev Space := ↥(submodule A B Q «λ»)

-- Name the existing submodule structures so downstream map types use one path.
-- In particular this is the inherited ambient maximum norm.
instance spaceGroup : NormedAddCommGroup (Space A B Q «λ») :=
  (submodule A B Q «λ»).normedAddCommGroup

instance spaceModule : NormedSpace ℝ (Space A B Q «λ») :=
  (submodule A B Q «λ»).normedSpace

theorem isClosed_submodule : IsClosed (submodule A B Q «λ» : Set (L1Sum A × C0Sum B)) := by
  have hs : (submodule A B Q «λ» : Set (L1Sum A × C0Sum B)) =
      ⋂ j, {z : L1Sum A × C0Sum B | Q j (z.1 j) = «λ» j • z.2 j} := by
    ext z
    change (∀ j, Q j (z.1 j) = «λ» j • z.2 j) ↔ _
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (Q j).continuous.comp ((lp.evalCLM ℝ A 1 j).continuous.comp continuous_fst)
  · exact continuous_const.smul ((C0Sum.evalCLM B j).continuous.comp continuous_snd)

instance completeSpace [∀ j, CompleteSpace (A j)] [∀ j, CompleteSpace (B j)] :
    CompleteSpace (Space A B Q «λ») := (isClosed_submodule A B Q «λ»).isComplete.completeSpace_coe

instance separableSpace [∀ j, SeparableSpace (A j)] [∀ j, SeparableSpace (B j)] :
    SeparableSpace (Space A B Q «λ») := by infer_instance

def weighted : Space A B Q «λ» →L[ℝ] L1Sum A :=
  (ContinuousLinearMap.fst ℝ (L1Sum A) (C0Sum B)).comp (submodule A B Q «λ»).subtypeL

def output : Space A B Q «λ» →L[ℝ] C0Sum B :=
  (ContinuousLinearMap.snd ℝ (L1Sum A) (C0Sum B)).comp (submodule A B Q «λ»).subtypeL

def coord (j : ℕ) : Space A B Q «λ» →L[ℝ] A j :=
  («λ» j)⁻¹ • (lp.evalCLM ℝ A 1 j).comp (weighted A B Q «λ»)

@[simp] theorem coord_apply (j : ℕ) (x : Space A B Q «λ») :
    coord A B Q «λ» j x = («λ» j)⁻¹ • x.1.1 j := rfl

theorem norm_weighted_le (x : Space A B Q «λ») : ‖weighted A B Q «λ» x‖ ≤ ‖x‖ := norm_fst_le x.1
theorem norm_output_le (x : Space A B Q «λ») : ‖output A B Q «λ» x‖ ≤ ‖x‖ := norm_snd_le x.1

theorem norm_coord_le («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    ‖coord A B Q «λ» j x‖ ≤ («λ» j)⁻¹ * ‖x‖ := by
  rw [coord_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr («hλ» j))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr («hλ» j).le)
  exact (lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) x.1.1 j).trans
    (norm_fst_le x.1)

theorem opNorm_coord_le («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) :
    ‖coord A B Q «λ» j‖ ≤ («λ» j)⁻¹ :=
  (coord A B Q «λ» j).opNorm_le_bound (inv_nonneg.mpr («hλ» j).le) (norm_coord_le A B Q «λ» «hλ» j)

theorem coord_output («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    Q j (coord A B Q «λ» j x) = output A B Q «λ» x j := by
  change Q j ((«λ» j)⁻¹ • x.1.1 j) = x.1.2 j
  rw [map_smul, x.2 j, smul_smul, inv_mul_cancel₀ («hλ» j).ne', one_smul]

theorem weight_coord_norm («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    «λ» j * ‖coord A B Q «λ» j x‖ = ‖x.1.1 j‖ := by
  rw [coord_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr («hλ» j)),
    ← mul_assoc, mul_inv_cancel₀ («hλ» j).ne', one_mul]

/-- Exact identification of the fixed graph norm in the scaled representation. -/
theorem norm_formula («hλ» : ∀ j, 0 < «λ» j) (x : Space A B Q «λ») :
    ‖x‖ = max (∑' j, «λ» j * ‖coord A B Q «λ» j x‖)
      (⨆ j, ‖Q j (coord A B Q «λ» j x)‖) := by
  change max ‖x.1.1‖ ‖x.1.2‖ = _
  congr 1
  · rw [l1_norm_eq_tsum]
    exact tsum_congr (fun j => (weight_coord_norm A B Q «λ» «hλ» j x).symm)
  · rw [C0Sum.norm_eq_iSup]
    congr 1
    funext j
    exact congrArg norm (coord_output A B Q «λ» «hλ» j x).symm

theorem output_null (x : Space A B Q «λ») :
    Filter.Tendsto (fun j => ‖output A B Q «λ» x j‖) Filter.atTop (nhds 0) := x.1.2.null_atTop

theorem coordinate_images_null («hλ» : ∀ j, 0 < «λ» j) (x : Space A B Q «λ») :
    Filter.Tendsto (fun j => ‖Q j (coord A B Q «λ» j x)‖) Filter.atTop (nhds 0) := by
  simpa only [coord_output A B Q «λ» «hλ»] using output_null A B Q «λ» x

theorem recover_weighted_coord («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    «λ» j • coord A B Q «λ» j x = x.1.1 j := by
  rw [coord_apply, smul_smul, mul_inv_cancel₀ («hλ» j).ne', one_smul]

/-- The original coordinates determine both components of the graph. -/
theorem coordinates_injective («hλ» : ∀ j, 0 < «λ» j) {x y : Space A B Q «λ»}
    (hxy : ∀ j, coord A B Q «λ» j x = coord A B Q «λ» j y) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · apply lp.ext; funext j
    rw [← recover_weighted_coord A B Q «λ» «hλ» j x,
      ← recover_weighted_coord A B Q «λ» «hλ» j y, hxy j]
  · apply C0Sum.ext; intro j
    change output A B Q «λ» x j = output A B Q «λ» y j
    rw [← coord_output A B Q «λ» «hλ» j x, ← coord_output A B Q «λ» «hλ» j y, hxy j]

end WeightedGraph
end BanachGeometry
