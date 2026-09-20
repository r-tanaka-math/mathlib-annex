import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.MeanCentrality
import Mathlib.Analysis.Convex.Combination

/-!
# Finite probability averages of genuine isometries

This finite witness is intentionally smaller than a mean on all bounded
functions. It carries actual points s with s* s = 1, common nonnegative
weights, and normalization. It does not assert existence of balanced
averages. That existence is the next source-author-A boundary.
C04 source candidate, unbuilt.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open scoped BigOperators CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.TensorAveraging
universe u
variable (M : Type u) [CStarAlgebra M] [Nontrivial M]

structure FiniteIsometryAverage where
  size : ℕ
  point : Fin size → Isometry M
  weight : Fin size → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1

namespace FiniteIsometryAverage
variable {M}

/-- A nonempty witness exists even for an empty set of balancing tests. -/
def dirac (s : Isometry M) : FiniteIsometryAverage M where
  size := 1
  point := fun _ => s
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  weight_sum := by simp

instance : Nonempty (FiniteIsometryAverage M) :=
  ⟨dirac (Classical.choice (inferInstance : Nonempty (Isometry M)))⟩

/-- Weighted evaluation in the required V(s*,s), not V(s,s*), orientation. -/
def value (d : FiniteIsometryAverage M) (B : ContinuousBilinearForm M) : ℂ :=
  ∑ i, (d.weight i : ℂ) * B (star (d.point i).val) (d.point i).val

@[simp] theorem value_add (d : FiniteIsometryAverage M) (B C : ContinuousBilinearForm M) :
    d.value (B + C) = d.value B + d.value C := by
  simp only [value, ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem value_smul (d : FiniteIsometryAverage M) (c : ℂ) (B : ContinuousBilinearForm M) :
    d.value (c • B) = c * d.value B := by
  simp only [value, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

@[simp] theorem value_sub (d : FiniteIsometryAverage M) (B C : ContinuousBilinearForm M) :
    d.value (B - C) = d.value B - d.value C := by
  simp only [value, ContinuousLinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Positive weights, rather than a sum of absolute weights left as a new
hypothesis, give the exact norm-one budget. -/
theorem norm_value_le (d : FiniteIsometryAverage M) (B : ContinuousBilinearForm M) :
    ‖d.value B‖ ≤ ‖B‖ := by
  calc
    ‖d.value B‖ ≤ ∑ i, ‖(d.weight i : ℂ) *
        B (star (d.point i).val) (d.point i).val‖ := norm_sum_le _ _
    _ = ∑ i, d.weight i * ‖B (star (d.point i).val) (d.point i).val‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (d.weight_nonneg i)]
    _ ≤ ∑ i, d.weight i * ‖B‖ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (sample_bound M B (d.point i)) (d.weight_nonneg i)
    _ = ‖B‖ := by rw [← Finset.sum_mul, d.weight_sum, one_mul]

private noncomputable instance : NormedAddCommGroup (ContinuousBilinearForm M) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := M) (F := M →L[ℂ] ℂ)
    (σ₁₂ := RingHom.id ℂ)

private noncomputable instance : NormedSpace ℂ (ContinuousBilinearForm M) :=
  ContinuousLinearMap.toNormedSpace (E := M) (F := M →L[ℂ] ℂ)
    (σ₁₂ := RingHom.id ℂ)

private def valueLinear (d : FiniteIsometryAverage M) : ContinuousBilinearForm M →ₗ[ℂ] ℂ where
  toFun := d.value
  map_add' := fun B C => d.value_add B C
  map_smul' := by
    intro c B
    simpa only [smul_eq_mul, RingHom.id_apply] using d.value_smul c B

def functional (d : FiniteIsometryAverage M) : ContinuousBilinearForm M →L[ℂ] ℂ :=
  (d.valueLinear).mkContinuous 1
    (by intro B; change ‖d.value B‖ ≤ 1 * ‖B‖; simpa only [one_mul] using d.norm_value_le B)

@[simp] theorem functional_apply (d : FiniteIsometryAverage M) (B : ContinuousBilinearForm M) :
    d.functional B = d.value B := rfl

/-- Every sample, and hence every finite average, has exactly the SAME
multiplication moment. No limit argument or normalization correction is used. -/
theorem value_mulForm (d : FiniteIsometryAverage M) (phi : M →L[ℂ] ℂ) :
    d.value (mulForm M phi) = phi 1 := by
  have hi (i : Fin d.size) :
      (mulForm M phi) (star (d.point i).val) (d.point i).val = phi 1 := by
    change phi (star (d.point i).val * (d.point i).val) = phi 1
    rw [(d.point i).property]
  simp only [value, hi, ← Finset.sum_mul]
  have hw : (∑ i, (d.weight i : ℂ)) = 1 := by exact_mod_cast d.weight_sum
  rw [hw, one_mul]

/-- Linear commutator defect; all later finite tests share this d. -/
def defect (d : FiniteIsometryAverage M) (a : M) (B : ContinuousBilinearForm M) : ℂ :=
  d.value (leftForm M a B) - d.value (rightForm M a B)

@[simp] theorem defect_eq_sum (d : FiniteIsometryAverage M) (a : M) (B : ContinuousBilinearForm M) :
    d.defect a B = ∑ i, (d.weight i : ℂ) *
      (B (a * star (d.point i).val) (d.point i).val -
       B (star (d.point i).val) ((d.point i).val * a)) := by
  simp only [defect, value, ← Finset.sum_sub_distrib, mul_sub]
  rfl

@[simp] theorem defect_sub (d : FiniteIsometryAverage M) (a b : M) (B : ContinuousBilinearForm M) :
    d.defect (a - b) B = d.defect a B - d.defect b B := by
  have hl : leftForm M (a - b) B = leftForm M a B - leftForm M b B := by
    ext x y
    simp only [leftForm_apply, sub_mul, map_sub, ContinuousLinearMap.sub_apply]
  have hr : rightForm M (a - b) B = rightForm M a B - rightForm M b B := by
    ext x y
    simp only [rightForm_apply, mul_sub, map_sub, ContinuousLinearMap.sub_apply]
  simp only [defect, hl, hr, value_sub]
  ring

/-- Exact finite-corner balance needs to hold only AFTER averaging.
The error bound, in contrast, is uniform at every orbit point. -/
theorem norm_defect_le_of_balanced_approximation
    (d : FiniteIsometryAverage M) (a b : M) (B : ContinuousBilinearForm M)
    (hbalance : d.defect b B = 0) (epsilon : ℝ)
    (herror : ∀ i, ‖B ((a - b) * star (d.point i).val) (d.point i).val -
      B (star (d.point i).val) ((d.point i).val * (a - b))‖ ≤ epsilon) :
    ‖d.defect a B‖ ≤ epsilon := by
  have heq : d.defect a B = d.defect (a - b) B := by
    rw [defect_sub, hbalance, sub_zero]
  rw [heq]
  rw [defect_eq_sum]
  calc
    _ ≤ ∑ i, ‖(d.weight i : ℂ) *
      (B ((a - b) * star (d.point i).val) (d.point i).val -
       B (star (d.point i).val) ((d.point i).val * (a - b)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, d.weight i * epsilon := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (d.weight_nonneg i)]
      exact mul_le_mul_of_nonneg_left (herror i) (d.weight_nonneg i)
    _ = epsilon := by rw [← Finset.sum_mul, d.weight_sum, one_mul]

/-- Uniform pointwise control passes through normalized nonnegative weights. -/
theorem norm_defect_le (d : FiniteIsometryAverage M) (a : M) (B : ContinuousBilinearForm M)
    (epsilon : ℝ)
    (h : ∀ i, ‖B (a * star (d.point i).val) (d.point i).val -
      B (star (d.point i).val) ((d.point i).val * a)‖ ≤ epsilon) :
    ‖d.defect a B‖ ≤ epsilon := by
  rw [defect_eq_sum]
  calc
    _ ≤ ∑ i, ‖(d.weight i : ℂ) * (B (a * star (d.point i).val) (d.point i).val -
       B (star (d.point i).val) ((d.point i).val * a))‖ := norm_sum_le _ _
    _ ≤ ∑ i, d.weight i * epsilon := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (d.weight_nonneg i)]
      exact mul_le_mul_of_nonneg_left (h i) (d.weight_nonneg i)
    _ = epsilon := by rw [← Finset.sum_mul, d.weight_sum, one_mul]

end FiniteIsometryAverage
end MathlibAnnex.CStarAlgebra.TensorAveraging
