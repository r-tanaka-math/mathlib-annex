import Mathlib.Analysis.Convex.Combination
import MathlibAnnex.Analysis.CStarAlgebra.FiniteRow
import MathlibAnnex.Analysis.Normed.TensorProduct.Algebra

/-!
# Finite rows from the projective tensor convex hull

This file turns membership in the real convex hull of tensors `x ⊗ x⋆`
into an actual finite row.  The ambient tensor product is the ordinary
complex Banach projective tensor product, not a C*-tensor product.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.ProjectiveTensorProduct.Algebra

universe u

noncomputable section

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The completed complex projective tensor square of `A`. -/
abbrev Tensor := Completion ℂ A A

/-- The generating contractions `x ⊗ x⋆`. -/
def rowGenerators : Set (Tensor A) :=
  {t | ∃ x : A, ‖x‖ ≤ 1 ∧ t = tprod ℂ A A x (star x)}

/-- The (non-closed) real convex hull used in the finite-row argument. -/
def rowConvexSet : Set (Tensor A) := convexHull ℝ (rowGenerators A)

theorem convex_rowConvexSet : Convex ℝ (rowConvexSet A) :=
  convex_convexHull ℝ (rowGenerators A)

/-- The projective tensor represented by a finite row. -/
def rowTensor {n : ℕ} (x : Fin n → A) : Tensor A :=
  ∑ i, tprod ℂ A A (x i) (star (x i))

/-- The positive row square `Σ xᵢxᵢ⋆`. -/
def rowSquare {n : ℕ} (x : Fin n → A) : A :=
  ∑ i, x i * star (x i)

@[simp]
theorem multiplication_rowTensor {n : ℕ} (x : Fin n → A) :
    multiplication ℂ A (rowTensor A x) = rowSquare A x := by
  simp [rowTensor, rowSquare]

/-- The continuous sandwich sum associated to a finite row. -/
def rowMap {n : ℕ} (x : Fin n → A) : A →L[ℂ] A :=
  sandwichOperator ℂ A (rowTensor A x)

@[simp]
theorem rowMap_apply {n : ℕ} (x : Fin n → A) (b : A) :
    rowMap A x b = ∑ i, x i * b * star (x i) := by
  simp [rowMap, rowTensor]

theorem rowSquare_nonneg {n : ℕ} (x : Fin n → A) : 0 ≤ rowSquare A x := by
  unfold rowSquare
  exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg (x i)

theorem norm_rowSquare_le_budget {n : ℕ} (x : Fin n → A) :
    ‖rowSquare A x‖ ≤ ∑ i, ‖x i‖ ^ 2 := by
  calc
    ‖rowSquare A x‖ ≤ ∑ i, ‖x i * star (x i)‖ := by
      simpa [rowSquare] using norm_sum_le Finset.univ (fun i ↦ x i * star (x i))
    _ = ∑ i, ‖x i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [pow_two] using (CStarRing.norm_self_mul_star (x := x i))

theorem norm_rowMap_le_budget {n : ℕ} (x : Fin n → A) :
    ‖rowMap A x‖ ≤ ∑ i, ‖x i‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) fun b ↦ ?_
  rw [rowMap_apply]
  calc
    ‖∑ i, x i * b * star (x i)‖ ≤ ∑ i, ‖x i * b * star (x i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (‖x i‖ ^ 2) * ‖b‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖x i * b * star (x i)‖ ≤ (‖x i‖ * ‖b‖) * ‖star (x i)‖ :=
          (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ = (‖x i‖ ^ 2) * ‖b‖ := by rw [norm_star]; ring
    _ = (∑ i, ‖x i‖ ^ 2) * ‖b‖ := by rw [Finset.sum_mul]

theorem rowMap_nonneg {n : ℕ} (x : Fin n → A) {b : A} (hb : 0 ≤ b) :
    0 ≤ rowMap A x b := by
  rw [rowMap_apply]
  exact Finset.sum_nonneg fun i _ => star_right_conjugate_nonneg hb (x i)

theorem norm_rowMap_le_one {n : ℕ} (x : Fin n → A)
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ 1) : ‖rowMap A x‖ ≤ 1 :=
  (norm_rowMap_le_budget A x).trans hx

private theorem tprod_sqrt_weight (w : ℝ) (hw : 0 ≤ w) (x : A) :
    tprod ℂ A A ((Real.sqrt w : ℂ) • x) (star ((Real.sqrt w : ℂ) • x)) =
      w • tprod ℂ A A x (star x) := by
  have hp : pair A A ((Real.sqrt w : ℂ) • x) (star ((Real.sqrt w : ℂ) • x)) =
      (fun i ↦ (Real.sqrt w : ℂ) • pair A A x (star x) i) := by
    funext i
    rcases i with i | i <;> cases i
    · rfl
    · apply ULift.ext
      change star ((Real.sqrt w : ℂ) • x) = (Real.sqrt w : ℂ) • star x
      simp
  change toCompletion ℂ A A
      (PiTensorProduct.tprod ℂ
        (pair A A ((Real.sqrt w : ℂ) • x) (star ((Real.sqrt w : ℂ) • x)))) = _
  rw [hp, MultilinearMap.map_smul_univ, map_smul]
  have hprod : (∏ _ : PairIndex, (Real.sqrt w : ℂ)) =
      (Real.sqrt w : ℂ) * (Real.sqrt w : ℂ) := by
    rw [Fintype.prod_sum_type]
    simp
  rw [hprod, RCLike.real_smul_eq_coe_smul (K := ℂ) w]
  change ((Real.sqrt w : ℂ) * (Real.sqrt w : ℂ)) •
      toCompletion ℂ A A (pureAlgebraic ℂ A A x (star x)) =
    (w : ℂ) • toCompletion ℂ A A (pureAlgebraic ℂ A A x (star x))
  congr 1
  norm_cast
  simpa [pow_two] using Real.sq_sqrt hw

/-- Every point of the real convex hull is represented by an actual finite
row with squared-norm budget at most one. -/
theorem exists_row_of_mem_rowConvexSet {t : Tensor A} (ht : t ∈ rowConvexSet A) :
    ∃ (n : ℕ) (y : Fin n → A), rowTensor A y = t ∧ ∑ i, ‖y i‖ ^ 2 ≤ 1 := by
  rw [rowConvexSet, mem_convexHull_iff_exists_fintype] at ht
  rcases ht with ⟨ι, hι, w, z, hw, hws, hz, hsum⟩
  letI : Fintype ι := hι
  choose x hxnorm hxz using fun i ↦ hz i
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let y : Fin (Fintype.card ι) → A := fun j ↦ (Real.sqrt (w (e j)) : ℂ) • x (e j)
  refine ⟨Fintype.card ι, y, ?_, ?_⟩
  · rw [rowTensor]
    calc
      (∑ j, tprod ℂ A A (y j) (star (y j))) =
          ∑ j, w (e j) • tprod ℂ A A (x (e j)) (star (x (e j))) := by
        apply Finset.sum_congr rfl
        intro j _
        exact tprod_sqrt_weight A (w (e j)) (hw (e j)) (x (e j))
      _ = ∑ i, w i • tprod ℂ A A (x i) (star (x i)) :=
        Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = ∑ i, w i • z i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hxz i]
      _ = t := hsum
  · calc
      (∑ j, ‖y j‖ ^ 2) ≤ ∑ j, w (e j) := by
        apply Finset.sum_le_sum
        intro j _
        simp only [y, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
        rw [Real.sq_sqrt (hw (e j))]
        exact mul_le_of_le_one_right (hw (e j)) (pow_le_one₀ (norm_nonneg _) (hxnorm (e j)))
      _ = ∑ i, w i := Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ ≤ 1 := hws.le

/-- The commutator map `b ↦ a Φ_y(b) - Φ_y(b) a`. -/
def rowCommutator {n : ℕ} (a : A) (x : Fin n → A) : A →L[ℂ] A :=
  (leftMul ℂ A a).comp (rowMap A x) - (rightMul ℂ A a).comp (rowMap A x)

@[simp]
theorem rowCommutator_apply {n : ℕ} (a : A) (x : Fin n → A) (b : A) :
    rowCommutator A a x b = a * rowMap A x b - rowMap A x b * a := rfl

theorem norm_rowCommutator_le_tensor {n : ℕ} (a : A) (x : Fin n → A) :
    ‖rowCommutator A a x‖ ≤
      ‖leftAction ℂ A a (rowTensor A x) - rightAction ℂ A a (rowTensor A x)‖ := by
  have heq : rowCommutator A a x = sandwichOperator ℂ A
      (leftAction ℂ A a (rowTensor A x) - rightAction ℂ A a (rowTensor A x)) := by
    apply ContinuousLinearMap.ext
    intro b
    exact (sandwichOperator_action_sub ℂ A a b (rowTensor A x)).symm
  rw [heq]
  calc
    ‖sandwichOperator ℂ A
        (leftAction ℂ A a (rowTensor A x) - rightAction ℂ A a (rowTensor A x))‖ ≤
        ‖sandwichOperator ℂ A‖ *
          ‖leftAction ℂ A a (rowTensor A x) - rightAction ℂ A a (rowTensor A x)‖ :=
      (sandwichOperator ℂ A).le_opNorm _
    _ ≤ 1 * ‖leftAction ℂ A a (rowTensor A x) -
        rightAction ℂ A a (rowTensor A x)‖ :=
      mul_le_mul_of_nonneg_right (norm_sandwichOperator_le ℂ A) (norm_nonneg _)
    _ = _ := one_mul _

end

end MathlibAnnex.CStarAlgebra.TensorAveraging
