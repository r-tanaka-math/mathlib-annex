import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Determinant difference estimates for finite sup-norm coordinate spaces

For a finite type `ι`, the function space `ι → ℝ` has the sup norm.  The dual norm
of a matrix row is therefore its `ℓ¹` norm.  Replacing rows one at a time gives a
locally Lipschitz estimate for the determinant of continuous linear endomorphisms.

The stronger bound uses `max ‖P‖ ‖Q‖`; the source-compatible bound with
`‖P‖ + ‖Q‖` follows immediately.  These statements are specific to the operator
norm induced by the sup norm on the displayed Pi spaces; they are not Euclidean
operator-norm statements.
-/

noncomputable section

open Equiv Finset
open scoped BigOperators

namespace MathlibAnnex

namespace Matrix

universe u

/-- The `ℓ¹` norm of one row of a finite real matrix. -/
def rowL1Norm {ι : Type u} [Fintype ι]
    (M : _root_.Matrix ι ι ℝ) (i : ι) : ℝ :=
  ∑ j, |M i j|

private theorem abs_det_le_sum_perm_products
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) :
    |M.det| ≤ ∑ σ : Equiv.Perm ι, ∏ i, |M (σ i) i| := by
  rw [_root_.Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm ι,
        ((((Equiv.Perm.sign σ : Units ℤ) : ℤ) : ℝ) *
          ∏ i, M (σ i) i)| ≤
        ∑ σ : Equiv.Perm ι,
          |((((Equiv.Perm.sign σ : Units ℤ) : ℤ) : ℝ) *
            ∏ i, M (σ i) i)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |M (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      have hsignZ : |(((Equiv.Perm.sign σ : Units ℤ) : ℤ))| = 1 :=
        Equiv.Perm.sign_abs σ
      have hsignR : |((((Equiv.Perm.sign σ : Units ℤ) : ℤ) : ℝ))| = 1 := by
        exact_mod_cast hsignZ
      rw [abs_mul, hsignR, one_mul, abs_prod]

private theorem perm_product_reindex_by_rows
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) (σ : Equiv.Perm ι) :
    (∏ i, |M (σ i) i|) = ∏ i, |M i (σ.symm i)| := by
  apply Fintype.prod_equiv σ
  intro i
  simp

private theorem sum_perm_products_le_sum_all_row_choices
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) :
    (∑ σ : Equiv.Perm ι, ∏ i, |M i (σ.symm i)|) ≤
      ∑ f : ι → ι, ∏ i, |M i (f i)| := by
  classical
  let e : Equiv.Perm ι → (ι → ι) := fun σ => σ.symm
  have he : Function.Injective e := by
    intro σ τ h
    apply Equiv.symm_bijective.injective
    apply Equiv.ext
    exact congrFun h
  let S : Finset (ι → ι) := Finset.univ.image e
  calc
    (∑ σ : Equiv.Perm ι, ∏ i, |M i (σ.symm i)|) =
        S.sum (fun f => ∏ i, |M i (f i)|) := by
      dsimp [S]
      rw [Finset.sum_image]
      exact he.injOn
    _ ≤ Finset.univ.sum (fun f : ι → ι => ∏ i, |M i (f i)|) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro f _hf _hnot
      positivity

/-- Hadamard's determinant bound using the product of row `ℓ¹` norms. -/
theorem abs_det_le_prod_rowL1Norm
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) :
    |M.det| ≤ ∏ i, rowL1Norm M i := by
  calc
    |M.det| ≤ ∑ σ : Equiv.Perm ι, ∏ i, |M (σ i) i| :=
      abs_det_le_sum_perm_products M
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ.symm i)| := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact perm_product_reindex_by_rows M σ
    _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
      sum_perm_products_le_sum_all_row_choices M
    _ = ∏ i, rowL1Norm M i := by
      change (∑ f : ι → ι, ∏ i, |M i (f i)|) =
        ∏ i, ∑ j, |M i j|
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
        Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun _ : ι => Finset.univ)
          (fun i j => |M i j|)).symm

end Matrix

namespace ContinuousLinearMap

universe u

private def stdMatrix {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) : _root_.Matrix ι ι ℝ :=
  fun i j => A (Pi.single j 1) i

private theorem stdMatrix_eq_toMatrix'
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    stdMatrix A = LinearMap.toMatrix' (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
  ext i j
  rfl

private theorem stdMatrix_mulVec
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    (stdMatrix A).mulVec x = A x := by
  rw [stdMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_mulVec (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) x

@[simp] private theorem stdMatrix_sub
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    stdMatrix (P - Q) = stdMatrix P - stdMatrix Q := by
  ext i j
  simp [stdMatrix]

private def rowSign {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) (i : ι) : ι → ℝ :=
  fun j => if 0 ≤ M i j then 1 else -1

private theorem norm_rowSign_le_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) (i : ι) :
    ‖rowSign M i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro j
  by_cases h : 0 ≤ M i j
  · simp [rowSign, h]
  · simp [rowSign, h]

private theorem mulVec_rowSign_apply
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (M : _root_.Matrix ι ι ℝ) (i : ι) :
    M.mulVec (rowSign M i) i = Matrix.rowL1Norm M i := by
  unfold _root_.Matrix.mulVec Matrix.rowL1Norm
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 0 ≤ M i j
  · simp [rowSign, h, abs_of_nonneg h]
  · have h' : M i j ≤ 0 := le_of_not_ge h
    simp [rowSign, h, abs_of_nonpos h']

private theorem rowL1_stdMatrix_le_opNorm
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i : ι) :
    Matrix.rowL1Norm (stdMatrix A) i ≤ ‖A‖ := by
  let σ : ι → ℝ := rowSign (stdMatrix A) i
  have hσ : ‖σ‖ ≤ 1 := norm_rowSign_le_one (stdMatrix A) i
  have hrow : Matrix.rowL1Norm (stdMatrix A) i = A σ i := by
    calc
      Matrix.rowL1Norm (stdMatrix A) i = (stdMatrix A).mulVec σ i :=
        (mulVec_rowSign_apply (stdMatrix A) i).symm
      _ = A σ i := congrFun (stdMatrix_mulVec A σ) i
  calc
    Matrix.rowL1Norm (stdMatrix A) i = A σ i := hrow
    _ ≤ |A σ i| := le_abs_self _
    _ = ‖A σ i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A σ‖ := norm_le_pi_norm (A σ) i
    _ ≤ ‖A‖ * ‖σ‖ := A.le_opNorm σ
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hσ (norm_nonneg A)
    _ = ‖A‖ := mul_one _

private def rowsFrom {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) (s : Finset ι) : _root_.Matrix ι ι ℝ :=
  fun i => if i ∈ s then P i else Q i

@[simp] private theorem rowsFrom_apply_of_mem
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) (s : Finset ι) {i : ι} (hi : i ∈ s) :
    rowsFrom P Q s i = P i := by
  simp [rowsFrom, hi]

@[simp] private theorem rowsFrom_apply_of_not_mem
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) (s : Finset ι) {i : ι} (hi : i ∉ s) :
    rowsFrom P Q s i = Q i := by
  simp [rowsFrom, hi]

@[simp] private theorem rowsFrom_empty
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) : rowsFrom P Q ∅ = Q := by
  ext i j
  simp [rowsFrom]

@[simp] private theorem rowsFrom_univ
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) : rowsFrom P Q Finset.univ = P := by
  ext i j
  simp [rowsFrom]

private def oneRowDifference
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) (s : Finset ι) (i : ι) :
    _root_.Matrix ι ι ℝ :=
  (rowsFrom P Q s).updateRow i (P i - Q i)

private theorem det_rowsFrom_insert_sub
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : _root_.Matrix ι ι ℝ) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (rowsFrom P Q (insert i s)).det - (rowsFrom P Q s).det =
      (oneRowDifference P Q s i).det := by
  have hins : rowsFrom P Q (insert i s) =
      (rowsFrom P Q s).updateRow i (P i) := by
    ext r c
    by_cases hri : r = i
    · subst r
      simp [rowsFrom, hi, _root_.Matrix.updateRow]
    · simp [rowsFrom, _root_.Matrix.updateRow, hri]
  have hbase : (rowsFrom P Q s).updateRow i (Q i) = rowsFrom P Q s := by
    simpa [rowsFrom, hi] using
      _root_.Matrix.updateRow_eq_self (rowsFrom P Q s) i
  have hrow : P i = (P i - Q i) + Q i := by
    ext c
    simp
  rw [hins, hrow, _root_.Matrix.det_updateRow_add, hbase]
  simp [oneRowDifference]

private theorem prod_le_pow_mul_of_distinguished
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : ι → ℝ) {S δ : ℝ}
    (hf : ∀ j, 0 ≤ f j) (_hS : 0 ≤ S) (hδ : 0 ≤ δ)
    (hi : f i ≤ δ) (hrest : ∀ j, j ≠ i → f j ≤ S) :
    (∏ j, f j) ≤ S ^ (Fintype.card ι - 1) * δ := by
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  calc
    (∏ j, f j) = f i * (Finset.univ.erase i).prod f := by
      symm
      exact Finset.mul_prod_erase (Finset.univ : Finset ι) f hmem
    _ ≤ δ * (Finset.univ.erase i).prod (fun _ => S) := by
      apply mul_le_mul hi
      · apply Finset.prod_le_prod
        · intro j _
          exact hf j
        · intro j hj
          exact hrest j (Finset.ne_of_mem_erase hj)
      · exact Finset.prod_nonneg fun j _ => hf j
      · exact hδ
    _ = δ * S ^ (Fintype.card ι - 1) := by
      congr 1
      rw [Finset.prod_const]
      congr 1
      simp
    _ = S ^ (Fintype.card ι - 1) * δ := mul_comm _ _

private theorem abs_det_rowsFrom_insert_sub_le_max
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) (s : Finset ι)
    (i : ι) (hi : i ∉ s) :
    |(rowsFrom (stdMatrix P) (stdMatrix Q) (insert i s)).det -
      (rowsFrom (stdMatrix P) (stdMatrix Q) s).det| ≤
      (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
  rw [det_rowsFrom_insert_sub (stdMatrix P) (stdMatrix Q) s i hi]
  apply (Matrix.abs_det_le_prod_rowL1Norm _).trans
  apply prod_le_pow_mul_of_distinguished i
  · intro j
    unfold Matrix.rowL1Norm
    positivity
  · positivity
  · positivity
  · have h := rowL1_stdMatrix_le_opNorm (P - Q) i
    rw [stdMatrix_sub] at h
    simpa [oneRowDifference, Matrix.rowL1Norm, _root_.Matrix.updateRow] using h
  · intro j hji
    by_cases hjs : j ∈ s
    · simpa [oneRowDifference, Matrix.rowL1Norm, _root_.Matrix.updateRow,
        hji, rowsFrom, hjs] using
        (rowL1_stdMatrix_le_opNorm P j).trans (le_max_left _ _)
    · simpa [oneRowDifference, Matrix.rowL1Norm, _root_.Matrix.updateRow,
        hji, rowsFrom, hjs] using
        (rowL1_stdMatrix_le_opNorm Q j).trans (le_max_right _ _)

private theorem abs_det_rowsFrom_sub_le_max
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) (s : Finset ι) :
    |(rowsFrom (stdMatrix P) (stdMatrix Q) s).det - (stdMatrix Q).det| ≤
      (s.card : ℝ) * (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      calc
        |(rowsFrom (stdMatrix P) (stdMatrix Q) (insert i s)).det -
            (stdMatrix Q).det| ≤
            |(rowsFrom (stdMatrix P) (stdMatrix Q) (insert i s)).det -
              (rowsFrom (stdMatrix P) (stdMatrix Q) s).det| +
            |(rowsFrom (stdMatrix P) (stdMatrix Q) s).det -
              (stdMatrix Q).det| := abs_sub_le _ _ _
        _ ≤ (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ +
            (s.card : ℝ) * (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ :=
          add_le_add (abs_det_rowsFrom_insert_sub_le_max P Q s i hi) ih
        _ = ((insert i s).card : ℝ) *
              (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
          simp [hi]
          ring

private theorem det_stdMatrix
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    (stdMatrix A).det = LinearMap.det (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
  rw [stdMatrix_eq_toMatrix']
  exact LinearMap.det_toMatrix' (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- Strong determinant difference estimate for finite Pi spaces with their sup norm. -/
theorem abs_det_sub_le_max
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    |LinearMap.det (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) -
      LinearMap.det (Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| ≤
      (Fintype.card ι : ℝ) *
        (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
  simpa [det_stdMatrix] using
    abs_det_rowsFrom_sub_le_max P Q (Finset.univ : Finset ι)

/-- Source-compatible determinant difference estimate using `‖P‖ + ‖Q‖`. -/
theorem abs_det_sub_le
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    |LinearMap.det (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) -
      LinearMap.det (Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| ≤
      (Fintype.card ι : ℝ) *
        (‖P‖ + ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
  calc
    |LinearMap.det (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) -
      LinearMap.det (Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| ≤
        (Fintype.card ι : ℝ) *
          (max ‖P‖ ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ :=
      abs_det_sub_le_max P Q
    _ ≤ (Fintype.card ι : ℝ) *
        (‖P‖ + ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
      have hmax : max ‖P‖ ‖Q‖ ≤ ‖P‖ + ‖Q‖ := by
        exact max_le
          (le_add_of_nonneg_right (norm_nonneg Q))
          (le_add_of_nonneg_left (norm_nonneg P))
      gcongr

/-- Norm-valued form of `abs_det_sub_le`. -/
theorem norm_det_sub_le
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    ‖LinearMap.det (P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) -
      LinearMap.det (Q : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))‖ ≤
      (Fintype.card ι : ℝ) *
        (‖P‖ + ‖Q‖) ^ (Fintype.card ι - 1) * ‖P - Q‖ := by
  simpa only [Real.norm_eq_abs] using abs_det_sub_le P Q

end ContinuousLinearMap
end MathlibAnnex
