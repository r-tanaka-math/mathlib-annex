/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite relations between matrix coefficients

The source slot is linear and the target slot is conjugate-linear. The matrix
criterion consequently has `star (C j k)` in the source equation and `C j k`
in the target equation. Only the span of the finitely many target vectors
is made finite-dimensional. Neither the ambient spaces nor the index type
are assumed nontrivial; the empty sum is included.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Testing on rank-one operators separates a finite coefficient relation. -/
theorem sum_inner_smul_eq_zero_of_sum_matrixCoefficient_eq_zero
    (x : ι → E) (y : ι → F)
    (h : (∑ j, matrixCoefficient 𝕜 (x j) (y j)) = 0) (v : F) :
    ∑ j, inner 𝕜 (y j) v • x j = 0 := by
  classical
  apply ext_inner_left 𝕜
  intro z
  have hz := congrArg
    (fun f : (E →L[𝕜] F) →L[𝕜] 𝕜 => f (rankOne 𝕜 v z)) h
  simpa [matrixCoefficient_apply_rankOne, inner_sum, inner_smul_right, mul_comm]
    using hz

/-- The matrix equations imply the zero relation, even for zero or dependent vectors. -/
theorem sum_matrixCoefficient_eq_zero_of_matrix
    (x : ι → E) (y : ι → F) (C : Matrix ι ι 𝕜)
    (hx : ∀ k, ∑ j, star (C j k) • x j = 0)
    (hy : ∀ j, ∑ k, C j k • y k = y j) :
    (∑ j, matrixCoefficient 𝕜 (x j) (y j)) = 0 := by
  classical
  ext T
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply, matrixCoefficient_apply]
  calc
    (∑ j, inner 𝕜 (y j) (T (x j))) =
        ∑ j, ∑ k, star (C j k) * inner 𝕜 (y k) (T (x j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hy j]
      simp [sum_inner, inner_smul_left, RCLike.star_def]
    _ = ∑ k, ∑ j, star (C j k) * inner 𝕜 (y k) (T (x j)) :=
      Finset.sum_comm
    _ = ∑ k, inner 𝕜 (y k) (T (∑ j, star (C j k) • x j)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [map_sum, inner_sum, inner_smul_right]
    _ = 0 := by simp only [hx, map_zero, inner_zero_right, Finset.sum_const_zero]

/-- A finite matrix coefficient relation is equivalent to the conjugate matrix
criterion. The orthonormal basis is only for `span (range y)`. -/
theorem sum_matrixCoefficient_eq_zero_iff_exists_matrix
    (x : ι → E) (y : ι → F) :
    (∑ j, matrixCoefficient 𝕜 (x j) (y j)) = 0 ↔
      ∃ C : Matrix ι ι 𝕜,
        (∀ k, ∑ j, star (C j k) • x j = 0) ∧
        (∀ j, ∑ k, C j k • y k = y j) := by
  classical
  constructor
  · intro h
    let M : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range y)
    letI : FiniteDimensional 𝕜 M :=
      FiniteDimensional.span_of_finite 𝕜 (Set.finite_range y)
    let e := stdOrthonormalBasis 𝕜 M
    let a : ι → Fin (Module.finrank 𝕜 M) → 𝕜 :=
      fun j l => inner 𝕜 (e l : F) (y j)
    have ha (j : ι) : ∑ l, a j l • (e l : F) = y j := by
      have hrep := congrArg (fun z : M => (z : F))
        (e.sum_repr ⟨y j, Submodule.subset_span (Set.mem_range_self j)⟩)
      simpa [a, OrthonormalBasis.repr_apply_apply] using hrep
    have he (l : Fin (Module.finrank 𝕜 M)) :
        ∃ b : ι → 𝕜, ∑ k, b k • y k = (e l : F) :=
      (Submodule.mem_span_range_iff_exists_fun 𝕜).mp (e l).property
    choose b hb using he
    have hz (l : Fin (Module.finrank 𝕜 M)) :
        ∑ j, star (a j l) • x j = 0 := by
      simpa [a, RCLike.star_def, inner_conj_symm] using
        sum_inner_smul_eq_zero_of_sum_matrixCoefficient_eq_zero x y h (e l : F)
    let C : Matrix ι ι 𝕜 := Matrix.of (fun j k => ∑ l, a j l * b l k)
    refine ⟨C, ?_, ?_⟩
    · intro k
      calc
        (∑ j, star (C j k) • x j) =
            ∑ j, ∑ l, (star (b l k) * star (a j l)) • x j := by
          simp [C, Finset.sum_smul, mul_comm]
        _ = ∑ l, ∑ j, (star (b l k) * star (a j l)) • x j := Finset.sum_comm
        _ = ∑ l, star (b l k) • (∑ j, star (a j l) • x j) := by
          simp only [Finset.smul_sum, mul_smul]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro l _
          rw [hz l, smul_zero]
    · intro j
      calc
        (∑ k, C j k • y k) = ∑ k, ∑ l, (a j l * b l k) • y k := by
          simp [C, Finset.sum_smul]
        _ = ∑ l, ∑ k, (a j l * b l k) • y k := Finset.sum_comm
        _ = ∑ l, a j l • (∑ k, b l k • y k) := by
          simp only [Finset.smul_sum, mul_smul]
        _ = ∑ l, a j l • (e l : F) := by simp only [hb]
        _ = y j := ha j
  · rintro ⟨C, hx, hy⟩
    exact sum_matrixCoefficient_eq_zero_of_matrix x y C hx hy

end InnerProductSpace
