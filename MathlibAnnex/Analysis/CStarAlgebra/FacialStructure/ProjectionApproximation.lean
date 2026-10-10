/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.BoundedApproximation
import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation

/-!
# Restricted operator-norm control for a finite family

The common finite-vector approximation budget is converted to an
operator-norm budget on every finite-dimensional subspace. The Hilbert
spaces themselves have unrestricted dimension. The norm bound remains
on the original algebra element. This supplies the quantitative input for
successive corrections, not just pointwise or weak approximation.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Simultaneous approximation in the operator norm restricted to each
finite-dimensional subspace, with a common source norm budget. -/
theorem exists_selfAdjoint_norm_le_forall_norm_sub_mul_starProjection_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ C ∧
      ∀ i, ‖(pi i a - T i) * (E i).starProjection‖ < epsilon := by
  classical
  let N : ℝ := ∑ i : I, (Module.finrank ℂ (E i) : ℝ)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hNi (i : I) : (Module.finrank ℂ (E i) : ℝ) ≤ N := by
    change (Module.finrank ℂ (E i) : ℝ) ≤
      ∑ k : I, (Module.finrank ℂ (E k) : ℝ)
    exact Finset.single_le_sum
      (fun k _ => Nat.cast_nonneg (Module.finrank ℂ (E k))) (Finset.mem_univ i)
  let delta : ℝ := epsilon / (N + 1)
  have hd : 0 < delta := div_pos hepsilon (by linarith)
  let x : ∀ i, Fin (Module.finrank ℂ (E i)) → H i :=
    fun i j => ((stdOrthonormalBasis ℂ (E i) j : E i) : H i)
  obtain ⟨a, ha, hanorm, happ⟩ := exists_selfAdjoint_norm_le_forall_apply_sub_norm_lt
    pi hirr hne x T hT C hC hTC hd
  refine ⟨a, ha, hanorm, fun i => ?_⟩
  calc
    ‖(pi i a - T i) * (E i).starProjection‖ ≤
        ∑ j : Fin (Module.finrank ℂ (E i)), ‖(pi i a - T i) (x i j)‖ :=
      norm_comp_starProjection_le_sum (E i) (pi i a - T i)
    _ ≤ ∑ _j : Fin (Module.finrank ℂ (E i)), delta :=
      Finset.sum_le_sum (fun j _ => (happ i j).le)
    _ = (Module.finrank ℂ (E i) : ℝ) * delta := by simp
    _ < (N + 1) * delta :=
      mul_lt_mul_of_pos_right (by linarith [hNi i]) hd
    _ = epsilon := by
      have hden : N + 1 ≠ 0 := ne_of_gt (by linarith)
      dsimp [delta]
      field_simp [hden]

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
