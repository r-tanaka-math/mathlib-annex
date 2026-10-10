/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SelfAdjointApproximation
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.BoundedTransform

/-!
# Simultaneous self-adjoint approximation with a source norm budget

For strict contractions, take a scalar-CFC preimage of the bounded transform,
request its two resolvent vectors, and apply nonunital CFC to the resulting
self-adjoint element of the original algebra. The closed-ball statement
first shrinks the target by a quantitatively chosen scalar, not the
uncontrolled approximant. The final theorem allows a common nonnegative
norm budget, including budget zero and empty test families.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {J : I → Type t} [∀ i, Fintype (J i)]
variable {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Strict target contractions admit simultaneous self-adjoint approximation
by a contraction in the original, possibly nonunital, algebra. -/
theorem exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_norm_lt_one
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : ∀ i, J i → H i) (T : ∀ i, H i →L[ℂ] H i)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hTnorm : ∀ i, ‖T i‖ < 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i j, ‖pi i a (x i j) - T i (x i j)‖ < epsilon := by
  classical
  letI : ∀ i, Nontrivial (H i) := fun i => nontrivial_of_isNonzero (pi i) (hirr i).1
  let S : ∀ i, H i →L[ℂ] H i := fun i => strictContractionPreimage (T i)
  have hS (i : I) : IsSelfAdjoint (S i) := isSelfAdjoint_strictContractionPreimage (T i)
  let y : ∀ i, Sum (J i) (J i) → H i := fun i => Sum.elim
    (fun j => lowerSelfAdjointResolvent (S i) (x i j))
    (fun j => upperSelfAdjointResolvent (S i) (x i j))
  obtain ⟨b, hb, happ⟩ := exists_selfAdjoint_forall_apply_sub_norm_lt
    pi hirr hne y S hS (half_pos hepsilon)
  refine ⟨cfcₙ boundedSelfAdjointScalar b, isSelfAdjoint_cfcₙ_boundedSelfAdjointScalar b,
    norm_cfcₙ_boundedSelfAdjointScalar_le_one b, ?_⟩
  intro i j
  have hpre : boundedSelfAdjointTransform (S i) = T i :=
    boundedSelfAdjointTransform_strictContractionPreimage (hT i) (hTnorm i)
  have hlow : ‖(S i - pi i b) (lowerSelfAdjointResolvent (S i) (x i j))‖ < epsilon / 2 := by
    have hh := happ i (Sum.inl j)
    change ‖pi i b (lowerSelfAdjointResolvent (S i) (x i j)) -
      S i (lowerSelfAdjointResolvent (S i) (x i j))‖ < epsilon / 2 at hh
    simpa only [ContinuousLinearMap.sub_apply, norm_sub_rev] using hh
  have hupp : ‖(S i - pi i b) (upperSelfAdjointResolvent (S i) (x i j))‖ < epsilon / 2 := by
    have hh := happ i (Sum.inr j)
    change ‖pi i b (upperSelfAdjointResolvent (S i) (x i j)) -
      S i (upperSelfAdjointResolvent (S i) (x i j))‖ < epsilon / 2 at hh
    simpa only [ContinuousLinearMap.sub_apply, norm_sub_rev] using hh
  rw [(pi i).map_cfcₙ_boundedSelfAdjointScalar b hb, ← hpre]
  have hbound := norm_boundedSelfAdjointTransform_sub_apply_le (hb.map (pi i)) (hS i) (x i j)
  change ‖(boundedSelfAdjointTransform (pi i b) - boundedSelfAdjointTransform (S i)) (x i j)‖ < _
  exact hbound.trans_lt (by linarith)

/-- Simultaneous approximation of self-adjoint contractions on arbitrary
finite test families by one self-adjoint contraction in the original algebra.
The algebra need not be unital or faithfully represented. -/
theorem exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : ∀ i, J i → H i) (T : ∀ i, H i →L[ℂ] H i)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hTnorm : ∀ i, ‖T i‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i j, ‖pi i a (x i j) - T i (x i j)‖ < epsilon := by
  classical
  by_cases htests : Nonempty (Sigma J)
  swap
  · exact ⟨0, IsSelfAdjoint.zero A, by simp, fun i j => (htests ⟨⟨i, j⟩⟩).elim⟩
  let M : ℝ := ∑ q : Sigma J, ‖x q.1 q.2‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun q _ => norm_nonneg (x q.1 q.2))
  have hxM (i : I) (j : J i) : ‖x i j‖ ≤ M :=
    Finset.single_le_sum (fun (q : Sigma J) _ => norm_nonneg (x q.1 q.2))
      (Finset.mem_univ (⟨i, j⟩ : Sigma J))
  let d : ℝ := min (1 / 2) (epsilon / (2 * (M + 1)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hde : d ≤ epsilon / (2 * (M + 1)) := min_le_right _ _
  have hbudget : d * M < epsilon / 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp hde
    nlinarith
  let r : ℝ := 1 - d
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let S : ∀ i, H i →L[ℂ] H i := fun i => (r : ℂ) • T i
  have hS (i : I) : IsSelfAdjoint (S i) := by
    rw [isSelfAdjoint_iff]
    simp [S, star_smul, (hT i).star_eq]
  have hSnorm (i : I) : ‖S i‖ < 1 := by
    calc
      ‖S i‖ = r * ‖T i‖ := by
        simp [S, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left (hTnorm i) hr.le
      _ < 1 := by simpa using hr1
  obtain ⟨a, ha, hanorm, happ⟩ :=
    exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_norm_lt_one
      pi hirr hne x S hS hSnorm (half_pos hepsilon)
  refine ⟨a, ha, hanorm, fun i j => ?_⟩
  have htail : ‖S i (x i j) - T i (x i j)‖ < epsilon / 2 := by
    have heq : S i (x i j) - T i (x i j) = -(d : ℂ) • T i (x i j) := by
      simp only [S, ContinuousLinearMap.smul_apply]
      calc
        (r : ℂ) • T i (x i j) - T i (x i j) =
            ((r : ℂ) - 1) • T i (x i j) := by rw [sub_smul, one_smul]
        _ = -(d : ℂ) • T i (x i j) := by
          congr 1
          simp [r]
    rw [heq, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    calc
      d * ‖T i (x i j)‖ ≤ d * (‖T i‖ * ‖x i j‖) :=
        mul_le_mul_of_nonneg_left ((T i).le_opNorm _) hd.le
      _ ≤ d * (1 * M) := by gcongr; exact hTnorm i; exact hxM i j
      _ < epsilon / 2 := by simpa using hbudget
  calc
    ‖pi i a (x i j) - T i (x i j)‖ =
        ‖(pi i a (x i j) - S i (x i j)) + (S i (x i j) - T i (x i j))‖ := by
      congr 1
      abel
    _ ≤ ‖pi i a (x i j) - S i (x i j)‖ + ‖S i (x i j) - T i (x i j)‖ :=
      norm_add_le _ _
    _ < epsilon := by linarith [happ i j]

/-- A common source norm budget can be imposed, including budget zero.
This is the version used for geometric residual corrections. -/
theorem exists_selfAdjoint_norm_le_forall_apply_sub_norm_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : ∀ i, J i → H i) (T : ∀ i, H i →L[ℂ] H i)
    (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ C ∧
      ∀ i j, ‖pi i a (x i j) - T i (x i j)‖ < epsilon := by
  classical
  by_cases hzero : C = 0
  · subst C
    have hTzero (i : I) : T i = 0 := norm_eq_zero.mp (le_antisymm (hTC i) (norm_nonneg _))
    exact ⟨0, IsSelfAdjoint.zero A, by simp, by intro i j; simpa [hTzero] using hepsilon⟩
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  let S : ∀ i, H i →L[ℂ] H i := fun i => (C⁻¹ : ℂ) • T i
  have hS (i : I) : IsSelfAdjoint (S i) := by
    rw [isSelfAdjoint_iff]
    simp [S, star_smul, (hT i).star_eq]
  have hSnorm (i : I) : ‖S i‖ ≤ 1 := by
    calc
      ‖S i‖ = C⁻¹ * ‖T i‖ := by
        simp [S, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCpos]
      _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left (hTC i) (inv_nonneg.mpr hC)
      _ = 1 := inv_mul_cancel₀ hzero
  obtain ⟨a, ha, hanorm, happ⟩ := exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt
    pi hirr hne x S hS hSnorm (div_pos hepsilon hCpos)
  refine ⟨(C : ℂ) • a, ?_, ?_, fun i j => ?_⟩
  · rw [isSelfAdjoint_iff]
    simp [star_smul, ha.star_eq]
  · calc
      ‖(C : ℂ) • a‖ = C * ‖a‖ := by
        simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCpos]
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hanorm hC
      _ = C := mul_one _
  · have heq : pi i ((C : ℂ) • a) (x i j) - T i (x i j) =
        (C : ℂ) • (pi i a (x i j) - S i (x i j)) := by
      rw [map_smul]
      simp [S, smul_sub, smul_apply, smul_smul, hzero]
    rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCpos]
    have hh := mul_lt_mul_of_pos_left (happ i j) hCpos
    have hcancel : C * (epsilon / C) = epsilon := by
      rw [mul_comm C (epsilon / C), div_mul_cancel₀ epsilon hzero]
    exact hh.trans_eq hcancel

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
