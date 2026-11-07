import BanachGeometry.SequenceSpaces.UnitBall
import BanachGeometry.SequenceSpaces.C0Blocks
import BanachGeometry.SequenceSpaces.L1Separable
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped ENNReal

/-! Explicit Banach-space duality maps for a heterogeneous c₀ sum. Inverse maps and
bounds ‖sumEval φ‖≤‖φ‖ and ‖coeff f‖≤2‖f‖ suffice here for dual separability.
Exact isometry is proved downstream in WeakSequences/C0DualIsometry. No norm
attainment or abstract duality theorem is supplied as an unproved input.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace C0Dual
variable (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
abbrev CoordinateDual (j : ℕ) := V j →L[ℝ] ℝ
abbrev L1Dual := L1Sum (CoordinateDual V)
abbrev Dual := C0Sum V →L[ℝ] ℝ

def coefficient (f : Dual V) (j : ℕ) : CoordinateDual V j :=
  f.comp (C0Sum.singleLinearIsometry (E := V) j).toContinuousLinearMap

theorem sum_norm_coefficient_le (f : Dual V) (s : Finset ℕ) :
    (∑ j ∈ s, ‖coefficient V f j‖) ≤ 2 * ‖f‖ := by
  classical
  choose v hv hnorm using fun j => UnitBall.exists_half_norm_eval (coefficient V f j)
  let u : ℕ → C0Sum V := fun j => C0Sum.single j (v j)
  have hu : ∀ j, ‖u j‖ ≤ 1 := by intro j; simpa only [u, C0Sum.norm_single] using hv j
  have hd : C0Sum.CoordinateDisjoint V u := by
    intro j k hjk i
    by_cases hi : i = j
    · subst i
      exact Or.inr (C0Sum.single_apply_ne k (v k) hjk)
    · exact Or.inl (C0Sum.single_apply_ne j (v j) hi)
  let w := ∑ j ∈ s, u j
  have hw : ‖w‖ ≤ 1 := by
    simpa only [one_smul] using C0Sum.norm_sum_smul_le_one V u hd hu
      (fun _ => 1) (by intro j; norm_num) s
  have heval : (∑ j ∈ s, coefficient V f j (v j)) = f w := by
    simp only [w, u, map_sum, coefficient, ContinuousLinearMap.comp_apply]
    rfl
  calc
    (∑ j ∈ s, ‖coefficient V f j‖) ≤ ∑ j ∈ s, 2 * coefficient V f j (v j) :=
      Finset.sum_le_sum (fun j hj => hnorm j)
    _ = 2 * f w := by rw [← Finset.mul_sum, heval]
    _ ≤ 2 * ‖f w‖ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 2 * (‖f‖ * ‖w‖) := mul_le_mul_of_nonneg_left (f.le_opNorm _) (by norm_num)
    _ ≤ 2 * ‖f‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hw (norm_nonneg f)]

theorem summable_norm_coefficient (f : Dual V) : Summable (fun j => ‖coefficient V f j‖) :=
  summable_of_sum_le (fun j => norm_nonneg _) (sum_norm_coefficient_le V f)

def coefficients (f : Dual V) : L1Dual V := ⟨coefficient V f, by
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_one, Real.rpow_one] using summable_norm_coefficient V f⟩

@[simp] theorem coefficients_apply (f : Dual V) (j : ℕ) : coefficients V f j = coefficient V f j := rfl

theorem norm_coefficients_le (f : Dual V) : ‖coefficients V f‖ ≤ 2 * ‖f‖ := by
  rw [l1_norm_eq_tsum]
  exact Real.tsum_le_of_sum_le (fun j => norm_nonneg _) (sum_norm_coefficient_le V f)

theorem summable_norm_eval (φ : L1Dual V) (x : C0Sum V) : Summable (fun j => ‖φ j (x j)‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
  · intro j
    exact ((φ j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (x.norm_apply_le j) (norm_nonneg _))
  · exact (l1_summable φ).mul_right ‖x‖

theorem summable_eval (φ : L1Dual V) (x : C0Sum V) : Summable (fun j => φ j (x j)) :=
  (summable_norm_eval V φ x).of_norm

theorem norm_tsum_eval_le (φ : L1Dual V) (x : C0Sum V) : ‖∑' j, φ j (x j)‖ ≤ ‖φ‖ * ‖x‖ := by
  calc
    _ ≤ ∑' j, ‖φ j (x j)‖ := norm_tsum_le_tsum_norm (summable_norm_eval V φ x)
    _ ≤ ∑' j, ‖φ j‖ * ‖x‖ :=
      (summable_norm_eval V φ x).tsum_le_tsum
        (fun j => ((φ j).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (x.norm_apply_le j) (norm_nonneg _)))
        ((l1_summable φ).mul_right ‖x‖)
    _ = ‖φ‖ * ‖x‖ := by rw [tsum_mul_right, ← l1_norm_eq_tsum]

def sumEval (φ : L1Dual V) : Dual V :=
  ({ toFun := fun x => ∑' j, φ j (x j)
     map_add' := by
       intro x y
       simp only [C0Sum.add_apply, map_add]
       exact (summable_eval V φ x).tsum_add (summable_eval V φ y)
     map_smul' := by
       intro r x
       simp only [C0Sum.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
       rw [tsum_mul_left] } : C0Sum V →ₗ[ℝ] ℝ).mkContinuous ‖φ‖ (norm_tsum_eval_le V φ)

theorem norm_sumEval_le (φ : L1Dual V) : ‖sumEval V φ‖ ≤ ‖φ‖ :=
  (sumEval V φ).opNorm_le_bound (norm_nonneg _) (norm_tsum_eval_le V φ)

theorem sumEval_coefficients (f : Dual V) : sumEval V (coefficients V f) = f := by
  ext x
  have hs := (summable_eval V (coefficients V f) x).hasSum.tendsto_sum_nat
  have hf := (f.continuous.tendsto x).comp (C0Sum.tendsto_head V x)
  have heq (n : ℕ) : (∑ j ∈ Finset.range n, coefficients V f j (x j)) = f (C0Sum.head V n x) := by
    simp only [C0Sum.head, map_sum, coefficients_apply, coefficient, ContinuousLinearMap.comp_apply]
    rfl
  change (∑' j, coefficients V f j (x j)) = f x
  exact tendsto_nhds_unique hs (by simpa only [Function.comp_def, heq] using hf)

theorem coefficients_sumEval (φ : L1Dual V) : coefficients V (sumEval V φ) = φ := by
  apply lp.ext
  funext j
  ext v
  change (∑' i, φ i (C0Sum.single j v i)) = φ j v
  calc
    _ = φ j (C0Sum.single j v j) := tsum_eq_single j (by
      intro i hij
      rw [C0Sum.single_apply_ne j v hij, map_zero])
    _ = φ j v := by rw [C0Sum.single_apply_self]

def coefficientCLM : Dual V →L[ℝ] L1Dual V := by
  let f : Dual V →ₗ[ℝ] L1Dual V :=
    { toFun := coefficients V
      map_add' := by
        intro f g; apply lp.ext; funext j; ext v
        change (f + g) (C0Sum.single j v) = _
        rfl
      map_smul' := by
        intro r f; apply lp.ext; funext j; ext v
        change (r • f) (C0Sum.single j v) = _
        rfl }
  refine ⟨f, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound f 2 (norm_coefficients_le V)

def sumEvalCLM : L1Dual V →L[ℝ] Dual V := by
  let g : L1Dual V →ₗ[ℝ] Dual V :=
    { toFun := sumEval V
      map_add' := by
        intro φ ψ; ext x
        change (∑' j, (φ j + ψ j) (x j)) = (∑' j, φ j (x j)) + ∑' j, ψ j (x j)
        simp only [ContinuousLinearMap.add_apply]
        exact (summable_eval V φ x).tsum_add (summable_eval V ψ x)
      map_smul' := by
        intro r φ; ext x
        change (∑' j, (r • φ j) (x j)) = r * ∑' j, φ j (x j)
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [tsum_mul_left] }
  refine ⟨g, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound g 1 (by
    intro φ
    change ‖sumEval V φ‖ ≤ 1 * ‖φ‖
    simpa only [one_mul] using norm_sumEval_le V φ)

def equiv : Dual V ≃L[ℝ] L1Dual V where
  toLinearEquiv :=
    { toFun := coefficients V
      invFun := sumEval V
      left_inv := sumEval_coefficients V
      right_inv := coefficients_sumEval V
      map_add' := (coefficientCLM V).map_add
      map_smul' := (coefficientCLM V).map_smul }
  continuous_toFun := (coefficientCLM V).continuous
  continuous_invFun := (sumEvalCLM V).continuous

theorem separableSpace_dual [∀ j, SeparableSpace (CoordinateDual V j)] : SeparableSpace (Dual V) :=
  (equiv V).symm.surjective.denseRange.separableSpace (equiv V).symm.continuous

end C0Dual
end BanachGeometry
