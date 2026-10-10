/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.Lp.L1Dual
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-!
# Extreme ℓ¹ dual functionals have unimodular coefficients

If a coefficient has norm strictly below one, perturb only that coordinate in
two opposite directions. The exact coefficient-norm formula keeps both actual
continuous functionals in the dual unit ball. Their midpoint is the original
functional and the perturbation is nonzero. This argument proves the required
extreme-point implication without assuming a dual-ball classification.
Extremality is over ℝ, including for complex scalar-valued functionals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped lp ENNReal

universe u v

namespace lp

variable {ι : Type u} [DecidableEq ι] {𝕜 : Type v} [RCLike 𝕜]

/-- Every coefficient of an extreme point of the dual unit ball has norm one. -/
theorem norm_dualCoefficients_apply_eq_one_of_mem_extremePoints
    {f : StrongDual 𝕜 ℓ¹(ι, 𝕜)}
    (hf : f ∈ (closedBall (0 : StrongDual 𝕜 ℓ¹(ι, 𝕜)) 1).extremePoints ℝ) (i : ι) :
    ‖dualCoefficients f i‖ = 1 := by
  let u : ℓ^∞(ι, 𝕜) := dualCoefficients f
  have hunorm : ‖u‖ ≤ 1 := by
    change ‖dualCoefficients f‖ ≤ 1
    rw [norm_dualCoefficients]
    exact mem_closedBall_zero_iff.1 hf.1
  have hu (j : ι) : ‖u j‖ ≤ 1 :=
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u j).trans hunorm
  change ‖u i‖ = 1
  by_contra hne
  have hlt : ‖u i‖ < 1 := by
    rcases lt_or_eq_of_le (hu i) with h | h
    · exact h
    · exact (hne h).elim
  let r : ℝ := (1 - ‖u i‖) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let c : 𝕜 := r • (1 : 𝕜)
  have hcnorm : ‖c‖ = r := by
    dsimp [c]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_one, mul_one]
  have hc : ‖c‖ ≤ 1 - ‖u i‖ := by rw [hcnorm]; dsimp [r]; linarith
  have hcne : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hcnorm]; exact hr.ne')
  let d : StrongDual 𝕜 ℓ¹(ι, 𝕜) := coefficientFunctional (lp.single ∞ i c)
  have hbound (a : 𝕜) (ha : ‖a‖ ≤ 1 - ‖u i‖) :
      ‖coefficientFunctional (u + lp.single ∞ i a)‖ ≤ 1 := by
    rw [norm_coefficientFunctional]
    apply lp.norm_le_of_forall_le zero_le_one
    intro j
    by_cases hji : j = i
    · subst j
      change ‖u i + lp.single (E := fun _ : ι => 𝕜) ∞ i a i‖ ≤ 1
      rw [lp.single_apply_self]
      exact (norm_add_le _ _).trans (by linarith)
    · change ‖u j + lp.single (E := fun _ : ι => 𝕜) ∞ i a j‖ ≤ 1
      have hz : lp.single (E := fun _ : ι => 𝕜) ∞ i a j = 0 :=
        lp.single_apply_ne (E := fun _ : ι => 𝕜) ∞ i a hji
      rw [hz, add_zero]
      exact hu j
  have hplus : ‖f + d‖ ≤ 1 := by
    simpa only [coefficientFunctional_add, u, coefficientFunctional_dualCoefficients, d]
      using hbound c hc
  have hminus : ‖f - d‖ ≤ 1 := by
    simpa only [coefficientFunctional_add, lp.single_neg, coefficientFunctional_neg,
      u, coefficientFunctional_dualCoefficients, sub_eq_add_neg, d]
      using hbound (-c) ((_root_.norm_neg c).le.trans hc)
  have hsegment : f ∈ openSegment ℝ (f + d) (f - d) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_sub]
    calc
      (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • d +
          ((1 / 2 : ℝ) • f - (1 / 2 : ℝ) • d) =
          (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • f := by abel
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • f := (add_smul _ _ _).symm
      _ = f := by norm_num
  have heq : f + d = f := hf.2
    (mem_closedBall_zero_iff.2 hplus) (mem_closedBall_zero_iff.2 hminus) hsegment
  have hd : d = 0 := add_left_cancel (show f + d = f + 0 by simpa only [add_zero] using heq)
  have hval := congrArg (fun q : StrongDual 𝕜 ℓ¹(ι, 𝕜) => q (lp.single 1 i 1)) hd
  apply hcne
  simpa only [d, coefficientFunctional_single, lp.single_apply_self, one_mul,
    ContinuousLinearMap.zero_apply] using hval

end lp
