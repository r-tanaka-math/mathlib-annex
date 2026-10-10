/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.ExposedFace
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Norm attainment from analytic reflexivity

Analytic reflexivity is stated in its defining form: surjectivity of Mathlib's
canonical map into the double continuous dual. This is not algebraic module
reflexivity. Hahn--Banach on the continuous dual, followed by this surjectivity,
supplies an actual norm-attaining vector. Norm attainment and the geometric
structure family are conclusions, not fields of an assumed provider.

No compactness of a norm-topological dual ball is used. The argument needs no
separate completeness hypothesis once surjectivity of the canonical map is given.
-/

@[expose] public section

set_option autoImplicit false

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-one functional on an analytically reflexive space has a nonempty
value-one slice. The double-dual witness is obtained from Hahn--Banach. -/
theorem nonempty_unitBallSupportFace_of_surjective_inclusionInDoubleDual
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E))
    {f : StrongDual 𝕜 E} (hf : ‖f‖ = 1) : (unitBallSupportFace 𝕜 f).Nonempty := by
  obtain ⟨Φ, hΦnorm, hΦf⟩ := exists_dual_vector'' 𝕜 f
  obtain ⟨x, hx⟩ := hreflexive Φ
  have hxnorm : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = ‖inclusionInDoubleDual 𝕜 E x‖ :=
        ((inclusionInDoubleDualLi (E := E) 𝕜).norm_map x).symm
      _ = ‖Φ‖ := congrArg norm hx
      _ ≤ 1 := hΦnorm
  have hfx : f x = 1 := by
    calc
      f x = Φ f := congrArg (fun Ψ : StrongDual 𝕜 (StrongDual 𝕜 E) => Ψ f) hx
      _ = (‖f‖ : 𝕜) := hΦf
      _ = 1 := by rw [hf]; simp
  exact ⟨x, mem_closedBall_zero_iff.2 hxnorm, hfx⟩

/-- The vector supplied by analytic reflexivity can be chosen on the unit sphere. -/
theorem exists_norm_eq_one_apply_eq_one_of_surjective_inclusionInDoubleDual
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E))
    {f : StrongDual 𝕜 E} (hf : ‖f‖ = 1) : ∃ x : E, ‖x‖ = 1 ∧ f x = 1 := by
  obtain ⟨x, hx⟩ := nonempty_unitBallSupportFace_of_surjective_inclusionInDoubleDual
    𝕜 hreflexive hf
  refine ⟨x, ?_, hx.2⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using
    unitBallSupportFace_subset_sphere 𝕜 hf.le hx

/-- Positive real normalization produces a norm-one functional with the same kernel.
The equality is between subsets, with no new quotient or submodule representation. -/
theorem exists_norm_eq_one_preimage_zero_eq_of_ne_zero {f : StrongDual 𝕜 E} (hf : f ≠ 0) :
    ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧
      (g : E → 𝕜) ⁻¹' {0} = (f : E → 𝕜) ⁻¹' {0} := by
  have hpos : 0 < ‖f‖ := norm_pos_iff.2 hf
  refine ⟨(‖f‖⁻¹ : ℝ) • f, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
    exact inv_mul_cancel₀ hpos.ne'
  · apply Set.ext
    intro x
    change (‖f‖⁻¹ : ℝ) • f x = 0 ↔ f x = 0
    simp only [smul_eq_zero, inv_ne_zero hpos.ne', false_or]

end NormedSpace
