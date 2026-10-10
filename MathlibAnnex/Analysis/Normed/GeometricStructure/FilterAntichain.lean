/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFilter
public import Mathlib.Tactic.Ring

/-!
# Antichain of maximal-filter kernels

A norm-one functional whose kernel is contained in the right orthogonality set
of `x` must attain the norm at `x`. This operator-norm argument gives an
alternative to the affine-coset reconstruction route: it directly proves that
inclusion of maximal-filter kernels forces equality of the filters.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A norm-one functional attains the norm at `x` whenever all of its kernel
vectors are Birkhoff-James orthogonal to `x` on the right. No primal norm
attainment, completeness, or closed-subspace quotient is assumed. -/
theorem mem_absoluteNormingFunctionals_of_kernel_subset {f : StrongDual 𝕜 E}
    (hf : ‖f‖ = 1) {x : E}
    (hker : ∀ y : E, f y = 0 → BirkhoffJamesOrthogonal 𝕜 x y) :
    f ∈ absoluteNormingFunctionals 𝕜 x := by
  have bound (z : E) : ‖x‖ * ‖f z‖ ≤ ‖f x‖ * ‖z‖ := by
    by_cases hfz : f z = 0
    · rw [hfz, norm_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    let a : 𝕜 := f x * (f z)⁻¹
    let y : E := x - a • z
    have hfy : f y = 0 := by
      change f (x - (f x * (f z)⁻¹) • z) = 0
      rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hfz, mul_one, sub_self]
    have hxy := hker y hfy (-1)
    have hcancel : x + (-1 : 𝕜) • y = a • z := by
      simp only [y, neg_one_smul]
      abel
    have hle : ‖x‖ ≤ (‖f x‖ * ‖f z‖⁻¹) * ‖z‖ := by
      simpa only [hcancel, norm_smul, a, norm_mul, norm_inv] using hxy
    have hprod := mul_le_mul_of_nonneg_left hle (norm_nonneg (f z))
    have hnormfz : ‖f z‖ ≠ 0 := norm_ne_zero_iff.mpr hfz
    have heq : ‖f z‖ * ((‖f x‖ * ‖f z‖⁻¹) * ‖z‖) = ‖f x‖ * ‖z‖ := by
      calc
        _ = ‖f x‖ * ((‖f z‖ * ‖f z‖⁻¹) * ‖z‖) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hnormfz, one_mul]
    simpa only [heq, mul_comm ‖f z‖ ‖x‖] using hprod
  have hnorm : ‖(‖x‖ : 𝕜) • f‖ ≤ ‖f x‖ :=
    ((‖x‖ : 𝕜) • f).opNorm_le_bound (norm_nonneg _) (fun z => by
      change ‖(‖x‖ : 𝕜) * f z‖ ≤ ‖f x‖ * ‖z‖
      simpa only [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)] using bound z)
  have hlow : ‖x‖ ≤ ‖f x‖ := by
    simpa only [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x), hf, mul_one]
      using hnorm
  have hupp : ‖f x‖ ≤ ‖x‖ := by simpa only [hf, one_mul] using f.le_opNorm x
  exact ⟨hf.le, le_antisymm hupp hlow⟩

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] [Nontrivial V]

/-- Inclusion of the kernels of two maximal filters forces the filters
themselves to be equal. In particular, their kernels form an antichain. -/
theorem IsMaximalBirkhoffJamesFilter.eq_of_kernel_subset {U W : Set V}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) (hW : IsMaximalBirkhoffJamesFilter 𝕜 W)
    (hUW : birkhoffJamesKernel 𝕜 U ⊆ birkhoffJamesKernel 𝕜 W) : U = W := by
  obtain ⟨f, hf⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
  have hfnorm := hU.norm_eq_one 𝕜 hf
  have hWU : W ⊆ U := by
    rw [hU.eq_absoluteNormAttainmentSet 𝕜 hf]
    intro x hx
    exact (mem_absoluteNormingFunctionals_of_kernel_subset 𝕜 hfnorm (fun y hfy =>
      hUW (fun z hz => birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero
        𝕜 (hf z hz) hfy) x hx)).2
  exact Subset.antisymm (hW.2 hU.1 hWU) hWU

end Normed

end NormedSpace
