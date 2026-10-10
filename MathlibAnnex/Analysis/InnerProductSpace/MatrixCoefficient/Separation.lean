/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Basic
import Mathlib.Tactic

/-!
# Equality at a rank-one test for unit matrix coefficients

Two unit-vector coefficients that both take the value one at the rank-one
operator of the first pair are identical. The equality case of Cauchy--Schwarz
keeps the common scalar phase. Thus this result includes linearly dependent
source vectors and pure phase changes; a different coefficient need not have
absolute value strictly less than one at the test operator.

No completeness, finite dimension or representation-surjectivity hypothesis
is used. This is an assertion on the full bounded-operator space; realizing
its finite action in a C-star algebra is a separate interpolation step.
-/

set_option autoImplicit false
noncomputable section

namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Equality at the rank-one test forces equality of the entire coefficients,
not just equality of the norms of their values. -/
theorem matrixCoefficient_eq_of_apply_rankOne_eq_one
    (x v : E) (y w : F) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (hy : ‖y‖ = 1) (hw : ‖w‖ = 1)
    (h : matrixCoefficient 𝕜 v w (rankOne 𝕜 y x) = 1) :
    matrixCoefficient 𝕜 x y = matrixCoefficient 𝕜 v w := by
  have hx0 : x ≠ 0 := by intro h0; simpa [h0] using hx
  have hv0 : v ≠ 0 := by intro h0; simpa [h0] using hv
  have hprod : inner 𝕜 x v * inner 𝕜 w y = 1 := by
    simpa only [matrixCoefficient_apply_rankOne] using h
  have hn : ‖inner 𝕜 x v‖ * ‖inner 𝕜 w y‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hleft : ‖inner 𝕜 x v‖ ≤ 1 := by
    simpa only [hx, hv, one_mul] using norm_inner_le_norm (𝕜 := 𝕜) x v
  have hright : ‖inner 𝕜 w y‖ ≤ 1 := by
    simpa only [hw, hy, one_mul] using norm_inner_le_norm (𝕜 := 𝕜) w y
  have hleft_eq : ‖inner 𝕜 x v‖ = 1 := le_antisymm hleft <| by
    calc
      1 = ‖inner 𝕜 x v‖ * ‖inner 𝕜 w y‖ := hn.symm
      _ ≤ ‖inner 𝕜 x v‖ * 1 :=
        mul_le_mul_of_nonneg_left hright (norm_nonneg _)
      _ = ‖inner 𝕜 x v‖ := mul_one _
  obtain ⟨c, _, hvc⟩ := (norm_inner_eq_norm_iff (𝕜 := 𝕜) hx0 hv0).mp
    (by simpa only [hx, hv, one_mul] using hleft_eq)
  have hc : ‖c‖ = 1 := by
    simpa only [hvc, norm_smul, hx, mul_one] using hv
  have hcy : ‖c • y‖ = 1 := by rw [norm_smul, hc, hy, one_mul]
  have hwcy : inner 𝕜 w (c • y) = 1 := by
    simpa only [hvc, inner_smul_right,
      inner_self_eq_one_of_norm_eq_one hx, mul_one] using hprod
  have hwc : w = c • y := (inner_eq_one_iff_of_norm_eq_one hw hcy).mp hwcy
  have hphase : c * star c = 1 := by
    have hself := inner_self_eq_one_of_norm_eq_one (𝕜 := 𝕜) hcy
    simpa only [inner_smul_left, inner_smul_right,
      inner_self_eq_one_of_norm_eq_one hy, mul_one, one_mul, RCLike.star_def, mul_comm] using hself
  rw [hvc, hwc, matrixCoefficient_smul_left, matrixCoefficient_smul_right,
    smul_smul, hphase, one_smul]

/-- Distinct unit coefficients are separated by the rank-one test with value
one for the first coefficient. The second value is unequal to one, not
necessarily smaller than one in absolute value. -/
theorem matrixCoefficient_apply_rankOne_ne_one_of_ne
    (x v : E) (y w : F) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (hy : ‖y‖ = 1) (hw : ‖w‖ = 1)
    (hne : matrixCoefficient 𝕜 x y ≠ matrixCoefficient 𝕜 v w) :
    matrixCoefficient 𝕜 v w (rankOne 𝕜 y x) ≠ 1 :=
  fun h => hne (matrixCoefficient_eq_of_apply_rankOne_eq_one x v y w hx hv hy hw h)

end InnerProductSpace
