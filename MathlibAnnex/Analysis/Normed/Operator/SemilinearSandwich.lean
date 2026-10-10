/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# Bounded semilinear sandwiches with commuting scalar involutions

The actual equivalence U composed with P composed with the inverse of V,
its inverse, and norm bounds use no inner product or C-star algebra. The two
scalar endomorphisms are explicitly assumed involutive and commuting.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
variable {σ τ : 𝕜 →+* 𝕜} [RingHomInvPair σ σ] [RingHomInvPair τ τ]

/-- The actual bounded equivalence `U ∘ P ∘ V⁻¹`. Commutation of the two
involutive scalar maps identifies its scalar map with that of `P`.
The outer maps need not be equal. No adjoint is used here. -/
def sandwichOfCommute (hcomm : ∀ c : 𝕜, σ (τ c) = τ (σ c))
    (U V : E ≃SL[σ] F) (P : E ≃SL[τ] E) : F ≃SL[τ] F where
  toLinearEquiv :=
    { toEquiv := V.toEquiv.symm.trans (P.toEquiv.trans U.toEquiv)
      map_add' x y := by
        change U (P (V.symm (x + y))) = U (P (V.symm x)) + U (P (V.symm y))
        simp only [map_add]
      map_smul' c x := by
        change U (P (V.symm (c • x))) = τ c • U (P (V.symm x))
        simp only [map_smulₛₗ, hcomm, RingHomInvPair.comp_apply_eq] }
  continuous_toFun := U.continuous.comp (P.continuous.comp V.symm.continuous)
  continuous_invFun := V.continuous.comp (P.symm.continuous.comp U.symm.continuous)

@[simp]
theorem sandwichOfCommute_apply (hcomm : ∀ c : 𝕜, σ (τ c) = τ (σ c))
    (U V : E ≃SL[σ] F) (P : E ≃SL[τ] E) (x : F) :
    sandwichOfCommute hcomm U V P x = U (P (V.symm x)) := rfl

@[simp]
theorem sandwichOfCommute_symm_apply (hcomm : ∀ c : 𝕜, σ (τ c) = τ (σ c))
    (U V : E ≃SL[σ] F) (P : E ≃SL[τ] E) (x : F) :
    (sandwichOfCommute hcomm U V P).symm x = V (P.symm (U.symm x)) := rfl

/-- An explicit bound for the same composite, not a newly chosen bounded map. -/
theorem norm_sandwichOfCommute_apply_le [RingHomIsometric σ] [RingHomIsometric τ]
    (hcomm : ∀ c : 𝕜, σ (τ c) = τ (σ c))
    (U V : E ≃SL[σ] F) (P : E ≃SL[τ] E) (x : F) :
    ‖sandwichOfCommute hcomm U V P x‖ ≤
      (‖U.toContinuousLinearMap‖ * ‖P.toContinuousLinearMap‖ *
        ‖V.symm.toContinuousLinearMap‖) * ‖x‖ := by
  change ‖U (P (V.symm x))‖ ≤ _
  calc
    _ ≤ ‖U.toContinuousLinearMap‖ * ‖P (V.symm x)‖ := U.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖U.toContinuousLinearMap‖ *
        (‖P.toContinuousLinearMap‖ * ‖V.symm x‖) := by
      gcongr
      exact P.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖U.toContinuousLinearMap‖ *
        (‖P.toContinuousLinearMap‖ * (‖V.symm.toContinuousLinearMap‖ * ‖x‖)) := by
      gcongr
      exact V.symm.toContinuousLinearMap.le_opNorm _
    _ = _ := by ring

/-- The inverse bound follows with exactly the reversed factors. -/
theorem norm_sandwichOfCommute_symm_apply_le [RingHomIsometric σ] [RingHomIsometric τ]
    (hcomm : ∀ c : 𝕜, σ (τ c) = τ (σ c))
    (U V : E ≃SL[σ] F) (P : E ≃SL[τ] E) (x : F) :
    ‖(sandwichOfCommute hcomm U V P).symm x‖ ≤
      (‖V.toContinuousLinearMap‖ * ‖P.symm.toContinuousLinearMap‖ *
        ‖U.symm.toContinuousLinearMap‖) * ‖x‖ :=
  norm_sandwichOfCommute_apply_le hcomm V U P.symm x

end ContinuousLinearEquiv

