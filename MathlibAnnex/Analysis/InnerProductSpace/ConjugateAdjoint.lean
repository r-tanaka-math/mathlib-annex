/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Adjoint of a bounded conjugate-linear map

For V : H -> K conjugate-linear, V* : K -> H is conjugate-linear and satisfies
`inner (V* y) x = inner (V x) y`. Consequently a conjugate-linear pair U,V
transforms a linear operator b into the LINEAR operator V* b U, with a
conjugation in the coefficient identity. The ordinary adjoint is not applied
to an antilinear map. No algebraic, possibly unbounded map is given an adjoint.
-/

set_option autoImplicit false
noncomputable section

namespace InnerProductSpace

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- The linear functional used in the Riesz construction of the antilinear adjoint. -/
def conjugateAdjointFunctional (V : H →L⋆[𝕜] K) (y : K) : StrongDual 𝕜 H :=
  LinearMap.mkContinuous
    { toFun := fun x => inner 𝕜 (V x) y
      map_add' := by intro x z; simp [inner_add_left]
      map_smul' := by
        intro c x
        simp [map_smulₛₗ, inner_smul_left, RCLike.star_def] }
    (‖V‖ * ‖y‖)
    (by
      intro x
      calc
        ‖inner 𝕜 (V x) y‖ ≤ ‖V x‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ (‖V‖ * ‖x‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (V.le_opNorm x) (norm_nonneg _)
        _ = (‖V‖ * ‖y‖) * ‖x‖ := by ring)

@[simp]
theorem conjugateAdjointFunctional_apply (V : H →L⋆[𝕜] K) (y : K) (x : H) :
    conjugateAdjointFunctional V y x = inner 𝕜 (V x) y := rfl

/-- The bounded conjugate-linear adjoint, constructed by the genuine Riesz equivalence. -/
def conjugateAdjoint (V : H →L⋆[𝕜] K) : K →L⋆[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := fun y => (toDual 𝕜 H).symm (conjugateAdjointFunctional V y)
      map_add' := by
        intro y z
        apply (toDual 𝕜 H).injective
        ext x
        simp [conjugateAdjointFunctional_apply, inner_add_right]
      map_smul' := by
        intro c y
        apply (toDual 𝕜 H).injective
        ext x
        simp [conjugateAdjointFunctional_apply, inner_smul_right, map_smulₛₗ,
          RCLike.star_def] }
    ‖V‖
    (by
      intro y
      change ‖(toDual 𝕜 H).symm (conjugateAdjointFunctional V y)‖ ≤ ‖V‖ * ‖y‖
      rw [(toDual 𝕜 H).symm.norm_map]
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      intro x
      change ‖inner 𝕜 (V x) y‖ ≤ ‖V‖ * ‖y‖ * ‖x‖
      calc
        ‖inner 𝕜 (V x) y‖ ≤ ‖V x‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ (‖V‖ * ‖x‖) * ‖y‖ :=
          mul_le_mul_of_nonneg_right (V.le_opNorm x) (norm_nonneg _)
        _ = ‖V‖ * ‖y‖ * ‖x‖ := by ring)

/-- The orientation of the adjoint identity for an antilinear map. -/
theorem conjugateAdjoint_inner_left (V : H →L⋆[𝕜] K) (x : H) (y : K) :
    inner 𝕜 (conjugateAdjoint V y) x = inner 𝕜 (V x) y := by
  exact toDual_symm_apply

/-- The equivalent identity with conjugation, needed for coefficient transport. -/
theorem conjugateAdjoint_inner_right (V : H →L⋆[𝕜] K) (x : H) (y : K) :
    inner 𝕜 x (conjugateAdjoint V y) = star (inner 𝕜 (V x) y) := by
  simpa only [conjugateAdjoint_inner_left, RCLike.star_def] using
    (inner_conj_symm (𝕜 := 𝕜) x (conjugateAdjoint V y)).symm

/-- An antilinear adjoint is involutive, just like its linear counterpart. -/
@[simp]
theorem conjugateAdjoint_conjugateAdjoint (V : H →L⋆[𝕜] K) :
    conjugateAdjoint (conjugateAdjoint V) = V := by
  ext x
  apply ext_inner_right 𝕜
  intro y
  rw [conjugateAdjoint_inner_left, conjugateAdjoint_inner_left]

/-- Two antilinear factors give a linear operator. -/
def conjugateAdjointSandwich (U V : H →L⋆[𝕜] K) (b : K →L[𝕜] K) : H →L[𝕜] H :=
  (conjugateAdjoint V).comp (b.comp U)

/-- The coefficient identity contains a conjugation in the antilinear case. -/
theorem inner_conjugateAdjointSandwich (U V : H →L⋆[𝕜] K)
    (b : K →L[𝕜] K) (x y : H) :
    inner 𝕜 (V y) (b (U x)) = star (inner 𝕜 y (conjugateAdjointSandwich U V b x)) := by
  change inner 𝕜 (V y) (b (U x)) =
    star (inner 𝕜 y (conjugateAdjoint V (b (U x))))
  rw [conjugateAdjoint_inner_right, star_star]

/-- In particular the zero conditions are equivalent, not the unconjugated values. -/
theorem inner_conjugateAdjointSandwich_eq_zero_iff (U V : H →L⋆[𝕜] K)
    (b : K →L[𝕜] K) (x y : H) :
    inner 𝕜 (V y) (b (U x)) = 0 ↔ inner 𝕜 y (conjugateAdjointSandwich U V b x) = 0 := by
  rw [inner_conjugateAdjointSandwich]
  exact star_eq_zero

/-- The literal linear operator V* b U for bounded linear factors. -/
def adjointSandwich (U V : H →L[𝕜] K) (b : K →L[𝕜] K) : H →L[𝕜] H :=
  V.adjoint.comp (b.comp U)

/-- Ordinary linear factors have an unconjugated coefficient identity. -/
theorem inner_adjointSandwich (U V : H →L[𝕜] K)
    (b : K →L[𝕜] K) (x y : H) :
    inner 𝕜 (V y) (b (U x)) = inner 𝕜 y (adjointSandwich U V b x) :=
  (ContinuousLinearMap.adjoint_inner_right V y (b (U x))).symm

variable {σ : 𝕜 →+* 𝕜} [RingHomInvPair σ σ]
variable (U V : H ≃ₛₗ[σ] K)

/-- Opposite coefficient identities force the two operator pullbacks to be inverse. -/
theorem leftInverse_of_inner_semilinear_transport
    (Q : (K →L[𝕜] K) → (H →L[𝕜] H))
    (R : (H →L[𝕜] H) → (K →L[𝕜] K))
    (hQ : ∀ (b : K →L[𝕜] K) (x y : H),
      inner 𝕜 (V y) (b (U x)) = σ (inner 𝕜 y (Q b x)))
    (hR : ∀ (a : H →L[𝕜] H) (x y : K),
      inner 𝕜 (V.symm y) (a (U.symm x)) = σ (inner 𝕜 y (R a x))) :
    Function.LeftInverse Q R := by
  intro a
  ext x
  apply ext_inner_left 𝕜
  intro y
  have hh := congrArg σ (hR a (U x) (V y))
  simp only [LinearEquiv.symm_apply_apply, RingHomInvPair.comp_apply_eq] at hh
  have he := (hQ (R a) x y).symm.trans hh.symm
  have he' := congrArg σ he
  simpa only [RingHomInvPair.comp_apply_eq] using he'

end InnerProductSpace
