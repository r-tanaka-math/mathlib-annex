/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Bounded coefficients as continuous functionals on ℓ¹

The pairing is bilinear: `a ↦ ∑' i, a i * u i`, without conjugating the
coefficient. It is constructed as a continuous linear map, not assumed as a
provider. Evaluation on single-coordinate vectors recovers the coefficients;
finite-support density gives the reverse representation of every continuous
functional. The index type is arbitrary. Nonemptiness is used only for the
norm-one conclusion for unimodular coefficients.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set
open scoped lp ENNReal

universe u v

namespace lp

variable {ι : Type u} {𝕜 : Type v} [RCLike 𝕜]

/-- Absolute summability of the bounded-coefficient pairing. -/
theorem summable_norm_mul_coefficients (a : ℓ¹(ι, 𝕜)) (u : ℓ^∞(ι, 𝕜)) :
    Summable (fun i => ‖a i * u i‖) := by
  have ha : Summable (fun i => ‖a i‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.memℓp a).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  apply (ha.mul_right ‖u‖).of_norm_bounded
  intro i
  rw [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u i) (norm_nonneg _)

/-- The pairing series itself is summable over the complete scalar field. -/
theorem summable_mul_coefficients (a : ℓ¹(ι, 𝕜)) (u : ℓ^∞(ι, 𝕜)) :
    Summable (fun i => a i * u i) :=
  (summable_norm_mul_coefficients a u).of_norm

/-- The sharp upper estimate for the coefficient pairing. -/
theorem norm_tsum_mul_coefficients_le (a : ℓ¹(ι, 𝕜)) (u : ℓ^∞(ι, 𝕜)) :
    ‖∑' i, a i * u i‖ ≤ ‖u‖ * ‖a‖ := by
  have ha : HasSum (fun i => ‖a i‖) ‖a‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      lp.hasSum_norm (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  have hb := tsum_of_norm_bounded (ha.mul_right ‖u‖) (fun i =>
    (norm_mul (a i) (u i)).le.trans
      (mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm ENNReal.top_ne_zero u i) (norm_nonneg _)))
  simpa only [mul_comm] using hb

/-- The continuous functional on ℓ¹ associated to bounded coefficients. -/
def coefficientFunctional (u : ℓ^∞(ι, 𝕜)) : StrongDual 𝕜 ℓ¹(ι, 𝕜) :=
  LinearMap.mkContinuous
    { toFun a := ∑' i, a i * u i
      map_add' a b := by
        change (∑' i, (a i + b i) * u i) =
          (∑' i, a i * u i) + ∑' i, b i * u i
        simpa only [add_mul] using
          (summable_mul_coefficients a u).tsum_add (summable_mul_coefficients b u)
      map_smul' c a := by
        change (∑' i, (c * a i) * u i) = c * ∑' i, a i * u i
        simp only [mul_assoc, tsum_mul_left] }
    ‖u‖ (fun a => norm_tsum_mul_coefficients_le a u)

@[simp]
theorem coefficientFunctional_apply (u : ℓ^∞(ι, 𝕜)) (a : ℓ¹(ι, 𝕜)) :
    coefficientFunctional u a = ∑' i, a i * u i := rfl

-- Coordinate vectors use decidable equality; all index types admit it classically.
variable [DecidableEq ι]

/-- Every coefficient is recovered on the corresponding coordinate vector. -/
@[simp]
theorem coefficientFunctional_single (u : ℓ^∞(ι, 𝕜)) (i : ι) (c : 𝕜) :
    coefficientFunctional u (lp.single 1 i c) = c * u i := by
  rw [coefficientFunctional_apply, tsum_eq_single i, lp.single_apply_self]
  intro j hji
  change (lp.single (E := fun _ : ι => 𝕜) 1 i c) j * u j = 0
  have hz : (lp.single (E := fun _ : ι => 𝕜) 1 i c) j = 0 :=
    lp.single_apply_ne (E := fun _ : ι => 𝕜) 1 i c hji
  exact (congrArg (fun z : 𝕜 => z * u j) hz).trans (zero_mul _)

/-- The operator norm is exactly the ℓ∞ coefficient norm, also for an empty index type. -/
@[simp]
theorem norm_coefficientFunctional (u : ℓ^∞(ι, 𝕜)) :
    ‖coefficientFunctional u‖ = ‖u‖ := by
  apply le_antisymm
  · exact (coefficientFunctional u).opNorm_le_bound (norm_nonneg _)
      (fun a => norm_tsum_mul_coefficients_le a u)
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro i
    have h := (coefficientFunctional u).le_opNorm (lp.single 1 i (1 : 𝕜))
    simpa only [coefficientFunctional_single, one_mul,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one, mul_one] using h

/-- Equal pairing functionals have equal coefficient sequences. -/
theorem coefficientFunctional_injective :
    Function.Injective (coefficientFunctional : ℓ^∞(ι, 𝕜) → StrongDual 𝕜 ℓ¹(ι, 𝕜)) := by
  intro u v h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun f : StrongDual 𝕜 ℓ¹(ι, 𝕜) => f (lp.single 1 i 1)) h
  simpa only [coefficientFunctional_single, one_mul] using hi

/-- Coordinate values of a continuous ℓ¹ functional form a bounded sequence. -/
def dualCoefficients (f : StrongDual 𝕜 ℓ¹(ι, 𝕜)) : ℓ^∞(ι, 𝕜) := by
  refine ⟨fun i => f (lp.single 1 i 1), memℓp_infty ⟨‖f‖, ?_⟩⟩
  rintro r ⟨i, rfl⟩
  simpa only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one, mul_one]
    using f.le_opNorm (lp.single 1 i (1 : 𝕜))

@[simp]
theorem dualCoefficients_apply (f : StrongDual 𝕜 ℓ¹(ι, 𝕜)) (i : ι) :
    dualCoefficients f i = f (lp.single 1 i 1) := rfl

/-- Finite-support density proves representation of every continuous functional. -/
@[simp]
theorem coefficientFunctional_dualCoefficients (f : StrongDual 𝕜 ℓ¹(ι, 𝕜)) :
    coefficientFunctional (dualCoefficients f) = f := by
  apply lp.ext_continuousLinearMap (by simp : (1 : ℝ≥0∞) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  change coefficientFunctional (dualCoefficients f) (lp.single 1 i c) =
    f (lp.single 1 i c)
  rw [coefficientFunctional_single, dualCoefficients_apply]
  have hs : lp.single (E := fun _ : ι => 𝕜) 1 i c = c • lp.single 1 i (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ι => 𝕜) 1 i c (1 : 𝕜)
  rw [hs, map_smul, smul_eq_mul]

@[simp]
theorem dualCoefficients_coefficientFunctional (u : ℓ^∞(ι, 𝕜)) :
    dualCoefficients (coefficientFunctional u) = u := by
  apply Subtype.ext
  funext i
  simp only [dualCoefficients_apply, coefficientFunctional_single, one_mul]

/-- The reverse coefficient representation also preserves norm. -/
@[simp]
theorem norm_dualCoefficients (f : StrongDual 𝕜 ℓ¹(ι, 𝕜)) : ‖dualCoefficients f‖ = ‖f‖ := by
  rw [← norm_coefficientFunctional, coefficientFunctional_dualCoefficients]

/-- Linearity in the coefficient sequence. -/
theorem coefficientFunctional_add (u v : ℓ^∞(ι, 𝕜)) :
    coefficientFunctional (u + v) = coefficientFunctional u + coefficientFunctional v := by
  apply ContinuousLinearMap.ext
  intro a
  change (∑' i, a i * (u i + v i)) = (∑' i, a i * u i) + ∑' i, a i * v i
  simpa only [mul_add] using
    (summable_mul_coefficients a u).tsum_add (summable_mul_coefficients a v)

/-- Scalar multiplication does not conjugate the coefficient. -/
theorem coefficientFunctional_smul (c : 𝕜) (u : ℓ^∞(ι, 𝕜)) :
    coefficientFunctional (c • u) = c • coefficientFunctional u := by
  apply ContinuousLinearMap.ext
  intro a
  change (∑' i, a i * (c * u i)) = c * ∑' i, a i * u i
  calc
    (∑' i, a i * (c * u i)) = ∑' i, c * (a i * u i) :=
      tsum_congr (fun i => mul_left_comm (a i) c (u i))
    _ = c * ∑' i, a i * u i := tsum_mul_left

/-- Negation in the bounded coefficient family. -/
theorem coefficientFunctional_neg (u : ℓ^∞(ι, 𝕜)) :
    coefficientFunctional (-u) = -coefficientFunctional u := by
  rw [← neg_one_smul 𝕜 u, coefficientFunctional_smul]
  apply ContinuousLinearMap.ext
  intro a
  change (-1 : 𝕜) * coefficientFunctional u a = -coefficientFunctional u a
  rw [neg_one_mul]

/-- Subtraction in the bounded coefficient family. -/
theorem coefficientFunctional_sub (u v : ℓ^∞(ι, 𝕜)) :
    coefficientFunctional (u - v) = coefficientFunctional u - coefficientFunctional v := by
  rw [sub_eq_add_neg, coefficientFunctional_add, coefficientFunctional_neg, sub_eq_add_neg]

/-- Nonzero scalar multiplication leaves the kernel set unchanged. -/
theorem preimage_zero_coefficientFunctional_smul (u : ℓ^∞(ι, 𝕜))
    {c : 𝕜} (hc : c ≠ 0) :
    (coefficientFunctional (c • u) : ℓ¹(ι, 𝕜) → 𝕜) ⁻¹' {0} =
      (coefficientFunctional u : ℓ¹(ι, 𝕜) → 𝕜) ⁻¹' {0} := by
  rw [coefficientFunctional_smul]
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ContinuousLinearMap.smul_apply,
    smul_eq_mul, mul_eq_zero, hc, false_or]

/-- An everywhere unimodular family, as an actual bounded sequence. -/
def inftyOfNormOne (u : ι → 𝕜) (hu : ∀ i, ‖u i‖ = 1) : ℓ^∞(ι, 𝕜) :=
  ⟨u, memℓp_infty ⟨1, by rintro r ⟨i, rfl⟩; exact (hu i).le⟩⟩

@[simp]
theorem inftyOfNormOne_apply (u : ι → 𝕜) (hu : ∀ i, ‖u i‖ = 1) (i : ι) :
    inftyOfNormOne u hu i = u i := rfl

/-- Unimodular coefficients give a norm-one functional when there is a coordinate. -/
theorem norm_coefficientFunctional_eq_one_of_forall_norm_eq_one [Nonempty ι]
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1) : ‖coefficientFunctional u‖ = 1 := by
  rw [norm_coefficientFunctional]
  apply le_antisymm
  · exact lp.norm_le_of_forall_le zero_le_one (fun i => (hu i).le)
  · have h := lp.norm_apply_le_norm ENNReal.top_ne_zero u (Classical.arbitrary ι)
    rwa [hu] at h

end lp
