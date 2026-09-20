import MathlibAnnex.Analysis.Normed.Sequence.GeneralizedLimit
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Norm-preserving extension of a bilinear form to bounded-sequence spaces

The same scalar generalized limit is applied after pointwise bilinear
sampling.  This constructs the extension with its exact norm.  Unlike an
ultrapower construction, neither a quotient ideal nor a multiplication law
for the generalized limit is needed.  If the input spaces are C*-algebras,
the bounded-sequence spaces carry the existing pointwise C*-structure.

Controller checkpoint C01.  No arbitrary-bilinear weak compactness is
claimed from this construction alone.  Compilation pending.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology BoundedContinuousFunction

namespace MathlibAnnex.SequenceBilinear

open MathlibAnnex.SequenceLimit

universe u v
variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable {D : Type v} [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- Simultaneous bounded sampling, with one index for the two arguments. -/
def sample (B : A →L[ℂ] D →L[ℂ] ℂ) (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) : ScalarSequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => B (x n) (y n)) (‖B‖ * ‖x‖ * ‖y‖) (by
      intro n
      calc
        ‖B (x n) (y n)‖ ≤ ‖B (x n)‖ * ‖y n‖ := (B (x n)).le_opNorm _
        _ ≤ (‖B‖ * ‖x n‖) * ‖y n‖ := mul_le_mul_of_nonneg_right
          (B.le_opNorm _) (norm_nonneg _)
        _ ≤ (‖B‖ * ‖x‖) * ‖y‖ := by
          gcongr
          · exact norm_coe_le_norm x n
          · exact norm_coe_le_norm y n)

@[simp]
theorem sample_apply (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) (n : ℕ) : sample B x y n = B (x n) (y n) := rfl

theorem norm_sample_le (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) : ‖sample B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  calc
    ‖sample B x y n‖ ≤ ‖B (x n)‖ * ‖y n‖ := (B (x n)).le_opNorm _
    _ ≤ (‖B‖ * ‖x n‖) * ‖y n‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖B‖ * ‖x‖) * ‖y‖ := by
      gcongr
      · exact norm_coe_le_norm x n
      · exact norm_coe_le_norm y n

@[simp]
theorem sample_add_left (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x z : ℕ →ᵇ A) (y : ℕ →ᵇ D) : sample B (x + z) y = sample B x y + sample B z y := by
  ext n
  simp only [sample_apply, BoundedContinuousFunction.add_apply,
    map_add, ContinuousLinearMap.add_apply]

@[simp]
theorem sample_smul_left (B : A →L[ℂ] D →L[ℂ] ℂ)
    (c : ℂ) (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) : sample B (c • x) y = c • sample B x y := by
  ext n
  simp only [sample_apply, BoundedContinuousFunction.smul_apply,
    map_smul, ContinuousLinearMap.smul_apply]

@[simp]
theorem sample_add_right (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : ℕ →ᵇ A) (y z : ℕ →ᵇ D) : sample B x (y + z) = sample B x y + sample B x z := by
  ext n
  simp only [sample_apply, BoundedContinuousFunction.add_apply, map_add]

@[simp]
theorem sample_smul_right (B : A →L[ℂ] D →L[ℂ] ℂ)
    (c : ℂ) (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) : sample B x (c • y) = c • sample B x y := by
  ext n
  simp only [sample_apply, BoundedContinuousFunction.smul_apply, map_smul]

/-- The actual bounded bilinear form on the two sequence spaces. -/
def sequenceExtension (B : A →L[ℂ] D →L[ℂ] ℂ) :
    (ℕ →ᵇ A) →L[ℂ] (ℕ →ᵇ D) →L[ℂ] ℂ :=
  (LinearMap.mk₂ ℂ (fun x y => generalizedLimit (sample B x y))
    (by intro x z y; rw [sample_add_left, map_add])
    (by intro c x y; rw [sample_smul_left, map_smul])
    (by intro x y z; rw [sample_add_right, map_add])
    (by intro c x y; rw [sample_smul_right, map_smul])).mkContinuous₂ ‖B‖ (by
      intro x y
      calc
        ‖generalizedLimit (sample B x y)‖ ≤ ‖generalizedLimit‖ * ‖sample B x y‖ :=
          generalizedLimit.le_opNorm _
        _ = ‖sample B x y‖ := by rw [norm_generalizedLimit, one_mul]
        _ ≤ ‖B‖ * ‖x‖ * ‖y‖ := norm_sample_le B x y)

@[simp]
theorem sequenceExtension_apply (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) :
    sequenceExtension B x y = generalizedLimit (sample B x y) := rfl

/-- Agreement with every ordinary scalar limit, not just constant pairs. -/
theorem sequenceExtension_of_tendsto (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : ℕ →ᵇ A) (y : ℕ →ᵇ D) (z : ℂ)
    (hz : Tendsto (fun n : ℕ => B (x n) (y n)) atTop (𝓝 z)) :
    sequenceExtension B x y = z := generalizedLimit_of_tendsto _ z hz

@[simp]
theorem sequenceExtension_const (B : A →L[ℂ] D →L[ℂ] ℂ) (a : A) (d : D) :
    sequenceExtension B (BoundedContinuousFunction.const ℕ a)
      (BoundedContinuousFunction.const ℕ d) = B a d :=
  sequenceExtension_of_tendsto B _ _ (B a d) tendsto_const_nhds

theorem norm_sequenceExtension_le (B : A →L[ℂ] D →L[ℂ] ℂ) :
    ‖sequenceExtension B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg B) (norm_nonneg x))
  intro y
  calc
    ‖sequenceExtension B x y‖ ≤ ‖generalizedLimit‖ * ‖sample B x y‖ :=
      generalizedLimit.le_opNorm _
    _ = ‖sample B x y‖ := by rw [norm_generalizedLimit, one_mul]
    _ ≤ ‖B‖ * ‖x‖ * ‖y‖ := norm_sample_le B x y

/-- Restriction to constants proves that the extension loses no norm. -/
theorem norm_sequenceExtension (B : A →L[ℂ] D →L[ℂ] ℂ) :
    ‖sequenceExtension B‖ = ‖B‖ := by
  apply le_antisymm (norm_sequenceExtension_le B)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (sequenceExtension B))
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg (sequenceExtension B)) (norm_nonneg a))
  intro d
  let x := BoundedContinuousFunction.const ℕ a
  let y := BoundedContinuousFunction.const ℕ d
  calc
    ‖B a d‖ = ‖sequenceExtension B x y‖ := by rw [sequenceExtension_const]
    _ ≤ ‖sequenceExtension B x‖ * ‖y‖ := (sequenceExtension B x).le_opNorm y
    _ ≤ (‖sequenceExtension B‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right ((sequenceExtension B).le_opNorm x) (norm_nonneg y)
    _ = ‖sequenceExtension B‖ * ‖a‖ * ‖d‖ := by
      simp only [x, y, norm_const_eq]

end MathlibAnnex.SequenceBilinear
