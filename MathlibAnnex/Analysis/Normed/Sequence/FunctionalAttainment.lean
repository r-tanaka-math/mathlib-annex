import MathlibAnnex.Analysis.Normed.Sequence.GeneralizedLimit
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.SequenceNormAttainment

/-!
# Norm-preserving, norm-attaining extensions of individual functionals

This is the scalar-functional version of the already written sequence argument.
The extension agrees with the original functional on constants.  Its norm is
attained, with positive real value, at one actual bounded sequence of contractions.
No weak compactness, Jordan decomposition, polar decomposition, or invariant mean
is assumed.  C03 controller proof source; not elaborated in this environment.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology BoundedContinuousFunction

namespace MathlibAnnex.SequenceFunctional
open MathlibAnnex.SequenceLimit
open MathlibAnnex.SequenceBilinear (tolerance tolerance_pos tendsto_tolerance_zero
  positivePhase norm_positivePhase positivePhase_mul)

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

def sample (f : StrongDual ℂ X) (x : ℕ →ᵇ X) : ScalarSequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => f (x n)) (‖f‖ * ‖x‖) (by
      intro n
      exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_coe_le_norm x n) (norm_nonneg f)))

@[simp] theorem sample_apply (f : StrongDual ℂ X) (x : ℕ →ᵇ X) (n : ℕ) :
    sample f x n = f (x n) := rfl

theorem norm_sample_le (f : StrongDual ℂ X) (x : ℕ →ᵇ X) :
    ‖sample f x‖ ≤ ‖f‖ * ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (norm_coe_le_norm x n) (norm_nonneg f))

def sampleMap (f : StrongDual ℂ X) : (ℕ →ᵇ X) →L[ℂ] ScalarSequence :=
  ({ toFun := sample f
     map_add' := by intro x y; ext n; simp [sample_apply]
     map_smul' := by intro c x; ext n; simp [sample_apply] } :
    (ℕ →ᵇ X) →ₗ[ℂ] ScalarSequence).mkContinuous ‖f‖ (norm_sample_le f)

def extend (f : StrongDual ℂ X) : StrongDual ℂ (ℕ →ᵇ X) :=
  generalizedLimit.comp (sampleMap f)

@[simp] theorem extend_apply (f : StrongDual ℂ X) (x : ℕ →ᵇ X) :
    extend f x = generalizedLimit (sample f x) := rfl

theorem extend_of_tendsto (f : StrongDual ℂ X) (x : ℕ →ᵇ X) (z : ℂ)
    (h : Tendsto (fun n : ℕ => f (x n)) atTop (𝓝 z)) : extend f x = z :=
  generalizedLimit_of_tendsto _ z h

@[simp] theorem extend_const (f : StrongDual ℂ X) (x : X) :
    extend f (BoundedContinuousFunction.const ℕ x) = f x :=
  extend_of_tendsto f _ _ tendsto_const_nhds

theorem norm_extend_le (f : StrongDual ℂ X) : ‖extend f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro x
  calc
    ‖extend f x‖ ≤ ‖generalizedLimit‖ * ‖sample f x‖ := generalizedLimit.le_opNorm _
    _ = ‖sample f x‖ := by rw [norm_generalizedLimit, one_mul]
    _ ≤ ‖f‖ * ‖x‖ := norm_sample_le f x

@[simp] theorem norm_extend (f : StrongDual ℂ X) : ‖extend f‖ = ‖f‖ := by
  apply le_antisymm (norm_extend_le f)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (extend f))
  intro x
  calc
    ‖f x‖ = ‖extend f (BoundedContinuousFunction.const ℕ x)‖ := by rw [extend_const]
    _ ≤ ‖extend f‖ * ‖BoundedContinuousFunction.const ℕ x‖ := (extend f).le_opNorm _
    _ = ‖extend f‖ * ‖x‖ := by rw [norm_const_eq]

theorem exists_contraction_value_gt (f : StrongDual ℂ X) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ r < ‖f x‖ := by
  by_cases hn : r < 0
  · exact ⟨0, by simp, by simpa using hn⟩
  have hr0 : 0 ≤ r := le_of_not_gt hn
  by_contra h
  push_neg at h
  have hb : ‖f‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hr0
    intro x hx
    exact h x hx.le
  exact (not_lt_of_ge hb) hr

def nearVector (f : StrongDual ℂ X) (n : ℕ) : X :=
  Classical.choose (exists_contraction_value_gt f (sub_lt_self ‖f‖ (tolerance_pos n)))

theorem nearVector_spec (f : StrongDual ℂ X) (n : ℕ) :
    ‖nearVector f n‖ ≤ 1 ∧ ‖f‖ - tolerance n < ‖f (nearVector f n)‖ :=
  Classical.choose_spec (exists_contraction_value_gt f (sub_lt_self ‖f‖ (tolerance_pos n)))

def attainer (f : StrongDual ℂ X) : ℕ →ᵇ X :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => positivePhase (f (nearVector f n)) • nearVector f n) 1 (by
      intro n
      rw [norm_smul, norm_positivePhase, one_mul]
      exact (nearVector_spec f n).1)

theorem norm_attainer_le (f : StrongDual ℂ X) : ‖attainer f‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro n
  change ‖positivePhase (f (nearVector f n)) • nearVector f n‖ ≤ 1
  rw [norm_smul, norm_positivePhase, one_mul]
  exact (nearVector_spec f n).1

@[simp] theorem attainer_value (f : StrongDual ℂ X) (n : ℕ) :
    f (attainer f n) = (‖f (nearVector f n)‖ : ℂ) := by
  change f (positivePhase (f (nearVector f n)) • nearVector f n) = _
  rw [map_smul, smul_eq_mul, positivePhase_mul]

theorem tendsto_near_value (f : StrongDual ℂ X) :
    Tendsto (fun n => ‖f (nearVector f n)‖) atTop (𝓝 ‖f‖) := by
  have hub (n : ℕ) : ‖f (nearVector f n)‖ ≤ ‖f‖ :=
    f.unit_le_opNorm _ (nearVector_spec f n).1
  have hb (n : ℕ) : ‖‖f (nearVector f n)‖ - ‖f‖‖ ≤ tolerance n := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hub n))]
    have hv := (nearVector_spec f n).2
    linarith
  have hz : Tendsto (fun n => ‖‖f (nearVector f n)‖ - ‖f‖‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hb tendsto_tolerance_zero
  have hd := tendsto_zero_iff_norm_tendsto_zero.mpr hz
  convert hd.add_const ‖f‖ using 1 <;> simp

@[simp] theorem extend_attainer (f : StrongDual ℂ X) :
    extend f (attainer f) = (‖f‖ : ℂ) := by
  apply extend_of_tendsto
  simpa only [attainer_value, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_near_value f)

end MathlibAnnex.SequenceFunctional
