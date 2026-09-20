import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.SequenceExtension

/-!
# Actual norm attainment on bounded-sequence spaces

Every bounded complex bilinear form extends, without changing its norm, to
the bounded-sequence spaces of its arguments.  A single pair of contractions
there attains the original norm as a nonnegative real scalar.  The proof
constructs norm-approximating pairs, fixes their phases, and uses the actual
generalized limit supplied by `GeneralizedLimit`.

This is a construction, not an assumption of norm attainment.  The attained
pair consists of contractions; neither unitary attainment nor normalization
at `(1,1)` is asserted.  The downstream C*-normalization bridge is implemented separately in
`NormalizedSequenceForm`; it is not hidden in a Lean axiom.

Controller checkpoint C01.  Not compiled.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology BoundedContinuousFunction

namespace MathlibAnnex.SequenceBilinear

universe u v
variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable {D : Type v} [NormedAddCommGroup D] [NormedSpace ℂ D]

/-- The two operator suprema can be approximated by one pair, with no
nontriviality assumption on the source spaces. -/
theorem exists_pair_value_gt (B : A →L[ℂ] D →L[ℂ] ℂ) {r : ℝ}
    (hr : r < ‖B‖) :
    ∃ p : A × D, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 ∧ r < ‖B p.1 p.2‖ := by
  by_cases hrneg : r < 0
  · refine ⟨(0, 0), by simp, by simp, ?_⟩
    simpa only [map_zero, ContinuousLinearMap.zero_apply, norm_zero] using hrneg
  have hr0 : 0 ≤ r := le_of_not_gt hrneg
  by_contra hn
  push_neg at hn
  have hnorm : ‖B‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hr0
    intro a ha
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hr0
    intro d hd
    exact hn (a, d) ha.le hd.le
  exact (not_lt_of_ge hnorm) hr

/-- Positive approximation scale, including `n = 0`. -/
def tolerance (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ))⁻¹

theorem tolerance_pos (n : ℕ) : 0 < tolerance n := by
  unfold tolerance
  positivity

theorem tendsto_tolerance_zero : Tendsto tolerance atTop (𝓝 0) := by
  unfold tolerance
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The entire near-maximizing pair is chosen once at each index. -/
def nearPair (B : A →L[ℂ] D →L[ℂ] ℂ) (n : ℕ) : A × D :=
  Classical.choose (exists_pair_value_gt B
    (sub_lt_self ‖B‖ (tolerance_pos n)))

theorem nearPair_spec (B : A →L[ℂ] D →L[ℂ] ℂ) (n : ℕ) :
    ‖(nearPair B n).1‖ ≤ 1 ∧ ‖(nearPair B n).2‖ ≤ 1 ∧
      ‖B‖ - tolerance n < ‖B (nearPair B n).1 (nearPair B n).2‖ :=
  Classical.choose_spec (exists_pair_value_gt B
    (sub_lt_self ‖B‖ (tolerance_pos n)))

/-- Phase convention gives `phase z * z = |z|`; it is well defined at zero. -/
def positivePhase (z : ℂ) : ℂ := if z = 0 then 1 else (‖z‖ : ℂ) / z

@[simp]
theorem norm_positivePhase (z : ℂ) : ‖positivePhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [positivePhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [positivePhase, hz, norm_div, Complex.norm_real,
      abs_of_nonneg (norm_nonneg z), hn]

@[simp]
theorem positivePhase_mul (z : ℂ) : positivePhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [positivePhase, hz]
  · simp [positivePhase, hz]

/-- The left sequence carries the phase correction. -/
def attainingLeft (B : A →L[ℂ] D →L[ℂ] ℂ) : ℕ →ᵇ A :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => positivePhase (B (nearPair B n).1 (nearPair B n).2) • (nearPair B n).1)
    1 (by
      intro n
      rw [norm_smul, norm_positivePhase, one_mul]
      exact (nearPair_spec B n).1)

/-- The right sequence uses the same selected pairs and the same indices. -/
def attainingRight (B : A →L[ℂ] D →L[ℂ] ℂ) : ℕ →ᵇ D :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (nearPair B n).2) 1 (fun n => (nearPair_spec B n).2.1)

theorem norm_attainingLeft_le (B : A →L[ℂ] D →L[ℂ] ℂ) : ‖attainingLeft B‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro n
  change ‖positivePhase (B (nearPair B n).1 (nearPair B n).2) • (nearPair B n).1‖ ≤ 1
  rw [norm_smul, norm_positivePhase, one_mul]
  exact (nearPair_spec B n).1

theorem norm_attainingRight_le (B : A →L[ℂ] D →L[ℂ] ℂ) : ‖attainingRight B‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro n
  exact (nearPair_spec B n).2.1

/-- After phase correction the bilinear value is exactly real and
nonnegative at every index, not just in the limit. -/
theorem attaining_value (B : A →L[ℂ] D →L[ℂ] ℂ) (n : ℕ) :
    B (attainingLeft B n) (attainingRight B n) =
      (‖B (nearPair B n).1 (nearPair B n).2‖ : ℂ) := by
  change B (positivePhase (B (nearPair B n).1 (nearPair B n).2) • (nearPair B n).1)
    (nearPair B n).2 = _
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, positivePhase_mul]

theorem nearPair_value_le_norm (B : A →L[ℂ] D →L[ℂ] ℂ) (n : ℕ) :
    ‖B (nearPair B n).1 (nearPair B n).2‖ ≤ ‖B‖ :=
  ((B (nearPair B n).1).unit_le_opNorm (nearPair B n).2
    (nearPair_spec B n).2.1).trans
    (B.unit_le_opNorm (nearPair B n).1 (nearPair_spec B n).1)

theorem tendsto_nearPair_value (B : A →L[ℂ] D →L[ℂ] ℂ) :
    Tendsto (fun n => ‖B (nearPair B n).1 (nearPair B n).2‖) atTop (𝓝 ‖B‖) := by
  have hbound (n : ℕ) :
      ‖‖B (nearPair B n).1 (nearPair B n).2‖ - ‖B‖‖ ≤ tolerance n := by
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (nearPair_value_le_norm B n))]
    have h := (nearPair_spec B n).2.2
    linarith
  have hnorm : Tendsto (fun n => ‖‖B (nearPair B n).1 (nearPair B n).2‖ - ‖B‖‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound tendsto_tolerance_zero
  have hzero : Tendsto (fun n => ‖B (nearPair B n).1 (nearPair B n).2‖ - ‖B‖)
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  convert hzero.add_const ‖B‖ using 1 <;> simp

/-- An actual simultaneous scalar limit, with the same left and right
sequences. -/
theorem tendsto_attaining_value (B : A →L[ℂ] D →L[ℂ] ℂ) :
    Tendsto (fun n => B (attainingLeft B n) (attainingRight B n))
      atTop (𝓝 (‖B‖ : ℂ)) := by
  simpa only [attaining_value, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_nearPair_value B)

/-- Every bounded bilinear form has a norm-preserving sequence-space
extension which attains its norm at a pair of contractions. -/
theorem exists_normAttaining_extension (B : A →L[ℂ] D →L[ℂ] ℂ) :
    ∃ (B' : (ℕ →ᵇ A) →L[ℂ] (ℕ →ᵇ D) →L[ℂ] ℂ)
      (x : ℕ →ᵇ A) (y : ℕ →ᵇ D),
      ‖B'‖ = ‖B‖ ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ B' x y = (‖B‖ : ℂ) ∧
      (∀ a : A, ∀ d : D,
        B' (BoundedContinuousFunction.const ℕ a) (BoundedContinuousFunction.const ℕ d) = B a d) := by
  refine ⟨sequenceExtension B, attainingLeft B, attainingRight B,
    norm_sequenceExtension B, norm_attainingLeft_le B, norm_attainingRight_le B, ?_, ?_⟩
  · exact sequenceExtension_of_tendsto B _ _ _ (tendsto_attaining_value B)
  · exact sequenceExtension_const B

end MathlibAnnex.SequenceBilinear
