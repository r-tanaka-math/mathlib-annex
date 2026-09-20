import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.AdditiveSelection

/-!
# From a finite sequence estimate to weighted minimax data

This file handles the bookkeeping that is easy to state informally but
essential in the finite-family argument: simultaneous complex phase
alignment, square-root probability weights (including zero weights), and
the conversion of a norm-of-sum estimate into the weighted additive premise
used by `AdditiveSelection.lean`.

The remaining analytic supplier is `HasFiniteSummedAdditiveEstimate`.  It is
a genuine finite sequence inequality, not the final pointwise product
conclusion.
-/

set_option autoImplicit false

open Finset Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear

universe uA uD

noncomputable section

variable {A : Type uA} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- A unit complex scalar which rotates `z` to the nonnegative real axis.
At zero we choose one, rather than zero, so that quadratic gauges are
unchanged even for a vanishing bilinear value. -/
def normingPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else star z / (‖z‖ : ℂ)

theorem norm_normingPhase (z : ℂ) : ‖normingPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [normingPhase, hz, norm_div, hn]

theorem normingPhase_mul (z : ℂ) :
    normingPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [normingPhase, hz]
  · have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
    rw [normingPhase, if_neg hz, div_mul_eq_mul_div, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    apply (div_eq_iff hnC).2
    push_cast
    ring

/-- A sequence form of additive Grothendieck domination.  The four states
may depend on the entire pair of sequences, but are common to all summands. -/
def HasFiniteSummedAdditiveEstimate
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ {ι : Type (max uA uD)} [Fintype ι] [Nonempty ι]
    (x : ι → A) (y : ι → D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ‖∑ i, B (x i) (y i)‖ ≤
          (C / 2) * ∑ i, (leftSquare z (x i) + rightSquare z (y i))

private theorem norm_sum_coe_norm
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ‖∑ i, (‖v i‖ : ℂ)‖ = ∑ i, ‖v i‖ := by
  have hcoe : (∑ i, (‖v i‖ : ℂ)) =
      ((∑ i, ‖v i‖ : ℝ) : ℂ) := by
    norm_cast
  rw [hcoe, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg fun i _ ↦ norm_nonneg (v i))]

/-- Complex phases convert a norm of a sum into the sum of the norms while
preserving every left quadratic gauge. -/
theorem exists_sum_norm_additiveControl
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hsum : HasFiniteSummedAdditiveEstimate B C)
    {ι : Type (max uA uD)} [Fintype ι] [Nonempty ι]
    (x : ι → A) (y : ι → D) :
    ∃ z ∈ stateControls (A := A) (D := D),
      ∑ i, ‖B (x i) (y i)‖ ≤
        (C / 2) * ∑ i, (leftSquare z (x i) + rightSquare z (y i)) := by
  let p : ι → ℂ := fun i ↦ normingPhase (B (x i) (y i))
  obtain ⟨z, hz, h⟩ := hsum (fun i ↦ p i • x i) y
  refine ⟨z, hz, ?_⟩
  have hleft : ‖∑ i, B (p i • x i) (y i)‖ =
      ∑ i, ‖B (x i) (y i)‖ := by
    calc
      ‖∑ i, B (p i • x i) (y i)‖ =
          ‖∑ i, (‖B (x i) (y i)‖ : ℂ)‖ := by
        apply congrArg norm
        apply sum_congr rfl
        intro i _
        simp only [map_smul, smul_apply, smul_eq_mul, p]
        exact normingPhase_mul (B (x i) (y i))
      _ = ∑ i, ‖B (x i) (y i)‖ := norm_sum_coe_norm _
  rw [hleft] at h
  simpa only [leftSquare_complex_smul, norm_normingPhase, one_pow,
    one_mul, p] using h

private theorem norm_bilinear_sqrt_smul
    (B : A →L[ℂ] D →L[ℂ] ℂ) {w : ℝ} (hw : 0 ≤ w) (x : A) (y : D) :
    ‖B ((Real.sqrt w : ℂ) • x) ((Real.sqrt w : ℂ) • y)‖ =
      w * ‖B x y‖ := by
  simp [map_smul, norm_smul, abs_of_nonneg (Real.sqrt_nonneg w)]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt hw]

private theorem leftSquare_sqrt_smul
    (z : StateControl A D) {w : ℝ} (hw : 0 ≤ w) (x : A) :
    leftSquare z ((Real.sqrt w : ℂ) • x) = w * leftSquare z x := by
  rw [leftSquare_complex_smul]
  simp [abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw]

private theorem rightSquare_sqrt_smul
    (z : StateControl A D) {w : ℝ} (hw : 0 ≤ w) (y : D) :
    rightSquare z ((Real.sqrt w : ℂ) • y) = w * rightSquare z y := by
  rw [rightSquare_complex_smul]
  simp [abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw]

/-- Phase alignment followed by square-root weighting supplies the precise
weighted premise required by finite minimax.  No strict positivity of a
weight is used. -/
theorem hasWeightedFiniteAdditiveEstimate_of_finiteSummed
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hsum : HasFiniteSummedAdditiveEstimate B C) :
    HasWeightedFiniteAdditiveEstimate B C := by
  intro ι _ _ x y w hw
  obtain ⟨z, hz, h⟩ :=
    exists_sum_norm_additiveControl B C hsum
      (fun i ↦ (Real.sqrt (w i) : ℂ) • x i)
      (fun i ↦ (Real.sqrt (w i) : ℂ) • y i)
  refine ⟨z, hz, ?_⟩
  have hscaled :
      (∑ i, w i * ‖B (x i) (y i)‖) ≤
        (C / 2) * ∑ i,
          (w i * leftSquare z (x i) + w i * rightSquare z (y i)) := by
    simpa only [norm_bilinear_sqrt_smul B (hw.1 _),
      leftSquare_sqrt_smul z (hw.1 _),
      rightSquare_sqrt_smul z (hw.1 _)] using h
  unfold weightedViolation additiveViolation
  calc
    (∑ i, w i *
        (‖B (x i) (y i)‖ -
          C / 2 * (leftSquare z (x i) + rightSquare z (y i)))) =
        (∑ i, w i * ‖B (x i) (y i)‖) -
          (C / 2) * ∑ i,
            (w i * leftSquare z (x i) +
              w i * rightSquare z (y i)) := by
      simp_rw [mul_sub]
      rw [sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ 0 := sub_nonpos.mpr hscaled

/-- End-to-end W1: the finite summed sequence inequality supplies the exact
finite common-state product premise. -/
theorem finite_stateControl_of_finiteSummedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsum : HasFiniteSummedAdditiveEstimate B C) :
    ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy :=
  finite_stateControl_of_weightedAdditive B C hC
    (hasWeightedFiniteAdditiveEstimate_of_finiteSummed B C hsum)

/-- End-to-end W2 through the already accepted two-sided GNS factorization. -/
theorem exists_twoSidedDomination_of_finiteSummedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsum : HasFiniteSummedAdditiveEstimate B C) :
    ∃ (p q : A →ₚ[ℂ] ℂ) (r t : D →ₚ[ℂ] ℂ),
      IsTwoSidedDominated B p q r t C :=
  exists_twoSidedDomination_of_weightedAdditive B C hC
    (hasWeightedFiniteAdditiveEstimate_of_finiteSummed B C hsum)

theorem isWeaklyCompact_of_finiteSummedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsum : HasFiniteSummedAdditiveEstimate B C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B :=
  isWeaklyCompact_of_weightedAdditive B C hC
    (hasWeightedFiniteAdditiveEstimate_of_finiteSummed B C hsum)

end

end MathlibAnnex.CStarBilinear
