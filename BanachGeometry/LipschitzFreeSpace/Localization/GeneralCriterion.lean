/- Provenance adaptation: scalar pairing uniqueness and normalized-sequence argument; arbitrary Hilbert/compact-relative generalization.
Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/CompleteContinuity.lean.
Apache-2.0 upstream material; current attribution and proof ranges: ATTRIBUTION/PROVENANCE.json. -/
/- R6 Theorem 8.1 in its general increment form.
Scalar normalization/pairing architecture adapted from upstream CompleteContinuity
(openai/math@4eaee87548250b2682affda7d05d947c05554bae; Apache-2.0, LICENSES/OPENAI_MATH_APACHE_2_0.txt).
New steps: arbitrary real Hilbert target; compact-relative basis and bad points;
compact stage for the original weakly-null measures, without weak convergence of approximants.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.CompactSelection
import BanachGeometry.LipschitzFreeSpace.Localization.RelativeCompact
import BanachGeometry.LipschitzFreeGeometry.CompactReduction

noncomputable section
open scoped Topology NNReal InnerProductSpace
open Filter Set
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry
open BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization

universe uM uH
variable {M : Type uM} {H : Type uH} [MetricSpace M] [Zero M]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem scalar_test_lipschitz (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D)
    (b : H) (hb : ‖b‖ ≤ 1) : LipschitzWith L (fun x => ⟪D x, b⟫_ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by
      simpa only [mul_one, ← dist_eq_norm] using hD.dist_le_mul x y))

/-- The actual universal-property linearization pairing, for arbitrary H. -/
theorem scalar_test_pairing (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D)
    (hD0 : D 0 = 0) (b : H) (hb : ‖b‖ ≤ 1) (μ : FreeSpace.Space M) :
    test (normalized (fun x => ⟪D x, b⟫_ℝ) (scalar_test_lipschitz D hD b hb)) μ =
      ⟪FreeSpace.linearize D μ, b⟫_ℝ := by
  let d : M → ℝ := fun x => ⟪D x, b⟫_ℝ
  have hd : LipschitzWith L d := scalar_test_lipschitz D hD b hb
  have hd0 : d 0 = 0 := by simp [d, hD0]
  have h₁ : FreeSpace.linearize d = test (normalized d hd) :=
    FreeSpace.linearize_unique d hd hd0 _ (by intro x; change d x - d 0 = d x; rw [hd0, sub_zero])
  have h₂ : FreeSpace.linearize d = (innerSL ℝ b).comp (FreeSpace.linearize D) :=
    FreeSpace.linearize_unique d hd hd0 _ (by
      intro x
      rw [ContinuousLinearMap.comp_apply, FreeSpace.linearize_point D hD hD0]
      exact (real_inner_comm b (D x)).symm)
  have he := congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) (h₁.symm.trans h₂)
  change test (normalized d hd) μ = ⟪FreeSpace.linearize D μ, b⟫_ℝ
  rw [he]
  exact (real_inner_comm b (FreeSpace.linearize D μ)).symm

/-- General complete-continuity criterion with a separately proved compact-reduction input.
There is no separability assumption on M or H and no coordinate-tail hypothesis. -/
theorem completelyContinuous_linearize_of_compactReduction
    (hcompact : FreeSpace.HasCompactReduction (M := M))
    (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : IncrementLocality D) : BanachGeometry.CompletelyContinuous (FreeSpace.linearize D) := by
  by_cases hL : L = 0
  · have hnorm := FreeSpace.norm_linearize_le D hD hD0
    have hzero : FreeSpace.linearize D = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [hL, NNReal.coe_zero] using hnorm) (norm_nonneg _))
    rw [hzero]
    intro μ hw
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))
  have hLpos : 0 < L := lt_of_le_of_ne (by positivity) (Ne.symm hL)
  intro μ hw
  by_contra hn
  obtain ⟨ε, hε, s, hs, hlarge⟩ := WeakSequences.exists_large_subsequence
    (fun i => FreeSpace.linearize D (μ i)) hn
  let μ₁ : ℕ → FreeSpace.Space M := fun i => μ (s i)
  have hw₁ : WeakSequences.WeakNull μ₁ := fun f => (hw f).comp hs.tendsto_atTop
  let b := WeakSequences.unitNormalize (fun i => FreeSpace.linearize D (μ₁ i))
  have hwq : WeakSequences.WeakNull (fun i => FreeSpace.linearize D (μ₁ i)) := hw₁.map _
  have hbn (i : ℕ) : ‖b i‖ = 1 := WeakSequences.norm_unitNormalize _ hε hlarge i
  have hbw : BanachGeometry.WeakNull b := hwq.unitNormalize hε hlarge
  let d : ℕ → M → ℝ := fun i x => ⟪D x, b i⟫_ℝ
  have hd (i : ℕ) : LipschitzWith L (d i) := scalar_test_lipschitz D hD (b i) (hbn i).le
  have hpoint (x : M) : Tendsto (fun i => d i x) atTop (𝓝 0) := hbw (innerSL ℝ (D x))
  have hpair (i : ℕ) : test (normalized (d i) (hd i)) (μ₁ i) = ‖FreeSpace.linearize D (μ₁ i)‖ := by
    rw [scalar_test_pairing D hD hD0 (b i) (hbn i).le]
    change ⟪FreeSpace.linearize D (μ₁ i), ‖FreeSpace.linearize D (μ₁ i)‖⁻¹ • FreeSpace.linearize D (μ₁ i)⟫_ℝ = _
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    have hn' : ‖FreeSpace.linearize D (μ₁ i)‖ ≠ 0 := ne_of_gt (hε.trans_le (hlarge i))
    field_simp [hn']
  obtain ⟨C, hC⟩ := (show WeakSequences.WeakCauchy μ₁ from fun f => (hw₁ f).cauchySeq).bounded
  have hC0 : 0 ≤ C := (norm_nonneg (μ₁ 0)).trans (hC 0)
  let τ : ℝ := min 1 (ε / (56 * ((L : ℝ) + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτerr : 7 * (L : ℝ) * τ ≤ ε / 8 := by
    have ht : τ ≤ ε / (56 * ((L : ℝ) + 1)) := min_le_right _ _
    have he := (le_div_iff₀ (show 0 < 56 * ((L : ℝ) + 1) by positivity)).mp ht
    nlinarith [mul_nonneg L.coe_nonneg hτ.le]
  obtain ⟨K, hK, hK0, hν⟩ := hcompact μ₁ hw₁ τ hτ
  choose ν hνK hνdist using hν
  have hνnorm (i : ℕ) : ‖ν i‖ ≤ C + 1 := by
    have hsplit : μ₁ i + (ν i - μ₁ i) = ν i := by abel
    have ht := norm_add_le (μ₁ i) (ν i - μ₁ i)
    rw [hsplit, norm_sub_rev] at ht
    linarith [hνdist i, hC i]
  obtain ⟨t, ht, hgood⟩ := exists_compact_good_subsequence D hD hLpos hloc b
    (fun i => (hbn i).le) hbw hK
  let η : ℝ≥0 := ⟨ε / (16 * (C + 1)), (div_pos hε (by positivity)).le⟩
  have hη : 0 < η := div_pos hε (by positivity)
  have hηerr : 2 * (η : ℝ) * (C + 1) = ε / 8 := by
    change 2 * (ε / (16 * (C + 1))) * (C + 1) = ε / 8
    field_simp [ne_of_gt (show 0 < C + 1 by positivity)]
    ring
  obtain ⟨Z, hZ, hgoodZ⟩ := hgood η hη
  have hbound := eventually_pairing_bound_on_compact
    (μ := fun i => μ₁ (t i)) (ν := fun i => ν (t i)) (hw₁.subseq ht)
    (fun i => d (t i)) (fun i => hd (t i))
    (fun x => (hpoint x).comp ht.tendsto_atTop) hK hK0 hτ.le (by linarith : 0 ≤ C + 1)
    (fun i => hνK (t i)) (fun i => (hνdist (t i)).le) (fun i => hνnorm (t i))
    hη Z hZ hgoodZ (show 0 < ε / 4 by positivity)
  obtain ⟨i, hi⟩ := hbound.exists
  rw [hpair, abs_of_nonneg (norm_nonneg _)] at hi
  have hl := hlarge (t i)
  nlinarith

/-- R6 Theorem 8.1 for the stated arbitrary complete real Hilbert target:
the increment-locality hypothesis gives complete continuity of linearization.
Local execution evidence is recorded in the external qualification receipts. -/
theorem completelyContinuous_linearize_of_incrementLocality [CompleteSpace M]
    (D : M → H) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : IncrementLocality D) : BanachGeometry.CompletelyContinuous (FreeSpace.linearize D) :=
  completelyContinuous_linearize_of_compactReduction FreeSpace.hasCompactReduction D hD hD0 hloc

end BanachGeometry.LipschitzFreeLocalization
