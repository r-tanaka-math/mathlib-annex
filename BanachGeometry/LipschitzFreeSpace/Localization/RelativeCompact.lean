/- Provenance adaptation: relative-compact remainder estimates and compact pairing bound.
Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/CompactLocalization.lean.
Apache-2.0 upstream material; current attribution and proof ranges: ATTRIBUTION/PROVENANCE.json. -/
/- R6 8.1 compact stage on an arbitrary ambient metric space.
Adapted from CompactLocalization.remainder_compact_lipschitz and scalar_localization,
openai/math@4eaee87548250b2682affda7d05d947c05554bae; Apache-2.0 (LICENSES/OPENAI_MATH_APACHE_2_0.txt).
Changes: local smallness only on K∩O, and an explicit fixed-compact pairing bound.
There is no second-countability or scalar-locality premise on the ambient domain.
The upstream archive remains unchanged; W04 Vendor repairs have a separate ledger.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeGeometry.CompactLocalization

noncomputable section
open scoped Topology NNReal BigOperators
open Filter Set
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization
open BanachGeometry.LipschitzFreeGeometry.LocalLipschitz
open BanachGeometry.LipschitzFreeGeometry

variable {M : Type*} [MetricSpace M]

/-- Relative good neighborhoods suffice for the actual cutoff remainder on K. -/
theorem remainder_compact_lipschitz_relative {I : Type*} [Fintype I]
    (d : ℕ → M → ℝ) {L : ℝ≥0} (hd : ∀ i, LipschitzWith L (d i))
    (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)))
    {η : ℝ≥0} (hη : 0 < η) {K : Set M} (hK : IsCompact K)
    (hgood : ∀ p ∈ K, p ∉ Set.range z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ᶠ i in atTop, LipschitzOnWith η (d i) (K ∩ O)) :
    ∀ᶠ i in atTop, LipschitzOnWith (2 * η) (remainder (d i) z r) K := by
  have hR := fun i => remainder_lipschitz (d i) (hd i) z hr hdis
  apply compact_eventual_lipschitz _ hK (by positivity)
  · intro ε hε
    exact uniform_zero_on_compact _ hR (remainder_tendsto_zero d hpoint z r) hK hε
  · intro p hp
    by_cases hpz : p ∈ Set.range z
    · obtain ⟨j, rfl⟩ := hpz
      refine ⟨Metric.ball (z j) ((r : ℝ) / 2), Metric.isOpen_ball,
        Metric.mem_ball_self (half_pos hr), ?_⟩
      exact Filter.Eventually.of_forall (fun i => LipschitzOnWith.of_dist_le_mul (by
        intro x hx y hy
        rw [remainder_inner (d i) z hr hdis j hx.2,
          remainder_inner (d i) z hr hdis j hy.2, dist_self]
        positivity))
    · obtain ⟨O, hO, hpO, hOi⟩ := hgood p hp hpz
      let B : ℝ≥0 := 2 / r
      let ε : ℝ≥0 := η / (2 * Fintype.card I * B + 1)
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hsmall := uniform_zero_on_compact d hd hpoint hK (show (0 : ℝ) < ε from hε)
      have hzsmall : ∀ᶠ i in atTop, ∀ j, |d i (z j)| ≤ (ε : ℝ) := by
        apply Filter.eventually_all.mpr
        intro j
        have ht := (hpoint (z j)).abs
        simp only [abs_zero] at ht
        exact (ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε from hε))).mono (fun _ hi => hi.le)
      refine ⟨O, hO, hpO, ?_⟩
      filter_upwards [hOi, hsmall, hzsmall] with i hi hsi hzi
      have hw := weightedRemainder_lipschitzOn (d i) z (fun j => cutoff (z j) r)
        (K := K ∩ O) (O := K ∩ O) hi
        (fun j => cutoff_lipschitz _ _) (sum_cutoff_bounds z hr hdis)
        (fun x hx => (hsi x hx.1).le) hzi
      apply (show LipschitzOnWith (η + 2 * Fintype.card I * (2 / r) * ε)
        (remainder (d i) z r) (K ∩ O) from by simpa only [Set.inter_self, remainder] using hw).weaken
      have herr : 2 * Fintype.card I * B * ε ≤ η := by
        dsimp [ε]
        have hden : 0 < 2 * (Fintype.card I : ℝ≥0) * B + 1 := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith
      dsimp [B] at herr
      nlinarith

variable [Zero M]

/-- Quantitative compact stage; ν is not assumed weakly null.
Only μ is weakly null, so small norm errors from compact reduction are legitimate. -/
theorem eventually_pairing_bound_on_compact {μ ν : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (d : ℕ → M → ℝ) {L : ℝ≥0}
    (hd : ∀ i, LipschitzWith L (d i)) (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) (hK0 : (0 : M) ∈ K)
    {τ B : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hνK : ∀ i, ν i ∈ FreeSpace.supported K) (hνdist : ∀ i, ‖μ i - ν i‖ ≤ τ)
    (hνnorm : ∀ i, ‖ν i‖ ≤ B) {η : ℝ≥0} (hη : 0 < η)
    (Z : Set M) (hZ : Z.Finite)
    (hgood : ∀ p ∈ K, p ∉ Z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ᶠ i in atTop, LipschitzOnWith η (d i) (K ∩ O)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, |test (normalized (d i) (hd i)) (μ i)| <
      ε + 2 * (η : ℝ) * B + 7 * (L : ℝ) * τ := by
  classical
  letI : Fintype Z := hZ.fintype
  let z : Z → M := Subtype.val
  obtain ⟨r₀, hr₀, hdis₀⟩ := CoordinateLocality.exists_disjoint_balls z Subtype.val_injective
  obtain ⟨δ, hδ, hremoved⟩ := removed_pairings_small hw d hd z hε
  let r : ℝ≥0 := ⟨min r₀ δ / 2, (half_pos (lt_min hr₀ hδ)).le⟩
  have hr : 0 < r := half_pos (lt_min hr₀ hδ)
  have hrr₀ : (r : ℝ) ≤ r₀ := (half_le_self (lt_min hr₀ hδ).le).trans (min_le_left _ _)
  have hrδ : (r : ℝ) < δ := (half_lt_self (lt_min hr₀ hδ)).trans_le (min_le_right _ _)
  have hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)) := by
    intro j k hjk
    exact (hdis₀ hjk).mono (Metric.ball_subset_ball hrr₀) (Metric.ball_subset_ball hrr₀)
  have hR := fun i => remainder_lipschitz (d i) (hd i) z hr hdis
  have hg := fun i => removed_lipschitz (d i) (hd i) z hr hdis
  have hsmallg := hremoved r hr hrδ hdis
  have hsmallR := remainder_compact_lipschitz_relative d hd hpoint z hr hdis hη hK (by
    intro p hp hpz
    exact hgood p hp (by simpa only [z, Subtype.range_coe] using hpz))
  filter_upwards [hsmallg, hsmallR] with i hgi hRi
  have hsupp := FreeSpace.supported_pairing_le hK0 (remainder (d i) z r) (hR i) hRi (ν i) (hνK i)
  have herr : |test (normalized (remainder (d i) z r) (hR i)) (μ i - ν i)| ≤ 7 * (L : ℝ) * τ := by
    have ht := (norm_test_apply_le (normalized (remainder (d i) z r) (hR i)) (μ i - ν i)).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le _ (hR i)) (norm_nonneg _))
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (by simpa using mul_le_mul_of_nonneg_left (hνdist i) (show 0 ≤ 7 * (L : ℝ) by positivity))
  have hRv : |test (normalized (remainder (d i) z r) (hR i)) (μ i)| ≤
      2 * (η : ℝ) * B + 7 * (L : ℝ) * τ := by
    have hsplit : ν i + (μ i - ν i) = μ i := by abel
    have ht := abs_add_le (test (normalized (remainder (d i) z r) (hR i)) (ν i))
      (test (normalized (remainder (d i) z r) (hR i)) (μ i - ν i))
    rw [← map_add, hsplit] at ht
    have hm := mul_le_mul_of_nonneg_left (hνnorm i) (show 0 ≤ 2 * (η : ℝ) by positivity)
    norm_num only [NNReal.coe_mul, NNReal.coe_ofNat] at hsupp
    linarith
  have hid : test (normalized (remainder (d i) z r) (hR i)) (μ i) =
      test (normalized (d i) (hd i)) (μ i) - test (normalized (removed (d i) z r) (hg i)) (μ i) :=
    test_normalized_sub (d i) (removed (d i) z r) (hd i) (hg i) (hR i) (μ i)
  have ht := abs_add_le (test (normalized (remainder (d i) z r) (hR i)) (μ i))
    (test (normalized (removed (d i) z r) (hg i)) (μ i))
  rw [hid, sub_add_cancel] at ht
  rw [hid] at hRv
  linarith

end BanachGeometry.LipschitzFreeLocalization
