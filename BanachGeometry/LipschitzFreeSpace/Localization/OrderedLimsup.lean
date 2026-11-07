/- R6 8.6 in the literal ordered limsup form, in addition to its epsilon formulation.
Real limsup is used only after proving the pairings uniformly bounded above and below.
The family is totalized by zero outside 0<r≤r0.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.Auxiliary
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open scoped Topology NNReal
open Filter
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry
open BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization

variable {M : Type*} [MetricSpace M] [Zero M]

/-- The upper limit in n, with the paper's restricted radius domain explicitly preserved. -/
def shrinkingPairingLimsup (μ : ℕ → FreeSpace.Space M) (f : ℕ → ℝ≥0 → M → ℝ)
    {L r₀ : ℝ≥0} (hf : ∀ i r, 0 < r → r ≤ r₀ → LipschitzWith L (f i r)) (r : ℝ≥0) : ℝ :=
  if hr : 0 < r ∧ r ≤ r₀ then
    Filter.limsup (fun i => |test (normalized (f i r) (hf i r hr.1 hr.2)) (μ i)|) atTop
  else 0

private theorem pairing_abs_bound {μ : ℕ → FreeSpace.Space M} {B : ℝ}
    (hB : ∀ i, ‖μ i‖ ≤ B) (f : ℕ → M → ℝ) {L : ℝ≥0} (hf : ∀ i, LipschitzWith L (f i)) (i : ℕ) :
    |test (normalized (f i) (hf i)) (μ i)| ≤ (L : ℝ) * B := by
  have ht := norm_test_apply_le (normalized (f i) (hf i)) (μ i)
  rw [Real.norm_eq_abs] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_right (norm_normalized_le _ (hf i)) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (hB i) L.coe_nonneg))

/-- Nonnegativity is justified using actual boundedness, not the default value of a real limsup. -/
theorem shrinkingPairingLimsup_nonneg {μ : ℕ → FreeSpace.Space M} (hw : WeakSequences.WeakNull μ)
    (f : ℕ → ℝ≥0 → M → ℝ) {L r₀ : ℝ≥0}
    (hf : ∀ i r, 0 < r → r ≤ r₀ → LipschitzWith L (f i r)) (r : ℝ≥0) :
    0 ≤ shrinkingPairingLimsup μ f hf r := by
  unfold shrinkingPairingLimsup
  split_ifs with hr
  · obtain ⟨B, hB⟩ := (show WeakSequences.WeakCauchy μ from fun g => (hw g).cauchySeq).bounded
    have hupper : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·)
        (fun i => |test (normalized (f i r) (hf i r hr.1 hr.2)) (μ i)|) :=
      isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (pairing_abs_bound hB (fun i => f i r) (fun i => hf i r hr.1 hr.2)))
    exact le_limsup_of_frequently_le (Filter.Frequently.of_forall fun _ => abs_nonneg _) hupper
  · exact le_rfl

/-- lim_{r↓0} limsup_n |<f_(n,r),μ_n>|=0, exactly in that order. -/
theorem tendsto_shrinkingPairingLimsup_zero (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (f : ℕ → ℝ≥0 → M → ℝ)
    {L r₀ : ℝ≥0} (hr₀ : 0 < r₀)
    (hf : ∀ i r, 0 < r → r ≤ r₀ → LipschitzWith L (f i r))
    (hfz : ∀ i r, 0 < r → r ≤ r₀ → f i r z = 0)
    (hfs : ∀ i r, 0 < r → r ≤ r₀ → ∀ x, (r : ℝ) ≤ dist x z → f i r x = 0) :
    Tendsto (shrinkingPairingLimsup μ f hf) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := ordered_shrinking_tests z hw f hr₀ hf hfz hfs (half_pos hε)
  have hevent : ∀ᶠ r : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), r < (⟨δ, hδ.le⟩ : ℝ≥0) :=
    (eventually_lt_nhds (show (0 : ℝ≥0) < ⟨δ, hδ.le⟩ from hδ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with r hr hrad
  have hrpos : 0 < r := hr
  have hn := shrinkingPairingLimsup_nonneg hw f hf r
  by_cases hrr : r ≤ r₀
  · have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·)
        (fun i => |test (normalized (f i r) (hf i r hrpos hrr)) (μ i)|) :=
      isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    have hle : shrinkingPairingLimsup μ f hf r ≤ ε / 2 := by
      rw [shrinkingPairingLimsup, dif_pos ⟨hrpos, hrr⟩]
      exact limsup_le_of_le hb.isCobounded_flip ((hsmall r hrpos hrr hrad).mono fun _ hi => hi.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
    exact hle.trans_lt (half_lt_self hε)
  · have hz : shrinkingPairingLimsup μ f hf r = 0 := by
      rw [shrinkingPairingLimsup, dif_neg (by simp [hrr])]
    simp only [hz, dist_self, hε]

end BanachGeometry.LipschitzFreeLocalization
