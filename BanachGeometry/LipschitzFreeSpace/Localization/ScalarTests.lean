/- Provenance adaptation: summable-family generalization of disjoint operator/coordinate uniqueness.
Source: openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/Localization.lean.
Apache-2.0 upstream material; current attribution and proof ranges: ATTRIBUTION/PROVENANCE.json. -/
/- R6 8.2 and 8.4: actual general summable-test linearization and disjoint increments.
Construction/coordinate uniqueness follows the generic upstream disjointOperator architecture
(openai/math@4eaee87548250b2682affda7d05d947c05554bae; Apache-2.0, LICENSES/OPENAI_MATH_APACHE_2_0.txt),
now with an arbitrary summable increment family, not only disjoint supports.
The summability conjunct is explicit: a nonsummable real tsum cannot default to 0 here.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeGeometry.CompactReduction
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped Topology BigOperators NNReal
open Filter
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry
open BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization

variable {M : Type*} [MetricSpace M] [Zero M]

/-- Genuine sum-of-increments bound, rather than an inequality for a possibly undefined real sum. -/
def HasSummableIncrements (C : ℝ≥0) (f : ℕ → M → ℝ) : Prop :=
  ∀ x y, Summable (fun j => |f j x - f j y|) ∧
    (∑' j, |f j x - f j y|) ≤ (C : ℝ) * dist x y

/-- Equivalent finite-sum formulation of the nonnegative series hypothesis in R6. -/
theorem hasSummableIncrements_iff_finset_sum_le {C : ℝ≥0} {f : ℕ → M → ℝ} :
    HasSummableIncrements C f ↔ ∀ x y (s : Finset ℕ),
      (∑ j ∈ s, |f j x - f j y|) ≤ (C : ℝ) * dist x y := by
  constructor
  · intro hf x y s
    exact ((hf x y).1.sum_le_tsum s (fun _ _ => abs_nonneg _)).trans (hf x y).2
  · intro hf x y
    exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) (hf x y),
      Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) (hf x y)⟩

theorem HasSummableIncrements.lipschitz {C : ℝ≥0} {f : ℕ → M → ℝ}
    (hf : HasSummableIncrements C f) (j : ℕ) : LipschitzWith C (f j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hsingle := (hf x y).1.sum_le_tsum ({j} : Finset ℕ) (fun _ _ => abs_nonneg _)
  have hj : |f j x - f j y| ≤ ∑' k, |f k x - f k y| := by
    simpa only [Finset.sum_singleton] using hsingle
  exact hj.trans (hf x y).2

def summableTestMap (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : HasSummableIncrements C f)
    (x : M) : WeakSequences.RealL1 :=
  ⟨fun j => f j x - f j 0, by
    apply memℓp_gen
    simpa using (hf x 0).1⟩

@[simp] theorem summableTestMap_apply (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) (x : M) (j : ℕ) :
    summableTestMap f hf x j = f j x - f j 0 := rfl

theorem summableTestMap_zero (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : HasSummableIncrements C f) :
    summableTestMap f hf 0 = 0 := by
  apply lp.ext
  funext j
  change f j 0 - f j 0 = 0
  exact sub_self _

theorem summableTestMap_lipschitz (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) : LipschitzWith C (summableTestMap f hf) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, WeakSequences.sumL1_norm]
  have he (j : ℕ) : (summableTestMap f hf x - summableTestMap f hf y) j = f j x - f j y := by
    change (f j x - f j 0) - (f j y - f j 0) = _
    ring
  simpa only [he, Real.norm_eq_abs] using (hf x y).2

/-- The operator in R6 8.2, produced by the actual free-space universal property. -/
def summableTestOperator (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : HasSummableIncrements C f) :
    FreeSpace.Space M →L[ℝ] WeakSequences.RealL1 := FreeSpace.linearize (summableTestMap f hf)

theorem norm_summableTestOperator_le (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) : ‖summableTestOperator f hf‖ ≤ C :=
  FreeSpace.norm_linearize_le _ (summableTestMap_lipschitz f hf) (summableTestMap_zero f hf)

@[simp] theorem summableTestOperator_point (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) (x : M) :
    summableTestOperator f hf (FreeSpace.point x) = summableTestMap f hf x :=
  FreeSpace.linearize_point _ (summableTestMap_lipschitz f hf) (summableTestMap_zero f hf) x

theorem summableTestOperator_coord (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) (μ : FreeSpace.Space M) (j : ℕ) :
    summableTestOperator f hf μ j = test (normalized (f j) (hf.lipschitz j)) μ := by
  have h₁ := FreeSpace.linearize_unique (fun x => f j x - f j 0)
    (lipschitz_sub_const _ (hf.lipschitz j) _) (by simp)
    ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 j).comp (summableTestOperator f hf))
    (by intro x; rw [ContinuousLinearMap.comp_apply, summableTestOperator_point]; rfl)
  have h₂ := FreeSpace.linearize_unique (fun x => f j x - f j 0)
    (lipschitz_sub_const _ (hf.lipschitz j) _) (by simp)
    (test (normalized (f j) (hf.lipschitz j))) (fun x => rfl)
  exact congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) (h₁.symm.trans h₂)

theorem tendsto_summableTestOperator_zero (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) {μ : ℕ → FreeSpace.Space M} (hw : WeakSequences.WeakNull μ) :
    Tendsto (fun n => summableTestOperator f hf (μ n)) atTop (𝓝 0) :=
  WeakSequences.schur (hw.map (summableTestOperator f hf))

/-- Includes the moving diagonal tests used in the shrinking-ball argument. -/
theorem tendsto_diagonal_summable_tests_zero (f : ℕ → M → ℝ) {C : ℝ≥0}
    (hf : HasSummableIncrements C f) {μ : ℕ → FreeSpace.Space M} (hw : WeakSequences.WeakNull μ) :
    Tendsto (fun n => test (normalized (f n) (hf.lipschitz n)) (μ n)) atTop (𝓝 0) := by
  have ht := (tendsto_summableTestOperator_zero f hf hw).norm
  apply squeeze_zero_norm (fun n => ?_) (by simpa only [norm_zero] using ht)
  rw [← summableTestOperator_coord f hf]
  exact lp.norm_apply_le_norm (by norm_num) _ _

/-- R6 8.4, including actual summability, from the sparse value map into l1. -/
theorem hasSummableIncrements_of_disjointTests {f : ℕ → M → ℝ} (hdis : DisjointTests f)
    {L : ℝ≥0} (hf : ∀ j, LipschitzWith L (f j)) : HasSummableIncrements (2 * L) f := by
  intro x y
  let v : WeakSequences.RealL1 := disjointMap hdis x - disjointMap hdis y
  have he (j : ℕ) : v j = f j x - f j y := by
    change disjointMap hdis x j - disjointMap hdis y j = _
    rw [disjointMap_apply, disjointMap_apply]
  constructor
  · simpa only [he] using WeakSequences.summable_norm v
  · have ht := (disjointMap_lipschitz hdis hf).dist_le_mul x y
    rw [dist_eq_norm] at ht
    have hv : ‖v‖ ≤ (2 * L : ℝ≥0) * dist x y := ht
    rw [WeakSequences.sumL1_norm] at hv
    simpa only [he, Real.norm_eq_abs] using hv

end BanachGeometry.LipschitzFreeLocalization
