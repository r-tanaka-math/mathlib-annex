/- R6 8.3, 8.5–8.7 interface: radius-restricted ordered shrinking tests and
explicit compact max-constant patching. Generic cutoff/shrinking proofs are
reused from the preserved upstream Apache-2.0 port; new restriction/patch bodies here.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.ScalarTests

noncomputable section
open scoped Topology NNReal BigOperators
open Filter Set
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry
open BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization

variable {M : Type*} [MetricSpace M] [Zero M]

/-- Both actual cutoff-product estimates with the R6 constant 3. -/
theorem cutoff_products_lipschitz (z : M) {r : ℝ≥0} (hr : 0 < r)
    (f : M → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) (hfz : f z = 0) :
    LipschitzWith (3 * L) (fun x => f x * cutoff z r x) ∧
    LipschitzWith (3 * L) (fun x => f x * (1 - cutoff z r x)) :=
  ⟨cutoff_product_lipschitz z hr f hf hfz, annular_product_lipschitz z hr f hf hfz⟩

/-- R6 8.5 with the genuine pairing (the value at 0 is subtracted by normalized). -/
theorem tendsto_shrinking_tests_zero (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto (fun i => (r i : ℝ)) atTop (𝓝 0))
    (f : ℕ → M → ℝ) {L : ℝ≥0} (hf : ∀ i, LipschitzWith L (f i))
    (hfz : ∀ i, f i z = 0) (hfs : ∀ i x, (r i : ℝ) ≤ dist x z → f i x = 0) :
    Tendsto (fun i => test (normalized (f i) (hf i)) (μ i)) atTop (𝓝 0) :=
  shrinking_tests z hw r hr hrlim f hf hfz hfs

/-- The ordered epsilon formulation: first choose a small radius, then an eventual
index bound. Bounds are only required for 0<r≤r0, as in R6 8.6. -/
theorem ordered_shrinking_tests (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (f : ℕ → ℝ≥0 → M → ℝ)
    {L r₀ : ℝ≥0} (hr₀ : 0 < r₀)
    (hf : ∀ i r, 0 < r → r ≤ r₀ → LipschitzWith L (f i r))
    (hfz : ∀ i r, 0 < r → r ≤ r₀ → f i r z = 0)
    (hfs : ∀ i r, 0 < r → r ≤ r₀ → ∀ x, (r : ℝ) ≤ dist x z → f i r x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ≥0, ∀ hr : 0 < r, ∀ hrr : r ≤ r₀,
      (r : ℝ) < δ → ∀ᶠ i in atTop, |test (normalized (f i r) (hf i r hr hrr)) (μ i)| < ε := by
  classical
  let g : ℕ → ℝ≥0 → M → ℝ := fun i r x => if r ≤ r₀ then f i r x else 0
  have hg (i : ℕ) (r : ℝ≥0) (hr : 0 < r) : LipschitzWith L (g i r) := by
    by_cases hrr : r ≤ r₀
    · simpa only [g, if_pos hrr] using hf i r hr hrr
    · simpa only [g, if_neg hrr] using (LipschitzWith.const (0 : ℝ)).weaken (bot_le : (0 : ℝ≥0) ≤ L)
  have hgz (i : ℕ) (r : ℝ≥0) (hr : 0 < r) : g i r z = 0 := by
    by_cases hrr : r ≤ r₀
    · simp only [g, if_pos hrr, hfz i r hr hrr]
    · simp only [g, if_neg hrr]
  have hgs (i : ℕ) (r : ℝ≥0) (hr : 0 < r) (x : M) (hx : (r : ℝ) ≤ dist x z) : g i r x = 0 := by
    by_cases hrr : r ≤ r₀
    · simp only [g, if_pos hrr, hfs i r hr hrr x hx]
    · simp only [g, if_neg hrr]
  obtain ⟨δ, hδ, hs⟩ := shrinking_radius_uniform z hw g hg hgz hgs hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrr hsmall
  simpa only [g, if_pos hrr] using hs r hr hsmall

omit [Zero M] in
/-- Explicit scale in R6 8.7, obtained from the metric Lebesgue-number lemma.
Empty compact sets and empty covers are admitted when the cover condition holds. -/
theorem exists_common_patch_scale {I : Type*} (K : Set M) (hK : IsCompact K)
    (V : I → Set M) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ «λ» : ℝ≥0, 0 < «λ» ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < «λ» → ∃ i, x ∈ V i ∧ y ∈ V i := by
  obtain ⟨«λ», «hλ», hLeb⟩ := lebesgue_number_lemma_of_metric hK hV hcover
  refine ⟨⟨«λ», «hλ».le⟩, «hλ», ?_⟩
  intro x hx y hy hxy
  have hxy' : dist x y < «λ» := hxy
  obtain ⟨i, hi⟩ := hLeb x hx
  exact ⟨i, hi (Metric.mem_ball_self «hλ»), hi (by simpa only [Metric.mem_ball, dist_comm] using hxy')⟩

omit [Zero M] in
/-- The precise max{local constants,2 eta/lambda} estimate, including singleton K. -/
theorem compact_patch_lipschitzOn {I : Type*} [Fintype I] (K : Set M)
    (V : I → Set M) (f : M → ℝ) (C : I → ℝ≥0) {η «λ» : ℝ≥0} («hλ» : 0 < «λ»)
    (hpair : ∀ x ∈ K, ∀ y ∈ K, dist x y < «λ» → ∃ i, x ∈ V i ∧ y ∈ V i)
    (hsmall : ∀ x ∈ K, |f x| ≤ η) (hlocal : ∀ i, LipschitzOnWith (C i) f (V i)) :
    LipschitzOnWith (max (Finset.univ.sup C) (2 * η / «λ»)) f K := by
  classical
  let B : ℝ≥0 := max (Finset.univ.sup C) (2 * η / «λ»)
  have hCi (i : I) : C i ≤ B := (Finset.le_sup (f := C) (Finset.mem_univ i)).trans (le_max_left _ _)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxy : dist x y < «λ»
  · obtain ⟨i, hxi, hyi⟩ := hpair x hx y hy hxy
    exact ((hlocal i).weaken (hCi i)).dist_le_mul x hxi y hyi
  · have hdist : («λ» : ℝ) ≤ dist x y := le_of_not_gt hxy
    have hquot : 2 * η ≤ B * «λ» := (div_le_iff₀ «hλ»).mp (le_max_right _ _)
    have hquot' : 2 * (η : ℝ) ≤ (B : ℝ) * «λ» := by exact_mod_cast hquot
    have hstep := mul_le_mul_of_nonneg_left hdist B.coe_nonneg
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hsmall x hx, hsmall y hy])

end BanachGeometry.LipschitzFreeLocalization
