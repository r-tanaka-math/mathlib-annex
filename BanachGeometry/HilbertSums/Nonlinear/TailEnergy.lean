/- Actual full-series dyadic tail budget, including the odd companion coordinate.
The proof controls arbitrary finite subsets, then invokes nonnegative summability;
no unproved partition of an infinite series is used.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.RecursiveInverse
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums.Nonlinear
open Clock

/-- Any finite subset whose tail radii are ≤R carries at most R² energy. -/
theorem finite_energy_of_radius_le (y : GradedHilbert) (s : Finset ℕ) {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ n ∈ s, ‖blockTail n y‖ ≤ R) :
    (∑ n ∈ s, ‖y n‖ ^ 2) ≤ R ^ 2 := by
  classical
  by_cases he : s.Nonempty
  · let N := s.min' he
    have hN : N ∈ s := Finset.min'_mem s he
    have hn (n : ℕ) (hn : n ∈ s) : N ≤ n := Finset.min'_le s n hn
    have hsum : (∑ n ∈ s, ‖y n‖ ^ 2) ≤ ‖blockTail N y‖ ^ 2 := by
      rw [l2_norm_sq]
      have heq : (∑ n ∈ s, ‖y n‖ ^ 2) = ∑ n ∈ s, ‖blockTail N y n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn'
        simp [blockTail_apply, not_lt.mpr (hn n hn')]
      rw [heq]
      exact (l2_summable_sq (blockTail N y)).sum_le_tsum s (fun _ _ => sq_nonneg _)
    exact hsum.trans ((sq_le_sq₀ (norm_nonneg _) hR).2 (hs N hN))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
    positivity

def tailGammaEnergy (c : ℝ) (y : GradedHilbert) (n : ℕ) : ℝ :=
  ‖y n‖ ^ 2 * gamma c ‖blockTail n y‖ ^ 2

theorem tailGammaEnergy_nonneg (c : ℝ) (y : GradedHilbert) (n : ℕ) :
    0 ≤ tailGammaEnergy c y n := by unfold tailGammaEnergy; positivity

theorem sum_tailGammaEnergy_le (c : ℝ) (y : GradedHilbert) (s : Finset ℕ) :
    (∑ n ∈ s, tailGammaEnergy c y n) ≤ c ^ 2 / 32 := by
  classical
  let t := s.filter (fun n => 0 < ‖blockTail n y‖ ∧ ‖blockTail n y‖ ≤ 1)
  let f := fun n => bandIndex ‖blockTail n y‖
  have hrestrict : (∑ n ∈ s, tailGammaEnergy c y n) = ∑ n ∈ t, tailGammaEnergy c y n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnt
    have hbad : ¬ (0 < ‖blockTail n y‖ ∧ ‖blockTail n y‖ ≤ 1) := by
      simpa [t, hn] using hnt
    unfold tailGammaEnergy gamma
    rw [if_neg hbad]
    simp
  rw [hrestrict]
  have hf : ∀ n ∈ t, f n ∈ t.image f := fun n hn => Finset.mem_image_of_mem f hn
  rw [← Finset.sum_fiberwise_of_maps_to hf]
  calc
    (∑ m ∈ t.image f, ∑ n ∈ t with f n = m, tailGammaEnergy c y n) ≤
        ∑ m ∈ t.image f, dyadicRadius m ^ 2 * dyadicSlope c m ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hr : ∀ n ∈ t.filter (fun n => f n = m), ‖blockTail n y‖ ≤ dyadicRadius m := by
        intro n hn
        obtain ⟨hnt, hnm⟩ := Finset.mem_filter.mp hn
        obtain ⟨_, hpos, hone⟩ := Finset.mem_filter.mp hnt
        simpa only [← hnm, f] using bandIndex_upper hpos hone
      have he : (∑ n ∈ t with f n = m, tailGammaEnergy c y n) =
          (∑ n ∈ t with f n = m, ‖y n‖ ^ 2) * dyadicSlope c m ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n hn
        obtain ⟨hnt, hnm⟩ := Finset.mem_filter.mp hn
        obtain ⟨_, hpos, hone⟩ := Finset.mem_filter.mp hnt
        simp only [tailGammaEnergy, gamma,
          if_pos (show 0 < ‖blockTail n y‖ ∧ ‖blockTail n y‖ ≤ 1 from ⟨hpos, hone⟩),
          ← hnm, f]
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (finite_energy_of_radius_le y _ (dyadicRadius_pos m).le hr) (sq_nonneg _)
    _ ≤ ∑' m, dyadicRadius m ^ 2 * dyadicSlope c m ^ 2 :=
      (dyadic_weight_summable c).sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ c ^ 2 / 32 := dyadic_weight_total_le c

theorem tailGammaEnergy_summable (c : ℝ) (y : GradedHilbert) : Summable (tailGammaEnergy c y) :=
  summable_of_sum_le (tailGammaEnergy_nonneg c y) (sum_tailGammaEnergy_le c y)

theorem tsum_tailGammaEnergy_le (c : ℝ) (y : GradedHilbert) :
    (∑' n, tailGammaEnergy c y n) ≤ c ^ 2 / 32 :=
  Real.tsum_le_of_sum_le (tailGammaEnergy_nonneg c y) (sum_tailGammaEnergy_le c y)

def companionGammaEnergy (c : ℝ) (y : GradedHilbert) (n : ℕ) : ℝ :=
  ‖y (2 * n + 1)‖ ^ 2 * gamma c ‖blockTail n y‖ ^ 2

/-- At a vanishing companion tail its block is zero, so gamma(0) is immaterial. -/
theorem companionGammaEnergy_le {c : ℝ} (hc : 0 ≤ c) (y : GradedHilbert) (n : ℕ) :
    companionGammaEnergy c y n ≤ tailGammaEnergy c y (2 * n + 1) := by
  by_cases hz : ‖blockTail (2 * n + 1) y‖ = 0
  · have hy := apply_eq_zero_of_norm_blockTail_eq_zero y hz (le_refl (2 * n + 1))
    simp [companionGammaEnergy, tailGammaEnergy, hy]
  · have hpos : 0 < ‖blockTail (2 * n + 1) y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hrad : ‖blockTail (2 * n + 1) y‖ ≤ ‖blockTail n y‖ :=
      norm_blockTail_antitone y (by omega)
    have hgamma := gamma_antitone_positive hc hpos (hpos.trans_le hrad) hrad
    have hsq := (sq_le_sq₀ (gamma_nonneg hc _) (gamma_nonneg hc _)).2 hgamma
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)

theorem companionGammaEnergy_summable {c : ℝ} (hc : 0 ≤ c) (y : GradedHilbert) :
    Summable (companionGammaEnergy c y) :=
  Summable.of_nonneg_of_le (fun _ => by unfold companionGammaEnergy; positivity)
    (companionGammaEnergy_le hc y)
    ((tailGammaEnergy_summable c y).comp_injective (by
      intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega))

theorem tsum_companionGammaEnergy_le {c : ℝ} (hc : 0 ≤ c) (y : GradedHilbert) :
    (∑' n, companionGammaEnergy c y n) ≤ c ^ 2 / 32 := by
  apply Real.tsum_le_of_sum_le (fun _ => by unfold companionGammaEnergy; positivity)
  intro s
  calc
    (∑ n ∈ s, companionGammaEnergy c y n) ≤ ∑ n ∈ s, tailGammaEnergy c y (2 * n + 1) :=
      Finset.sum_le_sum (fun n _ => companionGammaEnergy_le hc y n)
    _ = ∑ j ∈ s.image (fun n => 2 * n + 1), tailGammaEnergy c y j := by
      symm
      apply Finset.sum_image
      intro i _ j _ h
      change 2 * i + 1 = 2 * j + 1 at h
      omega
    _ ≤ c ^ 2 / 32 := sum_tailGammaEnergy_le c y _

def weightedGammaEnergy (c : ℝ) (y : GradedHilbert) (n : ℕ) : ℝ :=
  (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * gamma c ‖blockTail n y‖ ^ 2

theorem weightedGammaEnergy_summable {c : ℝ} (hc : 0 ≤ c) (y : GradedHilbert) :
    Summable (weightedGammaEnergy c y) := by
  change Summable (fun n => (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * gamma c ‖blockTail n y‖ ^ 2)
  simpa only [add_mul, tailGammaEnergy, companionGammaEnergy] using
    (tailGammaEnergy_summable c y).add (companionGammaEnergy_summable hc y)

theorem tsum_weightedGammaEnergy_le {c : ℝ} (hc : 0 ≤ c) (y : GradedHilbert) :
    (∑' n, weightedGammaEnergy c y n) ≤ c ^ 2 / 16 := by
  have he : (∑' n, weightedGammaEnergy c y n) =
      (∑' n, tailGammaEnergy c y n) + ∑' n, companionGammaEnergy c y n := by
    simp only [weightedGammaEnergy, add_mul]
    exact (tailGammaEnergy_summable c y).tsum_add (companionGammaEnergy_summable hc y)
  rw [he]
  linarith [tsum_tailGammaEnergy_le c y, tsum_companionGammaEnergy_le hc y]

end BanachGeometry.HilbertSums.Nonlinear
