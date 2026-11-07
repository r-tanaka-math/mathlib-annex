/- Actual late-block neighborhood separation for the tail-dependent directions.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.Support

noncomputable section
open scoped Topology
open Filter
namespace BanachGeometry.HilbertSums.Nonlinear
open Coding Clock

theorem codeDirection_coordinate_zero_of_code_zero (n k : ℕ) (hk : k < n + 1)
    (y : GradedHilbert) (a : BlockCoordinate n)
    (hz : unitCode a.1.val (fun j => scalarObservation j.val y) a.2 = 0) :
    codeDirection n k hk y a.1 a.2 = 0 := by
  by_cases he : a.1.val = k
  · subst k
    change (show GradedBlock n from PiLp.single 2 a.1
      (unitCode a.1.val (fun j => scalarObservation j.val y))) a.1 a.2 = 0
    rw [PiLp.single_eq_same]
    exact hz
  · have hne : a.1 ≠ (⟨k, hk⟩ : Fin (n + 1)) := fun h => he (congrArg Fin.val h)
    simp [codeDirection, levelIsometry, Pi.single_apply, hne]

theorem omegaPrefix_coordinate_zero_of_codes_zero (c : ℝ) (hc : 0 < c) (n : ℕ)
    (y : GradedHilbert) (t : ℝ) (a : BlockCoordinate n)
    (hz : ∀ k (hk : k < n + 1), codeDirection n k hk y a.1 a.2 = 0) :
    ∀ k (hk : k ≤ n), omegaPrefix c hc n y t k hk a.1 a.2 = 0 := by
  intro k
  induction k with
  | zero => intro hk; exact hz _ _
  | succ k ih =>
    intro hk
    rw [omegaPrefix]
    split_ifs
    · exact ih _
    · simp [bridge, unitSegment, NormedSpace.normalize, affineSegment, hz]

theorem omega_support_implies_code_support (c : ℝ) (hc : 0 < c) (n : ℕ)
    (y : GradedHilbert) (r : ℝ) (a : BlockCoordinate n)
    (ha : a ∈ scalarSupport n (omega c hc n y r)) :
    a ∈ scalarSupport n (codeDirection n a.1.val a.1.isLt y) := by
  by_contra h
  have hcode : unitCode a.1.val (fun j => scalarObservation j.val y) a.2 = 0 := by
    simpa [scalarSupport, codeDirection, levelIsometry] using h
  have hz (k : ℕ) (hk : k < n + 1) : codeDirection n k hk y a.1 a.2 = 0 :=
    codeDirection_coordinate_zero_of_code_zero n k hk y a hcode
  apply ha
  unfold omega
  split_ifs
  · exact omegaPrefix_coordinate_zero_of_codes_zero c hc n y _ a (fun k hk => hz k hk) n le_rfl
  · exact hz n (by omega)

/-- Simultaneously small tails on an entire ball, with an explicit block cutoff. -/
theorem exists_late_small_tails (a : GradedHilbert) {ρ : ℝ} (hρ : 0 < ρ) (K : ℕ) :
    ∃ N : ℕ, K < N ∧ ∀ n, N ≤ n → ∀ y, ‖y - a‖ < ρ / 2 → ‖blockTail n y‖ < ρ := by
  have ht := (tendsto_norm_blockTail_zero a).eventually (eventually_lt_nhds (half_pos hρ))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ht
  let N := max N₀ (K + 1)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro n hn y hy
  have hna : ‖blockTail n a‖ < ρ / 2 := hN₀ n ((le_max_left _ _).trans hn)
  have hdiff := abs_norm_blockTail_sub_norm_blockTail_le n y a
  have hle := le_abs_self (‖blockTail n y‖ - ‖blockTail n a‖)
  linarith

theorem exists_clock_radius (c : ℝ) (hc : 0 < c) (K : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ transitionStart c hc K + 8 < tau c ρ := by
  have ht := (tendsto_harmonicClockEndpoint_atTop hc).eventually
    (eventually_gt_atTop (transitionStart c hc K + 8))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  exact ⟨dyadicRadius N, dyadicRadius_pos N, by rw [tau_dyadic_endpoint]; exact hN N le_rfl⟩

/-- Two distinct centers have whole neighborhoods with disjoint direction supports in every late block. -/
theorem pair_local_direction_supports (c : ℝ) (hc : 0 < c) {a b : GradedHilbert} (hab : a ≠ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ y z,
      ‖y - a‖ < ε → ‖z - b‖ < ε →
      Disjoint (scalarSupport n (pointDirection c hc y n)) (scalarSupport n (pointDirection c hc z n)) := by
  obtain ⟨K, hK, ε₀, hε₀, hcodes⟩ := exists_pair_code_neighborhoods hab
  obtain ⟨ρ, hρ, hclock⟩ := exists_clock_radius c hc K
  obtain ⟨Na, hKa, hNa⟩ := exists_late_small_tails a hρ K
  obtain ⟨Nb, hKb, hNb⟩ := exists_late_small_tails b hρ K
  let ε := min ε₀ (ρ / 2)
  refine ⟨ε, lt_min hε₀ (half_pos hρ), max Na Nb, ?_⟩
  intro n hn y z hy hz
  have hna : Na ≤ n := (le_max_left _ _).trans hn
  have hnb : Nb ≤ n := (le_max_right _ _).trans hn
  have hKn : K < n := hKa.trans_le hna
  have hys : ‖blockTail n y‖ < ρ := hNa n hna y (hy.trans_le (min_le_right _ _))
  have hzs : ‖blockTail n z‖ < ρ := hNb n hnb z (hz.trans_le (min_le_right _ _))
  have hyclock : ‖blockTail n y‖ = 0 ∨ transitionStart c hc K + 8 < tau c ‖blockTail n y‖ := by
    by_cases hzero : ‖blockTail n y‖ = 0
    · exact Or.inl hzero
    · exact Or.inr (hclock.trans_le (tau_antitone_positive hc.le
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hρ hys.le))
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hlevel : K < p.1.val := by
    by_contra h
    exact hp (omega_no_low_level c hc n K hKn y (norm_nonneg _) hyclock p (le_of_not_gt h))
  have hd := hcodes y z (hy.trans_le (min_le_left _ _)) (hz.trans_le (min_le_left _ _))
    n p.1.val p.1.isLt hlevel.le
  exact Set.disjoint_left.mp hd
    (omega_support_implies_code_support c hc n y _ p hp)
    (omega_support_implies_code_support c hc n z _ p hq)

end BanachGeometry.HilbertSums.Nonlinear
