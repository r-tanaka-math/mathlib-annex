/- Strict clock order and activation thresholds.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.ScaleClock.Growth

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums.Clock

theorem tau_strict_order {c a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hab : a < b) (hb1 : b ≤ 1) : tau c b < tau c a := by
  obtain ⟨m, hm⟩ := exists_radius_cutoff ha
  let N := m + 1
  have hN : dyadicRadius N ≤ a := hm.le
  have hlength : (∑ n ∈ Finset.range N, (bandLength n a - bandLength n b)) = b - a := by
    rw [Finset.sum_sub_distrib, sum_bandLength, sum_bandLength,
      max_eq_left (sub_nonpos.mpr hN), max_eq_left (sub_nonpos.mpr (hN.trans hab.le)),
      max_eq_right (by linarith : 0 ≤ 1 - a), max_eq_right (by linarith : 0 ≤ 1 - b)]
    ring
  have hsum : dyadicSlope c 0 * (b - a) ≤ tau c a - tau c b := by
    rw [tau_eq_finite c ha hN, tau_eq_finite c (ha.trans hab) (hN.trans hab.le),
      ← Finset.sum_sub_distrib, ← hlength, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hs := slope_monotone hc.le (Nat.zero_le n)
    have hl := sub_nonneg.mpr (bandLength_antitone n hab.le)
    nlinarith [mul_le_mul_of_nonneg_right hs hl]
  have hpos : 0 < dyadicSlope c 0 * (b - a) :=
    mul_pos (dyadicSlope_pos hc 0) (sub_pos.mpr hab)
  linarith

theorem radius_le_of_tau_ge {c r R : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hR : 0 < R) (hR1 : R ≤ 1) (hT : 0 < tau c R) (h : tau c R ≤ tau c r) : r ≤ R := by
  by_contra hn
  have hlt : R < r := lt_of_not_ge hn
  by_cases hr1 : r ≤ 1
  · exact not_lt_of_ge h (tau_strict_order hc hR hlt hr1)
  · have hz := tau_zero_of_one_le c (le_of_not_ge hr1)
    linarith

theorem transitionStart_strictMono (c : ℝ) (hc : 0 < c) : StrictMono (transitionStart c hc) :=
  strictMono_nat_of_lt_succ (fun k => by linarith [transitionStart_gap c hc k])

theorem transitionStart_pos (c : ℝ) (hc : 0 < c) (k : ℕ) : 0 < transitionStart c hc k := by
  have h0 := (nextTransition_spec c hc 0 0).2.2
  have hk := (transitionStart_strictMono c hc).monotone (Nat.zero_le k)
  have he : harmonicClockEndpoint c 0 = 0 := by simp [harmonicClockEndpoint]
  change harmonicClockEndpoint c (nextTransition c hc 0 0) ≤ _ at hk
  rw [he] at h0
  linarith

/-- Every active transition has its prescribed Lipschitz budget at the current radius. -/
theorem active_transition_budget (c : ℝ) (hc : 0 < c) (k : ℕ) {r : ℝ}
    (hr : 0 < r) (ht : transitionStart c hc k ≤ tau c r) :
    2 * max (codeLipschitz k) (codeLipschitz (k + 1)) ≤ gamma c r := by
  let N := transitionIndex c hc k
  have hT : tau c (dyadicRadius N) = transitionStart c hc k := tau_dyadic_endpoint c N
  have hrad : r ≤ dyadicRadius N := radius_le_of_tau_ge hc hr (dyadicRadius_pos N)
    (radius_le_one N) (by rw [hT]; exact transitionStart_pos c hc k) (by rwa [hT])
  have hr1 : r ≤ 1 := hrad.trans (radius_le_one N)
  have hidx := index_ge_of_radius_le hr hrad
  have hg : dyadicSlope c N ≤ gamma c r := by
    simpa only [gamma, if_pos (show 0 < r ∧ r ≤ 1 from ⟨hr, hr1⟩)] using slope_monotone hc.le hidx
  exact (transitionSlope_bound c hc k).trans hg

end BanachGeometry.HilbertSums.Clock
