/- R6: unbounded dyadic slopes and clocks, and actual recursive transition choices.
All hypotheses are the visible scalar conditions 0<c; no analytic theorem is an instance. -/
import BanachGeometry.HilbertSums.ScaleClock.Global

noncomputable section
open scoped Topology
open Filter
namespace BanachGeometry.HilbertSums.Clock

theorem pow_two_quadratic_lower (n : ℕ) :
    ((n : ℝ) + 2) * (n + 3) ≤ 2 * (2 : ℝ) ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (show (0 : ℝ) ≤ n + 3 by positivity)]

theorem slope_linear_lower {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    c * ((n : ℝ) + 2) / 16 ≤ dyadicSlope c (n + 2) := by
  have h := mul_le_mul_of_nonneg_left (pow_two_quadratic_lower n) hc
  unfold dyadicSlope
  rw [le_div_iff₀ (by positivity)]
  push_cast
  nlinarith

theorem slope_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (dyadicSlope c) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨N, hN⟩ := exists_nat_gt (16 * B / c)
  have hNB : B < c * (N : ℝ) / 16 := by
    have h := (div_lt_iff₀ hc).mp hN
    nlinarith
  refine eventually_atTop.2 ⟨N + 2, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hNm : (N : ℝ) ≤ n + 2 := by exact_mod_cast (show N ≤ n + 2 by omega)
  calc
    B ≤ c * (N : ℝ) / 16 := hNB.le
    _ ≤ c * ((n : ℝ) + 2) / 16 := by gcongr
    _ ≤ dyadicSlope c (n + 2) := slope_linear_lower hc.le n

theorem tau_tendsto_zero_right_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (tau c) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨m, hm⟩ := eventually_atTop.mp
    ((tendsto_harmonicClockEndpoint_atTop hc).eventually_ge_atTop B)
  have he := hm m le_rfl
  have hs : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < dyadicRadius m :=
    (eventually_lt_nhds (dyadicRadius_pos m)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs] with r hr hsmall
  have hr' : 0 < r := hr
  calc
    B ≤ harmonicClockEndpoint c m := he
    _ = tau c (dyadicRadius m) := (tau_dyadic_endpoint c m).symm
    _ ≤ tau c r := tau_antitone_positive hc.le hr' (dyadicRadius_pos m) hsmall.le

theorem index_ge_of_radius_le {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : r ≤ dyadicRadius N) :
    N ≤ bandIndex r := by
  by_contra hn
  have hi : bandIndex r + 1 ≤ N := by omega
  have hrad := radius_strictAnti.antitone hi
  have hl := bandIndex_lower hr
  linarith

theorem gamma_tendsto_zero_right_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (gamma c) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((slope_tendsto_atTop hc).eventually_ge_atTop B)
  have hB : B ≤ dyadicSlope c N := hN N le_rfl
  have hs : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < dyadicRadius N :=
    (eventually_lt_nhds (dyadicRadius_pos N)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs] with r hr hsmall
  have hr' : 0 < r := hr
  have hr1 : r ≤ 1 := hsmall.le.trans (radius_le_one N)
  rw [gamma, if_pos ⟨hr', hr1⟩]
  exact hB.trans (slope_monotone hc.le (index_ge_of_radius_le hr' hsmall.le))

/-- The level-k Lipschitz constant is exactly the R6 finite-code constant. -/
def codeLipschitz (k : ℕ) : ℝ := 4 * k * Real.sqrt ((2 * k + 1 : ℕ) ^ k)

theorem exists_transition_index {c : ℝ} (hc : 0 < c) (previous k : ℕ) :
    ∃ N : ℕ, previous < N ∧
      2 * max (codeLipschitz k) (codeLipschitz (k + 1)) ≤ dyadicSlope c N ∧
      harmonicClockEndpoint c previous + 9 < harmonicClockEndpoint c N := by
  have h1 := (slope_tendsto_atTop hc).eventually_ge_atTop
    (2 * max (codeLipschitz k) (codeLipschitz (k + 1)))
  have h2 := (tendsto_harmonicClockEndpoint_atTop hc).eventually
    (eventually_gt_atTop (harmonicClockEndpoint c previous + 9))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h1.and h2)
  let M := max N (previous + 1)
  exact ⟨M, by omega, (hN M (le_max_left _ _)).1, (hN M (le_max_left _ _)).2⟩

def nextTransition (c : ℝ) (hc : 0 < c) (previous k : ℕ) : ℕ :=
  Nat.find (exists_transition_index hc previous k)

theorem nextTransition_spec (c : ℝ) (hc : 0 < c) (previous k : ℕ) :
    previous < nextTransition c hc previous k ∧
      2 * max (codeLipschitz k) (codeLipschitz (k + 1)) ≤
        dyadicSlope c (nextTransition c hc previous k) ∧
      harmonicClockEndpoint c previous + 9 <
        harmonicClockEndpoint c (nextTransition c hc previous k) :=
  Nat.find_spec (exists_transition_index hc previous k)

/-- N_(k+1), in zero-based storage, with all previous choices left unchanged. -/
def transitionIndex (c : ℝ) (hc : 0 < c) : ℕ → ℕ
  | 0 => nextTransition c hc 0 0
  | k + 1 => nextTransition c hc (transitionIndex c hc k) (k + 1)

theorem transitionIndex_strictMono (c : ℝ) (hc : 0 < c) : StrictMono (transitionIndex c hc) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (nextTransition_spec c hc (transitionIndex c hc k) (k + 1)).1

def transitionStart (c : ℝ) (hc : 0 < c) (k : ℕ) : ℝ :=
  harmonicClockEndpoint c (transitionIndex c hc k)

theorem transitionStart_gap (c : ℝ) (hc : 0 < c) (k : ℕ) :
    transitionStart c hc k + 9 < transitionStart c hc (k + 1) :=
  (nextTransition_spec c hc (transitionIndex c hc k) (k + 1)).2.2

theorem transitionSlope_bound (c : ℝ) (hc : 0 < c) (k : ℕ) :
    2 * max (codeLipschitz k) (codeLipschitz (k + 1)) ≤
      dyadicSlope c (transitionIndex c hc k) := by
  cases k with
  | zero => exact (nextTransition_spec c hc 0 0).2.1
  | succ k => exact (nextTransition_spec c hc (transitionIndex c hc k) (k + 1)).2.1

end BanachGeometry.HilbertSums.Clock
