/- Global dyadic clock as a locally finite sum with the actual band formula.
This representation equals the affine pieces. Values at r≤0 are totalized by 0
and are not used as gamma(0). No analytic supplier or missing theorem is assumed.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.DyadicEnergy

noncomputable section
open scoped BigOperators Topology
open Filter
namespace BanachGeometry.HilbertSums.Clock

theorem radius_strictAnti : StrictAnti dyadicRadius := by
  apply strictAnti_nat_of_succ_lt
  intro m
  rw [dyadicRadius_succ]
  linarith [dyadicRadius_pos m]

theorem radius_le_one (m : ℕ) : dyadicRadius m ≤ 1 := by
  simpa [dyadicRadius] using radius_strictAnti.antitone (Nat.zero_le m)

theorem exists_radius_cutoff {r : ℝ} (hr : 0 < r) : ∃ m, dyadicRadius (m + 1) < r := by
  have he := tendsto_dyadicRadius_zero.eventually (eventually_lt_nhds hr)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨N, (radius_strictAnti (Nat.lt_succ_self N)).le.trans_lt (hN N le_rfl)⟩

/-- The unique half-open band (r_(m+1),r_m] for a radius in (0,1]. -/
def bandIndex (r : ℝ) : ℕ :=
  if hr : 0 < r then Nat.find (exists_radius_cutoff hr) else 0

theorem bandIndex_lower {r : ℝ} (hr : 0 < r) : dyadicRadius (bandIndex r + 1) < r := by
  simpa only [bandIndex, dif_pos hr] using Nat.find_spec (exists_radius_cutoff hr)

theorem bandIndex_min {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : dyadicRadius (m + 1) < r) :
    bandIndex r ≤ m := by
  simpa only [bandIndex, dif_pos hr] using Nat.find_min' (exists_radius_cutoff hr) hm

theorem bandIndex_upper {r : ℝ} (hr : 0 < r) (h1 : r ≤ 1) : r ≤ dyadicRadius (bandIndex r) := by
  by_cases hi : bandIndex r = 0
  · simpa [hi, dyadicRadius] using h1
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi
    by_contra h
    have hcut : dyadicRadius (m + 1) < r := by simpa [hm] using lt_of_not_ge h
    have hmin := bandIndex_min hr hcut
    omega

theorem bandIndex_antitone {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    bandIndex b ≤ bandIndex a :=
  bandIndex_min hb ((bandIndex_lower ha).trans_le hab)

theorem bandIndex_eq {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hlo : dyadicRadius (m + 1) < r) (hhi : r ≤ dyadicRadius m) : bandIndex r = m := by
  apply Nat.le_antisymm (bandIndex_min hr hlo)
  by_contra h
  have hm : bandIndex r + 1 ≤ m := by omega
  have hrad := radius_strictAnti.antitone hm
  have h := bandIndex_lower hr
  linarith

/-- Length of the intersection of [r,∞) with the mth dyadic band. -/
def bandLength (m : ℕ) (r : ℝ) : ℝ :=
  max 0 (dyadicRadius m - r) - max 0 (dyadicRadius (m + 1) - r)

theorem bandLength_clamp (m : ℕ) (r : ℝ) :
    bandLength m r = max 0 (dyadicRadius m - max r (dyadicRadius (m + 1))) := by
  have hstep := (radius_strictAnti (Nat.lt_succ_self m)).le
  by_cases hr : r ≤ dyadicRadius (m + 1)
  · rw [bandLength, max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right hr, max_eq_right (by linarith)]
    ring
  · have hr' := le_of_not_ge hr
    rw [bandLength, max_eq_left (show dyadicRadius (m + 1) - r ≤ 0 by linarith),
      sub_zero, max_eq_left hr']

theorem bandLength_nonneg (m : ℕ) (r : ℝ) : 0 ≤ bandLength m r := by
  rw [bandLength_clamp]
  exact le_max_left _ _

theorem bandLength_antitone (m : ℕ) : Antitone (bandLength m) := by
  intro a b hab
  rw [bandLength_clamp, bandLength_clamp]
  exact max_le_max_left 0 (sub_le_sub_left (max_le_max_right _ hab) _)

theorem bandLength_zero {m : ℕ} {r : ℝ} (hr : dyadicRadius m ≤ r) : bandLength m r = 0 := by
  rw [bandLength_clamp, max_eq_left (by linarith [le_max_left r (dyadicRadius (m + 1))])]

theorem bandLength_full {m : ℕ} {r : ℝ} (hr : r ≤ dyadicRadius (m + 1)) :
    bandLength m r = dyadicRadius m - dyadicRadius (m + 1) := by
  rw [bandLength_clamp, max_eq_right hr,
    max_eq_right (sub_nonneg.mpr (radius_strictAnti (Nat.lt_succ_self m)).le)]

theorem bandLength_in_band {m : ℕ} {r : ℝ}
    (hlo : dyadicRadius (m + 1) ≤ r) (hhi : r ≤ dyadicRadius m) :
    bandLength m r = dyadicRadius m - r := by
  rw [bandLength_clamp, max_eq_left hlo, max_eq_right (sub_nonneg.mpr hhi)]

theorem sum_bandLength (N : ℕ) (r : ℝ) :
    (∑ m ∈ Finset.range N, bandLength m r) =
      max 0 (1 - r) - max 0 (dyadicRadius N - r) := by
  induction N with
  | zero => simp [dyadicRadius]
  | succ N ih => rw [Finset.sum_range_succ, ih, bandLength]; ring

/-- Original gamma on positive radii, with a harmless unused value at zero. -/
def gamma (c r : ℝ) : ℝ := if 0 < r ∧ r ≤ 1 then dyadicSlope c (bandIndex r) else 0

/-- Original tau on positive radii, written as a locally finite sum of band lengths. -/
def tau (c r : ℝ) : ℝ :=
  if 0 < r then ∑' m, dyadicSlope c m * bandLength m r else 0

theorem tau_eq_finite (c : ℝ) {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : dyadicRadius N ≤ r) :
    tau c r = ∑ m ∈ Finset.range N, dyadicSlope c m * bandLength m r := by
  rw [tau, if_pos hr]
  apply HasSum.tsum_eq
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  have hNm : N ≤ m := by simpa only [Finset.mem_range, not_lt] using hm
  rw [bandLength_zero ((radius_strictAnti.antitone hNm).trans hN), mul_zero]

theorem weighted_bandWidth_sum (c : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N, dyadicSlope c m * (dyadicRadius m - dyadicRadius (m + 1))) =
      harmonicClockEndpoint c N := by
  induction N with
  | zero => simp [harmonicClockEndpoint]
  | succ N ih => rw [Finset.sum_range_succ, ih, dyadic_band_increment, harmonicClockEndpoint_succ]

/-- The globally defined function agrees with the exact R6 formula on every band. -/
theorem tau_on_band (c : ℝ) {r : ℝ} {m : ℕ}
    (hlo : dyadicRadius (m + 1) < r) (hhi : r ≤ dyadicRadius m) :
    tau c r = clockOnBand c m r := by
  have hr : 0 < r := (dyadicRadius_pos _).trans hlo
  rw [tau_eq_finite c hr hlo.le, Finset.sum_range_succ]
  have hsum : (∑ n ∈ Finset.range m, dyadicSlope c n * bandLength n r) = harmonicClockEndpoint c m := by
    rw [← weighted_bandWidth_sum c m]
    apply Finset.sum_congr rfl
    intro n hn
    have hnm : n + 1 ≤ m := Finset.mem_range.mp hn
    rw [bandLength_full (hhi.trans (radius_strictAnti.antitone hnm))]
  rw [hsum, bandLength_in_band hlo.le hhi]
  rfl

theorem tau_dyadic_endpoint (c : ℝ) (m : ℕ) :
    tau c (dyadicRadius m) = harmonicClockEndpoint c m := by
  rw [tau_on_band c (radius_strictAnti (Nat.lt_succ_self m)) le_rfl,
    clockOnBand_upper_endpoint]

theorem tau_zero_of_one_le (c : ℝ) {r : ℝ} (hr : 1 ≤ r) : tau c r = 0 := by
  rw [tau_eq_finite c (by linarith) (N := 0) (by simpa [dyadicRadius] using hr)]
  simp

theorem gamma_nonneg {c : ℝ} (hc : 0 ≤ c) (r : ℝ) : 0 ≤ gamma c r := by
  unfold gamma
  split_ifs
  · exact dyadicSlope_nonneg hc _
  · exact le_rfl

theorem tau_nonneg {c : ℝ} (hc : 0 ≤ c) (r : ℝ) : 0 ≤ tau c r := by
  unfold tau
  split_ifs
  · exact tsum_nonneg (fun m => mul_nonneg (dyadicSlope_nonneg hc _) (bandLength_nonneg _ _))
  · exact le_rfl

theorem tau_antitone_positive {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : tau c b ≤ tau c a := by
  obtain ⟨m, hm⟩ := exists_radius_cutoff ha
  rw [tau_eq_finite c ha hm.le, tau_eq_finite c hb (hm.le.trans hab)]
  exact Finset.sum_le_sum (fun n _ =>
    mul_le_mul_of_nonneg_left (bandLength_antitone n hab) (dyadicSlope_nonneg hc _))

theorem slope_monotone {c : ℝ} (hc : 0 ≤ c) : Monotone (dyadicSlope c) := by
  apply monotone_nat_of_le_succ
  intro m
  unfold dyadicSlope
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one]
  have hcp : 0 ≤ c * (2 : ℝ) ^ m := by positivity
  nlinarith [mul_nonneg hcp (Nat.cast_nonneg m)]

theorem gamma_antitone_positive {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : gamma c b ≤ gamma c a := by
  by_cases hb1 : b ≤ 1
  · have ha1 : a ≤ 1 := hab.trans hb1
    simp only [gamma, if_pos (show 0 < a ∧ a ≤ 1 from ⟨ha, ha1⟩),
      if_pos (show 0 < b ∧ b ≤ 1 from ⟨hb, hb1⟩)]
    exact slope_monotone hc (bandIndex_antitone ha hb hab)
  · simp only [gamma, if_neg (by simp [hb1] : ¬ (0 < b ∧ b ≤ 1))]
    exact gamma_nonneg hc a

/-- All nonzero band-length contributions at radius a have slope at most gamma(a). -/
theorem slope_times_length_difference_le {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) (m : ℕ) :
    dyadicSlope c m * (bandLength m a - bandLength m b) ≤
      gamma c a * (bandLength m a - bandLength m b) := by
  by_cases hm : m ≤ bandIndex a
  · have hs : dyadicSlope c m ≤ gamma c a := by
      simpa only [gamma, if_pos (show 0 < a ∧ a ≤ 1 from ⟨ha, ha1⟩)] using slope_monotone hc hm
    exact mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr (bandLength_antitone m hab))
  · have hmi : bandIndex a + 1 ≤ m := by omega
    have hrad : dyadicRadius m < a :=
      (radius_strictAnti.antitone hmi).trans_lt (bandIndex_lower ha)
    rw [bandLength_zero hrad.le, bandLength_zero (hrad.le.trans hab)]
    simp

/-- Direct two-point estimate, without differentiation or an assumed global clock. -/
theorem tau_difference_le {c a b : ℝ} (hc : 0 ≤ c)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : tau c a - tau c b ≤ gamma c a * (b - a) := by
  by_cases ha1 : a ≤ 1
  · obtain ⟨m, hm⟩ := exists_radius_cutoff ha
    let N := m + 1
    have hN : dyadicRadius N ≤ a := hm.le
    rw [tau_eq_finite c ha hN, tau_eq_finite c hb (hN.trans hab)]
    have hlength : (∑ n ∈ Finset.range N, (bandLength n a - bandLength n b)) ≤ b - a := by
      rw [Finset.sum_sub_distrib, sum_bandLength, sum_bandLength,
        max_eq_left (sub_nonpos.mpr hN), max_eq_left (sub_nonpos.mpr (hN.trans hab)), sub_zero, sub_zero]
      have hmax := abs_max_sub_max_le_abs (1 - a) (1 - b) 0
      have habs : |(1 - a) - (1 - b)| = b - a := by
        have heq : (1 - a) - (1 - b) = b - a := by ring
        rw [heq, abs_of_nonneg (sub_nonneg.mpr hab)]
      have hmax' : |max 0 (1 - a) - max 0 (1 - b)| ≤ b - a := by
        rw [max_comm (0 : ℝ) (1 - a), max_comm (0 : ℝ) (1 - b)]
        exact hmax.trans_eq habs
      exact (le_abs_self _).trans hmax'
    calc
      (∑ n ∈ Finset.range N, dyadicSlope c n * bandLength n a) -
          ∑ n ∈ Finset.range N, dyadicSlope c n * bandLength n b =
          ∑ n ∈ Finset.range N, dyadicSlope c n * (bandLength n a - bandLength n b) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ ∑ n ∈ Finset.range N, gamma c a * (bandLength n a - bandLength n b) :=
        Finset.sum_le_sum (fun n _ => slope_times_length_difference_le hc ha ha1 hab n)
      _ = gamma c a * ∑ n ∈ Finset.range N, (bandLength n a - bandLength n b) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ gamma c a * (b - a) := mul_le_mul_of_nonneg_left hlength (gamma_nonneg hc _)
  · have hge : 1 ≤ a := le_of_not_ge ha1
    rw [tau_zero_of_one_le c hge, tau_zero_of_one_le c (hge.trans hab)]
    simpa only [sub_self] using mul_nonneg (gamma_nonneg hc a) (sub_nonneg.mpr hab)

theorem tau_abs_sub_le {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b) :
    |tau c a - tau c b| ≤ gamma c (min a b) * |a - b| := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonneg (sub_nonneg.mpr (tau_antitone_positive hc ha hb hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using tau_difference_le hc ha hb hab
  · rw [min_eq_right hba, abs_sub_comm (tau c a), abs_of_nonneg
      (sub_nonneg.mpr (tau_antitone_positive hc hb ha hba)), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact tau_difference_le hc hb ha hba

theorem tau_continuousAt {c r : ℝ} (hr : 0 < r) : ContinuousAt (tau c) r := by
  obtain ⟨m, hm⟩ := exists_radius_cutoff hr
  let N := m + 1
  let f : ℝ → ℝ := fun s => ∑ n ∈ Finset.range N, dyadicSlope c n * bandLength n s
  have hf : Continuous f := by unfold f bandLength; fun_prop
  have he : tau c =ᶠ[𝓝 r] f := by
    filter_upwards [eventually_gt_nhds hm] with s hs
    exact tau_eq_finite c ((dyadicRadius_pos N).trans hs) hs.le
  exact hf.continuousAt.congr he.symm

end BanachGeometry.HilbertSums.Clock
