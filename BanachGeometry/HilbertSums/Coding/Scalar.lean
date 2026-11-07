/-
Fixed Pair R6 §9, bounded scalar observations, reconstructed without derivatives.
Scalar observations for the Hilbert construction; exact execution evidence is external.
Source authority: the R6 manuscript preserved in the same W01 workspace and
explicit W02 user instruction. No change to Common or the previous modules.
-/
import BanachGeometry.HilbertSums.FrozenRearrangement

noncomputable section
namespace BanachGeometry.HilbertSums.Coding

/-- R6 p_j uses this scalar compression after a real Hilbert coordinate. -/
def boundedScalar (s : ℝ) : ℝ := s / (1 + |s|)

theorem abs_boundedScalar_lt_one (s : ℝ) : |boundedScalar s| < 1 := by
  have hp : 0 < 1 + |s| := by positivity
  rw [boundedScalar, abs_div, abs_of_pos hp, div_lt_one hp]
  linarith

theorem boundedScalar_strictMono : StrictMono boundedScalar := by
  intro s t hst
  rw [boundedScalar, boundedScalar, div_lt_div_iff₀ (by positivity) (by positivity)]
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := le_trans hs hst.le
    rw [abs_of_nonneg hs, abs_of_nonneg ht]
    nlinarith
  · have hs' : s ≤ 0 := le_of_not_ge hs
    by_cases ht : t ≤ 0
    · rw [abs_of_nonpos hs', abs_of_nonpos ht]
      nlinarith
    · have ht' : 0 ≤ t := le_of_not_ge ht
      rw [abs_of_nonpos hs', abs_of_nonneg ht']
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hs' ht']

theorem boundedScalar_injective : Function.Injective boundedScalar :=
  boundedScalar_strictMono.injective

/-- The same-sign difference formula and the cross-zero estimate give slope ≤ 1. -/
theorem boundedScalar_sub_le {s t : ℝ} (hst : s ≤ t) :
    boundedScalar t - boundedScalar s ≤ t - s := by
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := le_trans hs hst
    have hd : 1 ≤ (1 + s) * (1 + t) := by nlinarith [mul_nonneg hs ht]
    have hid : boundedScalar t - boundedScalar s = (t - s) / ((1 + s) * (1 + t)) := by
      simp only [boundedScalar, abs_of_nonneg hs, abs_of_nonneg ht]
      field_simp [show 1 + s ≠ 0 by linarith, show 1 + t ≠ 0 by linarith]
      ring
    rw [hid]
    exact div_le_self (sub_nonneg.mpr hst) hd
  · have hs' : s ≤ 0 := le_of_not_ge hs
    by_cases ht : t ≤ 0
    · have hd : 1 ≤ (1 - s) * (1 - t) := by nlinarith [mul_nonneg_of_nonpos_of_nonpos hs' ht]
      have hid : boundedScalar t - boundedScalar s = (t - s) / ((1 - s) * (1 - t)) := by
        simp only [boundedScalar, abs_of_nonpos hs', abs_of_nonpos ht]
        change t / (1 - t) - s / (1 - s) = (t - s) / ((1 - s) * (1 - t))
        field_simp [show 1 - s ≠ 0 by linarith, show 1 - t ≠ 0 by linarith]
        ring
      rw [hid]
      exact div_le_self (sub_nonneg.mpr hst) hd
    · have ht' : 0 ≤ t := le_of_not_ge ht
      have h1 : t / (1 + t) ≤ t := div_le_self ht' (by linarith)
      have h2 : -(s / (1 - s)) ≤ -s := by
        simpa only [neg_div] using
          (div_le_self (neg_nonneg.mpr hs') (by linarith : (1 : ℝ) ≤ 1 - s))
      simp only [boundedScalar, abs_of_nonpos hs', abs_of_nonneg ht']
      change t / (1 + t) - s / (1 - s) ≤ t - s
      linarith

theorem abs_boundedScalar_sub_le (s t : ℝ) :
    |boundedScalar s - boundedScalar t| ≤ |s - t| := by
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm (boundedScalar s), abs_sub_comm s,
      abs_of_nonneg (sub_nonneg.mpr (boundedScalar_strictMono.monotone hst)),
      abs_of_nonneg (sub_nonneg.mpr hst)]
    exact boundedScalar_sub_le hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (boundedScalar_strictMono.monotone hts)),
      abs_of_nonneg (sub_nonneg.mpr hts)]
    exact boundedScalar_sub_le hts

end BanachGeometry.HilbertSums.Coding
