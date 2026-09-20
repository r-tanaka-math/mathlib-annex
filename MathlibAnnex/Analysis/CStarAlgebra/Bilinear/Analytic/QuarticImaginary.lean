import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.SignedDyadic

/-!
# The normalized selfadjoint fourth-moment imaginary estimate

The constant 36 is deliberately coarse.  Its proof uses the original
C*-algebras, their normalized marginal states, finite continuous dyadic
effects and the explicitly proved phase bound.  There are no spectral
projection providers and no weak compactness or separate normality inputs.
Zero marginal fourth moments are handled by an explicit positive-cutoff
argument, not by division by zero.  SOURCE_UNBUILT.

This is not yet the all-finite-family row/column theorem: the real part and
noncommutative fourth-moment averaging remain separate subsequent steps.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear.Analytic

open MathlibAnnex.Analysis.CStarAlgebra
universe u v
variable {A : Type u} {D : Type v}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

/-- The nonnegative fourth root, using only the real square-root API. -/
def fourthRoot (m : ℝ) : ℝ := Real.sqrt (Real.sqrt m)

theorem fourthRoot_nonneg (m : ℝ) : 0 ≤ fourthRoot m := Real.sqrt_nonneg _

@[simp] theorem fourthRoot_zero : fourthRoot 0 = 0 := by simp [fourthRoot]

theorem fourthRoot_pos {m : ℝ} (hm : 0 < m) : 0 < fourthRoot m :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm)

theorem fourthRoot_sq (m : ℝ) : fourthRoot m ^ 2 = Real.sqrt m :=
  Real.sq_sqrt (Real.sqrt_nonneg m)

/-- Vanishing from a uniformly arbitrarily small positive cutoff.  The
argument is algebraic and gives the actual cutoff used in a contradiction. -/
theorem le_zero_of_forall_pos_le_mul (x K : ℝ) (hK : 0 ≤ K)
    (h : ∀ T : ℝ, 0 < T → x ≤ T * K) : x ≤ 0 := by
  by_contra hx
  have hx0 : 0 < x := lt_of_not_ge hx
  let T : ℝ := x / (2 * (K + 1))
  have hden : 0 < 2 * (K + 1) := by positivity
  have hT : 0 < T := div_pos hx0 hden
  have he : T * (2 * (K + 1)) = x := by
    dsimp [T]
    field_simp [ne_of_gt hden]
  have ht := h T hT
  have hmul := mul_le_mul_of_nonneg_right ht hden.le
  have hre : (T * K) * (2 * (K + 1)) = x * K := by
    calc
      _ = (T * (2 * (K + 1))) * K := by ring
      _ = x * K := by rw [he]
  rw [hre] at hmul
  nlinarith [mul_nonneg hx0.le hK]

/-- The two arbitrary cutoff parameters are retained until the last step. -/
theorem normalized_abs_im_cutoff_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (b : D) (hb : IsSelfAdjoint b)
    {T S : ℝ} (hT : 0 < T) (hS : 0 < S) :
    |(V a b).im| ≤
      (2 * T + 4 * Real.sqrt (fourthMoment (leftMarginal V) a) / T) *
      (2 * S + 4 * Real.sqrt (fourthMoment (rightMarginal V) b) / S) := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  obtain ⟨L, hL, hLa, hLc⟩ := exists_signed_effect_decomposition (leftMarginal V) hphi a ha hT
  obtain ⟨M, hM, hMb, hMc⟩ := exists_signed_effect_decomposition (rightMarginal V) hpsi b hb hS
  have h := normalized_abs_im_lists_le V hV h1 L hL M hM
  rw [hLa, hMb] at h
  apply h.trans
  exact mul_le_mul hLc hMc (effectCost_nonneg _ _)
    (by positivity)

/-- The analytic fourth-moment bound is a derived theorem for every normalized
bounded bilinear form on independent-universe C*-algebras. -/
theorem normalized_abs_im_quartic_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) (b : D) (hb : IsSelfAdjoint b) :
    |(V a b).im| ≤ 36 * fourthRoot (fourthMoment (leftMarginal V) a) *
      fourthRoot (fourthMoment (rightMarginal V) b) := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  let m : ℝ := fourthMoment (leftMarginal V) a
  let n : ℝ := fourthMoment (rightMarginal V) b
  have hm : 0 ≤ m := fourthMoment_nonneg _ hphi a ha
  have hn : 0 ≤ n := fourthMoment_nonneg _ hpsi b hb
  change |(V a b).im| ≤ 36 * fourthRoot m * fourthRoot n
  by_cases hm0 : m = 0
  · have hz : |(V a b).im| ≤ 0 := by
      apply le_zero_of_forall_pos_le_mul _ (2 * (2 + 4 * Real.sqrt n)) (by positivity)
      intro T hT
      have h := normalized_abs_im_cutoff_le V hV h1 a ha b hb (T := T) (S := 1) hT (by norm_num)
      change |(V a b).im| ≤ (2 * T + 4 * Real.sqrt m / T) *
        (2 * 1 + 4 * Real.sqrt n / 1) at h
      simp only [hm0, Real.sqrt_zero, mul_zero, zero_div, add_zero, mul_one, div_one] at h
      nlinarith [h]
    simpa [hm0] using hz
  · by_cases hn0 : n = 0
    · have hz : |(V a b).im| ≤ 0 := by
        apply le_zero_of_forall_pos_le_mul _ (2 * (2 + 4 * Real.sqrt m)) (by positivity)
        intro S hS
        have h := normalized_abs_im_cutoff_le V hV h1 a ha b hb (T := 1) (S := S) (by norm_num) hS
        change |(V a b).im| ≤ (2 * 1 + 4 * Real.sqrt m / 1) *
          (2 * S + 4 * Real.sqrt n / S) at h
        simp only [hn0, Real.sqrt_zero, mul_zero, zero_div, add_zero, mul_one, div_one] at h
        nlinarith [h]
      simpa [hn0] using hz
    · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
      have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
      have hT := fourthRoot_pos hmpos
      have hS := fourthRoot_pos hnpos
      have h := normalized_abs_im_cutoff_le V hV h1 a ha b hb hT hS
      have hmc : 2 * fourthRoot m + 4 * Real.sqrt m / fourthRoot m = 6 * fourthRoot m := by
        rw [← fourthRoot_sq m]
        field_simp [ne_of_gt hT] <;> ring
      have hnc : 2 * fourthRoot n + 4 * Real.sqrt n / fourthRoot n = 6 * fourthRoot n := by
        rw [← fourthRoot_sq n]
        field_simp [ne_of_gt hS] <;> ring
      change |(V a b).im| ≤
        (2 * fourthRoot m + 4 * Real.sqrt m / fourthRoot m) *
        (2 * fourthRoot n + 4 * Real.sqrt n / fourthRoot n) at h
      rw [hmc, hnc] at h
      nlinarith [h]

end MathlibAnnex.CStarBilinear.Analytic
