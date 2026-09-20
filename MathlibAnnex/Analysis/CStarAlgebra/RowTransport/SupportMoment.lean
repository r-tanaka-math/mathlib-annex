import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.TwoLegPath

set_option autoImplicit false
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem support_residual_sq_le (Q : H →L[ℂ] H) (hQ : ‖Q‖ ≤ 1)
    (v : H) (hv : ‖v‖ = 1) :
    ‖(1 - Q) v‖ ^ 2 ≤ 2 * ‖(1 : ℂ) - inner ℂ v (Q v)‖ := by
  have hQv : ‖Q v‖ ≤ 1 := by
    calc
      _ ≤ ‖Q‖ * ‖v‖ := Q.le_opNorm v
      _ ≤ 1 * 1 := mul_le_mul hQ hv.le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hre : 1 - (inner ℂ v (Q v)).re ≤
      ‖(1 : ℂ) - inner ℂ v (Q v)‖ := by
    have h := Complex.re_le_norm ((1 : ℂ) - inner ℂ v (Q v))
    simpa only [Complex.sub_re, Complex.one_re] using h
  have hnorm : ‖(1 - Q) v‖ = ‖v - Q v‖ := by
    simp only [sub_apply, one_apply_eq_self]
  have hQv2 : ‖Q v‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (Q v)]
  change 1 - RCLike.re (inner ℂ v (Q v)) ≤
    ‖(1 : ℂ) - inner ℂ v (Q v)‖ at hre
  rw [hnorm, norm_sub_sq (𝕜 := ℂ)]
  nlinarith

theorem support_residual_lt (Q : H →L[ℂ] H) (hQ : ‖Q‖ ≤ 1)
    (v : H) (hv : ‖v‖ = 1) {ρ μ : ℝ} (hρ : 0 < ρ)
    (hμ : 2 * μ < ρ ^ 2)
    (hmoment : ‖(1 : ℂ) - inner ℂ v (Q v)‖ < μ) :
    ‖(1 - Q) v‖ < ρ := by
  have hsq := support_residual_sq_le Q hQ v hv
  have hbound : ‖(1 - Q) v‖ ^ 2 < ρ ^ 2 := by
    nlinarith
  nlinarith [norm_nonneg ((1 - Q) v)]

end MathlibAnnex.Analysis.CStarAlgebra
