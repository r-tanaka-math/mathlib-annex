import MathlibAnnex.Analysis.CStarAlgebra.State.CompactPhase

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rankOne_moment (ξ η : H) :
    inner ℂ η ((InnerProductSpace.rankOne ℂ ξ ξ) η) =
      ((‖inner ℂ ξ η‖ ^ 2 : ℝ) : ℂ) := by
  rw [InnerProductSpace.rankOne_apply, inner_smul_right]
  have hs : inner ℂ η ξ = star (inner ℂ ξ η) := (inner_conj_symm η ξ).symm
  rw [hs]
  change inner ℂ ξ η * (starRingEnd ℂ) (inner ℂ ξ η) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem phase_align_of_rankOne_moment
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    {d : ℝ} (hd : 0 < d)
    (hm : ‖(1 : ℂ) - inner ℂ η ((InnerProductSpace.rankOne ℂ ξ ξ) η)‖ <
      min 1 (d ^ 2 / 2)) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧
      (∀ T : H →L[ℂ] H, inner ℂ ζ (T ζ) = inner ℂ η (T η)) ∧
      ‖ξ - ζ‖ < d := by
  let c : ℂ := inner ℂ ξ η
  have hr : ‖c‖ ≤ 1 := by
    simpa [c, hξ, hη] using norm_inner_le_norm ξ η
  have habs : |1 - ‖c‖ ^ 2| < min 1 (d ^ 2 / 2) := by
    rw [rankOne_moment] at hm
    have hcast : (1 : ℂ) - ((‖c‖ ^ 2 : ℝ) : ℂ) =
        ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [show inner ℂ ξ η = c from rfl, hcast, Complex.norm_real,
      Real.norm_eq_abs] at hm
    exact hm
  have hpos : 0 ≤ 1 - ‖c‖ ^ 2 := by
    have hcn : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith
  have hlt : 1 - ‖c‖ ^ 2 < d ^ 2 / 2 :=
    (abs_of_nonneg hpos ▸ habs).trans_le (min_le_right _ _)
  have hc : c ≠ 0 := by
    intro hc0
    have hnorm : ‖c‖ = 0 := by simp [hc0]
    rw [hnorm] at habs
    have hmin : min 1 (d ^ 2 / 2) ≤ 1 := min_le_left _ _
    norm_num at habs
  obtain ⟨ζ, hζ, hfunctional, hsquare⟩ := phase_align ξ η hξ hη hc
  refine ⟨ζ, hζ, hfunctional, ?_⟩
  have hcn : 0 ≤ ‖c‖ := norm_nonneg c
  have hnorm : 0 ≤ ‖ξ - ζ‖ := norm_nonneg _
  nlinarith

end MathlibAnnex.Analysis.CStarAlgebra

