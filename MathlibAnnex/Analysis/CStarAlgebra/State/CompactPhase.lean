import MathlibAnnex.Analysis.CStarAlgebra.State.FiniteFullImage
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SmallPath

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem phase_align (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hc : inner ℂ ξ η ≠ 0) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧
      (∀ T : H →L[ℂ] H, inner ℂ ζ (T ζ) = inner ℂ η (T η)) ∧
      ‖ξ - ζ‖ ^ 2 = 2 - 2 * ‖inner ℂ ξ η‖ := by
  let c : ℂ := inner ℂ ξ η
  let a : ℂ := star c / (‖c‖ : ℂ)
  have hc' : c ≠ 0 := hc
  have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc'
  have ha : ‖a‖ = 1 := by
    simp [a, hc']
  have hac : a * c = (‖c‖ : ℂ) := by
    dsimp [a]
    rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [hc0]
  have ha2 : a * star a = 1 := by
    change a * (starRingEnd ℂ) a = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  refine ⟨a • η, by simp [norm_smul, ha, hη], ?_, ?_⟩
  · intro T
    simp only [map_smul, inner_smul_left, inner_smul_right]
    change a * (starRingEnd ℂ) a = 1 at ha2
    rw [← mul_assoc, ha2, one_mul]
  · rw [norm_sub_sq (𝕜 := ℂ)]
    rw [hξ, norm_smul, ha, hη, inner_smul_right]
    change (1:ℝ) ^ 2 - 2 * (a * c).re + (1 * 1) ^ 2 = 2 - 2 * ‖c‖
    rw [hac]
    simp only [Complex.ofReal_re]
    ring

theorem phase_align_lt_two (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧
      (∀ T : H →L[ℂ] H, inner ℂ ζ (T ζ) = inner ℂ η (T η)) ∧
      ‖ξ - ζ‖ < 2 := by
  by_cases hc : inner ℂ ξ η = 0
  · refine ⟨η, hη, fun _ => rfl, ?_⟩
    have hs : ‖ξ - η‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ)]
      simp [hξ, hη, hc]
      norm_num
    have hn : 0 ≤ ‖ξ - η‖ := norm_nonneg _
    nlinarith
  · obtain ⟨ζ, hζ, hfun, hs⟩ := phase_align ξ η hξ hη hc
    refine ⟨ζ, hζ, hfun, ?_⟩
    have hn : 0 ≤ ‖ξ - ζ‖ := norm_nonneg _
    have hc0 : 0 ≤ ‖inner ℂ ξ η‖ := norm_nonneg _
    nlinarith

end MathlibAnnex.Analysis.CStarAlgebra

