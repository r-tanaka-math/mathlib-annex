import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.PathCompose

set_option autoImplicit false
noncomputable section
open NormedSpace
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem representation_unitary_norm_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (u : unitary A) (ξ : H) :
    ‖pi (u : A) ξ‖ = ‖ξ‖ := by
  have hu : pi (u : A) ∈ unitary (H →L[ℂ] H) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, u.property.1, map_one]
    · rw [← map_star, ← map_mul, u.property.2, map_one]
  exact (pi (u : A)).norm_map_of_mem_unitary hu ξ

theorem exists_corrected_exponential_path
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (b : A) (hb : 0 ≤ b) (F : Finset A)
    {ε : ℝ} (hε : 0 < ε)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hcomm : ∀ a ∈ F, ‖a * b - b * a‖ ≤ κ)
    (hbudget : Real.pi * κ ≤ ε / 2)
    (M : ℝ) (hM : 0 < M) (hMbound : ∀ a ∈ F, ‖a‖ ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        ‖pi (selfAdjoint.expUnitary ((Real.pi : ℝ) •
          (⟨b, IsSelfAdjoint.of_nonneg hb⟩ : selfAdjoint A)) : A) ξ - η‖ < δ →
        ∃ w : unitary A, ∃ p : Path 1 w,
          pi (w : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  let εcorr : ℝ := ε / (2 * M)
  have hεcorr : 0 < εcorr := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨δ, hδ, hsmall⟩ :=
    StarAlgHom.exists_small_unitary_path_apply_eq pi hpi hεcorr
  refine ⟨δ, hδ, ?_⟩
  intro ξ η hξ hη hclose
  let bs : selfAdjoint A := ⟨b, IsSelfAdjoint.of_nonneg hb⟩
  let u : unitary A := selfAdjoint.expUnitary ((Real.pi : ℝ) • bs)
  let pU : Path 1 u := expUnitaryPiPath bs
  have hzunit : ‖pi (u : A) ξ‖ = 1 := by
    rw [representation_unitary_norm_apply pi u ξ, hξ]
  have hclose' : ‖pi (u : A) ξ - η‖ < δ := hclose
  obtain ⟨v, pV, hvξ, hpv⟩ :=
    hsmall (pi (u : A) ξ) η hzunit hη hclose'
  let p : Path 1 (v * u) := unitaryPathProduct pU pV
  refine ⟨v * u, p, ?_, ?_⟩
  · change pi ((v : A) * (u : A)) ξ = η
    rw [map_mul]
    change pi (v : A) (pi (u : A) ξ) = η
    exact hvξ
  · intro t a ha
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have hh : (0 : H →L[ℂ] H) = 1 := by
        simpa using congrArg pi h
      exact zero_ne_one hh
    letI : Nontrivial A := ⟨0, 1, h01⟩
    have hUa (s : Set.Icc (0 : ℝ) 1) :
        ‖(pU s : A) * a * star (pU s : A) - a‖ ≤ Real.pi * κ ∧
        ‖star (pU s : A) * a * (pU s : A) - a‖ ≤ Real.pi * κ := by
      obtain ⟨hf, hi⟩ := expUnitaryPiPath_protection bs a s
      have hc : ‖(bs : A) * a - a * (bs : A)‖ ≤ κ := by
        simpa [bs, norm_sub_rev] using hcomm a ha
      exact ⟨hf.trans (mul_le_mul_of_nonneg_left hc Real.pi_pos.le),
        hi.trans (mul_le_mul_of_nonneg_left hc Real.pi_pos.le)⟩
    have hVa (s : Set.Icc (0 : ℝ) 1) :
        ‖(pV s : A) * a * star (pV s : A) - a‖ ≤ εcorr * ‖a‖ ∧
        ‖star (pV s : A) * a * (pV s : A) - a‖ ≤ εcorr * ‖a‖ := by
      obtain ⟨hi, hf⟩ := hpv s a
      exact ⟨hf, hi⟩
    have hprod := unitaryPathProduct_both_bounds pU pV a
      (mul_nonneg Real.pi_pos.le hκ)
      (mul_nonneg hεcorr.le (norm_nonneg a)) hUa hVa t
    have hcor : εcorr * ‖a‖ ≤ ε / 2 := by
      calc
        εcorr * ‖a‖ ≤ εcorr * M :=
          mul_le_mul_of_nonneg_left (hMbound a ha) hεcorr.le
        _ = ε / 2 := by
          dsimp [εcorr]
          field_simp
    exact ⟨hprod.1.trans (by linarith), hprod.2.trans (by linarith)⟩

theorem exists_corrected_exponential_path_uniform
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (F : Finset A)
    {ε : ℝ} (hε : 0 < ε)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hbudget : Real.pi * κ ≤ ε / 2)
    (M : ℝ) (hM : 0 < M) (hMbound : ∀ a ∈ F, ‖a‖ ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (b : A) (hb : 0 ≤ b),
      (∀ a ∈ F, ‖a * b - b * a‖ ≤ κ) →
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        ‖pi (selfAdjoint.expUnitary ((Real.pi : ℝ) •
          (⟨b, IsSelfAdjoint.of_nonneg hb⟩ : selfAdjoint A)) : A) ξ - η‖ < δ →
        ∃ w : unitary A, ∃ p : Path 1 w,
          pi (w : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  let εcorr : ℝ := ε / (2 * M)
  have hεcorr : 0 < εcorr := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨δ, hδ, hsmall⟩ :=
    StarAlgHom.exists_small_unitary_path_apply_eq pi hpi hεcorr
  refine ⟨δ, hδ, ?_⟩
  intro b hb hcomm ξ η hξ hη hclose
  let bs : selfAdjoint A := ⟨b, IsSelfAdjoint.of_nonneg hb⟩
  let u : unitary A := selfAdjoint.expUnitary ((Real.pi : ℝ) • bs)
  let pU : Path 1 u := expUnitaryPiPath bs
  have hzunit : ‖pi (u : A) ξ‖ = 1 := by
    rw [representation_unitary_norm_apply pi u ξ, hξ]
  have hclose' : ‖pi (u : A) ξ - η‖ < δ := hclose
  obtain ⟨v, pV, hvξ, hpv⟩ :=
    hsmall (pi (u : A) ξ) η hzunit hη hclose'
  let p : Path 1 (v * u) := unitaryPathProduct pU pV
  refine ⟨v * u, p, ?_, ?_⟩
  · change pi ((v : A) * (u : A)) ξ = η
    rw [map_mul]
    change pi (v : A) (pi (u : A) ξ) = η
    exact hvξ
  · intro t a ha
    have h01 : (0 : A) ≠ 1 := by
      intro h
      have hh : (0 : H →L[ℂ] H) = 1 := by
        simpa using congrArg pi h
      exact zero_ne_one hh
    letI : Nontrivial A := ⟨0, 1, h01⟩
    have hUa (s : Set.Icc (0 : ℝ) 1) :
        ‖(pU s : A) * a * star (pU s : A) - a‖ ≤ Real.pi * κ ∧
        ‖star (pU s : A) * a * (pU s : A) - a‖ ≤ Real.pi * κ := by
      obtain ⟨hf, hi⟩ := expUnitaryPiPath_protection bs a s
      have hc : ‖(bs : A) * a - a * (bs : A)‖ ≤ κ := by
        simpa [bs, norm_sub_rev] using hcomm a ha
      exact ⟨hf.trans (mul_le_mul_of_nonneg_left hc Real.pi_pos.le),
        hi.trans (mul_le_mul_of_nonneg_left hc Real.pi_pos.le)⟩
    have hVa (s : Set.Icc (0 : ℝ) 1) :
        ‖(pV s : A) * a * star (pV s : A) - a‖ ≤ εcorr * ‖a‖ ∧
        ‖star (pV s : A) * a * (pV s : A) - a‖ ≤ εcorr * ‖a‖ := by
      obtain ⟨hi, hf⟩ := hpv s a
      exact ⟨hf, hi⟩
    have hprod := unitaryPathProduct_both_bounds pU pV a
      (mul_nonneg Real.pi_pos.le hκ)
      (mul_nonneg hεcorr.le (norm_nonneg a)) hUa hVa t
    have hcor : εcorr * ‖a‖ ≤ ε / 2 := by
      calc
        εcorr * ‖a‖ ≤ εcorr * M :=
          mul_le_mul_of_nonneg_left (hMbound a ha) hεcorr.le
        _ = ε / 2 := by
          dsimp [εcorr]
          field_simp
    exact ⟨hprod.1.trans (by linarith), hprod.2.trans (by linarith)⟩
end MathlibAnnex.Analysis.CStarAlgebra
