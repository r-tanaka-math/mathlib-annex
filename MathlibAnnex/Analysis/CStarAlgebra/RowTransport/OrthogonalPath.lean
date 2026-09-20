import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.CorrectedPath

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra


private theorem local_budget (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    let σ : ℝ := δ / ((4 : ℝ) * Real.pi * ((n : ℝ) + 1))
    0 < σ ∧
      Real.pi / 2 * ((n : ℝ) * σ + ((n : ℝ) * σ + σ + σ)) < δ := by
  dsimp
  have hden : 0 < (4 : ℝ) * Real.pi * ((n : ℝ) + 1) := by positivity
  constructor
  · exact div_pos hδ hden
  · have hcancel : ((4 : ℝ) * Real.pi * ((n : ℝ) + 1)) *
        (δ / ((4 : ℝ) * Real.pi * ((n : ℝ) + 1))) = δ := by
      field_simp
    nlinarith [hcancel]

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem StarAlgHom.exists_orthogonal_protected_local_path
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε)
    (M : ℝ) (hM : 0 < M) (hMbound : ∀ a ∈ F, ‖a‖ ≤ M)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκbudget : Real.pi * κ ≤ ε / 2)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤ κ * ‖h‖) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        (∀ i j,
          inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) η) = 0) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
            inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ) →
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ < ρ →
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ < ρ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  obtain ⟨δ₀, hδ₀, hcorrect⟩ :=
    exists_corrected_exponential_path_uniform pi hpi F hε hκ hκbudget M hM hMbound
  let σ : ℝ := δ₀ / ((4 : ℝ) * Real.pi * ((n : ℝ) + 1))
  obtain ⟨hσ, hσbudget⟩ := local_budget n δ₀ hδ₀
  obtain ⟨δ, hδ, hrow⟩ :=
    StarAlgHom.exists_protected_row_average_of_orthogonal_gram
      pi hpi x hq F hκ hprotect hσ
  refine ⟨δ, σ, hδ, hσ, ?_⟩
  intro ξ η hξ hη horth hgram hsupportξ hsupportη
  obtain ⟨h, b, hh, hhnorm, hb, hbpos, hbnorm, hdiff, hsum, hcomm⟩ :=
    hrow ξ η hξ hη horth hgram
  have hE := representation_expUnitary_pi_endpoint_le pi b hbpos ξ η
  have hclose :
      ‖pi (selfAdjoint.expUnitary ((Real.pi : ℝ) •
        (⟨b, IsSelfAdjoint.of_nonneg hbpos⟩ : selfAdjoint A)) : A) ξ - η‖ < δ₀ := by
    have hcombine : ‖pi b (ξ + η)‖ + ‖pi b (ξ - η) - (ξ - η)‖ <
        (n : ℝ) * σ + ((n : ℝ) * σ + σ + σ) := by
      linarith
    have hπhalf : 0 < Real.pi / 2 := by positivity
    have hmul := mul_lt_mul_of_pos_left hcombine hπhalf
    exact hE.trans_lt (hmul.trans hσbudget)
  exact hcorrect b hbpos hcomm ξ η hξ hη hclose

end MathlibAnnex.Analysis.CStarAlgebra
