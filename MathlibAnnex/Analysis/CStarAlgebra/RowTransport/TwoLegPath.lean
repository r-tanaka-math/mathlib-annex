import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.OrthogonalPath

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem StarAlgHom.exists_two_leg_orthogonal_protected_path
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε)
    (M : ℝ) (hM : 0 < M) (hMbound : ∀ a ∈ F, ‖a‖ ≤ M)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκbudget : Real.pi * κ ≤ ε / 4)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤ κ * ‖h‖) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ ξ ζ η : H, ‖ξ‖ = 1 → ‖ζ‖ = 1 → ‖η‖ = 1 →
        (∀ i j,
          inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ζ) = 0) →
        (∀ i j,
          inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) η) = 0) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
            inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) ζ)‖ < δ) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) ζ) -
            inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ) →
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ < ρ →
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ζ‖ < ρ →
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ < ρ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  have hεhalf : 0 < ε / 2 := half_pos hε
  have hκhalf : Real.pi * κ ≤ (ε / 2) / 2 := by
    convert hκbudget using 1 <;> ring
  obtain ⟨δ, ρ, hδ, hρ, hlocal⟩ :=
    StarAlgHom.exists_orthogonal_protected_local_path
      pi hpi F hεhalf M hM hMbound x hq hκ hκhalf hprotect
  refine ⟨δ, ρ, hδ, hρ, ?_⟩
  intro ξ ζ η hξ hζ hη horth1 horth2 hgram1 hgram2 hsξ hsζ hsη
  obtain ⟨u₁, p₁, hu₁, hp₁⟩ :=
    hlocal ξ ζ hξ hζ horth1 hgram1 hsξ hsζ
  obtain ⟨u₂, p₂, hu₂, hp₂⟩ :=
    hlocal ζ η hζ hη horth2 hgram2 hsζ hsη
  let p : Path 1 (u₂ * u₁) := unitaryPathProduct p₁ p₂
  refine ⟨u₂ * u₁, p, ?_, ?_⟩
  · change pi ((u₂ : A) * (u₁ : A)) ξ = η
    rw [map_mul]
    change pi (u₂ : A) (pi (u₁ : A) ξ) = η
    rw [hu₁]
    exact hu₂
  · intro t a ha
    have hprod := unitaryPathProduct_both_bounds p₁ p₂ a
      hεhalf.le hεhalf.le
      (fun s => hp₁ s a ha) (fun s => hp₂ s a ha) t
    simpa only [add_halves] using hprod

end MathlibAnnex.Analysis.CStarAlgebra
