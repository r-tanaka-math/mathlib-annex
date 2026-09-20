import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GramMoment

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem Representation.exists_g_assisted_two_leg_local_path
    (pi : Representation A H)
    (hpi : StarAlgHom.IsIrreducible pi)
    (hno : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcoefficient : ∀ a : A, phi a = inner ℂ ξ (pi a ξ))
    (F : Finset A) {ε : ℝ} (hε : 0 < ε)
    (M : ℝ) (hM : 0 < M) (hMbound : ∀ a ∈ F, ‖a‖ ≤ M)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hqξ : pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ξ = ξ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκbudget : Real.pi * κ ≤ ε / 4)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤ κ * ‖h‖) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ η : H, ‖η‖ = 1 →
        (∀ i j : Fin n,
          ‖phi (x i * star (x j)) -
            inner ℂ η (pi (x i * star (x j)) η)‖ < μ) →
        ‖phi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) -
          inner ℂ η (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) η)‖ < μ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  let q : A := MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x
  obtain ⟨δ, ρ, hδ, hρ, hlocal⟩ :=
    StarAlgHom.exists_two_leg_orthogonal_protected_path
      pi hpi F hε M hM hMbound x hq hκ hκbudget hprotect
  let μ : ℝ := min (δ / 4) (ρ ^ 2 / 4)
  have hμ : 0 < μ := lt_min (div_pos hδ (by norm_num))
    (div_pos (sq_pos_of_pos hρ) (by norm_num))
  have hμδ : 2 * μ < δ := by
    have hle : μ ≤ δ / 4 := min_le_left _ _
    linarith
  have hμρ : 2 * μ < ρ ^ 2 := by
    have hle : μ ≤ ρ ^ 2 / 4 := min_le_right _ _
    nlinarith [sq_pos_of_pos hρ]
  have hpiq : ‖pi q‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le pi q).trans hq
  have hphiQ : phi q = 1 := by
    rw [hcoefficient q, hqξ, inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  refine ⟨μ, hμ, ?_⟩
  intro η hη hηmom hηq
  obtain ⟨ζ, hζ, hζxi, hζη, hζmom, hζq⟩ :=
    pi.exists_same_zeta_row_moments hno phi hphi hpure hker x ξ η hμ
  have horth1 (i j : Fin n) :
      inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ζ) = 0 := by
    rw [← inner_conj_symm]
    simp only [hζxi j i, map_zero]
  have horth2 (i j : Fin n) :
      inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) η) = 0 := hζη i j
  have hgram1 (i j : Fin n) :
      ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
        inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) ζ)‖ < δ := by
    exact (row_gram_base_z_lt pi phi x ξ ζ
      (fun i j => hcoefficient (x i * star (x j))) hζmom i j).trans
      (by linarith [hμδ])
  have hgram2 (i j : Fin n) :
      ‖inner ℂ (pi (star (x i)) ζ) (pi (star (x j)) ζ) -
        inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ :=
    (row_gram_z_eta_lt pi phi x ζ η hζmom hηmom i j).trans hμδ
  have hsξ : ‖(1 - pi q) ξ‖ < ρ := by
    have hz : (1 - pi q) ξ = 0 := by
      change ξ - pi q ξ = 0
      rw [hqξ]
      exact sub_self ξ
    rw [hz, norm_zero]
    exact hρ
  have hsζ : ‖(1 - pi q) ζ‖ < ρ := by
    apply support_residual_lt (pi q) hpiq ζ hζ hρ hμρ
    change ‖phi q - inner ℂ ζ (pi q ζ)‖ < μ at hζq
    rw [hphiQ] at hζq
    exact hζq
  have hsη : ‖(1 - pi q) η‖ < ρ := by
    apply support_residual_lt (pi q) hpiq η hη hρ hμρ
    change ‖phi q - inner ℂ η (pi q η)‖ < μ at hηq
    rw [hphiQ] at hηq
    exact hηq
  exact hlocal ξ ζ η hξ hζ hη horth1 horth2 hgram1 hgram2 hsξ hsζ hsη

theorem Representation.exists_g_assisted_two_leg_local_path_finite
    (pi : Representation A H)
    (hpi : StarAlgHom.IsIrreducible pi)
    (hno : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcoefficient : ∀ a : A, phi a = inner ℂ ξ (pi a ξ))
    (F : Finset A) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hqξ : pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ξ = ξ)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤
        (ε / (8 * Real.pi)) * ‖h‖) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ η : H, ‖η‖ = 1 →
        (∀ i j : Fin n,
          ‖phi (x i * star (x j)) -
            inner ℂ η (pi (x i * star (x j)) η)‖ < μ) →
        ‖phi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) -
          inner ℂ η (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) η)‖ < μ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  let M : ℝ := 1 + ∑ a ∈ F, ‖a‖
  have hM : 0 < M := by
    dsimp [M]
    have hsum : 0 ≤ ∑ a ∈ F, ‖a‖ := Finset.sum_nonneg fun a _ => norm_nonneg a
    linarith
  have hMbound : ∀ a ∈ F, ‖a‖ ≤ M := by
    intro a ha
    have hle : ‖a‖ ≤ ∑ b ∈ F, ‖b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg b) ha
    dsimp [M]
    linarith
  let κ : ℝ := ε / (8 * Real.pi)
  have hκ : 0 ≤ κ := (div_pos hε (mul_pos (by norm_num) Real.pi_pos)).le
  have hκbudget : Real.pi * κ ≤ ε / 4 := by
    have heq : Real.pi * κ = ε / 8 := by
      dsimp [κ]
      field_simp
    rw [heq]
    linarith
  exact pi.exists_g_assisted_two_leg_local_path hpi hno phi hphi hpure hker
    ξ hξ hcoefficient F hε M hM hMbound x hq hqξ hκ hκbudget hprotect
end MathlibAnnex.Analysis.CStarAlgebra
