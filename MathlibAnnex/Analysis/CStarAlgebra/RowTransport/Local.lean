import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Estimate
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SmallPath

/-!
The row-dependent orthogonal-family stage of local transport.  The row is
fixed before the comparison vector and before the Gram tolerance is chosen.
Both support residuals remain visible; no assertion that the second vector
is exactly fixed by the row square is made.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- A normalized finite row and close orthogonal transformed Gram families
yield one positive-contraction witness and its row average. The identity of
the same average is retained for downstream protection estimates. -/
theorem StarAlgHom.exists_row_average_witness_of_orthogonal_gram
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        (∀ i j,
          inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) η) = 0) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
            inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ) →
        ∃ h : A, 0 ≤ h ∧ ‖h‖ ≤ 1 ∧
          ∃ b : A,
          b = MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h ∧
          0 ≤ b ∧ ‖b‖ ≤ 1 ∧
          ‖pi b (ξ - η) - (ξ - η)‖ ≤
            (n : ℝ) * τ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ ∧
          ‖pi b (ξ + η)‖ ≤ (n : ℝ) * τ := by
  obtain ⟨δ, hδ, hGram⟩ :=
    StarAlgHom.exists_positive_contraction_of_orthogonal_gram
      pi hpi n hτ
  refine ⟨δ, hδ, ?_⟩
  intro ξ η hξ hη horth hclose
  let v : Fin n → H := fun i => pi (star (x i)) ξ
  let w : Fin n → H := fun i => pi (star (x i)) η
  have hv : (∑ i, ‖v i‖ ^ 2) ≤ 1 :=
    sum_norm_sq_map_star_le_one pi ξ x hξ hq
  have hw : (∑ i, ‖w i‖ ^ 2) ≤ 1 :=
    sum_norm_sq_map_star_le_one pi η x hη hq
  obtain ⟨h, hh, hhnorm, hdiff, hsum⟩ :=
    hGram v w hv hw horth hclose
  have hh1 : h ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg h hh).mp hhnorm
  let b : A := MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h
  have hbpos : 0 ≤ b :=
    MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap_nonneg A x hh
  have hbnorm : ‖b‖ ≤ 1 :=
    MathlibAnnex.CStarAlgebra.TensorAveraging.norm_rowMap_le_of_rowSquare_norm_le
      A x hh hh1 hq
  refine ⟨h, hh, hhnorm, b, rfl, hbpos, hbnorm, ?_, ?_⟩
  · apply norm_rowMap_sub_on_diff_le pi x h ξ η hτ.le hq
    intro i
    simpa only [map_sub] using (hdiff i).le
  · apply norm_rowMap_apply_le pi x h (ξ + η) hτ.le hq
    intro i
    simpa only [map_add] using (hsum i).le

/-- Compatibility wrapper for clients that only need the average. -/
theorem StarAlgHom.exists_row_average_of_orthogonal_gram
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        (∀ i j,
          inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) η) = 0) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
            inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ) →
        ∃ b : A, 0 ≤ b ∧ ‖b‖ ≤ 1 ∧
          ‖pi b (ξ - η) - (ξ - η)‖ ≤
            (n : ℝ) * τ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ ∧
          ‖pi b (ξ + η)‖ ≤ (n : ℝ) * τ := by
  obtain ⟨δ, hδ, hGram⟩ :=
    StarAlgHom.exists_row_average_witness_of_orthogonal_gram pi hpi x hq hτ
  refine ⟨δ, hδ, ?_⟩
  intro ξ η hξ hη horth hclose
  obtain ⟨h, hh, hhnorm, b, hb, hbpos, hbnorm, hdiff, hsum⟩ :=
    hGram ξ η hξ hη horth hclose
  exact ⟨b, hbpos, hbnorm, hdiff, hsum⟩

/-- The row protection estimate applies to the very average returned with
the two vector residuals. The witness `h` is kept in the conclusion. -/
theorem StarAlgHom.exists_protected_row_average_of_orthogonal_gram
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (F : Finset A) {κ : ℝ} (hκ : 0 ≤ κ)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤ κ * ‖h‖)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
        (∀ i j,
          inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) η) = 0) →
        (∀ i j,
          ‖inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) -
            inner ℂ (pi (star (x i)) η) (pi (star (x j)) η)‖ < δ) →
        ∃ h b : A, 0 ≤ h ∧ ‖h‖ ≤ 1 ∧
          b = MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h ∧
          0 ≤ b ∧ ‖b‖ ≤ 1 ∧
          ‖pi b (ξ - η) - (ξ - η)‖ ≤
            (n : ℝ) * τ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ +
              ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ ∧
          ‖pi b (ξ + η)‖ ≤ (n : ℝ) * τ ∧
          ∀ a ∈ F, ‖a * b - b * a‖ ≤ κ := by
  obtain ⟨δ, hδ, hGram⟩ :=
    StarAlgHom.exists_row_average_witness_of_orthogonal_gram pi hpi x hq hτ
  refine ⟨δ, hδ, ?_⟩
  intro ξ η hξ hη horth hclose
  obtain ⟨h, hh, hhnorm, b, hb, hbpos, hbnorm, hdiff, hsum⟩ :=
    hGram ξ η hξ hη horth hclose
  refine ⟨h, b, hh, hhnorm, hb, hbpos, hbnorm, hdiff, hsum, ?_⟩
  intro a ha
  rw [hb]
  calc
    _ ≤ κ * ‖h‖ := hprotect a ha h
    _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hhnorm hκ
    _ = κ := mul_one _

end MathlibAnnex.Analysis.CStarAlgebra
