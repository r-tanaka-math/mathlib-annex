import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Involution

/-! Row-average vector identities and estimates retaining both support
residuals.  No post-normalization sum-of-entry-norms budget is used. -/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem StarAlgHom.map_rowMap_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} (x : Fin n → A)
    (h : A) (ζ : H) :
    pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) ζ =
      ∑ i, pi (x i) (pi h (pi (star (x i)) ζ)) := by
  simp [MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap_apply,
    map_sum, map_mul, mul_apply_eq_comp]

theorem StarAlgHom.map_rowSquare_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} (x : Fin n → A)
    (ζ : H) :
    pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ζ =
      ∑ i, pi (x i) (pi (star (x i)) ζ) := by
  simp [MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare,
    map_sum, map_mul, mul_apply_eq_comp]

/-- Row averaging transports an approximate eigenvector estimate through
the entire row, with the row length (rather than an invalid entry-norm sum)
as the explicit loss. -/
theorem StarAlgHom.norm_rowMap_sub_rowSquare_apply_le
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} (x : Fin n → A)
    (h : A) (ζ : H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (heigen : ∀ i, ‖pi h (pi (star (x i)) ζ) - pi (star (x i)) ζ‖ ≤ τ) :
    ‖pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) ζ -
        pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ζ‖ ≤
      (n : ℝ) * τ := by
  let e : Fin n → H := fun i =>
    pi h (pi (star (x i)) ζ) - pi (star (x i)) ζ
  have heq :
      pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) ζ -
          pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ζ =
        ∑ i, pi (x i) (e i) := by
    rw [map_rowMap_apply pi x h ζ, map_rowSquare_apply pi x ζ,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_sub (pi (x i)) _ _).symm
  rw [heq]
  calc
    ‖∑ i, pi (x i) (e i)‖ ≤ ∑ i, ‖pi (x i) (e i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, τ := by
      apply Finset.sum_le_sum
      intro i _
      have hx : ‖x i‖ ≤ 1 :=
        MathlibAnnex.CStarAlgebra.TensorAveraging.norm_rowEntry_le_of_rowSquare_norm_le
          A x hq i
      have hmap : ‖pi (x i)‖ ≤ 1 :=
        (NonUnitalStarAlgHom.norm_apply_le pi (x i)).trans hx
      calc
        ‖pi (x i) (e i)‖ ≤ ‖pi (x i)‖ * ‖e i‖ := (pi (x i)).le_opNorm (e i)
        _ ≤ 1 * τ := by
          exact mul_le_mul hmap (heigen i) (norm_nonneg _) (by norm_num)
        _ = τ := one_mul _
    _ = (n : ℝ) * τ := by simp

theorem StarAlgHom.norm_rowMap_apply_le
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} (x : Fin n → A)
    (h : A) (ζ : H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hkill : ∀ i, ‖pi h (pi (star (x i)) ζ)‖ ≤ τ) :
    ‖pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) ζ‖ ≤
      (n : ℝ) * τ := by
  rw [map_rowMap_apply pi x h ζ]
  calc
    ‖∑ i, pi (x i) (pi h (pi (star (x i)) ζ))‖ ≤
        ∑ i, ‖pi (x i) (pi h (pi (star (x i)) ζ))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, τ := by
      apply Finset.sum_le_sum
      intro i _
      have hx : ‖x i‖ ≤ 1 :=
        MathlibAnnex.CStarAlgebra.TensorAveraging.norm_rowEntry_le_of_rowSquare_norm_le
          A x hq i
      have hmap : ‖pi (x i)‖ ≤ 1 :=
        (NonUnitalStarAlgHom.norm_apply_le pi (x i)).trans hx
      calc
        ‖pi (x i) (pi h (pi (star (x i)) ζ))‖ ≤
            ‖pi (x i)‖ * ‖pi h (pi (star (x i)) ζ)‖ :=
              (pi (x i)).le_opNorm _
        _ ≤ 1 * τ :=
          mul_le_mul hmap (hkill i) (norm_nonneg _) (by norm_num)
        _ = τ := one_mul _
    _ = (n : ℝ) * τ := by simp

/-- Both support residuals remain in the difference-vector estimate. -/
theorem StarAlgHom.norm_rowMap_sub_on_diff_le
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ} (x : Fin n → A)
    (h : A) (ξ η : H) {τ : ℝ} (hτ : 0 ≤ τ)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (heigen : ∀ i,
      ‖pi h (pi (star (x i)) ξ - pi (star (x i)) η) -
        (pi (star (x i)) ξ - pi (star (x i)) η)‖ ≤ τ) :
    ‖pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) (ξ - η) -
        (ξ - η)‖ ≤
      (n : ℝ) * τ +
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) ξ‖ +
        ‖(1 - pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)) η‖ := by
  let q := MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x
  have heigen' (i : Fin n) :
      ‖pi h (pi (star (x i)) (ξ - η)) - pi (star (x i)) (ξ - η)‖ ≤ τ := by
    simpa only [map_sub] using heigen i
  have hmain := norm_rowMap_sub_rowSquare_apply_le pi x h (ξ - η) hτ hq heigen'
  have hresid : pi q (ξ - η) - (ξ - η) =
      -((1 - pi q) ξ - (1 - pi q) η) := by
    simp [map_sub]
    module
  have hresidnorm : ‖pi q (ξ - η) - (ξ - η)‖ ≤
      ‖(1 - pi q) ξ‖ + ‖(1 - pi q) η‖ := by
    rw [hresid, norm_neg]
    exact norm_sub_le _ _
  calc
    ‖pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) (ξ - η) -
        (ξ - η)‖ ≤
        ‖pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h) (ξ - η) -
          pi q (ξ - η)‖ + ‖pi q (ξ - η) - (ξ - η)‖ := by
            convert norm_add_le
              (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h)
                (ξ - η) - pi q (ξ - η))
              (pi q (ξ - η) - (ξ - η)) using 1 <;> abel
    _ ≤ _ := by
      simpa only [q, add_assoc] using add_le_add hmain hresidnorm

end MathlibAnnex.Analysis.CStarAlgebra
