import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow

/-!
Positive finite-row averaging under the post-normalization budget.  The
assumption is on the row square, not on the sum of the entry norms.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

universe u

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp]
theorem rowMap_one {n : ℕ} (x : Fin n → A) : rowMap A x 1 = rowSquare A x := by
  simp [rowMap_apply, rowSquare]

/-- A positive contraction is averaged below the row square. -/
theorem rowMap_le_rowSquare {n : ℕ} (x : Fin n → A)
    {h : A} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    0 ≤ rowMap A x h ∧ rowMap A x h ≤ rowSquare A x := by
  constructor
  · exact rowMap_nonneg A x hh
  · have hpos : 0 ≤ rowMap A x (1 - h) :=
      rowMap_nonneg A x (sub_nonneg.mpr hh1)
    rw [map_sub, rowMap_one] at hpos
    exact sub_nonneg.mp hpos

/-- The normalized row gives a contractive positive average, even when
the sum of squared entry norms is larger than one. -/
theorem norm_rowMap_le_of_rowSquare_norm_le {n : ℕ} (x : Fin n → A)
    {h : A} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hq : ‖rowSquare A x‖ ≤ 1) : ‖rowMap A x h‖ ≤ 1 := by
  obtain ⟨hpos, hle⟩ := rowMap_le_rowSquare A x hh hh1
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hle).trans hq

/-- Each entry of a normalized row is contractive; this does not assert
that the sum of their squared norms is contractive. -/
theorem norm_rowEntry_le_of_rowSquare_norm_le {n : ℕ} (x : Fin n → A)
    (hq : ‖rowSquare A x‖ ≤ 1) (i : Fin n) : ‖x i‖ ≤ 1 := by
  have hle : x i * star (x i) ≤ rowSquare A x := by
    unfold rowSquare
    exact Finset.single_le_sum
      (fun j _ => mul_star_self_nonneg (x j)) (Finset.mem_univ i)
  have hnorm : ‖x i * star (x i)‖ ≤ 1 :=
    (CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (mul_star_self_nonneg (x i)) hle).trans hq
  rw [CStarRing.norm_self_mul_star] at hnorm
  nlinarith [norm_nonneg (x i)]

end MathlibAnnex.CStarAlgebra.TensorAveraging
