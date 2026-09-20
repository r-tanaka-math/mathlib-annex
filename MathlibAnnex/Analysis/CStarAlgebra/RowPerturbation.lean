import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow

/-!
# Finite-row perturbation by a left multiplier

The row norm budget need not survive a left correction.  Its square and
positive map transform by the same two-sided conjugation.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

universe u

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem rowSquare_left_mul {n : ℕ} (x : Fin n → A) (b : A) :
    rowSquare A (fun i => b * x i) = b * rowSquare A x * star b := by
  simp only [rowSquare, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  noncomm_ring

theorem rowMap_left_mul {n : ℕ} (x : Fin n → A) (b z : A) :
    rowMap A (fun i => b * x i) z = b * rowMap A x z * star b := by
  simp only [rowMap_apply, star_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  noncomm_ring

theorem norm_commutator_le_of_sub (a s t : A) :
    ‖a * s - s * a‖ ≤ ‖a * t - t * a‖ + 2 * ‖a‖ * ‖s - t‖ := by
  have h : a * s - s * a =
      (a * t - t * a) + (a * (s - t) - (s - t) * a) := by
    noncomm_ring
  rw [h]
  calc
    ‖(a * t - t * a) + (a * (s - t) - (s - t) * a)‖ ≤
        ‖a * t - t * a‖ + ‖a * (s - t) - (s - t) * a‖ := norm_add_le _ _
    _ ≤ ‖a * t - t * a‖ +
        (‖a‖ * ‖s - t‖ + ‖s - t‖ * ‖a‖) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = ‖a * t - t * a‖ + 2 * ‖a‖ * ‖s - t‖ := by ring

section Unital

variable (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A near-identity multiplier changes any sandwich by a controlled amount. -/
theorem norm_conjugate_sub_le (b t : B) :
    ‖b * t * star b - t‖ ≤
      (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖t‖ := by
  have hstar : ‖star b - 1‖ = ‖b - 1‖ := by
    simpa using (norm_star (b - 1))
  have hdecomp : b * t * star b - t =
      (b - 1) * t * star b + t * (star b - 1) := by
    noncomm_ring
  rw [hdecomp]
  calc
    ‖(b - 1) * t * star b + t * (star b - 1)‖ ≤
        ‖(b - 1) * t * star b‖ + ‖t * (star b - 1)‖ := norm_add_le _ _
    _ ≤ (‖b - 1‖ * ‖t‖) * ‖star b‖ + ‖t‖ * ‖star b - 1‖ := by
      gcongr
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · exact norm_mul_le _ _
    _ = (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖t‖ := by
      rw [norm_star, hstar]
      ring

theorem norm_rowMap_left_mul_sub_le {n : ℕ} (x : Fin n → B) (b z : B) :
    ‖rowMap B (fun i => b * x i) z - rowMap B x z‖ ≤
      (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap B x z‖ := by
  rw [rowMap_left_mul]
  exact norm_conjugate_sub_le B b (rowMap B x z)

theorem norm_commutator_rowMap_left_mul_le {n : ℕ}
    (x : Fin n → B) (b a z : B) :
    ‖a * rowMap B (fun i => b * x i) z -
        rowMap B (fun i => b * x i) z * a‖ ≤
      ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ *
          ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap B x z‖) := by
  calc
    _ ≤ ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ * ‖rowMap B (fun i => b * x i) z - rowMap B x z‖ :=
      norm_commutator_le_of_sub B a _ _
    _ ≤ ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ *
          ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap B x z‖) := by
      gcongr
      exact norm_rowMap_left_mul_sub_le B x b z

theorem norm_rowMap_left_mul_sub_le_budget {n : ℕ}
    (x : Fin n → B) (b z : B)
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖rowMap B (fun i => b * x i) z - rowMap B x z‖ ≤
      (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖ := by
  have hrow : ‖rowMap B x z‖ ≤ ‖z‖ := by
    calc
      ‖rowMap B x z‖ ≤ ‖rowMap B x‖ * ‖z‖ := (rowMap B x).le_opNorm z
      _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_rowMap_le_one B x hx) (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  calc
    _ ≤ (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖rowMap B x z‖ :=
      norm_rowMap_left_mul_sub_le B x b z
    _ ≤ (‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖ := by
      gcongr

theorem norm_commutator_rowMap_left_mul_le_budget {n : ℕ}
    (x : Fin n → B) (b a z : B)
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ‖a * rowMap B (fun i => b * x i) z -
        rowMap B (fun i => b * x i) z * a‖ ≤
      ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ *
          ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖) := by
  calc
    _ ≤ ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ * ‖rowMap B (fun i => b * x i) z - rowMap B x z‖ :=
      norm_commutator_le_of_sub B a _ _
    _ ≤ ‖a * rowMap B x z - rowMap B x z * a‖ +
        2 * ‖a‖ *
          ((‖b - 1‖ * ‖b‖ + ‖b - 1‖) * ‖z‖) := by
      gcongr
      exact norm_rowMap_left_mul_sub_le_budget B x b z hx

end Unital

end MathlibAnnex.CStarAlgebra.TensorAveraging
