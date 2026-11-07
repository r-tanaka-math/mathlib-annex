/- R6 finite-code bounds and the derivative-free normalization estimate.
Execution evidence is external and bound to exact source bytes. -/
import BanachGeometry.HilbertSums.Coding.Tent

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums.Coding

theorem codingError_le_add {k : ℕ} (x z : Fin k → ℝ) (a : GridPoint k)
    {d : ℝ} (hd : 0 ≤ d) (hxz : ∀ j, |x j - z j| ≤ d) :
    codingError k x a ≤ codingError k z a + k * d := by
  apply codingError_le (add_nonneg (codingError_nonneg k z a) (mul_nonneg (Nat.cast_nonneg k) hd))
  intro j
  calc
    |(k : ℝ) * x j - gridValue k (a j)| =
        |((k : ℝ) * z j - gridValue k (a j)) + k * (x j - z j)| := by congr 1; ring
    _ ≤ |(k : ℝ) * z j - gridValue k (a j)| + |(k : ℝ) * (x j - z j)| := abs_add_le _ _
    _ = |(k : ℝ) * z j - gridValue k (a j)| + k * |x j - z j| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    _ ≤ codingError k z a + k * d :=
      add_le_add (coordinate_le_codingError k z a j)
        (mul_le_mul_of_nonneg_left (hxz j) (Nat.cast_nonneg k))

theorem abs_codingError_sub_le {k : ℕ} (x z : Fin k → ℝ) (a : GridPoint k)
    {d : ℝ} (hd : 0 ≤ d) (hxz : ∀ j, |x j - z j| ≤ d) :
    |codingError k x a - codingError k z a| ≤ k * d := by
  have h1 := codingError_le_add x z a hd hxz
  have h2 := codingError_le_add z x a hd (fun j => by simpa [abs_sub_comm] using hxz j)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_tent_sub_le {k : ℕ} (x z : Fin k → ℝ) (a : GridPoint k)
    {d : ℝ} (hd : 0 ≤ d) (hxz : ∀ j, |x j - z j| ≤ d) :
    |tent k x a - tent k z a| ≤ k * d := by
  have hmax := abs_max_sub_max_le_abs
    (1 - codingError k x a) (1 - codingError k z a) 0
  have hid : (1 - codingError k x a) - (1 - codingError k z a) =
      -(codingError k x a - codingError k z a) := by ring
  unfold tent
  rw [max_comm (0 : ℝ) (1 - codingError k x a), max_comm (0 : ℝ) (1 - codingError k z a)]
  exact hmax.trans (by simpa only [hid, abs_neg] using abs_codingError_sub_le x z a hd hxz)

/-- R6's k sqrt(|A_k|) bound in the actual Euclidean norm of the full code. -/
theorem norm_tentVector_sub_le {k : ℕ} (x z : Fin k → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (hxz : ∀ j, |x j - z j| ≤ d) :
    ‖tentVector k x - tentVector k z‖ ≤ k * Real.sqrt ((2 * k + 1 : ℕ) ^ k) * d := by
  have hs : ‖tentVector k x - tentVector k z‖ ^ 2 ≤
      (Fintype.card (GridPoint k) : ℝ) * ((k : ℝ) * d) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ a : GridPoint k, ((tentVector k x - tentVector k z) a) ^ 2 ≤
          ∑ _a : GridPoint k, ((k : ℝ) * d) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have h := abs_tent_sub_le x z a hd hxz
        simpa only [PiLp.sub_apply, tentVector_apply, sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
      _ = _ := by simp
  rw [card_gridPoint] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  calc
    ‖tentVector k x - tentVector k z‖ ^ 2 ≤
        (((2 * k + 1 : ℕ) ^ k : ℕ) : ℝ) * ((k : ℝ) * d) ^ 2 := hs
    _ = ((k : ℝ) * Real.sqrt ((2 * k + 1 : ℕ) ^ k) * d) ^ 2 := by
      rw [Nat.cast_pow]
      simp only [mul_pow, Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg (2 * k + 1) : (0 : ℝ) ≤ (2 * k + 1 : ℕ)) k)]
      ring

section Normalization
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Clear the normalization denominator as a vector identity before taking norms. -/
theorem norm_smul_normalize_sub_normalize (x y : V) :
    ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
  rw [smul_sub, NormedSpace.norm_smul_normalize, sub_smul,
    NormedSpace.norm_smul_normalize]
  module

theorem norm_mul_norm_normalize_sub_le (x y : V) (hy : y ≠ 0) :
    ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ := by
  calc
    ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
        ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    _ = ‖(x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y‖ :=
      congrArg norm (norm_smul_normalize_sub_normalize x y)
    _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
    _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by rw [norm_smul, NormedSpace.norm_normalize hy]; simp
    _ ≤ ‖x - y‖ + ‖x - y‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = 2 * ‖x - y‖ := by ring

theorem norm_normalize_sub_le_of_le_norm {a : ℝ} (ha : 0 < a) (x y : V)
    (hx : a ≤ ‖x‖) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / a) * ‖x - y‖ := by
  have h := (mul_le_mul_of_nonneg_right hx (norm_nonneg
    (NormedSpace.normalize x - NormedSpace.normalize y))).trans
      (norm_mul_norm_normalize_sub_le x y hy)
  rw [div_mul_eq_mul_div, le_div_iff₀ ha]
  simpa only [mul_comm] using h
end Normalization

/-- The exact 4 k sqrt(|A_k|) constant used by R6's unit directions. -/
theorem norm_unitCode_sub_le {k : ℕ} (x z : Fin k → ℝ)
    (hx : ∀ j, |x j| ≤ 1) (hz : ∀ j, |z j| ≤ 1)
    {d : ℝ} (hd : 0 ≤ d) (hxz : ∀ j, |x j - z j| ≤ d) :
    ‖unitCode k x - unitCode k z‖ ≤
      (4 * k * Real.sqrt ((2 * k + 1 : ℕ) ^ k)) * d := by
  have hn := norm_normalize_sub_le_of_le_norm (by norm_num : (0 : ℝ) < 1 / 2)
    (tentVector k x) (tentVector k z) (one_half_le_norm_tentVector k x hx)
    (tentVector_ne_zero k z hz)
  have ht := norm_tentVector_sub_le x z hd hxz
  change ‖NormedSpace.normalize (tentVector k x) - NormedSpace.normalize (tentVector k z)‖ ≤ _
  norm_num at hn
  calc
    _ ≤ 4 * ‖tentVector k x - tentVector k z‖ := hn
    _ ≤ 4 * (k * Real.sqrt ((2 * k + 1 : ℕ) ^ k) * d) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = _ := by ring

end BanachGeometry.HilbertSums.Coding
