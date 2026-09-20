import MathlibAnnex.Analysis.CStarAlgebra.CAR.Completion
import MathlibAnnex.Analysis.CStarAlgebra.FiniteRow
import MathlibAnnex.Analysis.CStarAlgebra.PositiveMapBound
import MathlibAnnex.Analysis.CStarAlgebra.VectorGram

/-!
# Finite-row averaging in the completed CAR algebra

For a full matrix stage, the single column `e_(i,0)` gives an exactly
normalized row.  Its associated positive map commutes with that whole stage,
and the elementary norm bound is independent of the matrix dimension.  Dense
finite-stage approximation then gives simultaneous approximate centrality on
an arbitrary finite subset of the actual completed CAR algebra.
-/

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MathlibAnnex.CStarAlgebra.CAR

/-- A standard matrix unit in a binary CAR stage. -/
noncomputable def matrixUnit (n : ℕ) (i j : Fin (2 ^ n)) : Stage n :=
  CStarMatrix.ofMatrix (Matrix.single i j 1)

@[simp] theorem matrixUnit_apply (n : ℕ) (i j k l : Fin (2 ^ n)) :
    matrixUnit n i j k l = if i = k ∧ j = l then 1 else 0 := by
  simp [matrixUnit, Matrix.single]

@[simp] theorem star_matrixUnit (n : ℕ) (i j : Fin (2 ^ n)) :
    star (matrixUnit n i j) = matrixUnit n j i := by
  ext k l
  simp [matrixUnit, CStarMatrix.star_apply, Matrix.single, and_comm]

@[simp] theorem matrixUnit_mul_same (n : ℕ) (i j k : Fin (2 ^ n)) :
    matrixUnit n i j * matrixUnit n j k = matrixUnit n i k := by
  change CStarMatrix.ofMatrix (Matrix.single i j 1 * Matrix.single j k 1) = _
  rw [Matrix.single_mul_single_same]
  simp [matrixUnit]

@[simp] theorem matrixUnit_mul_of_ne (n : ℕ) (i j k l : Fin (2 ^ n)) (h : j ≠ k) :
    matrixUnit n i j * matrixUnit n k l = 0 := by
  change CStarMatrix.ofMatrix (Matrix.single i j 1 * Matrix.single k l 1) = _
  rw [Matrix.single_mul_single_of_ne _ _ _ _ h]
  rfl

@[simp] theorem sum_matrixUnit_diag (n : ℕ) :
    ∑ i : Fin (2 ^ n), matrixUnit n i i = 1 := by
  change CStarMatrix.ofMatrix (∑ i : Fin (2 ^ n), Matrix.single i i 1) = _
  rw [Matrix.sum_single_one]
  rfl

/-- A standard matrix unit viewed in the actual completed CAR algebra. -/
noncomputable def limitMatrixUnit (n : ℕ) (i j : Fin (2 ^ n)) : Limit :=
  ofStage n (matrixUnit n i j)

@[simp] theorem star_limitMatrixUnit (n : ℕ) (i j : Fin (2 ^ n)) :
    star (limitMatrixUnit n i j) = limitMatrixUnit n j i := by
  rw [limitMatrixUnit, ← map_star, star_matrixUnit]
  rfl

@[simp] theorem limitMatrixUnit_mul (n : ℕ) (i j k l : Fin (2 ^ n)) :
    limitMatrixUnit n i j * limitMatrixUnit n k l =
      if j = k then limitMatrixUnit n i l else 0 := by
  by_cases h : j = k
  · subst k
    rw [limitMatrixUnit, limitMatrixUnit, ← map_mul, matrixUnit_mul_same]
    simp [limitMatrixUnit]
  · rw [limitMatrixUnit, limitMatrixUnit, ← map_mul, matrixUnit_mul_of_ne _ _ _ _ _ h,
      map_zero]
    simp [h]

@[simp] theorem sum_limitMatrixUnit_diag (n : ℕ) :
    ∑ i : Fin (2 ^ n), limitMatrixUnit n i i = 1 := by
  calc
    ∑ i : Fin (2 ^ n), limitMatrixUnit n i i =
        ofStage n (∑ i : Fin (2 ^ n), matrixUnit n i i) := by
          rw [map_sum]
          rfl
    _ = 1 := by rw [sum_matrixUnit_diag, map_one]

/-- The finite-row average associated to a full matrix stage. -/
noncomputable def rowAverageLinear (n : ℕ) : Limit →ₗ[ℂ] Limit where
  toFun b := ∑ i : Fin (2 ^ n),
    limitMatrixUnit n i 0 * b * limitMatrixUnit n 0 i
  map_add' b c := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c b := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      limitMatrixUnit n i 0 * ((algebraMap ℂ Limit) c * b) *
          limitMatrixUnit n 0 i =
          (limitMatrixUnit n i 0 * (algebraMap ℂ Limit) c) * b *
            limitMatrixUnit n 0 i := by simp only [mul_assoc]
      _ = ((algebraMap ℂ Limit) c * limitMatrixUnit n i 0) * b *
            limitMatrixUnit n 0 i := by
              rw [Algebra.commutes c (limitMatrixUnit n i 0)]
      _ = (algebraMap ℂ Limit) c *
          (limitMatrixUnit n i 0 * b * limitMatrixUnit n 0 i) := by
            simp only [mul_assoc]

@[simp] theorem rowAverageLinear_apply (n : ℕ) (b : Limit) :
    rowAverageLinear n b = ∑ i : Fin (2 ^ n),
      limitMatrixUnit n i 0 * b * limitMatrixUnit n 0 i := rfl

@[simp] theorem rowAverageLinear_one (n : ℕ) : rowAverageLinear n 1 = 1 := by
  simp [rowAverageLinear]

theorem rowAverageLinear_nonneg (n : ℕ) (b : Limit) (hb : 0 ≤ b) :
    0 ≤ rowAverageLinear n b := by
  rw [rowAverageLinear_apply]
  apply Finset.sum_nonneg
  intro i _
  simpa only [star_limitMatrixUnit] using
    (star_right_conjugate_nonneg hb (limitMatrixUnit n i 0))

noncomputable def rowAveragePositive (n : ℕ) : Limit →ₚ[ℂ] Limit :=
  PositiveLinearMap.mk₀ (rowAverageLinear n) (rowAverageLinear_nonneg n)

theorem norm_rowAverageLinear_le (n : ℕ) (b : Limit) :
    ‖rowAverageLinear n b‖ ≤ 4 * ‖b‖ := by
  exact MathlibAnnex.CStarAlgebra.norm_apply_le_four (rowAveragePositive n)
    (rowAverageLinear_one n) b

/-- The finite-row average as a bounded linear operator. -/
noncomputable def rowAverage (n : ℕ) : Limit →L[ℂ] Limit :=
  (rowAverageLinear n).mkContinuous 4 (norm_rowAverageLinear_le n)

@[simp] theorem rowAverage_apply (n : ℕ) (b : Limit) :
    rowAverage n b = rowAverageLinear n b := rfl

/-- Commuting with `a` after applying the finite-row average. -/
noncomputable def commutatorAverageLinear (n : ℕ) (a : Limit) : Limit →ₗ[ℂ] Limit where
  toFun b := a * rowAverageLinear n b - rowAverageLinear n b * a
  map_add' b c := by simp only [map_add, mul_add, add_mul, sub_add_sub_comm]
  map_smul' c b := by
    rw [map_smul]
    simp only [RingHom.id_apply, Algebra.smul_def]
    rw [mul_sub]
    congr 1
    · calc
        a * ((algebraMap ℂ Limit) c * rowAverageLinear n b) =
            (a * (algebraMap ℂ Limit) c) * rowAverageLinear n b := by
              rw [mul_assoc]
        _ = ((algebraMap ℂ Limit) c * a) * rowAverageLinear n b := by
              rw [Algebra.commutes c a]
        _ = (algebraMap ℂ Limit) c * (a * rowAverageLinear n b) := by
              rw [mul_assoc]
    · rw [mul_assoc]

theorem norm_commutatorAverageLinear_le (n : ℕ) (a b : Limit) :
    ‖commutatorAverageLinear n a b‖ ≤ (8 * ‖a‖) * ‖b‖ := by
  change ‖a * rowAverageLinear n b - rowAverageLinear n b * a‖ ≤ _
  calc
    ‖a * rowAverageLinear n b - rowAverageLinear n b * a‖ ≤
        ‖a * rowAverageLinear n b‖ + ‖rowAverageLinear n b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖rowAverageLinear n b‖ + ‖rowAverageLinear n b‖ * ‖a‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖rowAverageLinear n b‖ := by ring
    _ ≤ 2 * ‖a‖ * (4 * ‖b‖) := by
      gcongr
      exact norm_rowAverageLinear_le n b
    _ = (8 * ‖a‖) * ‖b‖ := by ring

/-- The averaged commutator as a bounded linear operator on the CAR algebra. -/
noncomputable def commutatorAverage (n : ℕ) (a : Limit) : Limit →L[ℂ] Limit :=
  (commutatorAverageLinear n a).mkContinuous (8 * ‖a‖)
    (norm_commutatorAverageLinear_le n a)

@[simp] theorem commutatorAverage_apply (n : ℕ) (a b : Limit) :
    commutatorAverage n a b =
      a * rowAverageLinear n b - rowAverageLinear n b * a := rfl

theorem limitMatrixUnit_commute_rowAverage (n : ℕ) (k l : Fin (2 ^ n)) (b : Limit) :
    limitMatrixUnit n k l * rowAverageLinear n b =
      rowAverageLinear n b * limitMatrixUnit n k l := by
  calc
    limitMatrixUnit n k l * rowAverageLinear n b =
        ∑ i : Fin (2 ^ n), limitMatrixUnit n k l *
          (limitMatrixUnit n i 0 * b * limitMatrixUnit n 0 i) := by
            rw [rowAverageLinear_apply, Finset.mul_sum]
    _ = limitMatrixUnit n k 0 * b * limitMatrixUnit n 0 l := by
      rw [Finset.sum_eq_single l]
      · simp [← mul_assoc]
      · intro i _ hil
        have hli : l ≠ i := Ne.symm hil
        simp [← mul_assoc, hli]
      · simp
    _ = ∑ i : Fin (2 ^ n),
        (limitMatrixUnit n i 0 * b * limitMatrixUnit n 0 i) *
          limitMatrixUnit n k l := by
      rw [Finset.sum_eq_single k]
      · simp [mul_assoc]
      · intro i _ hik
        simp [mul_assoc, hik]
      · simp
    _ = rowAverageLinear n b * limitMatrixUnit n k l := by
      rw [rowAverageLinear_apply, Finset.sum_mul]

set_option backward.isDefEq.respectTransparency false in
theorem stage_eq_sum_smul_matrixUnit (n : ℕ) (c : Stage n) :
    c = ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n), c i j • matrixUnit n i j := by
  apply (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  simp only [map_sum, map_smul]
  change CStarMatrix.ofMatrix.symm c =
    ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n),
      c i j • Matrix.single i j 1
  rw [Matrix.matrix_eq_sum_single (CStarMatrix.ofMatrix.symm c)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ext k l
  simp [Matrix.single]

theorem ofStage_eq_sum_smul_limitMatrixUnit (n : ℕ) (c : Stage n) :
    ofStage n c =
      ∑ i : Fin (2 ^ n), ∑ j : Fin (2 ^ n), c i j • limitMatrixUnit n i j := by
  conv_lhs => rw [stage_eq_sum_smul_matrixUnit n c]
  simp only [map_sum, map_smul, limitMatrixUnit]

theorem ofStage_commute_rowAverage (n : ℕ) (c : Stage n) (b : Limit) :
    ofStage n c * rowAverageLinear n b = rowAverageLinear n b * ofStage n c := by
  rw [ofStage_eq_sum_smul_limitMatrixUnit]
  apply (Commute.sum_left Finset.univ _ _ fun i _ =>
    Commute.sum_left Finset.univ _ _ fun j _ => ?_).eq
  exact (show Commute (limitMatrixUnit n i j) (rowAverageLinear n b) from
    limitMatrixUnit_commute_rowAverage n i j b).smul_left (c i j)

theorem exists_stage_approx (a : Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ c : Stage n, ‖a - ofStage n c‖ < epsilon := by
  obtain ⟨y, hy, hya⟩ := dense_stageRange.exists_dist_lt a hepsilon
  rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
  rcases hn with ⟨c, rfl⟩
  exact ⟨n, c, by simpa only [dist_eq_norm, norm_sub_rev] using hya⟩

theorem exists_common_stage_approx (F : Finset Limit) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ n, ∀ a ∈ F, ∃ c : Stage n, ‖a - ofStage n c‖ < epsilon := by
  classical
  induction F using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a F ha ih =>
      obtain ⟨n, c, hc⟩ := exists_stage_approx a hepsilon
      obtain ⟨m, hm⟩ := ih
      refine ⟨max n m, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · refine ⟨embed n (max n m) (le_max_left n m) c, ?_⟩
        simpa only [ofStage_embed] using hc
      · obtain ⟨d, hd⟩ := hm x hx
        refine ⟨embed m (max n m) (le_max_right n m) d, ?_⟩
        simpa only [ofStage_embed] using hd

theorem norm_commutator_rowAverage_le (n : ℕ) (a b : Limit) (c : Stage n) :
    ‖a * rowAverageLinear n b - rowAverageLinear n b * a‖ ≤
      8 * ‖a - ofStage n c‖ * ‖b‖ := by
  let p := rowAverageLinear n b
  let d := a - ofStage n c
  have hcomm : ofStage n c * p = p * ofStage n c :=
    ofStage_commute_rowAverage n c b
  have hid : a * p - p * a = d * p - p * d := by
    dsimp only [d]
    noncomm_ring [hcomm]
  rw [hid]
  calc
    ‖d * p - p * d‖ ≤ ‖d * p‖ + ‖p * d‖ := norm_sub_le _ _
    _ ≤ ‖d‖ * ‖p‖ + ‖p‖ * ‖d‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖d‖ * ‖p‖ := by ring
    _ ≤ 2 * ‖d‖ * (4 * ‖b‖) := by
      gcongr
      exact norm_rowAverageLinear_le n b
    _ = 8 * ‖a - ofStage n c‖ * ‖b‖ := by
      dsimp only [d]
      ring

theorem norm_commutatorAverage_le_of_stage (n : ℕ) (a : Limit) (c : Stage n) :
    ‖commutatorAverage n a‖ ≤ 8 * ‖a - ofStage n c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  simpa only [commutatorAverage_apply, mul_assoc] using
    norm_commutator_rowAverage_le n a b c

@[simp] theorem row_isometry_sum (n : ℕ) :
    ∑ i : Fin (2 ^ n), limitMatrixUnit n i 0 * star (limitMatrixUnit n i 0) = 1 := by
  simpa using sum_limitMatrixUnit_diag n

/-- Exact normalization survives every unital star representation. -/
theorem map_row_isometry_sum
    {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) :
    ∑ i : Fin (2 ^ n),
      rho (limitMatrixUnit n i 0) * star (rho (limitMatrixUnit n i 0)) = 1 := by
  calc
    ∑ i : Fin (2 ^ n),
        rho (limitMatrixUnit n i 0) * star (rho (limitMatrixUnit n i 0)) =
        ∑ i : Fin (2 ^ n), rho
          (limitMatrixUnit n i 0 * star (limitMatrixUnit n i 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [map_mul, map_star]
    _ = rho (∑ i : Fin (2 ^ n),
        limitMatrixUnit n i 0 * star (limitMatrixUnit n i 0)) := by
          rw [map_sum]
    _ = 1 := by rw [row_isometry_sum, map_one]

/-- Consequently the Property 1.3 compression equation is exact for every
operator `E`; no faithfulness or finite-rank assumption is needed here. -/
theorem map_row_isometry_sum_mul
    {B : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (E : B) :
    (∑ i : Fin (2 ^ n),
      rho (limitMatrixUnit n i 0) * star (rho (limitMatrixUnit n i 0))) * E = E := by
  rw [map_row_isometry_sum rho n, one_mul]

/-- In a Hilbert-space representation, the pulled-back row vectors have
exact total squared norm.  This is the normalization used by the subsequent
Gram comparison; no orthogonality of the row vectors is asserted. -/
theorem sum_norm_sq_map_limitMatrixUnit_star
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) (ξ : H) :
    ∑ i : Fin (2 ^ n),
      ‖rho (star (limitMatrixUnit n i 0)) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  exact MathlibAnnex.Analysis.CStarAlgebra.Representation.sum_norm_sq_map_star_eq
    rho ξ (fun i => limitMatrixUnit n i 0) (row_isometry_sum n)

/-- Actual CAR finite-row averaging with a dimension-independent estimate.
The same row works simultaneously for the finite set and every test element `b`. -/
theorem exists_row_approx_central (F : Finset Limit) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ n,
      (∑ i : Fin (2 ^ n),
        limitMatrixUnit n i 0 * star (limitMatrixUnit n i 0) = 1) ∧
      ∀ a ∈ F, ∀ b : Limit,
        ‖a * rowAverageLinear n b - rowAverageLinear n b * a‖ ≤ epsilon * ‖b‖ := by
  obtain ⟨n, hn⟩ := exists_common_stage_approx F (show 0 < epsilon / 8 by positivity)
  refine ⟨n, row_isometry_sum n, ?_⟩
  intro a ha b
  obtain ⟨c, hc⟩ := hn a ha
  calc
    ‖a * rowAverageLinear n b - rowAverageLinear n b * a‖ ≤
        8 * ‖a - ofStage n c‖ * ‖b‖ := norm_commutator_rowAverage_le n a b c
    _ ≤ epsilon * ‖b‖ := by
      gcongr
      exact (lt_div_iff₀' (by norm_num : (0 : ℝ) < 8)).mp hc |>.le

/-- The actual completed CAR algebra supplies the source-independent
finite-row averaging property. -/
theorem hasFiniteRowAveraging_limit :
    MathlibAnnex.CStarAlgebra.HasFiniteRowAveraging Limit := by
  intro F epsilon hepsilon
  obtain ⟨n, hrow, hcomm⟩ := exists_row_approx_central F hepsilon
  refine ⟨2 ^ n, (fun i => limitMatrixUnit n i 0), hrow, ?_⟩
  intro a ha b
  simpa only [MathlibAnnex.CStarAlgebra.finiteRowAverage,
    star_limitMatrixUnit, rowAverageLinear_apply] using hcomm a ha b

/-- Operator-norm form of the CAR finite-row property.  This is the exact
`ad a ∘ Ad x` estimate used in Property 1.3, with an exactly normalized row. -/
theorem exists_row_average_opNorm_lt (F : Finset Limit) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ n,
      (∑ i : Fin (2 ^ n),
        limitMatrixUnit n i 0 * star (limitMatrixUnit n i 0) = 1) ∧
      ∀ a ∈ F, ‖commutatorAverage n a‖ < epsilon := by
  obtain ⟨n, hn⟩ := exists_common_stage_approx F (show 0 < epsilon / 8 by positivity)
  refine ⟨n, row_isometry_sum n, ?_⟩
  intro a ha
  obtain ⟨c, hc⟩ := hn a ha
  calc
    ‖commutatorAverage n a‖ ≤ 8 * ‖a - ofStage n c‖ :=
      norm_commutatorAverage_le_of_stage n a c
    _ < epsilon := (lt_div_iff₀' (by norm_num : (0 : ℝ) < 8)).mp hc

end MathlibAnnex.CStarAlgebra.CAR
