/-
Fixed Pair R6, Lemma 9.3: exact inverse difference and comparison energy.
New source from R6; no upstream implementation is imported here.
These statements use actual coordinates, not an axiom for the Hilbert map.
-/
import BanachGeometry.HilbertSums.ScalarSplitting
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

open scoped ENNReal

noncomputable section
open scoped InnerProductSpace BigOperators

namespace BanachGeometry.HilbertSums

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

/-- δ in R6 (9.3), on zero-based coordinates. -/
def directionDelta (ξ ζ y : ∀ n, G n) (n : ℕ) : ℝ :=
  ⟪ξ n - ζ n, y n⟫_ℝ

def inverseDifferenceA (ξ ζ y : ∀ n, G n) (n : ℕ) : G n :=
  (coefficient ξ y (2 * n + 1) - coefficient ξ y n) • (ξ n - ζ n)

def inverseDifferenceB (ξ ζ y : ∀ n, G n) (n : ℕ) : G n :=
  (directionDelta ξ ζ y (2 * n + 1) - directionDelta ξ ζ y n) • ζ n

/-- A single summand of the full comparison energy, with no finite truncation. -/
def comparisonWeight (ξ ζ y : ∀ n, G n) (n : ℕ) : ℝ :=
  (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * ‖ξ n - ζ n‖ ^ 2

def comparisonEnergy (ξ ζ y : ∀ n, G n) : ℝ :=
  Real.sqrt (∑' n, comparisonWeight ξ ζ y n)

theorem inverseU_difference (ξ ζ y : ∀ n, G n) (n : ℕ) :
    frozenInverseU ξ y n - frozenInverseU ζ y n =
      inverseDifferenceA ξ ζ y n + inverseDifferenceB ξ ζ y n := by
  simp only [frozenInverseU, inverseDifferenceA, inverseDifferenceB,
    directionDelta, inner_sub_left]
  unfold coefficient
  module

theorem inverseV_difference (ξ ζ y : ∀ n, G n) (n : ℕ) :
    frozenInverseV ξ y n - frozenInverseV ζ y n =
      directionDelta ξ ζ y (2 * n) := by
  simp only [frozenInverseV, coefficient, directionDelta, inner_sub_left]

theorem comparisonWeight_nonneg (ξ ζ y : ∀ n, G n) (n : ℕ) :
    0 ≤ comparisonWeight ξ ζ y n := by
  unfold comparisonWeight
  positivity

theorem directionDelta_sq_le (ξ ζ y : ∀ n, G n) (n : ℕ) :
    directionDelta ξ ζ y n ^ 2 ≤ ‖y n‖ ^ 2 * ‖ξ n - ζ n‖ ^ 2 := by
  have h := abs_real_inner_le_norm (ξ n - ζ n) (y n)
  have hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 h
  simpa [directionDelta, sq_abs, mul_pow, mul_comm] using hsq

theorem directionDelta_sq_le_weight (ξ ζ y : ∀ n, G n) (n : ℕ) :
    directionDelta ξ ζ y n ^ 2 ≤ comparisonWeight ξ ζ y n := by
  refine (directionDelta_sq_le ξ ζ y n).trans ?_
  unfold comparisonWeight
  exact mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (sq_nonneg ‖y (2 * n + 1)‖)) (sq_nonneg ‖ξ n - ζ n‖)

variable (ξ ζ : ∀ n, G n) (hξ : ∀ n, ‖ξ n‖ = 1) (hζ : ∀ n, ‖ζ n‖ = 1)

include hξ hζ

theorem direction_distance_le_two (n : ℕ) : ‖ξ n - ζ n‖ ≤ 2 := by
  calc
    ‖ξ n - ζ n‖ ≤ ‖ξ n‖ + ‖ζ n‖ := norm_sub_le _ _
    _ = 2 := by rw [hξ n, hζ n]; norm_num

theorem comparisonWeight_le (y : ∀ n, G n) (n : ℕ) :
    comparisonWeight ξ ζ y n ≤ 4 * (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) := by
  have hd := direction_distance_le_two ξ ζ hξ hζ n
  have hdsq : ‖ξ n - ζ n‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (ξ n - ζ n)]
  unfold comparisonWeight
  calc
    (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * ‖ξ n - ζ n‖ ^ 2 ≤
        (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) * 4 :=
      mul_le_mul_of_nonneg_left hdsq (add_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = 4 * (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) := mul_comm _ _

theorem inverseDifferenceA_sq_le (y : ∀ n, G n) (n : ℕ) :
    ‖inverseDifferenceA ξ ζ y n‖ ^ 2 ≤ 2 * comparisonWeight ξ ζ y n := by
  have h1 := coefficient_abs_le ξ hξ y (2 * n + 1)
  have h2 := coefficient_abs_le ξ hξ y n
  have habs : |coefficient ξ y (2 * n + 1) - coefficient ξ y n| ≤
      ‖y (2 * n + 1)‖ + ‖y n‖ :=
    (abs_sub _ _).trans (add_le_add h1 h2)
  have hs : (coefficient ξ y (2 * n + 1) - coefficient ξ y n) ^ 2 ≤
      2 * (‖y n‖ ^ 2 + ‖y (2 * n + 1)‖ ^ 2) := by
    have hs' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
    rw [sq_abs] at hs'
    nlinarith [sq_nonneg (‖y n‖ - ‖y (2 * n + 1)‖)]
  dsimp [inverseDifferenceA, comparisonWeight]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖ξ n - ζ n‖)]

/-- Square summability of the entire energy, rather than just of finite partial sums. -/
theorem comparisonWeight_summable (y : lp G 2) :
    Summable (comparisonWeight ξ ζ (fun n => y n)) := by
  have hy : Summable (fun n => ‖y n‖ ^ 2) := by
    simpa using (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have ho : Summable (fun n => ‖y (2 * n + 1)‖ ^ 2) :=
    hy.comp_injective (by
      intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega)
  exact Summable.of_nonneg_of_le (comparisonWeight_nonneg ξ ζ _) (comparisonWeight_le ξ ζ hξ hζ _)
    ((hy.add ho).mul_left 4)

theorem directionDelta_sq_summable (y : lp G 2) :
    Summable (fun n => directionDelta ξ ζ (fun n => y n) n ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (directionDelta_sq_le_weight ξ ζ _)
    (comparisonWeight_summable ξ ζ hξ hζ y)

theorem directionDelta_total_le (y : lp G 2) :
    (∑' n, directionDelta ξ ζ (fun n => y n) n ^ 2) ≤
      ∑' n, comparisonWeight ξ ζ (fun n => y n) n :=
  (directionDelta_sq_summable ξ ζ hξ hζ y).tsum_le_tsum
    (directionDelta_sq_le_weight ξ ζ _)
    (comparisonWeight_summable ξ ζ hξ hζ y)

theorem inverseDifferenceA_sq_summable (y : lp G 2) :
    Summable (fun n => ‖inverseDifferenceA ξ ζ (fun n => y n) n‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (inverseDifferenceA_sq_le ξ ζ hξ hζ _)
    ((comparisonWeight_summable ξ ζ hξ hζ y).mul_left 2)

theorem inverseDifferenceA_total_le (y : lp G 2) :
    (∑' n, ‖inverseDifferenceA ξ ζ (fun n => y n) n‖ ^ 2) ≤
      2 * ∑' n, comparisonWeight ξ ζ (fun n => y n) n := by
  simpa only [tsum_mul_left] using
    (inverseDifferenceA_sq_summable ξ ζ hξ hζ y).tsum_le_tsum
      (inverseDifferenceA_sq_le ξ ζ hξ hζ _)
      ((comparisonWeight_summable ξ ζ hξ hζ y).mul_left 2)

def directionDeltaL2 (y : lp G 2) : ScalarL2 :=
  ⟨directionDelta ξ ζ (fun n => y n), mem_l2_of_summable_sq _ (by
    simpa only [Real.norm_eq_abs, sq_abs] using directionDelta_sq_summable ξ ζ hξ hζ y)⟩

def inverseDifferenceAL2 (y : lp G 2) : lp G 2 :=
  ⟨inverseDifferenceA ξ ζ (fun n => y n),
    mem_l2_of_summable_sq _ (inverseDifferenceA_sq_summable ξ ζ hξ hζ y)⟩

theorem comparisonEnergy_sq (y : lp G 2) :
    comparisonEnergy ξ ζ (fun n => y n) ^ 2 =
      ∑' n, comparisonWeight ξ ζ (fun n => y n) n := by
  exact Real.sq_sqrt (tsum_nonneg (comparisonWeight_nonneg ξ ζ _))

theorem directionDeltaL2_norm_le (y : lp G 2) :
    ‖directionDeltaL2 ξ ζ hξ hζ y‖ ≤ comparisonEnergy ξ ζ (fun n => y n) := by
  have he : 0 ≤ comparisonEnergy ξ ζ (fun n => y n) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg (directionDeltaL2 ξ ζ hξ hζ y)) he).1
  rw [comparisonEnergy_sq ξ ζ hξ hζ y, l2_norm_sq]
  simpa only [directionDeltaL2, Real.norm_eq_abs, sq_abs] using
    directionDelta_total_le ξ ζ hξ hζ y

theorem inverseDifferenceAL2_norm_le (y : lp G 2) :
    ‖inverseDifferenceAL2 ξ ζ hξ hζ y‖ ≤ 2 * comparisonEnergy ξ ζ (fun n => y n) := by
  have he : 0 ≤ comparisonEnergy ξ ζ (fun n => y n) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) he)).1
  have hsum := inverseDifferenceA_total_le ξ ζ hξ hζ y
  have hnorm : ‖inverseDifferenceAL2 ξ ζ hξ hζ y‖ ^ 2 ≤
      2 * comparisonEnergy ξ ζ (fun n => y n) ^ 2 := by
    rw [comparisonEnergy_sq ξ ζ hξ hζ y, l2_norm_sq]
    exact hsum
  nlinarith [sq_nonneg (comparisonEnergy ξ ζ (fun n => y n))]

/-- R6 Lemma 9.3 with its coefficient 4 and the full comparison series.
The proof uses the actual inverse of Lemma 9.2, with no surjectivity hypothesis.
-/
theorem frozenInverse_comparison (y : lp G 2) :
    ‖(frozenL2Equiv ξ hξ).symm y - (frozenL2Equiv ζ hζ).symm y‖ ≤
      4 * comparisonEnergy ξ ζ (fun n => y n) := by
  let δ := directionDeltaL2 ξ ζ hξ hζ y
  let X : HilbertPair (lp G 2) := WithLp.toLp 2
    (inverseDifferenceAL2 ξ ζ hξ hζ y, (0 : ScalarL2))
  let Yeo : HilbertPair (lp G 2) := WithLp.toLp 2
    (scalarDirectionL2 ζ hζ (scalarOddL2 δ), scalarEvenL2 δ)
  let Yall : HilbertPair (lp G 2) := WithLp.toLp 2
    (scalarDirectionL2 ζ hζ δ, (0 : ScalarL2))
  have hid : (frozenL2Equiv ξ hξ).symm y - (frozenL2Equiv ζ hζ).symm y =
      X + Yeo - Yall := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext n
      change frozenInverseU ξ (fun k => y k) n - frozenInverseU ζ (fun k => y k) n =
        inverseDifferenceA ξ ζ (fun k => y k) n +
          directionDelta ξ ζ (fun k => y k) (2 * n + 1) • ζ n -
          directionDelta ξ ζ (fun k => y k) n • ζ n
      rw [inverseU_difference]
      unfold inverseDifferenceB
      module
    · apply lp.ext
      funext n
      change frozenInverseV ξ (fun k => y k) n - frozenInverseV ζ (fun k => y k) n =
        0 + directionDelta ξ ζ (fun k => y k) (2 * n) - 0
      simpa only [zero_add, sub_zero] using inverseV_difference ξ ζ (fun k => y k) n
  have hX : ‖X‖ ≤ 2 * comparisonEnergy ξ ζ (fun n => y n) := by
    change ‖WithLp.toLp 2 (inverseDifferenceAL2 ξ ζ hξ hζ y, (0 : ScalarL2))‖ ≤ _
    rw [WithLp.norm_toLp_fst]
    exact inverseDifferenceAL2_norm_le ξ ζ hξ hζ y
  have hYeo : ‖Yeo‖ = ‖δ‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    change ‖WithLp.toLp 2 (scalarDirectionL2 ζ hζ (scalarOddL2 δ), scalarEvenL2 δ)‖ ^ 2 = _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖scalarDirectionL2 ζ hζ (scalarOddL2 δ)‖ ^ 2 + ‖scalarEvenL2 δ‖ ^ 2 = ‖δ‖ ^ 2
    rw [scalarDirectionL2_norm]
    exact scalar_split_norm_sq δ
  have hYall : ‖Yall‖ = ‖δ‖ := by
    change ‖WithLp.toLp 2 (scalarDirectionL2 ζ hζ δ, (0 : ScalarL2))‖ = _
    rw [WithLp.norm_toLp_fst, scalarDirectionL2_norm]
  have hδ : ‖δ‖ ≤ comparisonEnergy ξ ζ (fun n => y n) :=
    directionDeltaL2_norm_le ξ ζ hξ hζ y
  calc
    ‖(frozenL2Equiv ξ hξ).symm y - (frozenL2Equiv ζ hζ).symm y‖ = ‖X + Yeo - Yall‖ :=
      congrArg norm hid
    _ ≤ ‖X + Yeo‖ + ‖Yall‖ := norm_sub_le _ _
    _ ≤ (‖X‖ + ‖Yeo‖) + ‖Yall‖ := add_le_add (norm_add_le X Yeo) le_rfl
    _ = ‖X‖ + ‖δ‖ + ‖δ‖ := by rw [hYeo, hYall]
    _ ≤ 4 * comparisonEnergy ξ ζ (fun n => y n) := by linarith

end BanachGeometry.HilbertSums
