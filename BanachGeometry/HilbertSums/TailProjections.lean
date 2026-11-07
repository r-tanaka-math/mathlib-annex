/- R6 §9 tail radii and finite-coordinate observations for general real
inner product blocks. The index hypotheses on observations are explicit at
each use. Graded/FiniteCoordinates enumerates the concrete block fibres;
Graded/Basic uses that enumeration for the constructed Hilbert space.
Local execution evidence is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Coding.Bounds
import BanachGeometry.HilbertSums.FrozenIsometry

open scoped ENNReal

noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace BanachGeometry.HilbertSums

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

def blockHead (N : ℕ) (y : lp G 2) : lp G 2 :=
  ∑ n ∈ Finset.range N, lp.single 2 n (y n)

def blockTail (N : ℕ) (y : lp G 2) : lp G 2 := y - blockHead N y

@[simp] theorem blockHead_apply (N : ℕ) (y : lp G 2) (n : ℕ) :
    blockHead N y n = if n < N then y n else 0 := by
  classical
  change (lp.evalCLM ℝ G 2 n) (∑ i ∈ Finset.range N, lp.single 2 i (y i)) = _
  rw [map_sum]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · exact lp.single_apply_self 2 n _
    · intro i hi hne
      exact lp.single_apply_ne 2 i _ (Ne.symm hne)
    · intro h
      exact (h (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    apply lp.single_apply_ne 2 i _
    intro hni
    exact hn (hni.symm ▸ Finset.mem_range.mp hi)

@[simp] theorem blockTail_apply (N : ℕ) (y : lp G 2) (n : ℕ) :
    blockTail N y n = if n < N then 0 else y n := by
  simp only [blockTail, lp.coeFn_sub, Pi.sub_apply, blockHead_apply]
  split_ifs <;> simp

theorem norm_blockTail_le (N : ℕ) (y : lp G 2) : ‖blockTail N y‖ ≤ ‖y‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [blockTail_apply]
  split_ifs <;> simp

theorem blockHead_sub (N : ℕ) (y z : lp G 2) :
    blockHead N (y - z) = blockHead N y - blockHead N z := by
  apply lp.ext
  funext n
  simp only [blockHead_apply, lp.coeFn_sub, Pi.sub_apply]
  split_ifs <;> simp

theorem blockTail_sub (N : ℕ) (y z : lp G 2) :
    blockTail N (y - z) = blockTail N y - blockTail N z := by
  rw [blockTail, blockHead_sub, blockTail, blockTail]
  module

theorem norm_blockTail_sq (N : ℕ) (y : lp G 2) :
    ‖blockTail N y‖ ^ 2 = ‖y‖ ^ 2 - ∑ n ∈ Finset.range N, ‖y n‖ ^ 2 := by
  simpa [blockTail, blockHead] using
    lp.norm_compl_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y (Finset.range N)

theorem norm_blockTail_sq_sub_norm_blockTail_succ_sq (N : ℕ) (y : lp G 2) :
    ‖blockTail N y‖ ^ 2 - ‖blockTail (N + 1) y‖ ^ 2 = ‖y N‖ ^ 2 := by
  rw [norm_blockTail_sq, norm_blockTail_sq, Finset.sum_range_succ]
  ring

theorem norm_blockTail_antitone (y : lp G 2) : Antitone (fun N => ‖blockTail N y‖) := by
  intro N M hNM
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  simp only [blockTail_apply]
  by_cases hn : n < N
  · have hm : n < M := lt_of_lt_of_le hn hNM
    simp [hn, hm]
  · by_cases hm : n < M <;> simp [hn, hm]

theorem abs_norm_blockTail_sub_norm_blockTail_le (N : ℕ) (y z : lp G 2) :
    |‖blockTail N y‖ - ‖blockTail N z‖| ≤ ‖y - z‖ := by
  calc
    _ ≤ ‖blockTail N y - blockTail N z‖ := abs_norm_sub_norm_le _ _
    _ = ‖blockTail N (y - z)‖ := congrArg norm (blockTail_sub N y z).symm
    _ ≤ ‖y - z‖ := norm_blockTail_le N _

theorem tendsto_blockHead (y : lp G 2) :
    Tendsto (fun N => blockHead N y) atTop (𝓝 y) := by
  simpa only [blockHead] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) y).tendsto_sum_nat

theorem tendsto_norm_blockTail_zero (y : lp G 2) :
    Tendsto (fun N => ‖blockTail N y‖) atTop (𝓝 0) := by
  have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).sub
    (tendsto_blockHead y)).norm
  simpa [blockTail] using ht

theorem apply_eq_zero_of_norm_blockTail_eq_zero {N : ℕ} (y : lp G 2)
    (h : ‖blockTail N y‖ = 0) {n : ℕ} (hn : N ≤ n) : y n = 0 := by
  have ht : blockTail N y = 0 := norm_eq_zero.mp h
  have he := congrArg (fun t : lp G 2 => t n) ht
  simpa [blockTail_apply, not_lt.mpr hn] using he

/-- A bounded Hilbert coordinate, using the exact R6 scalar function. -/
def blockObservation (b : ℕ) (e : G b) (y : lp G 2) : ℝ :=
  Coding.boundedScalar ⟪e, y b⟫_ℝ

theorem abs_blockObservation_lt_one (b : ℕ) (e : G b) (y : lp G 2) :
    |blockObservation b e y| < 1 := Coding.abs_boundedScalar_lt_one _

theorem abs_blockObservation_sub_le (b : ℕ) (e : G b) (he : ‖e‖ = 1) (y z : lp G 2) :
    |blockObservation b e y - blockObservation b e z| ≤ ‖y - z‖ := by
  calc
    _ ≤ |⟪e, y b⟫_ℝ - ⟪e, z b⟫_ℝ| := Coding.abs_boundedScalar_sub_le _ _
    _ = |⟪e, (y - z) b⟫_ℝ| := by simp [inner_sub_right]
    _ ≤ ‖e‖ * ‖(y - z) b‖ := abs_real_inner_le_norm _ _
    _ = ‖(y - z) b‖ := by rw [he, one_mul]
    _ ≤ ‖y - z‖ := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ b

theorem blockObservation_head {N b : ℕ} (e : G b) (hb : b < N) (y : lp G 2) :
    blockObservation b e (blockHead N y) = blockObservation b e y := by
  simp [blockObservation, blockHead_apply, hb]

/-- The code reads only the finitely many indicated Hilbert coordinates. -/
def observedUnitCode (k : ℕ) (b : Fin k → ℕ) (e : ∀ j, G (b j)) (y : lp G 2) :
    Coding.CodeSpace k := Coding.unitCode k (fun j => blockObservation (b j) (e j) y)

theorem norm_observedUnitCode (k : ℕ) (b : Fin k → ℕ) (e : ∀ j, G (b j)) (y : lp G 2) :
    ‖observedUnitCode k b e y‖ = 1 :=
  Coding.norm_unitCode k _ (fun j => (abs_blockObservation_lt_one _ _ _).le)

/-- Head-dependence is explicit: every observation index must lie before N. -/
theorem observedUnitCode_head (k N : ℕ) (b : Fin k → ℕ) (e : ∀ j, G (b j))
    (hb : ∀ j, b j < N) (y : lp G 2) :
    observedUnitCode k b e (blockHead N y) = observedUnitCode k b e y := by
  unfold observedUnitCode
  congr 1
  funext j
  exact blockObservation_head (e j) (hb j) y

theorem norm_observedUnitCode_sub_le (k : ℕ) (b : Fin k → ℕ) (e : ∀ j, G (b j))
    (he : ∀ j, ‖e j‖ = 1) (y z : lp G 2) :
    ‖observedUnitCode k b e y - observedUnitCode k b e z‖ ≤
      (4 * k * Real.sqrt ((2 * k + 1 : ℕ) ^ k)) * ‖y - z‖ :=
  Coding.norm_unitCode_sub_le _ _
    (fun _ => (abs_blockObservation_lt_one _ _ _).le)
    (fun _ => (abs_blockObservation_lt_one _ _ _).le)
    (norm_nonneg _) (fun j => abs_blockObservation_sub_le _ _ (he j) y z)

theorem observedUnitCode_support_disjoint {k : ℕ} (hk : 0 < k)
    (b : Fin k → ℕ) (e : ∀ j, G (b j)) (y z : lp G 2) (j : Fin k)
    (hsep : 2 / (k : ℝ) ≤ |blockObservation (b j) (e j) y - blockObservation (b j) (e j) z|) :
    Disjoint (Function.support (observedUnitCode k b e y))
      (Function.support (observedUnitCode k b e z)) :=
  Coding.unitCode_support_disjoint hk _ _
    (fun _ => (abs_blockObservation_lt_one _ _ _).le)
    (fun _ => (abs_blockObservation_lt_one _ _ _).le) j hsep

end BanachGeometry.HilbertSums
