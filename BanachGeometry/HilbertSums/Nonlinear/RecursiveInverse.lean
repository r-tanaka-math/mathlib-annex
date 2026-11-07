/- Actual inverse-first Phi and a concrete coordinate-recursive right inverse.
The recursion uses total Real.sqrt, then proves its radicand is the actual tail energy.
This avoids presupposing existence of a full vector or its radius during recursion.
No lower metric bound/injectivity is assumed in the surjectivity proof.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.UnitDirections

open scoped ENNReal

noncomputable section
open scoped BigOperators InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear

/-- Raw recursion state is data (output block, unit direction), with no product norm used. -/
abbrev RawState (n : ℕ) := GradedBlock n × GradedBlock n

def historyPrefix (n : ℕ) (previous : ∀ m, m < n → RawState m) : GradedHilbert :=
  ∑ j : Fin n, lp.single 2 j.val (previous j.val j.isLt).1

theorem historyPrefix_eq_head (n : ℕ) (previous : ∀ m, m < n → RawState m)
    (y : GradedHilbert) (hy : ∀ m (hm : m < n), (previous m hm).1 = y m) :
    historyPrefix n previous = blockHead n y := by
  unfold historyPrefix blockHead
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [hy j.val j.isLt]

def rawStep (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2)
    (n : ℕ) (previous : ∀ m, m < n → RawState m) : RawState n :=
  let p := historyPrefix n previous
  let s := Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖p‖ ^ 2)
  let ξ := omega c hc n p s
  let α := ⟪ξ, u n⟫_ℝ
  let C := if he : n % 2 = 0 then v (n / 2)
    else ⟪(previous (n / 2) (by
      have hn : 0 < n := by omega
      exact Nat.div_lt_self hn (by norm_num))).2, u (n / 2)⟫_ℝ
  (u n - α • ξ + C • ξ, ξ)

/-- Actual dependent strong recursion; every odd lookup uses the earlier n/2 block. -/
def recursiveState (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) : ∀ n, RawState n :=
  Nat.strongRec (rawStep c hc u v)

theorem recursiveState_eq (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    recursiveState c hc u v n = rawStep c hc u v n (fun m _ => recursiveState c hc u v m) := by
  rw [recursiveState, Nat.strongRec_eq]
  rfl

def recursiveCoordinates (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) : GradedBlock n :=
  (recursiveState c hc u v n).1

def recursiveDirections (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) : GradedBlock n :=
  (recursiveState c hc u v n).2

theorem norm_recursiveDirections (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    ‖recursiveDirections c hc u v n‖ = 1 := by
  change ‖(recursiveState c hc u v n).2‖ = 1
  rw [recursiveState_eq]
  exact norm_omega _ _ _ _ _

/-- All recursively produced coordinates satisfy exactly the frozen forward formula. -/
theorem recursiveCoordinates_forward (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    recursiveCoordinates c hc u v n =
      frozenForward (recursiveDirections c hc u v) (fun j => u j) (fun j => v j) n := by
  have hn := recursiveState_eq c hc u v n
  simp only [recursiveCoordinates, recursiveDirections, frozenForward, coefficient, interleave,
    hn, rawStep]
  split_ifs <;> rfl

/-- The raw sequence belongs to l2 because it is the actual frozen image of (u,v). -/
def recursiveInverse (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) : GradedHilbert :=
  frozenForwardL2 (recursiveDirections c hc u v) (norm_recursiveDirections c hc u v) u v

@[simp] theorem recursiveInverse_apply (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    recursiveInverse c hc u v n = recursiveCoordinates c hc u v n :=
  (recursiveCoordinates_forward c hc u v n).symm

theorem norm_recursiveInverse_sq (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) :
    ‖recursiveInverse c hc u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  frozenForward_total_energy _ _ _ _

theorem norm_blockHead_sq (N : ℕ) (y : GradedHilbert) :
    ‖blockHead N y‖ ^ 2 = ∑ n ∈ Finset.range N, ‖y n‖ ^ 2 := by
  simpa [blockHead] using lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun n => y n) (Finset.range N)

theorem norm_blockHead_sq_add_norm_blockTail_sq (N : ℕ) (y : GradedHilbert) :
    ‖blockHead N y‖ ^ 2 + ‖blockTail N y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [norm_blockHead_sq, norm_blockTail_sq]
  ring

theorem recursivePrefix_eq (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    historyPrefix n (fun m _ => recursiveState c hc u v m) =
      blockHead n (recursiveInverse c hc u v) := by
  apply historyPrefix_eq_head
  intro m hm
  exact (recursiveInverse_apply c hc u v m).symm

/-- The already constructed frozen image identifies the radicand exactly.
In particular, the strong recursion never needs an assumed final radius. -/
theorem recursive_radicand_eq_norm_blockTail_sq (c : ℝ) (hc : 0 < c)
    (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 -
      ‖historyPrefix n (fun m _ => recursiveState c hc u v m)‖ ^ 2 =
        ‖blockTail n (recursiveInverse c hc u v)‖ ^ 2 := by
  rw [recursivePrefix_eq]
  have he := norm_blockHead_sq_add_norm_blockTail_sq n (recursiveInverse c hc u v)
  have hn := norm_recursiveInverse_sq c hc u v
  linarith

theorem recursive_radicand_nonneg (c : ℝ) (hc : 0 < c)
    (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    0 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 -
      ‖historyPrefix n (fun m _ => recursiveState c hc u v m)‖ ^ 2 := by
  rw [recursive_radicand_eq_norm_blockTail_sq]
  exact sq_nonneg _

/-- The radius used before building block n is proved to be the true final tail radius. -/
theorem recursiveRadius_eq_tail (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2 -
      ‖historyPrefix n (fun m _ => recursiveState c hc u v m)‖ ^ 2) =
        ‖blockTail n (recursiveInverse c hc u v)‖ := by
  rw [recursive_radicand_eq_norm_blockTail_sq, Real.sqrt_sq (norm_nonneg _)]

/-- This direction matching is established after, not assumed in, the recursion. -/
theorem recursiveDirections_match (c : ℝ) (hc : 0 < c) (u : GradedHilbert) (v : ScalarL2) (n : ℕ) :
    recursiveDirections c hc u v n = pointDirection c hc (recursiveInverse c hc u v) n := by
  change (recursiveState c hc u v n).2 = _
  rw [recursiveState_eq]
  change omega c hc n _ _ = _
  rw [recursiveRadius_eq_tail, recursivePrefix_eq, omega_head]
  rfl

/-- The actual inverse-first map defined on the concrete Hilbert sum. -/
def inverseHilbertMap (c : ℝ) (hc : 0 < c) (y : GradedHilbert) : HilbertPair GradedHilbert :=
  (frozenLinearIsometryEquiv (pointDirection c hc y) (norm_pointDirection c hc y)).symm y

theorem norm_inverseHilbertMap (c : ℝ) (hc : 0 < c) (y : GradedHilbert) : ‖inverseHilbertMap c hc y‖ = ‖y‖ :=
  (frozenLinearIsometryEquiv (pointDirection c hc y) (norm_pointDirection c hc y)).symm.norm_map y

def recursiveHilbertMap (c : ℝ) (hc : 0 < c) (z : HilbertPair GradedHilbert) : GradedHilbert :=
  recursiveInverse c hc (WithLp.ofLp z).1 (WithLp.ofLp z).2

theorem frozen_forward_recursiveHilbertMap (c : ℝ) (hc : 0 < c) (z : HilbertPair GradedHilbert) :
    frozenLinearIsometryEquiv (pointDirection c hc (recursiveHilbertMap c hc z))
      (norm_pointDirection c hc (recursiveHilbertMap c hc z)) z = recursiveHilbertMap c hc z := by
  let u := (WithLp.ofLp z).1
  let v := (WithLp.ofLp z).2
  have hdir : pointDirection c hc (recursiveHilbertMap c hc z) = recursiveDirections c hc u v := by
    funext n
    exact (recursiveDirections_match c hc u v n).symm
  apply lp.ext
  funext n
  change frozenForward (pointDirection c hc (recursiveHilbertMap c hc z))
    (fun j => u j) (fun j => v j) n = recursiveInverse c hc u v n
  rw [hdir]
  rfl

/-- Actual right inverse and surjectivity, not a metric lower bound used as a surrogate. -/
theorem inverseHilbertMap_recursiveHilbertMap (c : ℝ) (hc : 0 < c) (z : HilbertPair GradedHilbert) :
    inverseHilbertMap c hc (recursiveHilbertMap c hc z) = z := by
  let e := frozenLinearIsometryEquiv (pointDirection c hc (recursiveHilbertMap c hc z))
    (norm_pointDirection c hc (recursiveHilbertMap c hc z))
  have he : e z = recursiveHilbertMap c hc z := frozen_forward_recursiveHilbertMap c hc z
  change e.symm (recursiveHilbertMap c hc z) = z
  rw [← he]
  exact e.symm_apply_apply z

theorem inverseHilbertMap_surjective (c : ℝ) (hc : 0 < c) : Function.Surjective (inverseHilbertMap c hc) :=
  fun z => ⟨recursiveHilbertMap c hc z, inverseHilbertMap_recursiveHilbertMap c hc z⟩

theorem norm_recursiveHilbertMap (c : ℝ) (hc : 0 < c) (z : HilbertPair GradedHilbert) :
    ‖recursiveHilbertMap c hc z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  exact (norm_recursiveInverse_sq c hc (WithLp.ofLp z).1 (WithLp.ofLp z).2).trans
    (WithLp.prod_norm_sq_eq_of_L2 z).symm

theorem recursiveHilbertMap_zero (c : ℝ) (hc : 0 < c) : recursiveHilbertMap c hc 0 = 0 := by
  apply norm_eq_zero.mp
  rw [norm_recursiveHilbertMap, norm_zero]

theorem recursiveHilbertMap_injective (c : ℝ) (hc : 0 < c) : Function.Injective (recursiveHilbertMap c hc) := by
  intro z z' h
  have he := congrArg (inverseHilbertMap c hc) h
  simpa only [inverseHilbertMap_recursiveHilbertMap] using he

end BanachGeometry.HilbertSums.Nonlinear
