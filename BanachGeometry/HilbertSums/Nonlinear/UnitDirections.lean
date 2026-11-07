/- Finite-level directions, including r=0, causal head dependence and time/radius
bounds. The full point-variable bound is proved downstream in Nonlinear/PointBounds.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Graded.Separable

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear
open Coding Clock

def saturate (s : ℝ) : ℝ := max 0 (min 1 s)

theorem saturate_nonneg (s : ℝ) : 0 ≤ saturate s := le_max_left _ _
theorem saturate_le_one (s : ℝ) : saturate s ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem saturate_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : saturate s = 0 := by
  simp [saturate, min_eq_right (by linarith : s ≤ 1), max_eq_left hs]

theorem saturate_one_of_one_le {s : ℝ} (hs : 1 ≤ s) : saturate s = 1 := by
  simp [saturate, min_eq_left hs]

theorem saturate_abs_sub_le (s t : ℝ) : |saturate s - saturate t| ≤ |s - t| := by
  have hmin : |min 1 s - min 1 t| ≤ |s - t| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (s - t))] using
      abs_min_sub_min_le_max (1 : ℝ) s 1 t
  simpa only [saturate, max_comm] using
    (abs_max_sub_max_le_abs (min 1 s) (min 1 t) 0).trans hmin

def transitionParameter (c : ℝ) (hc : 0 < c) (k : ℕ) (t : ℝ) : ℝ :=
  saturate ((t - transitionStart c hc k) / 8)

theorem transitionParameter_begin (c : ℝ) (hc : 0 < c) (k : ℕ) :
    transitionParameter c hc k (transitionStart c hc k) = 0 := by
  simp [transitionParameter, saturate]

theorem transitionParameter_mature (c : ℝ) (hc : 0 < c) (k : ℕ) {t : ℝ}
    (ht : transitionStart c hc k + 8 ≤ t) : transitionParameter c hc k t = 1 := by
  apply saturate_one_of_one_le
  change 1 ≤ (t - transitionStart c hc k) / 8
  linarith

theorem transitionParameter_abs_sub_le (c : ℝ) (hc : 0 < c) (k : ℕ) (s t : ℝ) :
    |transitionParameter c hc k s - transitionParameter c hc k t| ≤ |s - t| / 8 := by
  have h := saturate_abs_sub_le ((s - transitionStart c hc k) / 8)
    ((t - transitionStart c hc k) / 8)
  have heq : (s - transitionStart c hc k) / 8 - (t - transitionStart c hc k) / 8 = (s - t) / 8 := by ring
  simpa only [transitionParameter, heq, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 8)] using h

def bridge (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n)
    (y : GradedHilbert) (t : ℝ) : GradedBlock n :=
  unitSegment (codeDirection n k (by omega) y) (codeDirection n (k + 1) (by omega) y)
    (transitionParameter c hc k t)

theorem norm_bridge (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n) (y : GradedHilbert) (t : ℝ) :
    ‖bridge c hc n k hk y t‖ = 1 :=
  norm_unitSegment _ _ (norm_codeDirection _ _ _ _) (norm_codeDirection _ _ _ _)
    (level_inner_ne n k (k + 1) (by omega) (by omega) (by omega) _ _) _

theorem bridge_begin (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n) (y : GradedHilbert) :
    bridge c hc n k hk y (transitionStart c hc k) = codeDirection n k (by omega) y := by
  rw [bridge, transitionParameter_begin, unitSegment_zero _ _ (norm_codeDirection _ _ _ _)]

theorem bridge_mature (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n) (y : GradedHilbert)
    {t : ℝ} (ht : transitionStart c hc k + 8 ≤ t) :
    bridge c hc n k hk y t = codeDirection n (k + 1) (by omega) y := by
  rw [bridge, transitionParameter_mature c hc k ht, unitSegment_one _ _ (norm_codeDirection _ _ _ _)]

theorem bridge_time_bound (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k + 1 ≤ n)
    (y : GradedHilbert) (s t : ℝ) :
    ‖bridge c hc n k hk y s - bridge c hc n k hk y t‖ ≤ (1 / 2 : ℝ) * |s - t| := by
  have h1 := norm_unitSegment_sub_le _ _ (norm_codeDirection n k (by omega) y)
    (norm_codeDirection n (k + 1) (by omega) y)
    (level_inner_ne n k (k + 1) (by omega) (by omega) (by omega) _ _)
    (transitionParameter c hc k s) (transitionParameter c hc k t)
  have h2 := transitionParameter_abs_sub_le c hc k s t
  change ‖unitSegment _ _ _ - unitSegment _ _ _‖ ≤ _
  linarith

/-- Explicit finite recursion on the levels of a fixed block; no infinite selector is used. -/
def omegaPrefix (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (t : ℝ) :
    (k : ℕ) → k ≤ n → GradedBlock n
  | 0, _ => codeDirection n 0 (by omega) y
  | k + 1, hk => if t ≤ transitionStart c hc k
      then omegaPrefix c hc n y t k (by omega)
      else bridge c hc n k hk y t

theorem norm_omegaPrefix (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (t : ℝ) :
    ∀ k (hk : k ≤ n), ‖omegaPrefix c hc n y t k hk‖ = 1 := by
  intro k
  induction k with
  | zero => intro hk; exact norm_codeDirection _ _ _ _
  | succ k ih =>
    intro hk
    rw [omegaPrefix]
    split_ifs
    · exact ih _
    · exact norm_bridge _ _ _ _ _ _ _

theorem omegaPrefix_head (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (t : ℝ) :
    ∀ k (hk : k ≤ n), omegaPrefix c hc n (blockHead n y) t k hk = omegaPrefix c hc n y t k hk := by
  intro k
  induction k with
  | zero => intro hk; exact codeDirection_head _ _ _ _
  | succ k ih =>
    intro hk
    rw [omegaPrefix, omegaPrefix]
    split_ifs
    · exact ih _
    · unfold bridge
      rw [codeDirection_head, codeDirection_head]

theorem omegaPrefix_at_nextStart (c : ℝ) (hc : 0 < c) (n k : ℕ) (hk : k ≤ n) (y : GradedHilbert) :
    omegaPrefix c hc n y (transitionStart c hc k) k hk = codeDirection n k (by omega) y := by
  cases k with
  | zero => rfl
  | succ k =>
    have ht : transitionStart c hc k + 8 ≤ transitionStart c hc (k + 1) :=
      (by linarith [transitionStart_gap c hc k])
    rw [omegaPrefix, if_neg (by linarith [transitionStart_gap c hc k])]
    exact bridge_mature _ _ _ _ _ _ ht

section Glue
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem glue_cross_bound {L a s t : ℝ} (f g : ℝ → V)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * |x - y|)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * |x - y|) (he : f a = g a)
    (hs : s ≤ a) (ht : a ≤ t) : ‖f s - g t‖ ≤ L * |s - t| := by
  calc
    ‖f s - g t‖ = ‖(f s - f a) + (g a - g t)‖ := by rw [← he]; congr 1; module
    _ ≤ ‖f s - f a‖ + ‖g a - g t‖ := norm_add_le _ _
    _ ≤ L * |s - a| + L * |a - t| := add_le_add (hf _ _) (hg _ _)
    _ = L * |s - t| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs), abs_of_nonpos (sub_nonpos.mpr ht),
        abs_of_nonpos (sub_nonpos.mpr (hs.trans ht))]
      ring

theorem glue_time_bound {L a : ℝ} (f g : ℝ → V)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * |x - y|)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * |x - y|) (he : f a = g a) (s t : ℝ) :
    ‖(if s ≤ a then f s else g s) - (if t ≤ a then f t else g t)‖ ≤ L * |s - t| := by
  by_cases hs : s ≤ a <;> by_cases ht : t ≤ a
  · simpa [hs, ht] using hf s t
  · simpa [hs, ht] using glue_cross_bound f g hf hg he hs (le_of_not_ge ht)
  · simpa [hs, ht, norm_sub_rev, abs_sub_comm] using
      glue_cross_bound f g hf hg he ht (le_of_not_ge hs)
  · simpa [hs, ht] using hg s t
end Glue

theorem omegaPrefix_time_bound (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) :
    ∀ k (hk : k ≤ n) (s t : ℝ),
      ‖omegaPrefix c hc n y s k hk - omegaPrefix c hc n y t k hk‖ ≤ (1 / 2 : ℝ) * |s - t| := by
  intro k
  induction k with
  | zero => intro hk s t; simp [omegaPrefix]
  | succ k ih =>
    intro hk s t
    have he : omegaPrefix c hc n y (transitionStart c hc k) k (by omega) =
        bridge c hc n k hk y (transitionStart c hc k) := by
      rw [omegaPrefix_at_nextStart, bridge_begin]
    exact glue_time_bound _ _ (ih (by omega)) (bridge_time_bound c hc n k hk y) he s t

/-- Actual Omega_(n+1); radius zero uses the last level, exactly as in R6. -/
def omega (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (r : ℝ) : GradedBlock n :=
  if 0 < r then omegaPrefix c hc n y (tau c r) n le_rfl else codeDirection n n (by omega) y

theorem norm_omega (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (r : ℝ) :
    ‖omega c hc n y r‖ = 1 := by
  unfold omega
  split_ifs
  · exact norm_omegaPrefix _ _ _ _ _ _ _
  · exact norm_codeDirection _ _ _ _

theorem omega_head (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert) (r : ℝ) :
    omega c hc n (blockHead n y) r = omega c hc n y r := by
  unfold omega
  split_ifs
  · exact omegaPrefix_head _ _ _ _ _ _ _
  · exact codeDirection_head _ _ _ _

theorem omega_radius_bound (c : ℝ) (hc : 0 < c) (n : ℕ) (y : GradedHilbert)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ‖omega c hc n y r - omega c hc n y s‖ ≤
      (gamma c (min r s) / 2) * |r - s| := by
  rw [omega, if_pos hr, omega, if_pos hs]
  have h1 := omegaPrefix_time_bound c hc n y n le_rfl (tau c r) (tau c s)
  have h2 := tau_abs_sub_le hc.le hr hs
  nlinarith

/-- Actual point-dependent unit family, not necessarily an lp element. -/
def pointDirection (c : ℝ) (hc : 0 < c) (y : GradedHilbert) (n : ℕ) : GradedBlock n :=
  omega c hc n y ‖blockTail n y‖

theorem norm_pointDirection (c : ℝ) (hc : 0 < c) (y : GradedHilbert) (n : ℕ) :
    ‖pointDirection c hc y n‖ = 1 := norm_omega _ _ _ _ _

end BanachGeometry.HilbertSums.Nonlinear
