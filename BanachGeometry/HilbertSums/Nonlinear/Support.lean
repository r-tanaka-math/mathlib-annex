/- Support separation on tent coordinates and high-level stabilization of the
directions. LipschitzFreeSpace/HilbertLocality assembles the finite-family
neighborhood/cutoff conclusion from these support statements.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Nonlinear.Equivalence
import BanachGeometry.HilbertSums.Graded.CoordinateIsometry

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertSums.Nonlinear
open Coding Clock

def scalarSupport (n : ℕ) (x : GradedBlock n) : Set (BlockCoordinate n) :=
  {a | x a.1 a.2 ≠ 0}

theorem codeDirection_support_level (n k : ℕ) (hk : k < n + 1) (y : GradedHilbert)
    (a : BlockCoordinate n) (ha : a ∈ scalarSupport n (codeDirection n k hk y)) : a.1.val = k := by
  by_contra h
  have hne : a.1 ≠ (⟨k, hk⟩ : Fin (n + 1)) := fun he => h (congrArg Fin.val he)
  have hz : codeDirection n k hk y a.1 = 0 := by
    simp [codeDirection, levelIsometry, Pi.single_apply, hne]
  exact ha (by rw [hz]; rfl)

theorem codeDirection_support_disjoint_levels (n k l : ℕ) (hk : k < n + 1) (hl : l < n + 1)
    (hkl : k ≠ l) (y z : GradedHilbert) :
    Disjoint (scalarSupport n (codeDirection n k hk y)) (scalarSupport n (codeDirection n l hl z)) := by
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact hkl ((codeDirection_support_level n k hk y a ha).symm.trans
    (codeDirection_support_level n l hl z a hb))

theorem same_level_code_support_disjoint (n k : ℕ) (hk : k < n + 1) (hk0 : 0 < k)
    (y z : GradedHilbert) (j : Fin k)
    (hsep : 2 / (k : ℝ) ≤ |scalarObservation j.val y - scalarObservation j.val z|) :
    Disjoint (scalarSupport n (codeDirection n k hk y)) (scalarSupport n (codeDirection n k hk z)) := by
  have hd := unitCode_support_disjoint hk0 _ _
    (fun i => (abs_scalarObservation_lt_one i.val y).le)
    (fun i => (abs_scalarObservation_lt_one i.val z).le) j hsep
  apply Set.disjoint_left.mpr
  intro a ha hb
  have hlevel := codeDirection_support_level n k hk y a ha
  obtain ⟨a₁, a₂⟩ := a
  have hfin : a₁ = (⟨k, hk⟩ : Fin (n + 1)) := Fin.ext hlevel
  subst a₁
  have hy : unitCode k (fun i => scalarObservation i.val y) a₂ ≠ 0 := by
    change (show GradedBlock n from PiLp.single 2 (⟨k, hk⟩ : Fin (n + 1))
      (unitCode k (fun i => scalarObservation i.val y))) (⟨k, hk⟩ : Fin (n + 1)) a₂ ≠ 0 at ha
    simpa only [PiLp.single_eq_same] using ha
  have hz : unitCode k (fun i => scalarObservation i.val z) a₂ ≠ 0 := by
    change (show GradedBlock n from PiLp.single 2 (⟨k, hk⟩ : Fin (n + 1))
      (unitCode k (fun i => scalarObservation i.val z))) (⟨k, hk⟩ : Fin (n + 1)) a₂ ≠ 0 at hb
    simpa only [PiLp.single_eq_same] using hb
  exact Set.disjoint_left.mp hd hy hz

/-- A single observed scalar keeps two whole balls apart in every sufficiently fine code. -/
theorem observation_gap_on_balls (j : ℕ) (a b y z : GradedHilbert) {ε : ℝ}
    (hy : ‖y - a‖ < ε) (hz : ‖z - b‖ < ε) :
    |scalarObservation j a - scalarObservation j b| - 2 * ε <
      |scalarObservation j y - scalarObservation j z| := by
  have h₁ := abs_scalarObservation_sub_le j a y
  have h₂ := abs_scalarObservation_sub_le j z b
  have ht : |scalarObservation j a - scalarObservation j b| ≤
      |scalarObservation j a - scalarObservation j y| +
      |scalarObservation j y - scalarObservation j z| + |scalarObservation j z - scalarObservation j b| := by
    have he : scalarObservation j a - scalarObservation j b =
        (scalarObservation j a - scalarObservation j y) +
          (scalarObservation j y - scalarObservation j z) +
          (scalarObservation j z - scalarObservation j b) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [norm_sub_rev a y] at h₁
  linarith

theorem exists_separating_observation {a b : GradedHilbert} (hab : a ≠ b) :
    ∃ j, 0 < |scalarObservation j a - scalarObservation j b| := by
  by_contra h
  push_neg at h
  apply hab
  apply scalarObservations_separate
  intro j
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (h j))

/-- Explicit pairwise neighborhood data; all later coding levels separate their supports. -/
theorem exists_pair_code_neighborhoods {a b : GradedHilbert} (hab : a ≠ b) :
    ∃ K : ℕ, 0 < K ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y z, ‖y - a‖ < ε → ‖z - b‖ < ε →
      ∀ n k (hk : k < n + 1), K ≤ k →
        Disjoint (scalarSupport n (codeDirection n k hk y)) (scalarSupport n (codeDirection n k hk z)) := by
  obtain ⟨j, hj⟩ := exists_separating_observation hab
  let d := |scalarObservation j a - scalarObservation j b|
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / d)
  let K := max (j + 1) (N + 1)
  have hK : 0 < K := by dsimp [K]; omega
  have hKd : 4 / d < (K : ℝ) := hN.trans_le (by exact_mod_cast (show N ≤ K by dsimp [K]; omega))
  refine ⟨K, hK, d / 8, by dsimp [d]; positivity, ?_⟩
  intro y z hy hz n k hk hKk
  have hk0 : 0 < k := hK.trans_le hKk
  have hjk : j < k := by dsimp [K] at hKk; omega
  have hkd : 4 / d < (k : ℝ) := hKd.trans_le (by exact_mod_cast hKk)
  have hsep : 2 / (k : ℝ) ≤ |scalarObservation j y - scalarObservation j z| := by
    have hgap := observation_gap_on_balls j a b y z hy hz
    have hprod : 4 < (k : ℝ) * d := (div_lt_iff₀ hj).mp hkd
    have hfrac : 2 / (k : ℝ) < d / 2 := (div_lt_iff₀ (by exact_mod_cast hk0)).2 (by nlinarith)
    dsimp [d] at *
    linarith
  exact same_level_code_support_disjoint n k hk hk0 y z ⟨j, hjk⟩ hsep

/-- At/after a mature transition, the finite recursion has discarded every lower level. -/
theorem omegaPrefix_no_low_level (c : ℝ) (hc : 0 < c) (n K : ℕ) (hK : K ≤ n)
    (y : GradedHilbert) {t : ℝ} (ht : transitionStart c hc K + 8 < t) :
    ∀ k (hk : k ≤ n), K + 1 ≤ k → ∀ a : BlockCoordinate n, a.1.val ≤ K →
      omegaPrefix c hc n y t k hk a.1 a.2 = 0 := by
  intro k
  induction k with
  | zero => intro hk hKk; omega
  | succ k ih =>
    intro hk hKk a ha
    by_cases heq : k = K
    · subst k
      rw [omegaPrefix, if_neg (by linarith), bridge_mature c hc n K hk y ht.le]
      have hne : a.1 ≠ (⟨K + 1, by omega⟩ : Fin (n + 1)) := by
        intro he
        have hv : a.1.val = K + 1 := congrArg Fin.val he
        omega
      simp [codeDirection, levelIsometry, Pi.single_apply, hne]
    · have hKk' : K + 1 ≤ k := by omega
      rw [omegaPrefix]
      split_ifs
      · exact ih (by omega) hKk' a ha
      · have hne₁ : a.1 ≠ (⟨k, by omega⟩ : Fin (n + 1)) := by
          intro he
          have hv : a.1.val = k := congrArg Fin.val he
          omega
        have hne₂ : a.1 ≠ (⟨k + 1, by omega⟩ : Fin (n + 1)) := by
          intro he
          have hv : a.1.val = k + 1 := congrArg Fin.val he
          omega
        simp [bridge, unitSegment, NormedSpace.normalize, affineSegment,
          codeDirection, levelIsometry, Pi.single_apply, hne₁, hne₂]

/-- Radius zero is handled separately by the actual top-level branch. -/
theorem omega_no_low_level (c : ℝ) (hc : 0 < c) (n K : ℕ) (hK : K < n)
    (y : GradedHilbert) {r : ℝ} (hr : 0 ≤ r)
    (ht : r = 0 ∨ transitionStart c hc K + 8 < tau c r)
    (a : BlockCoordinate n) (ha : a.1.val ≤ K) : omega c hc n y r a.1 a.2 = 0 := by
  by_cases hz : r = 0
  · subst r
    rw [omega, if_neg (lt_irrefl 0)]
    have hne : a.1 ≠ (⟨n, by omega⟩ : Fin (n + 1)) := by
      intro he
      have hv : a.1.val = n := congrArg Fin.val he
      omega
    simp [codeDirection, levelIsometry, Pi.single_apply, hne]
  · rw [omega, if_pos (lt_of_le_of_ne hr (Ne.symm hz))]
    exact omegaPrefix_no_low_level c hc n K hK.le y (ht.resolve_left hz) n le_rfl (by omega) a ha

end BanachGeometry.HilbertSums.Nonlinear
