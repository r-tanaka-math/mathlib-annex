/- Provenance adaptation: finite signs in the c0-dual argument.
Upstream openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/WeakSums.lean,
OAI.LipschitzCounterexample.WeakSequences.summable_c0_dual. This records proof-route adaptation, not a measured claim of verbatim copying.
Applicable upstream material: Apache-2.0; see LICENSES and THIRD_PARTY_NOTICES.md.
Original-contribution source-license scope is recorded separately. -/
import BanachGeometry.SequenceSpaces.C0Operators
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Disjoint coordinate blocks in a heterogeneous c₀ sum. The finite signed
sum estimate proves weak nullity directly; no separability of the dual of
the whole c₀ sum is assumed. 

The standard finite-sign argument was compared with the Apache-2.0 upstream
WeakSequences.summable_c0_dual (source WeakSums.lean); here it is proved for arbitrary disjoint vectors
in the retained heterogeneous carrier, without importing a vendor model.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace C0Sum
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

theorem tailCLM_tailCLM_of_le (n k : ℕ) (hnk : n ≤ k) (x : C0Sum V) :
    tailCLM V n (tailCLM V k x) = tailCLM V k x := by
  apply C0Sum.ext
  intro i
  simp only [tailCLM_apply_coord]
  by_cases hi : i < k
  · simp only [if_pos hi]
    split_ifs <;> rfl
  · have hi' : ¬ i < n := by omega
    simp only [if_neg hi, if_neg hi']

theorem tendsto_norm_tailCLM (x : C0Sum V) :
    Tendsto (fun n => ‖tailCLM V n x‖) atTop (nhds 0) := by
  have ht : Tendsto (fun n => x - head V n x) atTop (nhds 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x)).sub
        (tendsto_head V x)
  change Tendsto (fun n => ‖x - head V n x‖) atTop (nhds 0)
  simpa only [norm_zero] using ht.norm

/-- At most one vector has a nonzero value at any coordinate. -/
def CoordinateDisjoint (u : ℕ → C0Sum V) : Prop :=
  ∀ j k : ℕ, j ≠ k → ∀ i, u j i = 0 ∨ u k i = 0

theorem norm_sum_smul_le_one (u : ℕ → C0Sum V)
    (hd : CoordinateDisjoint V u) (hu : ∀ j, ‖u j‖ ≤ 1)
    (a : ℕ → ℝ) (ha : ∀ j, |a j| ≤ 1) (s : Finset ℕ) :
    ‖∑ j ∈ s, a j • u j‖ ≤ 1 := by
  classical
  apply C0Sum.norm_le zero_le_one
  intro i
  change ‖evalCLM V i (∑ j ∈ s, a j • u j)‖ ≤ 1
  rw [map_sum]
  simp only [map_smul, evalCLM_apply]
  by_cases h : ∃ j ∈ s, u j i ≠ 0
  · obtain ⟨j, hj, hji⟩ := h
    rw [Finset.sum_eq_single j]
    · calc
        ‖a j • u j i‖ = |a j| * ‖u j i‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * 1 := mul_le_mul (ha j) (((u j).norm_apply_le i).trans (hu j))
          (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    · intro k hk hkj
      change a k • u k i = 0
      rw [(hd k j hkj i).resolve_right hji, smul_zero]
    · intro hj'; exact (hj' hj).elim
  · have hz : ∀ j ∈ s, a j • u j i = 0 := by
      intro j hj
      have hji : u j i = 0 := by
        by_contra hji
        exact h ⟨j, hj, hji⟩
      rw [hji, smul_zero]
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact zero_le_one

theorem summable_abs_evaluation (u : ℕ → C0Sum V)
    (hd : CoordinateDisjoint V u) (hu : ∀ j, ‖u j‖ ≤ 1)
    (f : C0Sum V →L[ℝ] ℝ) : Summable (fun j => |f (u j)|) := by
  classical
  apply summable_of_sum_le (fun _ => abs_nonneg _) (fun s => ?_) (c := ‖f‖)
  let a : ℕ → ℝ := fun j => if f (u j) < 0 then -1 else 1
  have ha : ∀ j, |a j| ≤ 1 := by intro j; dsimp [a]; split_ifs <;> norm_num
  let w : C0Sum V := ∑ j ∈ s, a j • u j
  have hw : ‖w‖ ≤ 1 := norm_sum_smul_le_one V u hd hu a ha s
  have heval : f w = ∑ j ∈ s, |f (u j)| := by
    simp only [w, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [a]
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (le_of_not_gt h), one_mul]
  calc
    (∑ j ∈ s, |f (u j)|) = f w := heval.symm
    _ ≤ ‖f w‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖w‖ := f.le_opNorm w
    _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg f)
    _ = ‖f‖ := mul_one _

theorem weakNull_of_coordinateDisjoint (u : ℕ → C0Sum V)
    (hd : CoordinateDisjoint V u) (hu : ∀ j, ‖u j‖ ≤ 1) : WeakNull u := by
  intro f
  have ht := (summable_abs_evaluation V u hd hu f).tendsto_atTop_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using ht

end C0Sum
end BanachGeometry
