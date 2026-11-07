import BanachGeometry.AlmostIsometric.Insertion
import BanachGeometry.SequenceSpaces.C0Banach
import Mathlib.Topology.MetricSpace.Cauchy

/-! R6 Remark 5.4, first observation: the specific insertion maps have a
uniformly separated image of one point and no norm-Cauchy subsequence.
This uses H1 alone and is separate from the Mazur–Ulam nonattainment proof.
The point and the two spaces/norms are fixed before the index.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace AlmostIsometricFamily

theorem exists_global_bound (d : AlmostIsometricFamily) : ∃ C : ℝ, 1 ≤ C ∧ ∀ i, d.bound i ≤ C := by
  obtain ⟨N,hN⟩ := d.exists_tail_bound 1 zero_lt_one
  let C := 2 + ∑ i ∈ Finset.range N, ‖d.bound i‖
  have hs : 0 ≤ ∑ i ∈ Finset.range N, ‖d.bound i‖ := Finset.sum_nonneg (fun i hi => norm_nonneg _)
  refine ⟨C,by change 1 ≤ 2 + ∑ i ∈ Finset.range N, ‖d.bound i‖; linarith,?_⟩
  intro i
  by_cases hi : i < N
  · have hsingle := Finset.single_le_sum (fun j hj => norm_nonneg (d.bound j)) (Finset.mem_range.mpr hi)
    have hi' : d.bound i ≤ ‖d.bound i‖ := le_abs_self _
    change d.bound i ≤ 2 + ∑ j ∈ Finset.range N, ‖d.bound j‖
    linarith
  · have ht := hN i (Nat.le_of_not_gt hi)
    change d.bound i ≤ 2 + ∑ j ∈ Finset.range N, ‖d.bound j‖
    linarith

theorem nearEquiv_of_extra (d : AlmostIsometricFamily) (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (z : d.ZInfty) :
    (d.nearEquiv N C hC htail).equiv (z,0) =
      C0Sum.single N ((d.intoRow N C hC htail).equiv z) := by
  apply C0Sum.ext
  intro k
  obtain ⟨j,rfl⟩ := (branchIndexEquiv N).surjective k
  cases j with
  | none =>
    change (d.nearEquiv N C hC htail).equiv (z,0) N =
      (C0Sum.single N ((d.intoRow N C hC htail).equiv z) : d.FixedY) N
    rw [d.nearEquiv_at_inserted, C0Sum.single_apply_self]
  | some j =>
    rw [d.nearEquiv_at_old_branch]
    have hne : branchIndexEquiv N (some j) ≠ N := by
      intro h
      have he : branchIndexEquiv N (some j) = branchIndexEquiv N none := h
      have hf := (branchIndexEquiv N).injective he
      cases hf
    rw [C0Sum.single_apply_ne N _ hne]
    exact (d.insertionComponent N C hC htail (some j)).zero_eq

theorem insertion_images_separated (d : AlmostIsometricFamily) (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ i, d.bound i ≤ C) (z : d.ZInfty) (N M : ℕ) (hNM : N ≠ M) :
    ‖z‖/C ≤ ‖(d.nearEquiv N C hC (fun i hi => hbound i)).equiv (z,0) -
      (d.nearEquiv M C hC (fun i hi => hbound i)).equiv (z,0)‖ := by
  let a := (d.intoRow N C hC (fun i hi => hbound i)).equiv z
  have hinv : ‖z‖ ≤ C*‖a‖ := by
    have h := (d.intoRow N C hC (fun i hi => hbound i)).symm_norm_le a
    simpa only [a, Equiv.symm_apply_apply] using h
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hfirst : ‖z‖/C ≤ ‖a‖ := (div_le_iff₀ hCp).mpr (by nlinarith)
  apply hfirst.trans
  let w := (d.nearEquiv N C hC (fun i hi => hbound i)).equiv (z,0) -
    (d.nearEquiv M C hC (fun i hi => hbound i)).equiv (z,0)
  have he : ‖w N‖ ≤ ‖w‖ := w.norm_apply_le N
  have hw : w N = a := by
    change ((d.nearEquiv N C hC (fun i hi => hbound i)).equiv (z,0) -
    (d.nearEquiv M C hC (fun i hi => hbound i)).equiv (z,0)) N
      = a
    rw [nearEquiv_of_extra, nearEquiv_of_extra, C0Sum.sub_apply,
      C0Sum.single_apply_self, C0Sum.single_apply_ne M _ hNM, sub_zero]
  rw [hw] at he
  exact he

theorem insertion_images_no_cauchy_subsequence (d : AlmostIsometricFamily) (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ i, d.bound i ≤ C) (z : d.ZInfty) (hz : z ≠ 0)
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ¬ CauchySeq (fun n => (d.nearEquiv (s n) C hC (fun i hi => hbound i)).equiv (z,0)) := by
  intro hc
  have hδ : 0 < ‖z‖/C := div_pos (norm_pos_iff.mpr hz) (lt_of_lt_of_le zero_lt_one hC)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc _ hδ
  have hclose := hN N le_rfl (N+1) (Nat.le_succ N)
  have hsep := d.insertion_images_separated C hC hbound z (s N) (s (N+1))
    (ne_of_lt (hs (Nat.lt_succ_self N)))
  rw [dist_eq_norm] at hclose
  exact hsep.not_gt hclose

end AlmostIsometricFamily
end BanachGeometry
