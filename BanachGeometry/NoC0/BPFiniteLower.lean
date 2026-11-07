import BanachGeometry.NoC0.BPSelection
import BanachGeometry.NoC0.BPC0Insertion

/-! The c₀ lower bound from the constructed triangular functionals.
The total geometric error is δ/8 and each diagonal is at least δ/4.
No basic-sequence theorem is assumed.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace BP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_abs_max (a : ℕ → ℝ) (s : Finset ℕ) (hne : s.Nonempty) :
    ∃ j ∈ s, ∀ i ∈ s, |a i| ≤ |a j| := by
  classical
  revert hne
  induction s using Finset.induction_on with
  | empty => intro h; simpa using h
  | @insert j s hjs ih =>
    intro hne
    by_cases hs : s.Nonempty
    · obtain ⟨k,hk,hmax⟩ := ih hs
      by_cases hjk : |a j| ≤ |a k|
      · refine ⟨k,Finset.mem_insert_of_mem hk,?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hjk
        · exact hmax i hi
      · refine ⟨j,Finset.mem_insert_self _ _,?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact le_rfl
        · exact (hmax i hi).trans (lt_of_not_ge hjk).le
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨j,by simp,?_⟩
      intro i hi
      have he : i = j := by simpa using hi
      subst i
      exact le_rfl

theorem mul_abs_le_norm_sum_smul {u : ℕ → E} {δ : ℝ} (hδ : 0 < δ) (d : TriangularData u δ)
    (a : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) (hj : j ∈ s)
    (hmax : ∀ i ∈ s, |a i| ≤ |a j|) :
    (δ/8) * |a j| ≤ ‖∑ i ∈ s, a i • u (d.k i)‖ := by
  classical
  let z := ∑ i ∈ s, a i • u (d.k i)
  let M := |a j|
  let r := ∑ i ∈ s.erase j, a i * d.f j (u (d.k i))
  have hterm (i : ℕ) (hi : i ∈ s.erase j) :
      ‖a i * d.f j (u (d.k i))‖ ≤ (M*δ) * budget i := by
    have his : i ∈ s := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rcases lt_or_gt_of_ne hij with hij | hji
    · rw [d.lower_zero j i hij,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hδ.le) (budget_pos i).le
    · rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul (hmax i his) (d.upper_small j i hji)
        (abs_nonneg _) (abs_nonneg _)).trans_eq (by dsimp [M]; ring)
  have herr : ‖r‖ ≤ M*δ/8 := by
    calc
      _ ≤ ∑ i ∈ s.erase j, ‖a i * d.f j (u (d.k i))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s.erase j, (M*δ)*budget i := Finset.sum_le_sum hterm
      _ ≤ ∑' i, (M*δ)*budget i := (summable_budget.mul_left (M*δ)).sum_le_tsum _
        (fun i hi => mul_nonneg (mul_nonneg (abs_nonneg _) hδ.le) (budget_pos i).le)
      _ = M*δ/8 := by rw [tsum_mul_left,tsum_budget]; ring
  have heval : d.f j z = a j * d.f j (u (d.k j)) + r := by
    dsimp [z]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
    exact (Finset.add_sum_erase s (fun i => a i * d.f j (u (d.k i))) hj).symm
  have hdiag : M*δ/4 ≤ ‖a j * d.f j (u (d.k j))‖ := by
    have hp : 0 ≤ d.f j (u (d.k j)) := (by positivity : 0 ≤ δ/4).trans (d.diag j)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hp]
    calc
      M*δ/4 = M*(δ/4) := by ring
      _ ≤ M*d.f j (u (d.k j)) := mul_le_mul_of_nonneg_left (d.diag j) (abs_nonneg _)
  have htri : ‖a j * d.f j (u (d.k j))‖ ≤ ‖d.f j z‖ + ‖r‖ := by
    have he : a j * d.f j (u (d.k j)) = d.f j z-r := by linarith
    rw [he]
    exact norm_sub_le _ _
  have hnorm : ‖d.f j z‖ ≤ ‖z‖ := (d.f j).le_opNorm z |>.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (d.norm_f_le j) (norm_nonneg z))
  change (δ/8)*M ≤ ‖z‖
  nlinarith

theorem mul_norm_scalarHead_le_norm_image (T : ScalarC0 →L[ℝ] E) (δ : ℝ) (hδ : 0 < δ)
    (d : TriangularData (fun k => T (CanonicalSequences.scalarBasis k)) δ)
    (N : ℕ) (a : ScalarC0) :
    (δ/8)*‖CanonicalSequences.scalarHead N a‖ ≤
      ‖T (insertCLM d.k (CanonicalSequences.scalarHead N a))‖ := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [CanonicalSequences.scalarHead,C0Sum.head]
  · have hnonempty : (Finset.range N).Nonempty := ⟨0,Finset.mem_range.mpr (Nat.pos_of_ne_zero hN)⟩
    obtain ⟨j,hj,hmax⟩ := exists_abs_max (fun i => a i) (Finset.range N) hnonempty
    have hn := norm_scalarHead_le_of_bound N a |a j| (abs_nonneg _) hmax
    have hl := mul_abs_le_norm_sum_smul hδ d (fun i => a i) (Finset.range N) j hj hmax
    apply (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ δ/8)).trans
    rw [insertCLM_scalarHead d.k d.strictMono_k.injective,map_sum]
    simpa only [map_smul] using hl

end BP
end BanachGeometry
