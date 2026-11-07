import BanachGeometry.SequenceSpaces.L1Map
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Compactness.Compact

open scoped ENNReal

/-! # Actual ℓ₁ head and tail operators

R6 §4 support. A head of length m keeps n<m; R_m keeps
n≥m. We prove the coordinate identities, contractivity, monotonicity, exact
tail norm, pointwise norm convergence, and uniform tails on norm-compact sets.
Norm-compactness is not substituted for weak precompactness in R6 Lemma 4.1.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace L1Tails

variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

def head (m : ℕ) : L1Sum V →L[ℝ] L1Sum V :=
  ∑ i ∈ Finset.range m,
    (lp.singleContinuousLinearMap ℝ V 1 i).comp (lp.evalCLM ℝ V 1 i)

theorem head_eq_sum (m : ℕ) (x : L1Sum V) :
    head V m x = ∑ i ∈ Finset.range m, lp.single 1 i (x i) := by
  simp [head, lp.evalCLM]

theorem head_apply (m : ℕ) (x : L1Sum V) (i : ℕ) :
    head V m x i = if i < m then x i else 0 := by
  induction m with
  | zero => simp [head]
  | succ m ih =>
    have hs : head V (m + 1) x = head V m x + lp.single 1 m (x m) := by
      simp only [head_eq_sum, Finset.sum_range_succ]
    rw [hs]
    change head V m x i + lp.single 1 m (x m) i = _
    rw [ih]
    by_cases he : i = m
    · subst i; simp [lp.single_apply_self]
    · rw [lp.single_apply_ne 1 m (x m) he, add_zero]
      by_cases hi : i < m
      · simp [hi, show i < m + 1 by omega]
      · simp [hi, show ¬ i < m + 1 by omega]

def tail (m : ℕ) : L1Sum V →L[ℝ] L1Sum V := ContinuousLinearMap.id ℝ (L1Sum V) - head V m

theorem tail_eq_sub_head (m : ℕ) (x : L1Sum V) : tail V m x = x - head V m x := rfl

theorem tail_apply (m : ℕ) (x : L1Sum V) (i : ℕ) :
    tail V m x i = if i < m then 0 else x i := by
  change x i - head V m x i = _
  rw [head_apply]
  split_ifs <;> simp

theorem tail_zero (x : L1Sum V) : tail V 0 x = x := by
  apply lp.ext; funext i; simp [tail_apply]

theorem norm_tail_le (m : ℕ) (x : L1Sum V) : ‖tail V m x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  intro i
  rw [tail_apply]
  split_ifs
  · simpa using norm_nonneg (x i)
  · exact le_rfl

theorem opNorm_tail_le (m : ℕ) : ‖tail V m‖ ≤ 1 :=
  (tail V m).opNorm_le_bound zero_le_one (fun x => by simpa using norm_tail_le V m x)

theorem norm_tail_antitone (x : L1Sum V) : Antitone (fun m => ‖tail V m x‖) := by
  intro m n hmn
  apply lp.norm_mono (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  intro i
  rw [tail_apply, tail_apply]
  by_cases hi : i < n
  · simp only [if_pos hi, norm_zero]
    exact norm_nonneg _
  · have hi' : ¬ i < m := by omega
    simp only [if_neg hi, if_neg hi']
    exact le_rfl

theorem tail_tail (m n : ℕ) (x : L1Sum V) :
    tail V m (tail V n x) = tail V (max m n) x := by
  apply lp.ext
  funext i
  simp only [tail_apply]
  by_cases hm : i < m <;> by_cases hn : i < n <;>
    simp [hm, hn, lt_max_iff]

/-- The remaining norm is the total norm minus the actual finite ℓ₁ head. -/
theorem norm_tail_eq_sub_sum (m : ℕ) (x : L1Sum V) :
    ‖tail V m x‖ = ‖x‖ - ∑ i ∈ Finset.range m, ‖x i‖ := by
  rw [tail_eq_sub_head, head_eq_sum]
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp.norm_compl_sum_single (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x (Finset.range m)

theorem tendsto_head (x : L1Sum V) : Tendsto (fun m => head V m x) atTop (nhds x) := by
  simpa only [head_eq_sum] using (lp.hasSum_single (p := 1) (by simp) x).tendsto_sum_nat

/-- Each fixed vector has norm-null tails. Uniformity over weakly Cauchy
sequences of different vectors is proved separately in WeakTailGliding. -/
theorem tendsto_tail (x : L1Sum V) : Tendsto (fun m => tail V m x) atTop (nhds 0) := by
  simpa only [tail_eq_sub_head, sub_self] using
    (tendsto_const_nhds.sub (tendsto_head V x) :
      Tendsto (fun m => x - head V m x) atTop (nhds (x - x)))

theorem tendsto_norm_tail (x : L1Sum V) :
    Tendsto (fun m => ‖tail V m x‖) atTop (nhds 0) := by
  simpa only [norm_zero] using (tendsto_tail V x).norm

/-- Uniform-tail smallness at one cutoff; contractivity of deletion gives
every later cutoff, as recorded by hasUniformlySmallTails_eventually. -/
def HasUniformlySmallTails (K : Set (L1Sum V)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ x ∈ K, ‖tail V m x‖ < ε

theorem hasUniformlySmallTails_eventually {K : Set (L1Sum V)} (hK : HasUniformlySmallTails V K)
    (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ m, N ≤ m → ∀ x ∈ K, ‖tail V m x‖ < ε := by
  obtain ⟨N, hN⟩ := hK ε hε
  exact ⟨N, fun m hm x hx => (norm_tail_antitone V x hm).trans_lt (hN x hx)⟩

theorem hasUniformlySmallTails_mono {K S : Set (L1Sum V)} (hK : HasUniformlySmallTails V K) (hSK : S ⊆ K) : HasUniformlySmallTails V S := by
  intro ε hε
  obtain ⟨m, hm⟩ := hK ε hε
  exact ⟨m, fun x hx => hm x (hSK hx)⟩

/-- Finite ball covers promote the pointwise estimates to norm-compact sets. -/
theorem hasUniformlySmallTails_of_isCompact {K : Set (L1Sum V)} (hK : IsCompact K) : HasUniformlySmallTails V K := by
  classical
  intro ε hε
  have hcover : K ⊆ ⋃ y : K, Metric.ball y.1 (ε / 2) := by
    intro x hx
    apply Set.mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, by simpa only [Metric.mem_ball, dist_self] using half_pos hε⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun y : K => Metric.ball y.1 (ε / 2))
    (fun _ => Metric.isOpen_ball) hcover
  have ht : ∀ᶠ m in atTop, ∀ y ∈ s, ‖tail V m y.1‖ < ε / 2 := by
    apply (Filter.eventually_all_finset s).2
    intro y hy
    exact (tendsto_norm_tail V y.1).eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ht
  refine ⟨N, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (hs hx)
  obtain ⟨hys, hxy⟩ := Set.mem_iUnion.1 hy
  have hd : ‖x - y.1‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  calc
    ‖tail V N x‖ = ‖tail V N (x - y.1) + tail V N y.1‖ := by
      rw [← map_add, sub_add_cancel]
    _ ≤ ‖tail V N (x - y.1)‖ + ‖tail V N y.1‖ := norm_add_le _ _
    _ ≤ ‖x - y.1‖ + ‖tail V N y.1‖ := add_le_add (norm_tail_le V N _) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hd (hN N le_rfl y hys)
    _ = ε := add_halves ε

/-- A sequential criterion for uniform tails. TailReduction transports
explicit weak-Cauchy subsequence hypotheses through this criterion, and
WeakTailGliding supplies uniform tails for weakly Cauchy ℓ₁ sequences. -/
theorem hasUniformlySmallTails_of_subsequence {K : Set (L1Sum V)}
    (hsub : ∀ u : ℕ → L1Sum V, (∀ n, u n ∈ K) →
      ∃ s : ℕ → ℕ, StrictMono s ∧ HasUniformlySmallTails V (Set.range (u ∘ s))) : HasUniformlySmallTails V K := by
  classical
  by_contra hfail
  unfold HasUniformlySmallTails at hfail
  push_neg at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  choose u huK hu using hbad
  obtain ⟨s, hs, htail⟩ := hsub u huK
  obtain ⟨N, hN⟩ := htail ε hε
  have hb : ‖tail V N (u (s N))‖ < ε := hN _ (Set.mem_range_self N)
  have hm : N ≤ s N := hs.id_le N
  exact (hu (s N)).not_gt ((norm_tail_antitone V (u (s N)) hm).trans_lt hb)

end L1Tails
end BanachGeometry
