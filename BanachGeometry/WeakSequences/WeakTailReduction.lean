import BanachGeometry.WeakSequences.TailReduction

/-! R6 Lemma 4.1: reduction of the weakly Cauchy case to the explicit
weak-null input hnull, without compactness of the range. WeakTailGliding
constructs the weak-null gliding-hump argument and applies this reduction. -/

noncomputable section
open Filter
namespace BanachGeometry

theorem weaklyCauchy_subsequence_difference {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → E} (hu : WeaklyCauchy u) (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) : WeakNull (fun n => u (s n) - u n) := by
  intro f
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hu f)
  simpa only [map_sub, Function.comp_def, sub_self] using (ha.comp hs).sub ha

namespace L1Tails
variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

theorem finite_vectors_tail_small (u : ℕ → L1Sum V) (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, n ≤ m ∧ ∀ k ≤ n, ‖tail V m (u k)‖ < δ := by
  have he : ∀ᶠ m in atTop, ∀ k ∈ Finset.range (n + 1), ‖tail V m (u k)‖ < δ := by
    apply (Filter.eventually_all_finset _).2
    intro k hk
    exact (tendsto_norm_tail V (u k)).eventually (eventually_lt_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  refine ⟨max n N, le_max_left _ _, ?_⟩
  intro k hk
  exact hN _ (le_max_right _ _) k (Finset.mem_range.mpr (by omega))

/-- Uniform tails for a weakly Cauchy sequence from the explicit weak-null
input hnull. WeakTailGliding.hasUniformlySmallTails_of_weakNull supplies hnull;
no compactness of the range is used in this local reduction. -/
theorem uniform_of_weaklyCauchy_of_weakNull_case
    (hnull : ∀ v : ℕ → L1Sum V, WeakNull v → HasUniformlySmallTails V (Set.range v))
    (u : ℕ → L1Sum V) (hu : WeaklyCauchy u) : HasUniformlySmallTails V (Set.range u) := by
  classical
  by_contra hfail
  unfold HasUniformlySmallTails at hfail
  push_neg at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  have hbad' : ∀ m, ∃ k, ε ≤ ‖tail V m (u k)‖ := by
    intro m
    obtain ⟨x, hx, hnorm⟩ := hbad m
    obtain ⟨k, rfl⟩ := hx
    exact ⟨k, hnorm⟩
  choose m hm hsmall using fun n => finite_vectors_tail_small V u n (ε / 4) (by positivity)
  choose s hsbad using fun n => hbad' (m n)
  have hslarge : ∀ n, n ≤ s n := by
    intro n
    by_contra hn
    have hsn : s n ≤ n := by omega
    have hc := hsmall n (s n) hsn
    have hb := hsbad n
    linarith
  have hs : Tendsto s atTop atTop := tendsto_atTop_mono hslarge tendsto_id
  let v : ℕ → L1Sum V := fun n => u (s n) - u n
  have hv : WeakNull v := weaklyCauchy_subsequence_difference hu s hs
  obtain ⟨M, hM⟩ := hnull v hv (3 * ε / 4) (by positivity)
  have hupper : ‖tail V (m M) (v M)‖ < 3 * ε / 4 :=
    (norm_tail_antitone V (v M) (hm M)).trans_lt (hM _ (Set.mem_range_self M))
  have hlower : ε - ε / 4 < ‖tail V (m M) (v M)‖ := by
    have hb := hsbad M
    have hc := hsmall M M le_rfl
    have hd := norm_sub_norm_le (tail V (m M) (u (s M))) (tail V (m M) (u M))
    change ‖tail V (m M) (u (s M))‖ - ‖tail V (m M) (u M)‖ ≤
      ‖tail V (m M) (u (s M)) - tail V (m M) (u M)‖ at hd
    have heq : tail V (m M) (v M) = tail V (m M) (u (s M)) - tail V (m M) (u M) :=
      (tail V (m M)).map_sub _ _
    rw [← heq] at hd
    linarith
  linarith

end L1Tails
end BanachGeometry
