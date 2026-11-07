import BanachGeometry.SequenceSpaces.C0Blocks
import BanachGeometry.Complemented.CornerAssembly
import BanachGeometry.WeakSequences.WeakTailGliding

/-! R6 Lemma 5.1 and finite-coordinate localization, with proof bodies.
The corner estimate is proved from disjoint c₀ blocks and weak ℓ₁ tails.
Neither the dual of the heterogeneous c₀ sum nor an unproved scalar-c₀
duality identification is an input..
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace Corner
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

def operator (T : C0Sum V →L[ℝ] L1Shifts.F E) (m n : ℕ) :
    C0Sum V →L[ℝ] L1Shifts.F E :=
  (L1Tails.tail (fun _ : ℕ => E) m).comp (T.comp (C0Sum.tailCLM V n))

theorem opNorm_operator_mono (T : C0Sum V →L[ℝ] L1Shifts.F E)
    {m k n l : ℕ} (hmk : m ≤ k) (hnl : n ≤ l) :
    ‖operator E V T k l‖ ≤ ‖operator E V T m n‖ := by
  apply (operator E V T k l).opNorm_le_bound (norm_nonneg (operator E V T m n))
  intro x
  change ‖L1Tails.tail (fun _ : ℕ => E) k (T (C0Sum.tailCLM V l x))‖ ≤ _
  calc
    _ ≤ ‖L1Tails.tail (fun _ : ℕ => E) m (T (C0Sum.tailCLM V l x))‖ :=
      L1Tails.norm_tail_antitone (fun _ : ℕ => E) _ hmk
    _ = ‖operator E V T m n (C0Sum.tailCLM V l x)‖ := by
      change _ = ‖L1Tails.tail (fun _ : ℕ => E) m
        (T (C0Sum.tailCLM V n (C0Sum.tailCLM V l x)))‖
      rw [C0Sum.tailCLM_tailCLM_of_le V n l hnl]
    _ ≤ ‖operator E V T m n‖ * ‖C0Sum.tailCLM V l x‖ :=
      (operator E V T m n).le_opNorm _
    _ ≤ ‖operator E V T m n‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left (C0Sum.norm_tailCLM_le V l x) (norm_nonneg (operator E V T m n))

structure BadData where
  T : C0Sum V →L[ℝ] L1Shifts.F E
  ε : ℝ
  positive : 0 < ε
  lower : ∀ m n, ε ≤ ‖operator E V T m n‖

namespace BadData
variable {E V} (d : BadData E V)

structure Step (j n : ℕ) where
  next : ℕ
  next_gt : n < next
  u : C0Sum V
  bound : ‖u‖ ≤ 1
  zero_before : ∀ i, i < n → u i = 0
  zero_after : ∀ i, next ≤ i → u i = 0
  separated : d.ε / 4 < ‖L1Tails.tail (fun _ : ℕ => E) j (d.T u)‖

theorem step_exists (j n : ℕ) : Nonempty (d.Step j n) := by
  have hε : 0 < d.ε / 4 := div_pos d.positive (by norm_num)
  have hw : ∃ x : C0Sum V, ‖x‖ ≤ 1 ∧ d.ε / 2 < ‖operator E V d.T j n x‖ := by
    by_contra h
    push_neg at h
    have hnorm : ‖operator E V d.T j n‖ ≤ d.ε / 2 := by
      apply L1Tails.opNorm_le_of_unit_bound (fun _ : ℕ => E) _ (d.ε / 2) (by linarith [d.positive])
      intro x hx
      exact h x hx
    have hl := d.lower j n
    linarith [d.positive]
  obtain ⟨x, hx, hlarge⟩ := hw
  let v := C0Sum.tailCLM V n x
  have hv : ‖v‖ ≤ 1 := (C0Sum.norm_tailCLM_le V n x).trans hx
  have ht : Tendsto (fun k => ‖d.T‖ * ‖C0Sum.tailCLM V k v‖) atTop (nhds 0) := by
    simpa only [mul_zero] using (C0Sum.tendsto_norm_tailCLM V v).const_mul ‖d.T‖
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (eventually_lt_nhds hε))
  let k := max (n + 1) N
  let u := C0Sum.head V k v
  have hkn : n < k := by dsimp [k]; omega
  have herror : ‖L1Tails.tail (fun _ : ℕ => E) j (d.T (v - u))‖ < d.ε / 4 := by
    calc
      _ ≤ ‖d.T (v - u)‖ := L1Tails.norm_tail_le (fun _ : ℕ => E) j _
      _ ≤ ‖d.T‖ * ‖v - u‖ := d.T.le_opNorm _
      _ = ‖d.T‖ * ‖C0Sum.tailCLM V k v‖ := rfl
      _ < d.ε / 4 := hN k (le_max_right _ _)
  have hsep : d.ε / 4 < ‖L1Tails.tail (fun _ : ℕ => E) j (d.T u)‖ := by
    have hsub := norm_sub_norm_le
      (L1Tails.tail (fun _ : ℕ => E) j (d.T v))
      (L1Tails.tail (fun _ : ℕ => E) j (d.T u))
    have heq : L1Tails.tail (fun _ : ℕ => E) j (d.T (v - u)) =
        L1Tails.tail (fun _ : ℕ => E) j (d.T v) -
        L1Tails.tail (fun _ : ℕ => E) j (d.T u) := by rw [map_sub, map_sub]
    rw [← heq] at hsub
    change d.ε / 2 < ‖L1Tails.tail (fun _ : ℕ => E) j (d.T v)‖ at hlarge
    linarith
  refine ⟨{
    next := k
    next_gt := hkn
    u := u
    bound := (C0Sum.norm_head_le V k v).trans hv
    zero_before := ?_
    zero_after := ?_
    separated := hsep }⟩
  · intro i hi
    have hik : i < k := lt_trans hi hkn
    change C0Sum.head V k v i = 0
    rw [C0Sum.head_apply, if_pos hik]
    change C0Sum.tailCLM V n x i = 0
    rw [C0Sum.tailCLM_apply_coord, if_pos hi]
  · intro i hi
    change C0Sum.head V k v i = 0
    rw [C0Sum.head_apply, if_neg (Nat.not_lt.mpr hi)]

def step (j n : ℕ) : d.Step j n := Classical.choice (d.step_exists j n)

def cutoff : ℕ → ℕ
  | 0 => 0
  | j + 1 => (d.step j (cutoff j)).next

def block (j : ℕ) : C0Sum V := (d.step j (d.cutoff j)).u

theorem cutoff_strictMono : StrictMono d.cutoff := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (d.step j (d.cutoff j)).next_gt

theorem block_norm_le (j : ℕ) : ‖d.block j‖ ≤ 1 := (d.step j (d.cutoff j)).bound

theorem block_zero_before (j i : ℕ) (hi : i < d.cutoff j) : d.block j i = 0 :=
  (d.step j (d.cutoff j)).zero_before i hi

theorem block_zero_after (j i : ℕ) (hi : d.cutoff (j + 1) ≤ i) : d.block j i = 0 :=
  (d.step j (d.cutoff j)).zero_after i hi

theorem block_disjoint : C0Sum.CoordinateDisjoint V d.block := by
  intro j k hjk i
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · by_cases hi : i < d.cutoff k
    · exact Or.inr (d.block_zero_before k i hi)
    · apply Or.inl
      apply d.block_zero_after j i
      exact (d.cutoff_strictMono.monotone (by omega : j + 1 ≤ k)).trans (Nat.le_of_not_gt hi)
  · by_cases hi : i < d.cutoff j
    · exact Or.inl (d.block_zero_before j i hi)
    · apply Or.inr
      apply d.block_zero_after k i
      exact (d.cutoff_strictMono.monotone (by omega : k + 1 ≤ j)).trans (Nat.le_of_not_gt hi)

include d in
theorem impossible : False := by
  have hw : WeakNull d.block := C0Sum.weakNull_of_coordinateDisjoint V d.block
    d.block_disjoint d.block_norm_le
  have hc : WeaklyCauchy (fun j => d.T (d.block j)) := by
    intro f
    exact (hw (f.comp d.T)).cauchySeq
  obtain ⟨N, hN⟩ := WeakTailGliding.eventually_uniform_tail_bound_of_weaklyCauchy
    (fun _ : ℕ => E) (fun j => d.T (d.block j)) hc (d.ε / 4) (by linarith [d.positive])
  have hsmall := hN N le_rfl N
  have hlarge := (d.step N (d.cutoff N)).separated
  exact hlarge.not_ge hsmall.le

end BadData

/-- R6 5.1. The proof needs no separability assumption on any V i or its dual. -/
theorem jointCorner (T : C0Sum V →L[ℝ] L1Shifts.F E) : Localization.JointCorner E V T := by
  classical
  by_contra hfail
  unfold Localization.JointCorner at hfail
  push_neg at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  have hlower : ∀ m n, ε ≤ ‖operator E V T m n‖ := by
    intro m n
    obtain ⟨k, hmk, l, hnl, hkl⟩ := hbad m n
    exact hkl.trans (opNorm_operator_mono E V T hmk hnl)
  let d : BadData E V := ⟨T, ε, hε, hlower⟩
  exact d.impossible

/-- R6 5.2, now without an assumed corner estimate. -/
theorem finite_head_localization (h : ContainsComplementedCopy (L1Shifts.F E) (C0Sum V)) :
    ∃ n : ℕ, ContainsComplementedCopy (L1Shifts.F E) (C0Sum.FiniteHead V n) := by
  obtain ⟨J, T, hTJ⟩ := h
  exact Localization.finite_head_of_joint_corner E V J T hTJ (jointCorner E V T)

theorem no_complemented_of_finite_heads
    (hheads : ∀ n, ¬ ContainsComplementedCopy (L1Shifts.F E) (C0Sum.FiniteHead V n)) :
    ¬ ContainsComplementedCopy (L1Shifts.F E) (C0Sum V) := by
  intro h
  obtain ⟨n, hn⟩ := finite_head_localization E V h
  exact hheads n hn

end Corner

namespace AlmostIsometricFamily
theorem exists_almostIsometric_nonisomorphic_pair_of_head_exclusions (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy)
    (hheads : ∀ n, ¬ ContainsComplementedCopy L1C0L2 (C0Sum.FiniteHead (fun k => d.Z k) n)) :
    ExistsAlmostIsometricNonisomorphicPair := by
  apply d.exists_almostIsometric_nonisomorphic_pair_of_complemented_obstruction h2
  exact Corner.no_complemented_of_finite_heads C0L2 (fun k => d.Z k) hheads
end AlmostIsometricFamily
end BanachGeometry
