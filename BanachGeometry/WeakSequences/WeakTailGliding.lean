import BanachGeometry.WeakSequences.L1DualBlocks
import BanachGeometry.WeakSequences.WeakTailReduction

/-! R6 Lemma 4.1: gliding-hump construction for the weak-null case.
All selections below are ordinary classical choices from proved existential
statements. The weakly Cauchy case follows through WeakTailReduction.
Local execution evidence is recorded in the external qualification receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace WeakTailGliding

variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℝ (V i)]

structure State where
  cutoff : ℕ
  index : ℕ
  coeff : ∀ i, V i →L[ℝ] ℝ
  bound : ∀ i, ‖coeff i‖ ≤ 1
  support : ∀ i, cutoff ≤ i → coeff i = 0

def initial : State V where
  cutoff := 0
  index := 0
  coeff := fun _ => 0
  bound := fun _ => by simp
  support := fun _ _ => rfl

structure Context where
  u : ℕ → L1Sum V
  ε : ℝ
  positive : 0 < ε
  weakNull : WeakNull u
  persistent : ∀ m N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ ‖L1Tails.tail V m (u n)‖

namespace Context
variable {V} (d : Context V)

structure Step (s : State V) where
  next : State V
  cutoff_lt : s.cutoff < next.cutoff
  index_lt : s.index < next.index
  agrees : ∀ i, i < s.cutoff → next.coeff i = s.coeff i
  norming : ∀ i, s.cutoff ≤ i → i < next.cutoff →
    next.coeff i (d.u next.index i) = ‖d.u next.index i‖
  past_small : ‖L1DualBlocks.functional V s.coeff s.bound (d.u next.index)‖ < d.ε / 8
  tail_large : d.ε ≤ ‖L1Tails.tail V s.cutoff (d.u next.index)‖
  tail_small : ‖L1Tails.tail V next.cutoff (d.u next.index)‖ < d.ε / 8

theorem step_exists (s : State V) : Nonempty (d.Step s) := by
  have hε : 0 < d.ε / 8 := div_pos d.positive (by norm_num)
  have hprev : Tendsto (fun n => ‖L1DualBlocks.functional V s.coeff s.bound (d.u n)‖)
      atTop (nhds 0) := by
    simpa only [norm_zero] using (d.weakNull (L1DualBlocks.functional V s.coeff s.bound)).norm
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hprev.eventually (eventually_lt_nhds hε))
  obtain ⟨n, hn, hlarge⟩ := d.persistent s.cutoff (max (s.index + 1) M)
  have hindex : s.index < n := by omega
  have hpast := hM n (le_trans (le_max_right _ _) hn)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((L1Tails.tendsto_norm_tail V (d.u n)).eventually (eventually_lt_nhds hε))
  let q := max (s.cutoff + 1) N
  have hq : s.cutoff < q := by dsimp [q]; omega
  have htail : ‖L1Tails.tail V q (d.u n)‖ < d.ε / 8 := hN q (le_max_right _ _)
  obtain ⟨ψ, hψ, hψnorm⟩ := L1DualBlocks.exists_norming_family V (d.u n)
  let φ : ∀ i, V i →L[ℝ] ℝ := fun i =>
    if i < s.cutoff then s.coeff i else if i < q then ψ i else 0
  have hφ : ∀ i, ‖φ i‖ ≤ 1 := by
    intro i; dsimp [φ]; split_ifs
    · exact s.bound i
    · exact hψ i
    · simp
  let t : State V := {
    cutoff := q, index := n, coeff := φ, bound := hφ,
    support := by
      intro i hi
      have hi' : ¬ i < s.cutoff := by omega
      simp only [φ, if_neg hi', if_neg (Nat.not_lt.mpr hi)] }
  refine ⟨{
    next := t
    cutoff_lt := hq
    index_lt := hindex
    agrees := ?_
    norming := ?_
    past_small := hpast
    tail_large := hlarge
    tail_small := htail }⟩
  · intro i hi
    change φ i = s.coeff i
    simp only [φ, if_pos hi]
  · intro i hlo hhi
    change φ i (d.u n i) = ‖d.u n i‖
    change i < q at hhi
    simp only [φ, if_neg (Nat.not_lt.mpr hlo), if_pos hhi, hψnorm i]

def step (s : State V) : d.Step s := Classical.choice (d.step_exists s)

def state : ℕ → State V
  | 0 => initial V
  | n + 1 => (d.step (state n)).next

def q (j : ℕ) : ℕ := (d.state j).cutoff
def selected (j : ℕ) : ℕ := (d.state (j + 1)).index

theorem q_strictMono : StrictMono d.q := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (d.step (d.state j)).cutoff_lt

theorem selected_strictMono : StrictMono d.selected := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (d.step (d.state (j + 1))).index_lt

theorem agrees_step (j i : ℕ) (hi : i < d.q j) :
    (d.state (j + 1)).coeff i = (d.state j).coeff i :=
  (d.step (d.state j)).agrees i hi

theorem coefficient_stable (j k i : ℕ) (hjk : j ≤ k) (hi : i < d.q j) :
    (d.state k).coeff i = (d.state j).coeff i := by
  induction k generalizing j with
  | zero =>
    have hj : j = 0 := by omega
    subst j; rfl
  | succ k ih =>
    by_cases hj : j ≤ k
    · have hik : i < d.q k := lt_of_lt_of_le hi (d.q_strictMono.monotone hj)
      exact (d.agrees_step k i hik).trans (ih j hj hi)
    · have hj' : j = k + 1 := by omega
      subst j; rfl

/-- For each coordinate, stage i+1 is already past it. Later stages agree. -/
def globalCoeff (i : ℕ) : V i →L[ℝ] ℝ := (d.state (i + 1)).coeff i

theorem global_bound (i : ℕ) : ‖d.globalCoeff i‖ ≤ 1 := (d.state (i + 1)).bound i

theorem global_agrees (j i : ℕ) (hi : i < d.q j) :
    d.globalCoeff i = (d.state j).coeff i := by
  have hi' : i < d.q (i + 1) := lt_of_lt_of_le (Nat.lt_succ_self i) (d.q_strictMono.id_le (i + 1))
  let k := max j (i + 1)
  exact (d.coefficient_stable (i + 1) k i (le_max_right _ _) hi').symm.trans
    (d.coefficient_stable j k i (le_max_left _ _) hi)

def functional : L1Sum V →L[ℝ] ℝ := L1DualBlocks.functional V d.globalCoeff d.global_bound

theorem past_evaluation (j : ℕ) (x : L1Sum V) :
    d.functional (L1Tails.head V (d.q j) x) =
      L1DualBlocks.functional V (d.state j).coeff (d.state j).bound x := by
  change (∑' i, d.globalCoeff i (L1Tails.head V (d.q j) x i)) =
    ∑' i, (d.state j).coeff i (x i)
  apply tsum_congr
  intro i
  rw [L1Tails.head_apply]
  by_cases hi : i < d.q j
  · rw [if_pos hi, d.global_agrees j i hi]
  · rw [if_neg hi, map_zero, (d.state j).support i (Nat.le_of_not_gt hi)]
    simp

def middle (j : ℕ) (x : L1Sum V) : L1Sum V :=
  L1Tails.head V (d.q (j + 1)) x - L1Tails.head V (d.q j) x

theorem middle_evaluation (j : ℕ) :
    d.functional (d.middle j (d.u (d.selected j))) = ‖d.middle j (d.u (d.selected j))‖ := by
  rw [functional, L1DualBlocks.functional_apply, l1_norm_eq_tsum]
  apply tsum_congr
  intro i
  change d.globalCoeff i
      (L1Tails.head V (d.q (j + 1)) (d.u (d.selected j)) i -
       L1Tails.head V (d.q j) (d.u (d.selected j)) i) = _
  rw [L1Tails.head_apply, L1Tails.head_apply]
  by_cases hlo : i < d.q j
  · have hhi : i < d.q (j + 1) := lt_trans hlo (d.q_strictMono (Nat.lt_succ_self j))
    simp only [if_pos hlo, if_pos hhi, sub_self, map_zero]
    change (0 : ℝ) = ‖d.middle j (d.u (d.selected j)) i‖
    simp only [middle, lp.coeFn_sub, Pi.sub_apply, L1Tails.head_apply,
      if_pos hlo, if_pos hhi, sub_self, norm_zero]
  · by_cases hhi : i < d.q (j + 1)
    · rw [if_neg hlo, if_pos hhi, sub_zero, d.global_agrees (j + 1) i hhi]
      have hn := (d.step (d.state j)).norming i (Nat.le_of_not_gt hlo) hhi
      change (d.state (j + 1)).coeff i (d.u (d.selected j) i) =
        ‖d.u (d.selected j) i‖ at hn
      simpa only [middle, lp.coeFn_sub, Pi.sub_apply, L1Tails.head_apply,
        if_neg hlo, if_pos hhi, sub_zero] using hn
    · simp only [if_neg hlo, if_neg hhi, sub_self, map_zero]
      change (0 : ℝ) = ‖d.middle j (d.u (d.selected j)) i‖
      simp only [middle, lp.coeFn_sub, Pi.sub_apply, L1Tails.head_apply,
        if_neg hlo, if_neg hhi, sub_self, norm_zero]

theorem positive_evaluation (j : ℕ) : 5 * d.ε / 8 ≤ d.functional (d.u (d.selected j)) := by
  let x := d.u (d.selected j)
  let pre := L1Tails.head V (d.q j) x
  let mid := d.middle j x
  let post := L1Tails.tail V (d.q (j + 1)) x
  have hpast : ‖d.functional pre‖ < d.ε / 8 := by
    rw [past_evaluation]
    exact (d.step (d.state j)).past_small
  have hpost : ‖d.functional post‖ < d.ε / 8 :=
    (L1DualBlocks.norm_eval_sum_le V d.globalCoeff d.global_bound post).trans_lt
      (d.step (d.state j)).tail_small
  have htail : d.ε ≤ ‖L1Tails.tail V (d.q j) x‖ := (d.step (d.state j)).tail_large
  have hpostnorm : ‖post‖ < d.ε / 8 := (d.step (d.state j)).tail_small
  have hsplit : L1Tails.tail V (d.q j) x = mid + post := by
    change x - L1Tails.head V (d.q j) x =
      (L1Tails.head V (d.q (j + 1)) x - L1Tails.head V (d.q j) x) +
      (x - L1Tails.head V (d.q (j + 1)) x)
    abel
  have hmidnorm : 7 * d.ε / 8 ≤ ‖mid‖ := by
    have hn := norm_add_le mid post
    rw [← hsplit] at hn
    linarith
  have hmid : d.functional mid = ‖mid‖ := d.middle_evaluation j
  have hsum : x = pre + mid + post := by
    change x = L1Tails.head V (d.q j) x +
      (L1Tails.head V (d.q (j + 1)) x - L1Tails.head V (d.q j) x) +
      (x - L1Tails.head V (d.q (j + 1)) x)
    abel
  have hsumF : d.functional x = d.functional pre + d.functional mid + d.functional post := by
    conv_lhs => rw [hsum]
    rw [map_add, map_add]
  have hp := (abs_le.mp (le_of_lt (show |d.functional pre| < d.ε / 8 from hpast))).1
  have hq := (abs_le.mp (le_of_lt (show |d.functional post| < d.ε / 8 from hpost))).1
  change 5 * d.ε / 8 ≤ d.functional x
  linarith

include d in
theorem impossible : False := by
  apply L1DualBlocks.not_weakNull_of_separated_functional V d.selected d.selected_strictMono
    d.functional (5 * d.ε / 8) (by linarith [d.positive]) d.positive_evaluation d.weakNull

end Context

theorem persistent_bad_tail (u : ℕ → L1Sum V) (ε : ℝ) (hε : 0 < ε)
    (hbad : ∀ m : ℕ, ∃ n : ℕ, ε ≤ ‖L1Tails.tail V m (u n)‖) :
    ∀ m N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ ‖L1Tails.tail V m (u n)‖ := by
  intro m N
  obtain ⟨q, hqN, hsmall⟩ := L1Tails.finite_vectors_tail_small V u N ε hε
  let r := max m q
  obtain ⟨n, hn⟩ := hbad r
  have hnN : N < n := by
    by_contra hnot
    have hle : n ≤ N := by omega
    have hs : ‖L1Tails.tail V r (u n)‖ < ε :=
      (L1Tails.norm_tail_antitone V (u n) (le_max_right m q)).trans_lt (hsmall n hle)
    exact hn.not_gt hs
  refine ⟨n, hnN.le, ?_⟩
  exact hn.trans (L1Tails.norm_tail_antitone V (u n) (le_max_left m q))

/-- Weak-null sequences have uniform ℓ₁ tails. No weak compactness,
finite-dimensionality of the coordinate spaces, or separable dual is assumed. -/
theorem hasUniformlySmallTails_of_weakNull (u : ℕ → L1Sum V) (hu : WeakNull u) :
    L1Tails.HasUniformlySmallTails V (Set.range u) := by
  classical
  by_contra hfail
  unfold L1Tails.HasUniformlySmallTails at hfail
  push_neg at hfail
  obtain ⟨ε, hε, hbad⟩ := hfail
  have hbad' : ∀ m, ∃ n, ε ≤ ‖L1Tails.tail V m (u n)‖ := by
    intro m
    obtain ⟨x, hx, hnorm⟩ := hbad m
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, hnorm⟩
  let d : Context V := {
    u := u, ε := ε, positive := hε, weakNull := hu,
    persistent := persistent_bad_tail V u ε hε hbad' }
  exact d.impossible

/-- R6 Lemma 4.1, expressed without a real-valued supremum convention. -/
theorem hasUniformlySmallTails_of_weaklyCauchy (u : ℕ → L1Sum V) (hu : WeaklyCauchy u) :
    L1Tails.HasUniformlySmallTails V (Set.range u) :=
  L1Tails.uniform_of_weaklyCauchy_of_weakNull_case V (hasUniformlySmallTails_of_weakNull V) u hu

theorem eventually_uniform_tail_bound_of_weaklyCauchy (u : ℕ → L1Sum V) (hu : WeaklyCauchy u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, ‖L1Tails.tail V m (u n)‖ < ε := by
  obtain ⟨N, hN⟩ := L1Tails.hasUniformlySmallTails_eventually V (hasUniformlySmallTails_of_weaklyCauchy V u hu) ε hε
  exact ⟨N, fun m hm n => hN m hm _ (Set.mem_range_self n)⟩

/-- R6 4.2 now needs only the domain subsequence input; its weak ℓ₁ tail
input is supplied by the preceding explicit construction. -/
theorem operator_norm_tails_of_domain_subsequences
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : B →L[ℝ] L1Sum V)
    (hsub : ∀ u : ℕ → B, (∀ n, ‖u n‖ ≤ 1) →
      ∃ s : ℕ → ℕ, StrictMono s ∧ WeaklyCauchy (u ∘ s)) :
    Tendsto (fun m => ‖(L1Tails.tail V m).comp T‖) atTop (nhds 0) :=
  L1Tails.tendsto_opNorm_tail_comp_of_weaklyCauchy_subseq V T (hasUniformlySmallTails_of_weaklyCauchy V) hsub

end WeakTailGliding
end BanachGeometry
