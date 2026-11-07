/- Provenance adaptation: Hilbert coordinate-null obstruction proof route.
Upstream openai/math@4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean,
OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null. This records proof-route adaptation, not a measured claim of verbatim copying.
Applicable upstream material: Apache-2.0; see LICENSES and THIRD_PARTY_NOTICES.md.
Original-contribution source-license scope is recorded separately. -/
import BanachGeometry.SequenceSpaces.C0Blocks
import BanachGeometry.AlmostIsometric.ApproximationParameters
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! R6 Lemma 6.5 on heterogeneous c₀ sums, for an arbitrary orthonormal
sequence in a real inner product space. Adapted finite-block proof route:
openai/math 4eaee87548250b2682affda7d05d947c05554bae,
GraphObstruction.no_lower_of_coordinate_null, Apache-2.0.
Changes: heterogeneous carrier, arbitrary orthonormal u, retained c₀ norm,
and explicit original norm-square identity.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace HilbertC0
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

theorem eventually_norm_head_lt (y : ℕ → C0Sum V)
    (hy : ∀ i, Tendsto (fun k => y k i) atTop (nhds 0)) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ‖C0Sum.head V n (y k)‖ < ε := by
  have he : ∀ᶠ k in atTop, ∀ i ∈ Finset.range n, ‖y k i‖ < ε / 2 := by
    apply (Filter.eventually_all_finset _).2
    intro i hi
    simpa only [norm_zero] using ((hy i).norm.eventually
      (eventually_lt_nhds (by simpa only [norm_zero] using half_pos hε)))
  filter_upwards [he] with k hk
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply C0Sum.norm_le (half_pos hε).le
  intro i
  rw [C0Sum.head_apply]
  split_ifs with hi
  · exact (hk i (Finset.mem_range.mpr hi)).le
  · simpa only [norm_zero] using (half_pos hε).le

theorem norm_head_sub_head_le (x : C0Sum V) {n m : ℕ} (hnm : n ≤ m) :
    ‖C0Sum.head V m x - C0Sum.head V n x‖ ≤ ‖x‖ := by
  apply C0Sum.norm_le (norm_nonneg _)
  intro i
  rw [C0Sum.sub_apply, C0Sum.head_apply, C0Sum.head_apply]
  by_cases hi : i < n
  · simp only [if_pos hi, if_pos (lt_of_lt_of_le hi hnm), sub_self, norm_zero]
    exact norm_nonneg x
  · by_cases him : i < m
    · simpa only [if_pos him, if_neg hi, sub_zero] using x.norm_apply_le i
    · simp only [if_neg him, if_neg hi, sub_self, norm_zero]; exact norm_nonneg x

theorem norm_sum_blocks_le (y : ℕ → C0Sum V) (n : ℕ → ℕ) (hn : StrictMono n)
    (C : ℝ) (hC : 0 ≤ C) (hy : ∀ j, ‖y j‖ ≤ C) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, (C0Sum.head V (n (j+1)) (y j) - C0Sum.head V (n j) (y j))‖ ≤ C := by
  classical
  apply C0Sum.norm_le hC
  intro i
  let z := fun j => C0Sum.head V (n (j+1)) (y j) - C0Sum.head V (n j) (y j)
  have hz (j : ℕ) : z j i = if n j ≤ i ∧ i < n (j+1) then y j i else 0 := by
    change C0Sum.head V (n (j+1)) (y j) i - C0Sum.head V (n j) (y j) i = _
    rw [C0Sum.head_apply, C0Sum.head_apply]
    have hj := hn (Nat.lt_succ_self j)
    split_ifs <;> simp_all <;> omega
  change ‖C0Sum.evalCLM V i (∑ j ∈ Finset.range J, z j)‖ ≤ C
  rw [map_sum]
  change ‖∑ j ∈ Finset.range J, z j i‖ ≤ C
  by_cases hex : ∃ j ∈ Finset.range J, n j ≤ i ∧ i < n (j+1)
  · obtain ⟨j, hj, hij⟩ := hex
    rw [Finset.sum_eq_single j]
    · rw [hz, if_pos hij]
      exact ((y j).norm_apply_le i).trans (hy j)
    · intro k hk hkj
      rw [hz, if_neg]
      intro hik
      rcases lt_or_gt_of_ne hkj with hkj | hjk
      · have h : n (k + 1) ≤ n j := hn.monotone (by omega)
        omega
      · have h : n (j + 1) ≤ n k := hn.monotone (by omega)
        omega
    · intro hj'; exact (hj' hj).elim
  · have hh : ∀ j ∈ Finset.range J, z j i = 0 := by
      intro j hj
      rw [hz, if_neg (by intro h; exact hex ⟨j, hj, h⟩)]
    simpa only [Finset.sum_eq_zero hh, norm_zero] using hC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sum_orthonormal_sq (u : ℕ → E) (hu : Orthonormal ℝ u)
    (k : ℕ → ℕ) (hk : Function.Injective k) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, u (k j)‖ ^ 2 = (N : ℝ) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  have hinner (j l : ℕ) : inner ℝ (u (k j)) (u (k l)) = if j = l then 1 else 0 := by
    rw [(orthonormal_iff_ite.mp hu) (k j) (k l)]
    simp only [hk.eq_iff]
  simp only [hinner]
  simp
  have hf : (Finset.range N).filter (fun j => j < N) = Finset.range N :=
    Finset.filter_eq_self.mpr (fun j hj => Finset.mem_range.mp hj)
  rw [hf, Finset.card_range]

theorem no_lower_of_coordinate_null (T : E →L[ℝ] C0Sum V) (u : ℕ → E) (hu : Orthonormal ℝ u)
    (hcoord : ∀ i, Tendsto (fun k => T (u k) i) atTop (nhds 0))
    (b : ℝ) (hb : 0 < b) (hlower : ∀ x, b * ‖x‖ ≤ ‖T x‖) : False := by
  classical
  let y := fun k => T (u k)
  have hnorm (k : ℕ) : ‖y k‖ ≤ ‖T‖ := by
    simpa only [y, hu.norm_eq_one, mul_one] using T.le_opNorm (u k)
  have step (j : ℕ) (p : ℕ × ℕ) : ∃ q : ℕ × ℕ, p.1 < q.1 ∧ p.2 < q.2 ∧
      ‖y q.1 - (C0Sum.head V q.2 (y q.1) - C0Sum.head V p.2 (y q.1))‖ ≤
        ApproximationParameters.weight 0 j := by
    have hw := ApproximationParameters.weight_pos 0 j
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      (eventually_norm_head_lt V y hcoord p.2 _ (half_pos hw))
    let k := max K (p.1+1)
    have hhead := hK k (le_max_left _ _)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
      ((C0Sum.tendsto_norm_tailCLM V (y k)).eventually (eventually_lt_nhds (half_pos hw)))
    let m := max M (p.2+1)
    have htail := hM m (le_max_left _ _)
    refine ⟨(k,m), by dsimp [k]; omega, by dsimp [m]; omega, ?_⟩
    have heq : y k - (C0Sum.head V m (y k) - C0Sum.head V p.2 (y k)) =
        C0Sum.tailCLM V m (y k) + C0Sum.head V p.2 (y k) := by
      change _ = (y k - C0Sum.head V m (y k)) + _
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  let next := fun j p => Classical.choose (step j p)
  let r : ℕ → ℕ × ℕ := fun j => Nat.rec (0,0) next j
  let k := fun j => (r (j+1)).1
  let n := fun j => (r j).2
  have hr (j : ℕ) : (r j).1 < (r (j+1)).1 ∧ n j < n (j+1) ∧
      ‖y (k j) - (C0Sum.head V (n (j+1)) (y (k j)) - C0Sum.head V (n j) (y (k j)))‖ ≤
        ApproximationParameters.weight 0 j := Classical.choose_spec (step j (r j))
  have hk : StrictMono k := strictMono_nat_of_lt_succ (fun j => (hr (j+1)).1)
  have hn : StrictMono n := strictMono_nat_of_lt_succ (fun j => (hr j).2.1)
  let z := fun j => C0Sum.head V (n (j+1)) (y (k j)) - C0Sum.head V (n j) (y (k j))
  have hbound (J : ℕ) : ‖T (∑ j ∈ Finset.range J, u (k j))‖ ≤ ‖T‖ + 1 := by
    rw [map_sum]
    change ‖∑ j ∈ Finset.range J, y (k j)‖ ≤ _
    have hsplit : (∑ j ∈ Finset.range J, y (k j)) =
        (∑ j ∈ Finset.range J, z j) + ∑ j ∈ Finset.range J, (y (k j) - z j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj; abel
    rw [hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact norm_sum_blocks_le V (fun j => y (k j)) n hn ‖T‖ (norm_nonneg T) (fun j => hnorm (k j)) J
    · apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum (fun j hj => (hr j).2.2)).trans
      have hs := (ApproximationParameters.weight_summable 0).sum_le_tsum (Finset.range J)
        (fun j hj => (ApproximationParameters.weight_pos 0 j).le)
      rw [ApproximationParameters.weights_sum] at hs
      exact hs.trans (ApproximationParameters.theta_le_one 0)
  obtain ⟨N, hN⟩ := exists_nat_gt (((‖T‖+1)/b)^2)
  have hlo := hlower (∑ j ∈ Finset.range N, u (k j))
  have hhi := hbound N
  have hsq := norm_sum_orthonormal_sq u hu k hk.injective N
  have hnle : ‖∑ j ∈ Finset.range N, u (k j)‖ ≤ (‖T‖+1)/b :=
    (le_div_iff₀ hb).mpr (by nlinarith)
  have hpos : 0 ≤ (‖T‖+1)/b := div_nonneg (by positivity) hb.le
  have hprod := mul_nonneg (sub_nonneg.mpr hnle)
    (add_nonneg hpos (norm_nonneg (∑ j ∈ Finset.range N, u (k j))))
  nlinarith

end HilbertC0
end BanachGeometry
