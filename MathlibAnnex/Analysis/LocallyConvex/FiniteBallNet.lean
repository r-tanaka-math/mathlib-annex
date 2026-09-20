import MathlibAnnex.Analysis.LocallyConvex.FiniteBallApproximation
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.MetricSpace.Basic

/-!
# A single directed net for an arbitrary set of representable finite tests

The index is finite test sets times accuracy.  Every sample uses the same
bidual point and its original norm bound. This is a net, not an unjustified
sequence replacement in a nonseparable weak-star topology.
C02 unbuilt proof-source candidate.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.FiniteApproximation

universe u v w
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type w} (Z : ι → Type v)
  [∀ i, NormedAddCommGroup (Z i)] [∀ i, NormedSpace ℝ (Z i)]

abbrev TestIndex (ι : Type w) := Finset ι × ℕ

/-- A positive accuracy for every index, including the initial index. -/
def testTolerance (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem testTolerance_pos (n : ℕ) : 0 < testTolerance n := by
  unfold testTolerance
  positivity

theorem testTolerance_antitone : Antitone testTolerance := by
  intro n m hnm
  unfold testTolerance
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
  exact one_div_le_one_div_of_le hn hcast

theorem exists_testTolerance_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, testTolerance n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n, ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < (n : ℝ) + 1 by positivity)).mpr
  have hh : (1 : ℝ) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  nlinarith

/-- One finite approximation problem at an index. -/
theorem exists_index_sample (F : StrongDual ℝ (StrongDual ℝ X))
    (T : ∀ i, X →L[ℝ] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    (d : TestIndex ι) :
    ∃ a : X, ‖a‖ ≤ ‖F‖ ∧ ∀ i ∈ d.1, ‖T i a - z i‖ < testTolerance d.2 := by
  classical
  obtain ⟨a, ha, he⟩ := exists_ball_finite_image_lt
    (fun i : d.1 => Z i) F (fun i => T i) (fun i => z i)
    (fun i g => hz i g) (testTolerance_pos d.2)
  exact ⟨a, ha, fun i hi => he ⟨i, hi⟩⟩

/-- Chosen only after the simultaneous finite existence theorem. -/
def ballSample (F : StrongDual ℝ (StrongDual ℝ X))
    (T : ∀ i, X →L[ℝ] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    (d : TestIndex ι) : X :=
  Classical.choose (exists_index_sample Z F T z hz d)

theorem ballSample_spec (F : StrongDual ℝ (StrongDual ℝ X))
    (T : ∀ i, X →L[ℝ] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    (d : TestIndex ι) :
    ‖ballSample Z F T z hz d‖ ≤ ‖F‖ ∧
      ∀ i ∈ d.1, ‖T i (ballSample Z F T z hz d) - z i‖ < testTolerance d.2 :=
  Classical.choose_spec (exists_index_sample Z F T z hz d)

/-- Every coordinate converges along the same directed set. -/
theorem tendsto_ballSample (F : StrongDual ℝ (StrongDual ℝ X))
    (T : ∀ i, X →L[ℝ] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    (i : ι) :
    Tendsto (fun d : TestIndex ι => T i (ballSample Z F T z hz d)) atTop (𝓝 (z i)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_testTolerance_lt hε
  filter_upwards [eventually_ge_atTop (({i} : Finset ι), n)] with d hd
  have hi : i ∈ d.1 := hd.1 (by simp)
  have he := (ballSample_spec Z F T z hz d).2 i hi
  have htol := testTolerance_antitone hd.2
  simpa only [dist_eq_norm] using he.trans_le (htol.trans hn.le)

end MathlibAnnex.FiniteApproximation
